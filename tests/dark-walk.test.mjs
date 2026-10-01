#!/usr/bin/env node
// Browser regression suite for viz/dark-walk (Playwright + Chromium with software WebGL).
//   node tests/dark-walk.test.mjs
// Reads page state through the read-only window.DARK_DEBUG probe and checks it against an independent implementation:
// U = e^{iAτ} by scaling and squaring of the Taylor series (no eigen-decomposition), the first-detection protocol iterated
// directly, and the dark space read off the Lean characterization ker(I − (Q†)^d Q^d) and the survival limit.
import path from 'node:path';
import { createRequire } from 'node:module';
import { createServer, BASE } from '../scripts/serve.mjs';
import { readRegistry } from '../scripts/site.mjs';

async function loadPlaywright() {
  try { return await import('playwright'); } catch { /* fall back to a global install */ }
  const { execSync } = await import('node:child_process');
  return createRequire(path.join(execSync('npm root -g').toString().trim(), 'noop.js'))('playwright');
}
const { chromium } = await loadPlaywright();
const server = createServer(); await new Promise(r => server.listen(0, '127.0.0.1', r));
const origin = `http://127.0.0.1:${server.address().port}`;
const browser = await chromium.launch({ args: ['--use-angle=swiftshader', '--enable-unsafe-swiftshader', '--ignore-gpu-blocklist'] });
const results = [];
const check = (name, ok, detail = '') => { results.push({ name, ok, detail }); console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? '  — ' + detail : ''}`); };
const ctx = await browser.newContext({ viewport: { width: 1440, height: 900 }, locale: 'zh-CN' });
const page = await ctx.newPage();
const errors = [];
page.on('pageerror', e => errors.push(e.message));
page.on('console', m => { if (m.type() === 'error' && !/ERR_CERT|fonts\.g/.test(m.text())) errors.push('console: ' + m.text()); });
const D = (expr, arg) => page.evaluate(expr, arg);
const settle = async () => {
  const start = await page.evaluate(() => DARK_DEBUG.frames());
  await page.waitForFunction((f0) => !DARK_DEBUG.pending() && DARK_DEBUG.frames() >= f0 + 2, start, { timeout: 20000 });
};
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => DARK_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => DARK_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => DARK_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => DARK_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => DARK_DEBUG.info());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const toastOn = async () => (await D(() => document.getElementById('toast').style.opacity)) === '1';

// --- independent implementation (complex matrices as {re, im} arrays of rows)
const zeros = (n) => ({ re: Array.from({ length: n }, () => new Array(n).fill(0)), im: Array.from({ length: n }, () => new Array(n).fill(0)) });
const eye = (n) => { const m = zeros(n); for (let i = 0; i < n; i++) m.re[i][i] = 1; return m; };
function mul(A, B) {
  const n = A.re.length, C = zeros(n);
  for (let i = 0; i < n; i++) for (let k = 0; k < n; k++) { const ar = A.re[i][k], ai = A.im[i][k]; if (!ar && !ai) continue; for (let j = 0; j < n; j++) { C.re[i][j] += ar * B.re[k][j] - ai * B.im[k][j]; C.im[i][j] += ar * B.im[k][j] + ai * B.re[k][j]; } }
  return C;
}
const add = (A, B, s = 1) => ({ re: A.re.map((r, i) => r.map((v, j) => v + s * B.re[i][j])), im: A.im.map((r, i) => r.map((v, j) => v + s * B.im[i][j])) });
const scale = (A, s) => ({ re: A.re.map((r) => r.map((v) => v * s)), im: A.im.map((r) => r.map((v) => v * s)) });
const dag = (A) => ({ re: A.re.map((r, i) => r.map((_, j) => A.re[j][i])), im: A.im.map((r, i) => r.map((_, j) => -A.im[j][i])) });
function adjacency(graph, N) { const A = Array.from({ length: N }, () => new Array(N).fill(0)); const e = (i, j) => { A[i][j] = 1; A[j][i] = 1; }; if (graph === 'ring') for (let i = 0; i < N; i++) e(i, (i + 1) % N); else for (let i = 0; i + 1 < N; i++) e(i, i + 1); return A; }
const detectorOf = (graph, N) => (graph === 'mid' ? Math.floor((N - 1) / 2) : 0);
function expm(Mre, Mim) {                                   // e^{M} by scaling and squaring of a 30-term Taylor series
  const n = Mre.length; let s = 0; let nrm = 0; for (const r of Mre) for (const v of r) nrm = Math.max(nrm, Math.abs(v)); for (const r of Mim) for (const v of r) nrm = Math.max(nrm, Math.abs(v));
  while (nrm * n / 2 ** s > 0.5) s++;
  const M = { re: Mre.map((r) => r.map((v) => v / 2 ** s)), im: Mim.map((r) => r.map((v) => v / 2 ** s)) };
  let term = eye(n), sum = eye(n);
  for (let k = 1; k <= 30; k++) { term = scale(mul(term, M), 1 / k); sum = add(sum, term); }
  for (let i = 0; i < s; i++) sum = mul(sum, sum);
  return sum;
}
function walkU(graph, N, tau) { const A = adjacency(graph, N); return expm(A.map((r) => r.map(() => 0)), A.map((r) => r.map((v) => v * tau))); }   // e^{iAτ}
function firstDetection(U, d, psi, rounds) {
  const n = U.re.length; let re = psi.slice(), im = new Array(n).fill(0); const F = [0], S = [1];
  for (let k = 1; k <= rounds; k++) {
    const r2 = new Array(n).fill(0), i2 = new Array(n).fill(0);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) { r2[i] += U.re[i][j] * re[j] - U.im[i][j] * im[j]; i2[i] += U.re[i][j] * im[j] + U.im[i][j] * re[j]; }
    F.push(r2[d] ** 2 + i2[d] ** 2); r2[d] = 0; i2[d] = 0; re = r2; im = i2; S.push(re.reduce((s, v, x) => s + v * v + im[x] ** 2, 0));
  }
  return { F, S };
}
function noClick(U, d) { const Q = { re: U.re.map((r) => r.slice()), im: U.im.map((r) => r.slice()) }; Q.re[d] = Q.re[d].map(() => 0); Q.im[d] = Q.im[d].map(() => 0); return Q; }
function matPow(A, k) { let R = eye(A.re.length), B = A; while (k > 0) { if (k & 1) R = mul(R, B); B = mul(B, B); k >>= 1; } return R; }
const applyReal = (A, v) => A.re.map((r, i) => [r.reduce((s, a, j) => s + a * v[j], 0), A.im[i].reduce((s, a, j) => s + a * v[j], 0)]);
const loc = (N, x) => Array.from({ length: N }, (_, i) => (i === x ? 1 : 0));

await page.goto(origin + BASE + 'viz/dark-walk/');
await page.waitForTimeout(700);
check('no toast pops up at load', !(await toastOn()));
check('page loads without script errors', errors.length === 0, errors.join(' | '));
await pause();

// --- the law against the independent implementation
let i = await info();
{
  const U = walkU('ring', 8, 1), ref = firstDetection(U, 0, loc(8, 3), i.R);
  const err = Math.max(...ref.F.map((f, k) => Math.abs(f - i.F[k])), ...ref.S.map((s, k) => Math.abs(s - i.S[k])));
  check('first-click law F_n and survival S_n match direct iteration with e^{iAτ} from a Taylor series', err < 1e-10, `max error ${err.toExponential(1)} over ${i.R} rounds`);
  check('Σ_{n≤N} F_n + S_N = 1 at every round', i.F.every((_, N) => Math.abs(i.F.slice(1, N + 1).reduce((a, b) => a + b, 0) + i.S[N] - 1) < 1e-12));
  const long = firstDetection(U, 0, loc(8, 3), 20000);
  check('half-dark preset: survival tends to P_dark = 1/2', Math.abs(long.S[20000] - 0.5) < 1e-6 && Math.abs(i.pDark - 0.5) < 1e-12 && Math.abs(i.pDet - 0.5) < 1e-12);
  { let m = 0, c = 0; long.F.forEach((f, k) => { m += k * f; c += f; });
    check('the mean click round given a click is the whole infinite series, not the shown window', Math.abs(i.meanRound - m / c) < 1e-6 && i.R < 200, `page ${i.meanRound.toFixed(6)}, 20000-round iteration ${(m / c).toFixed(6)}, window ${i.R}`); }
  // the dark space through the Lean characterizations: S_K = (Q†)^K Q^K → P_D, and ker(I − (Q†)^d Q^d)
  const Q = noClick(U, 0), QK = matPow(Q, 4096), SK = mul(dag(QK), QK);
  const trace = SK.re.reduce((s, r, k) => s + r[k], 0);
  check('dim 𝒟 equals the trace of the survival limit (Q†)^K Q^K', Math.abs(trace - i.darkDim) < 1e-6 && i.darkDim === 3, `trace ${trace.toFixed(6)}, page ${i.darkDim}`);
  const Qd = matPow(Q, 8), G = add(eye(8), mul(dag(Qd), Qd), -1);
  const ghost = await D(() => DARK_DEBUG.ghostAt(0)), dark = ghost.re;
  const Gd = applyReal(G, dark), GdNorm = Math.hypot(...Gd.flat());
  const bright = loc(8, 3).map((v, x) => v - dark[x]), Gb = applyReal(G, bright), GbNorm = Math.hypot(...Gb.flat());
  check('the page’s dark part lies in ker(I − (Q†)^d Q^d), the bright part does not', GdNorm < 1e-9 && GbNorm > 0.1 && Math.abs(dark.reduce((s, v) => s + v * v, 0) - 0.5) < 1e-12, `‖G·dark‖ ${GdNorm.toExponential(1)}, ‖G·bright‖ ${GbNorm.toFixed(3)}`);
  const g0 = await D(() => DARK_DEBUG.ghostAt(0)), g5 = await D(() => DARK_DEBUG.ghostAt(5));
  check('the dark part keeps its norm and has zero amplitude at the detector at every check', Math.abs(g5.re.reduce((s, v, x) => s + v * v + g5.im[x] ** 2, 0) - 0.5) < 1e-12 && Math.hypot(g5.re[0], g5.im[0]) < 1e-12 && Math.hypot(g0.re[0], g0.im[0]) < 1e-12);
}
{
  const Ucl = (() => { const A = adjacency('ring', 8), L = A.map((r, a) => r.map((v, b) => (a === b ? -r.reduce((s, x) => s + x, 0) : v))); return expm(L, L.map((r) => r.map(() => 0))); })();
  let p = loc(8, 3), S = [1];
  for (let k = 1; k <= i.R; k++) { const q = Ucl.re.map((r) => r.reduce((s, a, j) => s + a * p[j], 0)); q[0] = 0; p = q; S.push(p.reduce((s, v) => s + v, 0)); }
  const err = Math.max(...S.map((s, k) => Math.abs(s - i.classical.S[k])));
  check('classical random walk survival matches e^{Lτ} from a Taylor series, and keeps falling', err < 1e-10 && i.classical.S[i.R] < 0.1 && i.classical.S.every((s, k) => k === 0 || s <= i.classical.S[k - 1] + 1e-15), `max error ${err.toExponential(1)}`);
}

// --- presets and their claims
await preset('ret'); i = await info();
check('return preset: P_det = 1 and the mean return round is the integer 5 (= distinct eigenphases)', Math.abs(i.pDet - 1) < 1e-12 && i.returnCase && i.brightGroups === 5 && Math.abs(i.meanRound - 5) < 2e-3 && (await text('ro6')) === '5', `mean ${i.meanRound.toFixed(5)}`);
await preset('two'); i = await info();
check('two-paths preset (three-site chain, detector in the middle): P_det = 1/2', Math.abs(i.pDet - 0.5) < 1e-12 && i.d === 1 && i.darkDim === 1);
{ const ref = firstDetection(walkU('mid', 3, 1), 1, loc(3, 0), 6000); check('…and the long-run survival agrees', Math.abs(ref.S[6000] - 0.5) < 1e-6); }
await preset('chain'); i = await info();
check('chain-end preset: no dark state, always detected', Math.abs(i.pDet - 1) < 1e-12 && i.darkDim === 0);
await preset('darkstart'); i = await info();
check('dark-start preset: never detected, not even a little', i.pDet < 1e-12 && i.F.every((f) => f < 1e-20) && /一轮也不会响/.test(await text('presetNote')));
await preset('special'); i = await info();
{
  const tau = 2 * Math.PI / (2 + Math.SQRT2), ref = firstDetection(walkU('ring', 8, tau), 0, loc(8, 1), 20000);
  check('special-τ preset: P_det ≈ 0.014 at τ = 2π/(2+√2), confirmed by long iteration', Math.abs(i.pDet - 0.0143) < 2e-4 && Math.abs((1 - ref.S[20000]) - i.pDet) < 1e-6 && /1\.4%/.test(await text('presetNote')), `page ${i.pDet.toFixed(5)}, iteration ${(1 - ref.S[20000]).toFixed(5)}`);
  check('the special interval is flagged on the page', /✦/.test(await text('oTau')) && /特殊间隔/.test(await text('tauNote')));
}
await setRange('tau', 1.9);
check('nudging τ off the special interval restores P_det = 1/2', Math.abs((await info()).pDet - 0.5) < 1e-12);
await preset('alldark'); i = await info();
{
  const ref = firstDetection(walkU('ring', 6, 4 * Math.PI / 3), 0, loc(6, 1), 4000);
  check('all-dark preset: P_det = 0 on the six-site ring at τ = 4π/3', i.pDet < 1e-12 && 1 - ref.S[4000] < 1e-9);
}
await preset('zeno'); i = await info();
{
  const fast = firstDetection(walkU('ring', 8, 1), 0, loc(8, 4), 4000); let m = 0, c = 0; fast.F.forEach((f, k) => { m += k * f; c += f; });
  check('too-often preset: still P_det = 1, but about 400 rounds on average (vs about 4.8 at τ = 1)', Math.abs(i.pDet - 1) < 1e-12 && Math.abs(i.meanRound - 400) < 6 && Math.abs(m / c - 4.77) < 0.01 && /400/.test(await text('presetNote')), `${i.meanRound.toFixed(2)} vs ${(m / c).toFixed(3)} rounds`);
}

// --- special intervals: list, snapping, and π/√2 on the ring of 8
await preset('half'); i = await info();
{
  const expect = [Math.PI / 2, 2 * Math.PI / (2 + Math.SQRT2), Math.PI / Math.SQRT2, Math.PI, 4 * Math.PI / (2 + Math.SQRT2), Math.SQRT2 * Math.PI, 3 * Math.PI / 2];
  check('special intervals of the ring of 8 (τ ≤ 5)', i.specials.length === expect.length && i.specials.every(([t], k) => Math.abs(t - expect[k]) < 1e-9), i.specials.map(([t]) => t.toFixed(4)).join(' '));
  const ref = firstDetection(walkU('ring', 8, Math.PI / Math.SQRT2), 0, loc(8, 3), 20000);
  const sp = i.specials.find(([t]) => Math.abs(t - Math.PI / Math.SQRT2) < 1e-9);
  check('at τ = π/√2 the √2 and −√2 groups merge: P_det drops to 1/4, confirmed by iteration', Math.abs(sp[1] - 0.25) < 1e-12 && Math.abs((1 - ref.S[20000]) - 0.25) < 1e-6);
  const generic = i.scan.filter(([t]) => !i.specials.some(([s]) => Math.abs(s - t) < 1e-6));
  check('away from special intervals, P_det does not depend on τ', generic.every(([, p]) => Math.abs(p - 0.5) < 1e-9));
}
await setRange('tau', 1.57);
check('the τ slider snaps onto a nearby special interval', Math.abs((await D(() => DARK_DEBUG.state().tau)) - Math.PI / 2) < 1e-12 && Math.abs((await info()).pDet - 0.25) < 1e-12);
await click('#specialChips .chip:nth-child(4)');
check('a ✦ chip jumps to its special interval', Math.abs((await D(() => DARK_DEBUG.state().tau)) - Math.PI) < 1e-9);

// --- initial-state parts
await preset('half');
await click('#partChips [data-part="bright"]');
check('bright part only: always detected', Math.abs((await info()).pDet - 1) < 1e-12);
await click('#partChips [data-part="dark"]');
check('dark part only: never detected', (await info()).pDet < 1e-12);
await setRange('start', 0);
check('the detector site has no dark part: the page falls back to |x₀⟩ and says so', (await info()).partEmpty && /没有这一部分/.test(await text('startNote')));
await click('#partChips [data-part="all"]');

// --- graph controls, picking, ledger, run, keys
await click('#graphChips [data-graph="end"]');
check('chain with an end detector has no dark space', (await info()).darkDim === 0 && /一端/.test(await text('graphNote')));
await click('#graphChips [data-graph="ring"]');
await setRange('sites', 12);
check('the start slider follows N', (await D(() => document.getElementById('start').max)) === '11');
await preset('half'); await setFrac(0.5);
{
  const sb = await page.locator('#stage').boundingBox(), p = await D(() => DARK_DEBUG.project(5));
  await page.mouse.click(sb.x + p.x, sb.y + p.y); await settle();
  check('clicking a site in 3D makes it the start', (await D(() => DARK_DEBUG.state().x0)) === 5);
}
check('ledger: detected so far plus survival = 1', /1\.000000000000/.test(await text('ledgerNote')));
await preset('half');
{
  const h0 = (await info()).hash; let found = false;
  for (let k = 0; k < 12 && !found; k++) { await page.keyboard.press('r'); await settle(); found = (await info()).fate === 'click'; }
  const j = await info();
  check('R draws a new run; some runs click, and the fate follows the draw', found && j.hash !== h0 && j.nStar >= 1 && j.nStar <= j.R);
  await setFrac(0); await page.click('#play');
  await page.waitForFunction(() => DARK_DEBUG.info().round >= DARK_DEBUG.info().nStar, null, { timeout: 30000 }); await waitFrames(3);
  check('the click toast announces the round of the first click', new RegExp(`${j.nStar}`).test(await text('toast')) && /点击/.test(await text('toast')));
  await pause();
}
await setFrac(0.3);
const r0 = (await info()).round;
await page.mouse.click(5, 450);
await page.keyboard.press('ArrowRight'); await settle();
const r1 = (await info()).round;
await page.keyboard.press('ArrowLeft'); await settle();
const r2 = (await info()).round;
check('→ and ← step exactly one round', r1 === r0 + 1 && r2 === r0, `${r0} → ${r1} → ${r2}`);
const c0 = await D(() => DARK_DEBUG.state().classical);
await page.keyboard.press('c'); await settle();
check('C toggles the classical comparison', (await D(() => DARK_DEBUG.state().classical)) === !c0);
await page.keyboard.press('c'); await settle();

// --- presets
for (const p of ['ret', 'half', 'two', 'chain', 'darkstart', 'special', 'alldark', 'zeno']) {
  await page.click(`[data-preset="${p}"]`); await settle();
  check(`preset ${p} applies and explains itself`, (await D(() => DARK_DEBUG.state().preset)) === p && (await text('presetNote')).length > 40);
}
await pause();

// --- transport
await preset('half'); await setFrac(0.1);
await page.click('#play'); await waitFrames(4);
const f1 = (await D(() => DARK_DEBUG.state().nowFrac)); await waitFrames(12);
const f2 = (await D(() => DARK_DEBUG.state().nowFrac));
check('play advances the rounds', f2 > f1);
await page.click('#rev'); await waitFrames(4);
const f3 = (await D(() => DARK_DEBUG.state().nowFrac)); await waitFrames(12);
const f4 = (await D(() => DARK_DEBUG.state().nowFrac));
check('reverse runs backwards', f4 < f3);
await page.click('#rev'); await pause();
await page.focus('#tau'); await page.keyboard.press('Space'); await page.waitForTimeout(150);
const playing = await D(() => DARK_DEBUG.state().playing);
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await setRange('sites', 10);
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /DETECTOR/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('DARK//WALK · First detection and dark states'));
await page.click('#infoBtn'); await page.waitForTimeout(200);
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
await page.keyboard.press('Escape'); await page.waitForTimeout(150);
check('Esc closes the drawer', (await D(() => document.getElementById('drawer').hidden)) === true);
check('focus returns to the drawer button', (await D(() => document.activeElement?.id)) === 'infoBtn');

// --- index round trip
const live = readRegistry().visualizations.filter(v => v.status === 'live').length;
await page.click('.crumb'); await page.waitForLoadState('load'); await page.waitForTimeout(800);
check('language choice carries to the index', (await D(() => document.documentElement.dataset.lang)) === 'en');
check('index lists every live visualization', (await D(() => document.querySelectorAll('.card').length)) === live, `live ${live}`);
await page.click('.card:has(a[href*="dark-walk"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'dark-walk');

// --- narrow layouts in both languages
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await page.waitForTimeout(300);
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await page.waitForTimeout(700);
    check(`no horizontal scroll at ${w}px (${lang})`, (await D(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 }); await page.waitForTimeout(300);
}
check('no script errors during the whole session', errors.length === 0, errors.join(' | '));

const failed = results.filter(r => !r.ok);
console.log(`\n${results.length - failed.length}/${results.length} passed`);
await browser.close(); server.close();
if (failed.length) process.exit(1);
