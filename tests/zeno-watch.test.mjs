#!/usr/bin/env node
// Browser regression suite for viz/zeno-watch (Playwright + Chromium with software WebGL).
//   node tests/zeno-watch.test.mjs
// Reads page state through the read-only window.ZENO_DEBUG probe and checks it against independent
// implementations of the three models below. Exit code 1 lists the failed checks.
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
  const start = await page.evaluate(() => ZENO_DEBUG.frames());
  await page.waitForFunction((f0) => !ZENO_DEBUG.pending() && ZENO_DEBUG.frames() >= f0 + 2, start, { timeout: 20000 });
};
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => ZENO_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => ZENO_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => ZENO_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => ZENO_DEBUG.setFrac(f), f); await settle(); };
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const num = async (id) => parseFloat((await text(id)).replace(/[^0-9.eE+\-−]/g, '').replace('−', '-'));
const toastOn = async () => (await D(() => document.getElementById('toast').style.opacity)) === '1';
const close = (a, b, tol) => Math.abs(a - b) <= tol;

// --- independent implementations
// FREEZE: 2×2 density matrix in complex arithmetic: ρ → UρU† with U = exp(−i(δ/2)X), then the record multiplies the off-diagonals by η
function p1Complex(N, eta, T) {
  const steps = N || 1, d = T / steps, c = Math.cos(d / 2), s = Math.sin(d / 2);
  let rho = [[[1, 0], [0, 0]], [[0, 0], [0, 0]]];
  const U = [[[c, 0], [0, -s]], [[0, -s], [c, 0]]];
  const mul = (A, B) => A.map((row, i) => B[0].map((_, j) => row.reduce((acc, a, k) => [acc[0] + a[0] * B[k][j][0] - a[1] * B[k][j][1], acc[1] + a[0] * B[k][j][1] + a[1] * B[k][j][0]], [0, 0])));
  const dag = (A) => A[0].map((_, i) => A.map((row) => [row[i][0], -row[i][1]]));
  for (let k = 0; k < steps; k++) {
    rho = mul(mul(U, rho), dag(U));
    if (N) { rho[0][1] = rho[0][1].map((v) => v * eta); rho[1][0] = rho[1][0].map((v) => v * eta); }
  }
  return rho[1][1][0];
}
const h2 = (q) => (q <= 0 || q >= 1 ? 0 : -q * Math.log(q) - (1 - q) * Math.log(1 - q));
function rk4z(g, tEnd, n = 20000) {                                 // z̈ + γż + z = 0
  let z = 1, v = 0; const h = tEnd / n, f = (z, v) => [v, -g * v - z];
  for (let i = 0; i < n; i++) {
    const [k1z, k1v] = f(z, v), [k2z, k2v] = f(z + h / 2 * k1z, v + h / 2 * k1v), [k3z, k3v] = f(z + h / 2 * k2z, v + h / 2 * k2v), [k4z, k4v] = f(z + h * k3z, v + h * k3v);
    z += h / 6 * (k1z + 2 * k2z + 2 * k3z + k4z); v += h / 6 * (k1v + 2 * k2v + 2 * k3v + k4v);
  }
  return z;
}
// ANTI: direct quadrature of 2π∫J F_τ against the page's closed form
function gammaQuad(tt, a, G = 0.02) {
  const W = 3000, n = 600000; let s = 0;
  for (let i = 0; i < n; i++) { const w = -W + 2 * W * (i + 0.5) / n, J = G / Math.PI / ((w - a) ** 2 + 1), u = w * tt / 2, F = tt / (2 * Math.PI) * (Math.abs(u) < 1e-12 ? 1 : (Math.sin(u) / u) ** 2); s += J * F; }
  return 2 * Math.PI * s * 2 * W / n;
}

await page.goto(origin + BASE + 'viz/zeno-watch/');
await page.waitForTimeout(700);
check('no toast pops up at load', !(await toastOn()));
check('page loads without script errors', errors.length === 0, errors.join(' | '));
await pause();

// --- FREEZE: the law
let maxErr = 0;
for (const [N, eta, span] of [[4, 0, 1], [64, 0, 1], [17, 0.6, 1], [32, 0.35, 2.5], [9, 0.9, 0.75]]) {
  await setRange('span', span); await setRange('eta', eta); await setRange('looks', N);
  const p1 = (await D(() => ZENO_DEBUG.freeze())).p1;
  maxErr = Math.max(maxErr, Math.abs(p1 - p1Complex(N, eta, span * Math.PI)));
}
check('P₁(T) matches an independent density-matrix evolution for several N, η, T', maxErr < 1e-12, `max error ${maxErr.toExponential(1)}`);
await preset('itano');
{
  const vals = []; for (const N of [1, 2, 4, 8, 16, 32, 64]) vals.push([N, await D((N) => ZENO_DEBUG.p1Of(N, 'eta'), N)]);
  check('ideal projections: P₁(T) = (1 − cos^N(π/N))/2 for N = 1…64 (Itano protocol)', vals.every(([N, v]) => Math.abs(v - (1 - Math.cos(Math.PI / N) ** N) / 2) < 1e-12), vals.map(([N, v]) => `${N}:${v.toFixed(4)}`).join(' '));
  check('Itano preset reads 0.037 and 0.962', (await text('ro1')) === '0.037' && (await text('ro3')) === '0.962');
  const f = await D(() => ZENO_DEBUG.freeze()), q = Math.sin(Math.PI / 64 / 2) ** 2;
  check('flip probability per interval q = sin²(Ωδ/2)', Math.abs(f.q - q) < 1e-15);
  check('readouts: (1 − q)^N, bound κ²T²/N, entropy rate h₂(q)/δ, Fisher T²/N', close(await num('ro3'), (1 - q) ** 64, 6e-4) && close(await num('ro4'), Math.PI ** 2 / 256, 6e-4) && close(await num('ro5'), h2(q) / (Math.PI / 64), 6e-4) && close(await num('ro6'), Math.PI ** 2 / 64, 6e-4));
  let okBound = true; for (let N = 1; N <= 256; N++) { const leave = 1 - Math.cos(Math.PI / N / 2) ** (2 * N); if (leave > Math.min(1, Math.PI ** 2 / (4 * N)) + 1e-12) okBound = false; }
  check('the leaving probability never exceeds κ²T²/N (N = 1…256)', okBound);
  let bx = 0, bf = 0; for (let x = 0.5; x < 1.5; x += 1e-6) { const v = h2(Math.sin(x / 2) ** 2) / x; if (v > bf) { bf = v; bx = x; } }
  check('entropy-rate peak sits at Ωδ ≈ 0.9518 with value ≈ 0.5398 Ω (as quoted)', Math.abs(bx - 0.9518) < 5e-4 && Math.abs(bf - 0.5398) < 5e-4 && /0\.9518/.test(await text('roNote')), `${bx.toFixed(5)} ${bf.toFixed(5)}`);
  const ens = f.ens;
  check('ideal projection wipes the coherence at every refresh (y = 0 after each look)', ens.slice(1).every((b) => Math.abs(b[1]) < 1e-15));
  const single = f.single, outs = f.outcomes;
  check('the single run jumps to the pole it was found in', outs.length === 64 && single.slice(1).every((b, k) => b[0] === 0 && b[1] === 0 && b[2] === (outs[k] === 0 ? 1 : -1)));
}
await setRange('eta', 0.6);
{
  const f = await D(() => ZENO_DEBUG.freeze());
  let ok = true;
  for (let k = 1; k < f.ens.length; k++) { const [x, y, z] = f.ens[k - 1], d = f.delta, y1 = Math.cos(d) * y - Math.sin(d) * z; if (Math.abs(f.ens[k][1] - 0.6 * y1) > 1e-12) ok = false; }
  check('an incomplete record multiplies the coherence by η at each refresh', ok);
  const unit = f.single.every((b) => Math.abs(Math.hypot(...b) - 1) < 1e-12);
  check('with η > 0 the single run is a pure-state phase-kick unraveling (stays on the sphere)', unit && f.kicks.length === 64);
  check('incomplete records: per-look readouts are not defined', (await text('ro3')) === '—' && (await text('ro5')) === '—');
}
await preset('weak');
check('weak-looks preset: P₁(T) ≈ 0.23 as its note says', close(await num('ro1'), 0.226, 0.002) && /0\.23/.test(await text('presetNote')) && close(p1Complex(32, 0, Math.PI), 0.0716, 5e-4));
await preset('few');
check('four-looks preset: P₁(T) = 0.375 and q = sin²(π/8)', (await text('ro1')) === '0.375' && /15%/.test(await text('presetNote')));
await preset('free');
check('unwatched preset: full flip, no records', (await text('ro1')) === '1.000' && (await D(() => ZENO_DEBUG.freeze())).outcomes.length === 0);

// --- FREEZE: finite monitoring rate
await preset('rate');
{
  let maxZ = 0; for (const t of [0.5, 2, 5, 9]) maxZ = Math.max(maxZ, Math.abs((await D((t) => ZENO_DEBUG.zContinuum(t), t)) - rk4z(8, t)));
  check('continuous limit z̈ + γż + Ω²z = 0 matches an RK4 integration', maxZ < 1e-8, maxZ.toExponential(1));
  const zc = await D(() => ZENO_DEBUG.zContinuum(3 * Math.PI, 8)), p256 = await D(() => ZENO_DEBUG.p1Of(256, 'gamma')), p16 = await D(() => ZENO_DEBUG.p1Of(16, 'gamma'));
  check('with η = e^{−γδ}, more refreshes converge to the continuous limit instead of freezing', Math.abs(p256 - (1 - zc) / 2) < Math.abs(p16 - (1 - zc) / 2) && Math.abs(p256 - (1 - zc) / 2) < 0.01 && Math.abs((1 - zc) / 2 - (1 - Math.exp(-((8 - Math.sqrt(60)) / 2) * 3 * Math.PI)) / 2) < 0.01, `${p16.toFixed(4)} → ${p256.toFixed(4)} vs ${((1 - zc) / 2).toFixed(4)}`);
  const slow = (await D(() => ZENO_DEBUG.freeze())).slow;
  check('slow decay rate (γ − √(γ² − 4Ω²))/2 ≈ Ω²/γ', Math.abs(slow - (8 - Math.sqrt(60)) / 2) < 1e-12 && Math.abs(slow - 1 / 8) < 0.003 && (await text('ro5')) === slow.toFixed(3));
  const fixed = await D(() => ZENO_DEBUG.p1Of(256, 'eta'));
  check('with a fixed η each time, the same N freezes much harder', fixed < p256 / 3, `${fixed.toFixed(4)} vs ${p256.toFixed(4)}`);
}

// --- DRAG
await preset('drag');
{
  const d = await D(() => ZENO_DEBUG.drag()), th = Math.PI / 2;
  check('follow probability cos^{2N}(Θ/N) for N = 16, Θ = 90°', Math.abs(d.pFollow - Math.cos(th / 16) ** 32) < 1e-12 && /0\.86/.test(await text('presetNote')));
  // ending on the target, by a two-state Markov chain
  let pp = 1; const c2 = Math.cos(th / 16) ** 2; for (let j = 0; j < 16; j++) pp = pp * c2 + (1 - pp) * (1 - c2);
  check('chance of ending on the target matches a Markov chain', Math.abs(d.pOnTarget - pp) < 1e-12);
  let okB = true; for (let N = 1; N <= 256; N++) for (const deg of [10, 45, 90]) { const t = deg * Math.PI / 180, p = Math.cos(t / N) ** (2 * N); if (1 - p > t * t / N + 1e-12) okB = false; }
  check('1 − cos^{2N}(Θ/N) ≤ Θ²/N throughout', okB);
  let okS = true;
  for (let j = 0; j <= 16; j++) { const s = await D((t) => ZENO_DEBUG.dragAt(t), j + 0.5 > 16 ? 16 : j + 0.5); const sg = d.signs[j]; if (s.single.some((v, i) => Math.abs(v - sg * s.axis[i]) > 1e-12)) okS = false; }
  check('the dragged state sits along ±(current measurement axis) after each step', okS);
  const end = await D(() => ZENO_DEBUG.dragAt(16));
  check('the final axis is the orthogonal state |1⟩ on the Bloch sphere', Math.abs(end.axis[2] + 1) < 1e-12);
  check('drag ledger: first losses plus full success sum to 1', /1\.000000000000/.test(await text('ledgerNote')));
  {
    await setRange('looks', 4);
    const first = (await D(() => ZENO_DEBUG.drag())).signs.join(','), pf0 = (await D(() => ZENO_DEBUG.drag())).pFollow; let differs = false;
    for (let k = 0; k < 12 && !differs; k++) { await page.keyboard.press('r'); await settle(); differs = (await D(() => ZENO_DEBUG.drag())).signs.join(',') !== first; }
    check('R redraws the run: new outcomes, same law', differs && (await D(() => ZENO_DEBUG.drag())).pFollow === pf0);
  }
  await setRange('looks', 64);
  check('more steps, steadier drag', (await D(() => ZENO_DEBUG.drag())).pFollow > d.pFollow && (await D(() => ZENO_DEBUG.drag())).pFollow > 0.96);
}

// --- ANTI
await preset('anti');
{
  const a = await D(() => ZENO_DEBUG.anti());
  let rel = 0;
  for (const [tt, det] of [[0.4, 6], [0.05, 0], [3, 2], [0.02, 6]]) { const g = await D(([tt, det]) => ZENO_DEBUG.gammaTau(tt, det), [tt, det]); rel = Math.max(rel, Math.abs(g / gammaQuad(tt, det) - 1)); }
  check('closed-form Γ(τ) matches a direct quadrature of 2π∫J F_τ', rel < 1e-4, `max relative error ${rel.toExponential(1)}`);
  check('anti preset: measuring every 0.4/Λ speeds decay about 4.2-fold', a.regime === 'anti' && Math.abs(a.ratio - 4.166) < 0.01 && /4\.2/.test(await text('presetNote')) && /反芝诺/.test(await text('ro2')));
  const far = await D(() => ZENO_DEBUG.gammaTau(1e4, 6)), gr = a.gammaGR;
  check('rare measurements recover the golden rule Γ_GR = 2πJ(ω₀)', Math.abs(far / gr - 1) < 2e-3 && Math.abs(gr - 2 * Math.PI * (await D(() => ZENO_DEBUG.lorentz(0, 6)))) < 1e-15);
  let zenoOnly = true; for (let l = -2; l <= 2; l += 0.05) { if ((await D(([tt]) => ZENO_DEBUG.gammaTau(tt, 0), [10 ** l])) >= 2 * 0.02 * 0.999999) zenoOnly = false; }
  check('a resonant Lorentzian bath shows only the Zeno side (Γ < Γ_GR)', zenoOnly);
  check('the run is found decayed at a measurement time', Math.abs(a.decayWatched / a.tau - Math.round(a.decayWatched / a.tau)) < 1e-9);
}
await preset('decay');
{
  const a = await D(() => ZENO_DEBUG.anti());
  check('decay preset: Γ/Γ_GR ≈ 0.025, Zeno regime', a.regime === 'zeno' && Math.abs(a.ratio - 0.0246) < 5e-4 && /2\.5%/.test(await text('presetNote')));
}

// --- modes, controls, keys
await preset('itano');
const sectionVis = () => D(() => [...document.querySelectorAll('.deck [data-modes]')].map((el) => `${el.dataset.modes}:${el.hidden ? 0 : 1}`).join(','));
check('freeze mode shows the refresh and strength sections only', (await sectionVis()) === 'freeze drag:1,freeze:1,freeze:1,drag:0,anti:0');
await click('#modeChips [data-mode="drag"]');
check('drag mode shows the measurement path', (await sectionVis()) === 'freeze drag:1,freeze:0,freeze:0,drag:1,anti:0' && /跟上/.test(await text('roL1')));
await click('#modeChips [data-mode="anti"]');
check('anti-Zeno mode shows the bath controls', (await sectionVis()) === 'freeze drag:0,freeze:0,freeze:0,drag:0,anti:1' && /Γ/.test(await text('roL1')));
await page.mouse.click(5, 450);
await page.keyboard.press('1'); await settle();
check('key 1 returns to freeze', (await D(() => ZENO_DEBUG.state().mode)) === 'freeze');
await page.keyboard.press('2'); await settle();
check('key 2 switches to drag', (await D(() => ZENO_DEBUG.state().mode)) === 'drag');
await page.keyboard.press('3'); await settle();
check('key 3 switches to anti-Zeno', (await D(() => ZENO_DEBUG.state().mode)) === 'anti');
await preset('itano');
await click('#scaleChips [data-scale="gamma"]');
check('the γ chip swaps the η slider for γ', (await D(() => [document.getElementById('fieldEta').hidden, document.getElementById('fieldGamma').hidden].join())) === 'true,false');
await click('#scaleChips [data-scale="eta"]');
const h0 = await D(() => ZENO_DEBUG.hash()), o0 = (await D(() => ZENO_DEBUG.freeze())).outcomes.join('');
await page.keyboard.press('r'); await settle();
const h1 = await D(() => ZENO_DEBUG.hash()), o1 = (await D(() => ZENO_DEBUG.freeze())).outcomes.join('');
check('R draws a new run (new hash) with the same law', h1 !== h0 && (await text('ro1')) === '0.037', `${o0 === o1 ? 'same outcomes' : 'new outcomes'}`);
await setFrac(0.5);
const r0 = await D(() => ZENO_DEBUG.refreshes());
await page.keyboard.press('ArrowRight'); await settle();
const r1 = await D(() => ZENO_DEBUG.refreshes());
await page.keyboard.press('ArrowLeft'); await settle();
const r2 = await D(() => ZENO_DEBUG.refreshes());
check('→ and ← step exactly one refresh', r1 === r0 + 1 && r2 === r0, `${r0} → ${r1} → ${r2}`);
check('the record tape fills up to the refreshes done', r0 === 32);

// --- presets
for (const p of ['free', 'few', 'itano', 'weak', 'rate', 'drag', 'anti', 'decay']) {
  await page.click(`[data-preset="${p}"]`); await settle();
  check(`preset ${p} applies and explains itself`, (await D(() => ZENO_DEBUG.state().preset)) === p && (await text('presetNote')).length > 40);
}
await pause();

// --- transport
await preset('itano'); await setFrac(0.1);
await page.click('#play'); await waitFrames(4);
const f1 = await D(() => ZENO_DEBUG.t()); await waitFrames(12);
const f2 = await D(() => ZENO_DEBUG.t());
check('play advances time', f2 > f1);
await page.click('#rev'); await waitFrames(4);
const f3 = await D(() => ZENO_DEBUG.t()); await waitFrames(12);
const f4 = await D(() => ZENO_DEBUG.t());
check('reverse runs backwards', f4 < f3);
await page.click('#rev'); await pause();
await page.focus('#eta'); await page.keyboard.press('Space'); await page.waitForTimeout(150);
const playing = await D(() => ZENO_DEBUG.state().playing);
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await setRange('looks', 20);
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
for (const m of ['drag', 'anti']) { await click(`#modeChips [data-mode="${m}"]`); }
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /SPECTRAL PEAK ω_c/.test(tags), tags.slice(0, 160));
check('Greek labels keep their case', await D(() => getComputedStyle([...document.querySelectorAll('#tags .tag')].find(t => /ω_c/.test(t.textContent))).textTransform === 'none'));
check('readout labels are English in every mode', /Decay-rate ratio/.test(await text('roL1')));
check('English title', (await D(() => document.title)).startsWith('ZENO//WATCH · Quantum Zeno effect'));
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
await page.click('.card:has(a[href*="zeno-watch"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'zeno-watch');

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
