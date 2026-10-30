#!/usr/bin/env node
// Browser regression suite for viz/qaoa-support (Playwright + Chromium with software WebGL).
//   node tests/qaoa-support.test.mjs
// Reads page state through the read-only window.QS_DEBUG probe and checks it against an independent implementation: the 8×8
// mixer B = Σ Xⱼ built as a matrix, e^(−iβB) by scaling and squaring of its Taylor series in complex arithmetic, the state
// formed by matrix–vector products, the closed-form zero lattice of Lean’s energy derived by hand, and an independent search
// for zeros on a finer grid refined by Nelder–Mead. Fixed reference data: the frozen amplitude −(1 + i)e^(iπ/8)/√8.
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
  const start = await page.evaluate(() => QS_DEBUG.frames());
  await page.waitForFunction((f0) => !QS_DEBUG.pending() && QS_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => QS_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => QS_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => QS_DEBUG.info());
const state = () => D(() => QS_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => QS_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => QS_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 120000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
const N = 8, bitOf = (x, j) => (x >> j) & 1;
const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const matmul = (A, B) => A.map((row, i) => B[0].map((_, j) => row.reduce((s, a, k) => { const p = cmul(a, B[k][j]); return [s[0] + p[0], s[1] + p[1]]; }, [0, 0])));
const Bmix = Array.from({ length: N }, (_, x) => Array.from({ length: N }, (_, y) => { const d = x ^ y; return d === 1 || d === 2 || d === 4 ? 1 : 0; }));
/* e^(−iβB) by scaling and squaring of the Taylor series */
function expMix(beta) {
  const s = 6, h = beta / 2 ** s, M = Bmix.map((r) => r.map((v) => [0, -h * v]));
  let E = Array.from({ length: N }, (_, i) => Array.from({ length: N }, (_, j) => [+(i === j), 0])), term = E.map((r) => r.map((v) => v.slice()));
  for (let k = 1; k <= 24; k++) { term = matmul(term, M).map((r) => r.map(([a, b]) => [a / k, b / k])); E = E.map((r, i) => r.map((v, j) => [v[0] + term[i][j][0], v[1] + term[i][j][1]])); }
  for (let t = 0; t < s; t++) E = matmul(E, E);
  return E;
}
function stateOf(energy, beta, gamma) {
  const phi = energy.map((ev) => [Math.cos(-gamma * ev) / Math.sqrt(8), Math.sin(-gamma * ev) / Math.sqrt(8)]), E = expMix(beta);
  return E.map((row) => row.reduce((s, a, k) => { const p = cmul(a, phi[k]); return [s[0] + p[0], s[1] + p[1]]; }, [0, 0]));
}
const mag = (z) => Math.hypot(z[0], z[1]);
const LEAN = Array.from({ length: N }, (_, x) => (bitOf(x, 0) !== bitOf(x, 1) ? Math.PI / 2 : 2 * Math.PI));
const TRI = Array.from({ length: N }, (_, x) => (bitOf(x, 0) ^ bitOf(x, 1)) + (bitOf(x, 1) ^ bitOf(x, 2)) + (bitOf(x, 0) ^ bitOf(x, 2)));
/* a fast amplitude for the zero search (same physics, product over qubits written directly) */
function ampFast(energy, x, b, g) {
  let re = 0, im = 0; const c = Math.cos(b), s = Math.sin(b);
  for (let y = 0; y < N; y++) { let fr = [1, 0]; for (let j = 0; j < 3; j++) fr = cmul(fr, bitOf(x, j) === bitOf(y, j) ? [c, 0] : [0, -s]); const p = cmul(fr, [Math.cos(-g * energy[y]), Math.sin(-g * energy[y])]); re += p[0]; im += p[1]; }
  return Math.hypot(re, im) / Math.sqrt(8);
}
function nelderMead(f, p0, step) {
  let simplex = [p0, [p0[0] + step, p0[1]], [p0[0], p0[1] + step]].map((p) => ({ p, v: f(p) }));
  for (let it = 0; it < 400; it++) {
    simplex.sort((a, b) => a.v - b.v);
    const [best, mid, worst] = simplex, c = [(best.p[0] + mid.p[0]) / 2, (best.p[1] + mid.p[1]) / 2];
    const at = (t) => { const p = [c[0] + t * (worst.p[0] - c[0]), c[1] + t * (worst.p[1] - c[1])]; return { p, v: f(p) }; };
    const r = at(-1);
    if (r.v < best.v) { const e = at(-2); simplex[2] = e.v < r.v ? e : r; }
    else if (r.v < mid.v) simplex[2] = r;
    else { const k = at(0.5); if (k.v < worst.v) simplex[2] = k; else simplex = simplex.map((q, i) => (i ? { p: [(q.p[0] + best.p[0]) / 2, (q.p[1] + best.p[1]) / 2], v: f([(q.p[0] + best.p[0]) / 2, (q.p[1] + best.p[1]) / 2]) } : q)); }
  }
  simplex.sort((a, b) => a.v - b.v); return simplex[0];
}
function searchZeros(energy) {
  const NBb = 320, NGg = 640, found = [];
  for (let x = 0; x < N; x++) {
    const A = new Float64Array(NBb * (NGg + 1));
    for (let i = 0; i < NBb; i++) for (let j = 0; j <= NGg; j++) A[i * (NGg + 1) + j] = ampFast(energy, x, Math.PI * i / NBb, 2 * Math.PI * j / NGg);
    for (let i = 0; i < NBb; i++) for (let j = 0; j <= NGg; j++) {
      const v = A[i * (NGg + 1) + j]; if (v > 0.05) continue;
      let low = true; for (const [di, dj] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) { const ii = (i + di + NBb) % NBb, jj = j + dj; if (jj < 0 || jj > NGg) continue; if (A[ii * (NGg + 1) + jj] < v) low = false; }
      if (!low) continue;
      const r = nelderMead((p) => ampFast(energy, x, p[0], p[1]) ** 2, [Math.PI * i / NBb, 2 * Math.PI * j / NGg], 0.004);
      if (r.v > 1e-16) continue;
      const b = ((r.p[0] % Math.PI) + Math.PI) % Math.PI, g = r.p[1];
      if (g < -1e-6 || g > 2 * Math.PI + 1e-6) continue;
      if (!found.some((q) => q.x === x && Math.abs(q.b - b) < 1e-4 && Math.abs(q.g - g) < 1e-4)) found.push({ x, b, g });
    }
  }
  return found;
}
const close = (a, b, t = 1e-12) => Math.abs(a - b) < t;

/* ---------- load ---------- */
await page.goto(origin + BASE + 'viz/qaoa-support/');
await page.waitForFunction(() => window.QS_DEBUG && QS_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let st = await state(), i = await info();
check('opens on the frozen counterexample (Lean’s energy, β = π/8, γ = 1, paused)', st.preset === 'lean' && i.e === 'lean' && close(i.beta, Math.PI / 8) && i.g === 1 && st.playing === false);
check('Lean’s energy is π/2 where the first two bits differ and 2π elsewhere', i.energy.every((v, x) => close(v, LEAN[x])));
const ref = stateOf(LEAN, Math.PI / 8, 1), coef = cmul([-1 / Math.sqrt(8), -1 / Math.sqrt(8)], [Math.cos(Math.PI / 8), Math.sin(Math.PI / 8)]);
check('the page’s amplitudes equal the matrix-exponential state to 10⁻¹²', i.amps.every((a, x) => close(a[0], ref[x][0]) && close(a[1], ref[x][1])));
check('…and the frozen output: 0 when x₀ = x₁, −(1 + i)e^(iπ/8)/√8 otherwise', i.amps.every((a, x) => (bitOf(x, 0) === bitOf(x, 1) ? mag(a) < 1e-15 : close(a[0], coef[0], 1e-15) && close(a[1], coef[1], 1e-15))));
const ro3 = await text('ro3');
check('support 4 = {010, 011, 100, 101}, between 2 and 8', i.support === 4 && /4 · 2 < 4 < 8/.test(ro3) && ['010', '011', '100', '101'].every((s) => ro3.includes(s)) && !['000', '001', '110', '111'].some((s) => ro3.includes(s)), ro3);

/* ---------- zeros ---------- */
const zLean = i.zeros;
const lattice = []; for (let j = 0; j < 4; j++) for (let k = 0; (2 * k + 1) / 3 <= 2 * Math.PI; k++) lattice.push([(2 * j + 1) * Math.PI / 8, (2 * k + 1) / 3]);
check('Lean’s energy: the zeros are exactly the lattice β = (2j + 1)π/8, γ = (2k + 1)/3 (36 points), each removing 4 amplitudes', zLean.length === 36 && lattice.length === 36 && lattice.every(([b, g]) => zLean.some((z) => close(z.b, b, 1e-9) && close(z.g, g, 1e-9) && z.xs.length === 4 && z.support === 4)), `${zLean.length}`);
check('every zero of Lean’s energy is a true zero of the independent state and leaves exactly its 4 survivors', zLean.every((z) => { const s = stateOf(LEAN, z.b, z.g); return s.every((a, x) => (z.xs.includes(x) ? mag(a) < 1e-10 : mag(a) > 1e-3)); }));
const own = searchZeros(LEAN);
check('an independent finer grid search with Nelder–Mead finds the same 144 amplitude zeros', own.length === 144 && own.every((q) => zLean.some((z) => z.xs.includes(q.x) && Math.abs(z.b - q.b) < 1e-4 && Math.abs(z.g - q.g) < 1e-4)), `${own.length}`);
await preset('sweep'); i = await info();
check('sweep: at γ = 1 the zeros along β are π/8, 3π/8, 5π/8, 7π/8, alternating between the two groups of four', i.onLine.length === 4 && i.onLine.every((z, j) => close(z.b, (2 * j + 1) * Math.PI / 8, 1e-9) && z.xs.join() === (j % 2 ? '1,2,5,6' : '0,3,4,7')));
await preset('miss'); i = await info();
check('miss: at γ = 0.9, β = π/8 the cancelled amplitudes come back to ≈ 0.117 and the support is 8', i.support === 8 && i.mags.filter((m) => Math.abs(m - 0.117) < 0.0005).length === 4 && close(Math.min(...i.mags), Math.min(...stateOf(LEAN, Math.PI / 8, 0.9).map(mag))), `${Math.min(...i.mags)}`);
await preset('tri'); i = await info();
const triRef = stateOf(TRI, i.beta, i.g);
check('triangle MaxCut: the energy is the number of cut edges (0 on 000 and 111, 2 elsewhere)', i.energy.every((v, x) => v === TRI[x]));
check('tri preset: |000⟩ and |111⟩ vanish at (β, γ) ≈ (0.3077, 0.6155) and the other 6 do not (support 6)', Math.abs(i.beta - 0.3077) < 5e-5 && Math.abs(i.g - 0.6155) < 5e-5 && mag(triRef[0]) < 1e-10 && mag(triRef[7]) < 1e-10 && triRef.slice(1, 7).every((a) => mag(a) > 0.1) && i.support === 6, `${i.beta} ${i.g}`);
check('triangle MaxCut at β = π/4, γ = π/2 keeps only |000⟩ and |111⟩ (support 2), and the page lists that zero', (() => { const s = stateOf(TRI, Math.PI / 4, Math.PI / 2); return s.every((a, x) => ((x === 0 || x === 7) ? mag(a) > 0.7 : mag(a) < 1e-10)); })() && i.zeros.some((z) => close(z.b, Math.PI / 4, 1e-6) && close(z.g, Math.PI / 2, 1e-6) && z.support === 2));   // a degenerate zero (|ψ| vanishes to second order), so Newton's position is only good to ~10⁻⁸
check('every listed zero of the triangle energy is a true zero of the independent state', i.zeros.every((z) => { const s = stateOf(TRI, z.b, z.g); return s.every((a, x) => (z.xs.includes(x) ? mag(a) < 1e-10 : mag(a) > 1e-3)) && z.support === 8 - z.xs.length; }), `${i.zeros.length} zeros`);
const ownTri = searchZeros(TRI), zTriCount = i.zeros.reduce((s, z) => s + z.xs.length, 0);
check('the independent search finds the same amplitude zeros of the triangle energy', ownTri.length === zTriCount && ownTri.every((q) => i.zeros.some((z) => z.xs.includes(q.x) && Math.abs(z.b - q.b) < 1e-4 && Math.abs(z.g - q.g) < 1e-4)), `${ownTri.length} vs ${zTriCount}`);
await preset('asym'); i = await info();
const ASYM = i.energy;
check('no symmetry: the energy is 0.37 times a permutation of 0 … 7', ASYM.map((v) => Math.round(v / 0.37)).slice().sort((a, b) => a - b).join() === '0,1,2,3,4,5,6,7' && ASYM.every((v) => close(v / 0.37, Math.round(v / 0.37), 1e-12)));
check('asym preset: |000⟩ vanishes at (β, γ) ≈ (0.4833, 1.0765) and the other 7 do not (support 7)', (() => { const s = stateOf(ASYM, i.beta, i.g); return mag(s[0]) < 1e-10 && s.slice(1).every((a) => mag(a) > 0.1); })() && i.support === 7 && Math.abs(i.beta - 0.4833) < 5e-5 && Math.abs(i.g - 1.0765) < 5e-5);
check('without symmetry every zero removes a single amplitude', i.zeros.length > 0 && i.zeros.every((z) => z.xs.length === 1 && z.support === 7 && mag(stateOf(ASYM, z.b, z.g)[z.xs[0]]) < 1e-10));
const ownAsym = searchZeros(ASYM);
check('the independent search finds the same zeros of the asymmetric energy', ownAsym.length === i.zeros.length && ownAsym.every((q) => i.zeros.some((z) => z.xs[0] === q.x && Math.abs(z.b - q.b) < 1e-4 && Math.abs(z.g - q.g) < 1e-4)), `${ownAsym.length} vs ${i.zeros.length}`);

/* ---------- curves, controls, timeline ---------- */
await preset('sweep'); await setFrac(0.5); i = await info();
check('the probability curves are the independent probabilities at 41 values of β', i.curves.every((c, x) => c.every((p, k) => close(p, mag(stateOf(LEAN, Math.PI * k * 10 / i.steps, 1)[x]) ** 2, 1e-12))));
check('probabilities sum to 1 along the sweep', i.curves[0].every((_, k) => close(i.curves.reduce((s, c) => s + c[k], 0), 1, 1e-12)));
await click('#eChips [data-e="tri"]'); i = await info();
check('energy chips switch the energy and mark the settings custom', i.e === 'tri' && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await D(() => { const el = document.getElementById('gg'); el.value = '2.5'; el.dispatchEvent(new Event('input', { bubbles: true })); }); await settle(); i = await info();
check('the γ slider sets γ', Math.abs(i.g - 2.5) < 1e-9 && (await text('oG')) === '2.5000');
for (const p of ['lean', 'sweep', 'miss', 'tri', 'asym', 'map']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
check('the map preset looks from the top', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'top');
await preset('sweep'); await setFrac(0.95); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('sweeping β to the end reports the zeros on the γ line', await waitToast(/4 个零点.*π\/8.*3π\/8.*5π\/8.*7π\/8/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
await setFrac(0.25); const b1 = (await info()).beta;
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps β by π/400', close((await info()).beta - b1, Math.PI / 400, 1e-9));
await page.keyboard.press('e'); await settle();
check('E jumps to β = π and pauses', close((await info()).beta, Math.PI) && (await state()).playing === false);
check('the rail marks 0, π/4, π/2, 3π/4, π', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' '))) === '0 π/4 π/2 3π/4 π');
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit[0] > 2000 && lit[1] > 500, `${lit}`);   // the phasor chart is a few thin arrows

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'tri']) {
  await preset(p);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#eChips [data-e="asym"]');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('QAOA//SUPPORT · A genuine four-state superposition from level-one QAOA'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['streif-leib-2020-level-one-qaoa-genuine-superposition.md', 'LevelOneQAOAGenuineSuperposition.lean', 'Blueprint/D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.md', 'streifleib2020forbidden.md', '10.1103/PhysRevA.102.042416', 'arxiv.org/abs/2007.13563'].every((s) => h.includes(s)); })));
await page.keyboard.press('Escape'); await page.waitForFunction(() => document.getElementById('drawer').hidden === true, null, { timeout: 10000 }).catch(() => {});
check('Esc closes the drawer', (await D(() => document.getElementById('drawer').hidden)) === true);
await page.waitForFunction(() => document.activeElement?.id === 'infoBtn', null, { timeout: 10000 }).catch(() => {});
check('focus returns to the drawer button', (await D(() => document.activeElement?.id)) === 'infoBtn');

/* ---------- index round trip ---------- */
const live = readRegistry().visualizations.filter(v => v.status === 'live').length;
await page.click('.crumb'); await page.waitForLoadState('load');
await page.waitForFunction((n) => document.querySelectorAll('.card').length >= n, live, { timeout: 30000 }).catch(() => {});
check('language choice carries to the index', (await D(() => document.documentElement.dataset.lang)) === 'en');
check('index lists every live visualization', (await D(() => document.querySelectorAll('.card').length)) === live, `live ${live}`);
await page.click('.card:has(a[href*="qaoa-support"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.QS_DEBUG && QS_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'qaoa-support');

/* ---------- narrow layouts in both languages ---------- */
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await waitFrames(3);
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await waitFrames(6);
    check(`no horizontal scroll at ${w}px (${lang})`, (await D(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 });
}
check('no script errors during the whole session', errors.length === 0, errors.slice(0, 3).join(' | '));

await browser.close(); server.close();
const failed = results.filter(r => !r.ok).length;
console.log(`\n${results.length - failed}/${results.length} passed`);
process.exit(failed ? 1 : 0);
