#!/usr/bin/env node
// Browser regression suite for viz/auric-pyramid (Playwright + Chromium with software WebGL).
//   node tests/auric-pyramid.test.mjs
// Reads page state through the read-only window.AP_DEBUG probe and checks it against an independent implementation: the
// substitution as a string morphism a → b, b → ba, legal words by brute force over all binary strings, pyramid membership by
// barycentric coordinates in a two-tetrahedron triangulation, the hidden fibre by enumerating basic feasible solutions of the
// means system with Gaussian elimination, and the gluing laws checked against brute-force independent sets on edge lists.
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
  const start = await page.evaluate(() => AP_DEBUG.frames());
  await page.waitForFunction((f0) => !AP_DEBUG.pending() && AP_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => AP_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => AP_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => AP_DEBUG.info());
const state = () => D(() => AP_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => AP_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => AP_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};
const near = (a, b, tol = 1e-9) => Math.abs(a - b) <= tol;

// --- independent implementation
const FIB = [0n, 1n]; for (let k = 2; k <= 40; k++) FIB.push(FIB[k - 1] + FIB[k - 2]);
const F = (k) => Number(FIB[k]);
const sigma = (n) => { let w = 'a'; for (let k = 0; k < n; k++) w = [...w].map((c) => (c === 'a' ? 'b' : 'ba')).join(''); return w; };
const bruteWords = (n) => { const out = []; for (let m = 0; m < 2 ** n; m++) { const s = m.toString(2).padStart(n, '0'); if (n === 0 || !s.includes('11')) out.push(n === 0 ? '' : s); } return out; };
// the pyramid: vertices in (X, Y, Z) = (low end, high end, middle); split along the base diagonal 0 – 25
const V = { 0: [0, 0, 0], 2: [1, 0, 0], 25: [1, 1, 0], 5: [0, 1, 0], 3: [0, 0, 1] };
const TETS = [[V[0], V[2], V[25], V[3]], [V[0], V[25], V[5], V[3]]];
const det3 = (a, b, c) => a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0]) + a[2] * (b[0] * c[1] - b[1] * c[0]);
const sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
function bary(T, p) {   // Cramer's rule for p − T₀ = Σ λᵢ (Tᵢ − T₀)
  const e1 = sub(T[1], T[0]), e2 = sub(T[2], T[0]), e3 = sub(T[3], T[0]), q = sub(p, T[0]), d = det3(e1, e2, e3);
  const l1 = det3(q, e2, e3) / d, l2 = det3(e1, q, e3) / d, l3 = det3(e1, e2, q) / d; return [1 - l1 - l2 - l3, l1, l2, l3];
}
const inPyr = (p, eps = 1e-9) => TETS.some((T) => bary(T, p).every((l) => l >= -eps));
const tetVol = (T) => Math.abs(det3(sub(T[1], T[0]), sub(T[2], T[0]), sub(T[3], T[0]))) / 6;
let seed = 20261010; const rnd = () => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed / 2147483648; };
// the hidden fibre: rows 1, X, Y, Z over the modes (0, 2, 3, 5, 25); a vertex of the fibre is a basic feasible solution
const A = [[1, 1, 1, 1, 1], [0, 1, 0, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 0, 0]];
function solve(M, b) {   // Gaussian elimination with partial pivoting; null when singular
  const n = b.length, a = M.map((r, i) => [...r, b[i]]);
  for (let c = 0; c < n; c++) {
    let piv = c; for (let r = c + 1; r < n; r++) if (Math.abs(a[r][c]) > Math.abs(a[piv][c])) piv = r;
    if (Math.abs(a[piv][c]) < 1e-12) return null; [a[c], a[piv]] = [a[piv], a[c]];
    for (let r = 0; r < n; r++) if (r !== c) { const f = a[r][c] / a[c][c]; for (let k = c; k <= n; k++) a[r][k] -= f * a[c][k]; }
  }
  return a.map((r, i) => r[n] / r[i]);
}
function fibreVertices(X, Y, Z) {
  const b = [1, X, Y, Z], out = [];
  for (let drop = 0; drop < 5; drop++) {
    const cols = [0, 1, 2, 3, 4].filter((c) => c !== drop), x = solve(A.map((r) => cols.map((c) => r[c])), b);
    if (!x || x.some((v) => v < -1e-12)) continue; const p = [0, 0, 0, 0, 0]; cols.forEach((c, k) => { p[c] = x[k]; }); out.push(p);
  }
  return out;
}
// gluing: graphs as edge lists
const edgesOf = (graph, n) => { const E = []; for (let i = 0; i + 1 < n; i++) E.push([i, i + 1]); if (graph === 'cycle' && n > 2) E.push([n - 1, 0]); return E; };
const independent = (m, E) => E.every(([a, b]) => !(((m >> a) & 1) && ((m >> b) & 1)));
const bruteAlpha = (graph, n) => { const E = edgesOf(graph, n); let best = 0; for (let m = 0; m < 2 ** n; m++) if (independent(m, E)) best = Math.max(best, m.toString(2).split('').filter((c) => c === '1').length); return best; };

await page.goto(origin + BASE + 'viz/auric-pyramid/');
await page.waitForFunction(() => window.AP_DEBUG && AP_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
check('page loads with the probe', (await D(() => document.body.dataset.vizId)) === 'auric-pyramid');
check('starts on the slice preset in pyramid mode', (await state()).preset === 'slice' && (await info()).mode === 'pyramid');
check('four frozen Lean anchors are named', JSON.stringify(await D(() => [...document.querySelectorAll('.lean:not(.lit):not(.theory) code')].map((c) => c.textContent))) === JSON.stringify(['PathStableSetPolytope.convexHull_three_pyramid', 'PathStableSetPolytope.convexHull_vertices', 'AdmissibleCount.admissibleWord_card_eq_fib', 'FiniteEventCouplingSharpBounds.event_coupling_target_feasible_iff']));
check('…and the unformalized theory results sit in a separate THEORY box, the classics in a LIT box', (await D(() => document.querySelectorAll('.lean.theory').length)) === 1 && (await D(() => document.querySelectorAll('.lean.lit').length)) === 1 && /尚未形式化/.test(await D(() => document.querySelector('.lean.theory').textContent)));

// --- the substitution tree
await preset('tree');
let i;
const treeOK = [], sigmaLeaves = [];
for (let n = 0; n <= 10; n++) {
  await setFrac(n / 10); i = await info(); const s = sigma(n), A1 = [...s].filter((c) => c === 'a').length, B1 = s.length - A1;
  sigmaLeaves.push(s);
  treeOK.push(i.n === n && i.leaves === s && i.A === A1 && i.B === B1 && i.quantity === 2 * A1 + 3 * B1);
}
check('every level n ≤ 10: the leaves read left to right equal the morphism image σⁿ(a) of a → b, b → ba', treeOK.every(Boolean), treeOK.map((x) => (x ? 1 : 0)).join(''));
check('…the leaf count is F(n + 1), #α = F(n − 1), #β = F(n) (recomputed)', sigmaLeaves.every((s, n) => s.length === F(n + 1) && [...s].filter((c) => c === 'b').length === F(n)));
check('…the quantity 2·#α + 3·#β is F(n + 3) at every level', sigmaLeaves.every((s, n) => { const a = [...s].filter((c) => c === 'a').length; return 2 * a + 3 * (s.length - a) === F(n + 3); }) && i.stats.every((st) => st.quantity === F(st.n + 3)));
check('…and the page’s per-level table matches (leaves, words)', i.stats.length === 11 && i.stats.every((st) => st.leaves === F(st.n + 1) && st.words === F(st.n + 2)));
const wordsOK = []; for (let n = 0; n <= 10; n++) { await setFrac(n / 10); const pw = (await info()).words, bw = bruteWords(n); wordsOK.push(pw.length === bw.length && JSON.stringify([...pw].sort()) === JSON.stringify([...bw].sort()) && pw.length === F(n + 2)); }
check('legal words of length n ≤ 10: the page’s list equals the brute-force set with no “11”, F(n + 2) of them (frozen count)', wordsOK.every(Boolean), wordsOK.map((x) => (x ? 1 : 0)).join(''));
await preset('five'); i = await info();
check('the n = 3 preset lists exactly 000, 100, 010, 001, 101 — the five modes', i.n === 3 && JSON.stringify([...i.words].sort()) === JSON.stringify(['000', '001', '010', '100', '101']) && /\[25\]/.test(await text('roNote')));
await setFrac(0.7);
check('…the readouts pair the computed values with F: 55 · 55 and 34 · 34 at n = 7', (await text('ro3')) === '55 · 55' && (await text('ro4')) === '34 · 34', `${await text('ro3')} | ${await text('ro4')}`);

// --- the pyramid
await preset('slice'); i = await info();
const cloudAgree = i.cloud.every(([X, Y, Z, inn]) => inn === inPyr([X, Y, Z]));
check('all 1600 cloud points: the page’s inside flag agrees with barycentric coordinates in the two tetrahedra', i.cloud.length === 1600 && cloudAgree);
check('…the fraction inside is a Monte Carlo estimate of the exact volume 1/3 (within 0.04)', near(i.cloudInside / 1600, 1 / 3, 0.04) && near(tetVol(TETS[0]) + tetVol(TETS[1]), 1 / 3, 1e-12), `${i.cloudInside}/1600`);
const probeAgree = await D((pts) => pts.map(([X, Y, Z]) => AP_DEBUG.inside(X, Y, Z)), Array.from({ length: 3000 }, () => [rnd() * 1.2 - 0.1, rnd() * 1.2 - 0.1, rnd() * 1.2 - 0.1]));
seed = 20261010; const pts3 = Array.from({ length: 3000 }, () => [rnd() * 1.2 - 0.1, rnd() * 1.2 - 0.1, rnd() * 1.2 - 0.1]);
check('3000 random points around the cube: page membership = barycentric membership', probeAgree.every((v, k) => v === inPyr(pts3[k], 0)));
check('…the five modes lie in the pyramid, (½, ½, ½) on its boundary, and (0.3, 0.7, 0.5) with Y + Z > 1 outside', (await D(() => [[0, 0, 0], [1, 0, 0], [0, 0, 1], [0, 1, 0], [1, 1, 0], [0.5, 0.5, 0.5]].every(([X, Y, Z]) => AP_DEBUG.inside(X, Y, Z)) && !AP_DEBUG.inside(0.3, 0.7, 0.5))) && inPyr([0.5, 0.5, 0.5]) && !inPyr([0.3, 0.7, 0.5]));
const sliceOK = [];
for (const f of [0, 0.2, 0.45, 0.8, 1]) {
  await setFrac(f); i = await info(); const Z = f, P = [(1 - Z) * i.u + Z * 0, (1 - Z) * i.v, Z];
  let simpson = 0; const N = 200; for (let k = 0; k <= N; k++) { const z = Z * k / N, w = k === 0 || k === N ? 1 : k % 2 ? 4 : 2; simpson += w * (1 - z) ** 2; } simpson *= Z / N / 3;
  sliceOK.push(near(i.Z, Z) && near(i.X, P[0]) && near(i.Y, P[1]) && i.inside === inPyr(P) && near(i.sliceArea, (1 - Z) ** 2) && near(i.volBelow, simpson, 1e-9));
}
check('sweeping Z: the average point is (1 − Z)·(u, v, 0) + Z·(0, 0, 1), inside, with slice area (1 − Z)² and volume = Simpson integral', sliceOK.every(Boolean), sliceOK.map((x) => (x ? 1 : 0)).join(''));
check('…the readout reports the Monte Carlo count next to 1/3', /^\d+\/1600 = 0\.\d{4} ≈ 1\/3$/.test(await text('ro4')), await text('ro4'));

// --- the hidden fibre
const fibreOK = [], widthOK = [], deltaOK = [];
let pts = 0;
while (pts < 160) {
  const X = rnd(), Y = rnd(), Z = rnd(); if (!inPyr([X, Y, Z], 0) || Z > 0.98) continue; pts++;
  const verts = fibreVertices(X, Y, Z), ks = verts.map((p) => p[4]), lo = Math.min(...ks), hi = Math.max(...ks), r = 1 - Z;
  for (const f of [0, 0.37, 1]) {
    const g = await D(([X, Y, Z, f]) => AP_DEBUG.fiberAt(X, Y, Z, f), [X, Y, Z, f]);
    const resid = A.map((row, k) => row.reduce((s, a, c) => s + a * g.p[c], 0) - [1, X, Y, Z][k]);
    widthOK.push(near(g.width, Math.min(X, Y, r - X, r - Y)) && near(hi - lo, Math.min(X, Y, r - X, r - Y)));
    fibreOK.push(near(g.kLo, lo) && near(g.kHi, hi) && near(g.kappa, lo + (hi - lo) * f) && near(g.p[4], g.kappa) && g.p.every((v) => v >= -1e-12) && resid.every((e) => Math.abs(e) < 1e-12));
    const dlt = g.p[0] * g.p[4] - g.p[1] * g.p[3];
    deltaOK.push(near(g.delta, dlt) && near(dlt, r * g.kappa - X * Y) && Math.abs(dlt) <= r * r / 4 + 1e-12 && near(g.bound, r * r / 4) && near(g.cov, g.kappa - X * Y) && near(g.kStar, X * Y / r) && g.kStar >= lo - 1e-12 && g.kStar <= hi + 1e-12);
  }
}
check('160 random average points × 3 positions: the page’s κ interval equals [min, max] of p₂₅ over basic feasible solutions, and its law solves the means system', fibreOK.every(Boolean), `${fibreOK.filter(Boolean).length}/${fibreOK.length}`);
check('…the interval width is min{X, Y, r − X, r − Y} (theory volume, rechecked)', widthOK.every(Boolean), `${widthOK.filter(Boolean).length}/${widthOK.length}`);
check('…Δ = p₀p₂₅ − p₂p₅ = rκ − XY, |Δ| ≤ r²/4, and κ* = XY/r lies in the interval', deltaOK.every(Boolean), `${deltaOK.filter(Boolean).length}/${deltaOK.length}`);
const eq = await D(() => [0.1, 0.4, 0.7].map((Z) => { const r = 1 - Z, g = AP_DEBUG.fiberAt(r / 2, r / 2, Z, 1); return [g.delta, r * r / 4]; }));
check('…the bound is attained at X = Y = r/2 at the top of the interval', eq.every(([d, b]) => near(d, b, 1e-12)));
await preset('same');
const laws = []; for (const f of [0, 0.5, 1]) { await setFrac(f); i = await info(); laws.push(i); }
check('the same-average preset: (X, Y, Z) stays (½, ½, 0) while the law runs from (0, ½, 0, ½, 0) to (½, 0, 0, 0, ½)', laws.every((l) => near(l.X, 0.5) && near(l.Y, 0.5) && near(l.Z, 0)) && JSON.stringify(laws[0].p.map((x) => +x.toFixed(9))) === JSON.stringify([0, 0.5, 0, 0.5, 0]) && JSON.stringify(laws[2].p.map((x) => +x.toFixed(9))) === JSON.stringify([0.5, 0, 0, 0, 0.5]));
check('…two laws on the fibre differ by a multiple of (1, −1, 0, −1, 1)', laws[1].p.every((v, k) => near(v - laws[0].p[k], (laws[1].kappa - laws[0].kappa) * [1, -1, 0, -1, 1][k])));
await preset('uniform'); i = await info();
check('the uniform preset: every mode 1/5, average (2/5, 2/5, 1/5), κ = κ* = 1/5, Δ = 0, covariance 1/25 = XYZ/r', i.p.every((v) => near(v, 0.2)) && near(i.X, 0.4) && near(i.Y, 0.4) && near(i.Z, 0.2) && near(i.kappa, 0.2) && near(i.kStar, 0.2) && near(i.delta, 0) && near(i.cov, 1 / 25) && near(i.cov, i.X * i.Y * i.Z / i.r));
await preset('face'); i = await info();
check('the side-face preset: X = 0, the basic feasible solutions collapse to one law, width 0', near(i.X, 0) && i.width === 0 && new Set(fibreVertices(i.X, i.Y, i.Z).map((p) => p.map((v) => v.toFixed(9)).join())).size === 1 && /唯一决定/.test(await text('roNote')));

// --- gluing windows
const glueOK = [], margOK = [], suppOK = [];
for (const graph of ['path', 'cycle']) for (let n = 3; n <= 11; n++) {
  const alpha = bruteAlpha(graph, n), thr = graph === 'cycle' ? alpha / n : 0.5, E = edgesOf(graph, n);
  for (const t of [0, 0.1, 0.25, 1 / 3, thr, Math.min(0.5, thr + 0.01), 0.45, 0.5]) {
    const g = await D(([graph, n, t]) => AP_DEBUG.gluing(graph, n, t), [graph, n, t]);
    glueOK.push(g.alpha === alpha && near(g.threshold, thr) && g.feasible === (t <= thr + 1e-12));
    if (g.feasible) {
      const tot = g.dist.reduce((s, [, p]) => s + p, 0), marg = Array.from({ length: n }, (_, k) => g.dist.reduce((s, [m, p]) => s + (((m >> k) & 1) ? p : 0), 0));
      margOK.push(near(tot, 1, 1e-12) && marg.every((x) => near(x, t, 1e-12)) && g.marg.every((x, k) => near(x, marg[k], 1e-12)));
      suppOK.push(g.dist.every(([m, p]) => p > 0 && m >= 0 && m < 2 ** n && independent(m, E)));
    } else glueOK.push(g.dist.length === 0);
  }
}
check('paths and cycles with 3 – 11 positions: α by brute force, achievable exactly up to ½ on paths and α/n on cycles', glueOK.every(Boolean), `${glueOK.filter(Boolean).length}/${glueOK.length}`);
check('…every constructed law is a probability distribution with every occupancy equal to t', margOK.every(Boolean), `${margOK.length} laws`);
check('…and is supported on independent sets of the graph (wrap-around edge included)', suppOK.every(Boolean));
await preset('odd'); await setFrac(0.8); await waitFrames(20); i = await info();
check('C₅ at t = 2/5: still achievable, and every sample is an independent set of the cycle', i.feasible && near(i.t, 0.4) && i.alpha === 2 && i.samples.length > 0 && i.samples.every((m) => independent(m, edgesOf('cycle', 5))), `${i.samples.length} samples`);
await setFrac(1); i = await info();
check('C₅ at t = ½: every edge constraint holds but the page reports “not achievable”, no samples', !i.feasible && i.samples.length === 0 && /满足/.test(await text('ro2')) && (await text('ro4')) === '不能' && /最多 2 个点/.test(await text('roNote')));
check('…the rail marks the threshold 2/5', /2\/5/.test(await D(() => document.getElementById('marks').textContent)));
await preset('path'); await setFrac(0.9); await waitFrames(20); i = await info();
check('P₇ at t = 0.45: achievable, Markov law, samples are independent sets of the path', i.feasible && i.graph === 'path' && i.samples.length > 0 && i.samples.every((m) => independent(m, edgesOf('path', 7))));

// --- controls, keys, presets
for (const name of ['tree', 'five', 'slice', 'same', 'uniform', 'face', 'path', 'odd']) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
const fieldsShown = async () => { const out = []; for (const id of ['uField', 'vField', 'zField', 'graphField', 'nField']) if (await visible(id)) out.push(id); return out.join(','); };
await click('#modeChips [data-mode="tree"]');
check('the model chips switch to the tree, hide every field and mark the settings custom', (await info()).mode === 'tree' && (await fieldsShown()) === '' && (await state()).preset === null);
await click('#modeChips [data-mode="pyramid"]');
check('…pyramid shows u and v', (await fieldsShown()) === 'uField,vField');
await click('#modeChips [data-mode="fiber"]');
check('…fibre shows u, v and Z', (await fieldsShown()) === 'uField,vField,zField');
await D(() => { const el = document.getElementById('zz'); el.value = '0.33'; el.dispatchEvent(new Event('input', { bubbles: true })); }); await settle();
check('the Z slider snaps to steps of 0.05 and moves the average point', near((await state()).z, 0.35) && near((await info()).Z, 0.35));
await click('#modeChips [data-mode="glue"]');
check('…gluing shows the graph chips and n', (await fieldsShown()) === 'graphField,nField');
await click('#graphChips [data-graph="cycle"]');
await D(() => { const el = document.getElementById('nn'); el.value = '9'; el.dispatchEvent(new Event('input', { bubbles: true })); }); await settle(); i = await info();
check('the graph chip and n slider give the cycle C₉ with α = 4', i.graph === 'cycle' && i.n === 9 && i.alpha === 4 && near(i.threshold, 4 / 9));
await setFrac(0.6); await waitFrames(20); const s0 = (await state()).seed, n0 = (await info()).samples.length;
await page.keyboard.press('r'); await settle(); await waitFrames(2);
check('R draws a fresh sample record', (await state()).seed === s0 + 1 && n0 >= 10 && (await info()).samples.length < n0, `${n0} before`);
await click('#modeChips [data-mode="tree"]'); await setFrac(0); await page.keyboard.press('ArrowRight'); await settle();
check('→ moves one level in the tree', (await info()).n === 1);
await page.keyboard.press('e'); await settle();
check('E jumps to n = 10 and pauses', (await info()).n === 10 && (await state()).playing === false);

// --- play and toasts
await preset('tree'); await setFrac(0.985); await click('#play');
check('the tree toast reports F(13) = 233 and F(12) = 144', await waitToast(/233.*144/));
await pause();
await preset('slice'); await setFrac(0.985); await click('#play');
check('the slice toast fires at the apex', await waitToast(/Z = 1/));
await pause();
await preset('same'); await setFrac(0.985); await click('#play');
check('the fibre toast says the average never moved', await waitToast(/平均点没动/));
await pause();
await preset('odd'); await setFrac(0.985); await click('#play');
check('the odd-cycle toast names the limit 2/5', await waitToast(/2\/5/));
await pause();
await preset('same'); await setFrac(0.2); await click('#play'); await waitFrames(12); const p1 = (await state()).nowFrac; await pause();
check('play advances along the rail', p1 > 0.2);
await click('#rev'); await waitFrames(12); const p2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', p2 < p1);
await page.click('#rev'); await pause();
await page.focus('#now'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with the rail focused', playing === true);
await pause();

// --- language
await click('#modeChips [data-mode="pyramid"]');
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
for (const m of ['tree', 'fiber', 'glue', 'pyramid']) {
  await click(`#modeChips [data-mode="${m}"]`); await setFrac(0.5);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${m}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('AURIC//PYRAMID · What averages see and what they miss'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the three AURIC theory volumes and the three Lean files', (await D(() => { const h = [...document.querySelectorAll('#drawer a')].map((a) => a.href).join(' '); return ['AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL', 'AURIC_FIB_ATOM_PYRAMID_BOUNDARY', 'AURIC_FIB_ATOM_PYRAMID_LOCAL_FILLINGS', 'PathStableSetPolytope.lean', 'AdmissibleCount.lean', 'FiniteEventCouplingSharpBounds.lean'].every((s) => h.includes(s)); })));
await page.keyboard.press('Escape'); await page.waitForFunction(() => document.getElementById('drawer').hidden === true, null, { timeout: 10000 }).catch(() => {});
check('Esc closes the drawer', (await D(() => document.getElementById('drawer').hidden)) === true);
await page.waitForFunction(() => document.activeElement?.id === 'infoBtn', null, { timeout: 10000 }).catch(() => {});
check('focus returns to the drawer button', (await D(() => document.activeElement?.id)) === 'infoBtn');

// --- index round trip
const live = readRegistry().visualizations.filter(v => v.status === 'live').length;
await page.click('.crumb'); await page.waitForLoadState('load');
await page.waitForFunction((n) => document.querySelectorAll('.card').length >= n, live, { timeout: 30000 }).catch(() => {});
check('language choice carries to the index', (await D(() => document.documentElement.dataset.lang)) === 'en');
check('index lists every live visualization', (await D(() => document.querySelectorAll('.card').length)) === live, `live ${live}`);
await page.click('.card:has(a[href*="auric-pyramid"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.AP_DEBUG && AP_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'auric-pyramid');

// --- narrow layouts in both languages
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
