#!/usr/bin/env node
// Browser regression suite for viz/hofstadter-gap (Playwright + Chromium with software WebGL).
//   node tests/hofstadter-gap.test.mjs
// Reads page state through the read-only window.HG_DEBUG probe and checks it against an independent implementation: the
// Bloch matrix rebuilt from the source formula with complex exponentials, eigenvalues by cyclic Jacobi on the real 8 × 8
// embedding (the page uses the characteristic polynomial and Newton iteration), the determinant identity and inertia from those
// eigenvalues, Chambers' relation checked against eigenvalues of Harper matrices, and the closed-form band edges at α = 1/4.
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
page.on('console', m => { if (m.type() === 'error' && !/ERR_CERT/.test(m.text()) && !/^https:\/\/fonts\.(googleapis|gstatic)\.com\//.test((m.location() || {}).url || '')) errors.push('console: ' + m.text()); });
const D = (expr, arg) => page.evaluate(expr, arg);
const settle = async () => {
  const start = await page.evaluate(() => HG_DEBUG.frames());
  await page.waitForFunction((f0) => !HG_DEBUG.pending() && HG_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => HG_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => HG_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => HG_DEBUG.info());
const state = () => D(() => HG_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => HG_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => HG_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};
const near = (a, b, tol = 1e-9) => Math.abs(a - b) <= tol;

// --- independent implementation
const cx = (re, im = 0) => ({ re, im });
const cadd = (...zs) => zs.reduce((a, z) => cx(a.re + z.re, a.im + z.im), cx(0));
const cmul = (a, b) => cx(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re);
const cexp = (t) => cx(Math.cos(t), Math.sin(t));
const I = cx(0, 1), ONE = cx(1), ZERO = cx(0), neg = (z) => cx(-z.re, -z.im);
function sourceH(k1, k2, m) {   // −[[d, 1 − i e^{2ik₁}, 1 − i e^{2ik₂}, 0], [1 + i e^{−2ik₁}, 0, 0, −i + e^{2ik₂}], [1 + i e^{−2ik₂}, 0, 0, 1 + i e^{2ik₁}], [0, i + e^{−2ik₂}, 1 − i e^{−2ik₁}, −d]]
  const d = 2 + m, e1 = cexp(2 * k1), e2 = cexp(2 * k2), e1b = cexp(-2 * k1), e2b = cexp(-2 * k2);
  const A = [[cx(d), cadd(ONE, neg(cmul(I, e1))), cadd(ONE, neg(cmul(I, e2))), ZERO],
    [cadd(ONE, cmul(I, e1b)), ZERO, ZERO, cadd(neg(I), e2)],
    [cadd(ONE, cmul(I, e2b)), ZERO, ZERO, cadd(ONE, cmul(I, e1))],
    [ZERO, cadd(I, e2b), cadd(ONE, neg(cmul(I, e1b))), cx(-d)]];
  return A.map((row) => row.map(neg));
}
function jacobiEig(S) {   // cyclic Jacobi on a real symmetric matrix, eigenvalues ascending
  const n = S.length, a = S.map((r) => r.slice());
  for (let sweep = 0; sweep < 80; sweep++) {
    let off = 0; for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) off += a[p][q] ** 2;
    if (off < 1e-28) break;
    for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
      if (Math.abs(a[p][q]) < 1e-300) continue;
      const th = (a[q][q] - a[p][p]) / (2 * a[p][q]), t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), s = t * c;
      for (let k = 0; k < n; k++) { const x = a[k][p], y = a[k][q]; a[k][p] = c * x - s * y; a[k][q] = s * x + c * y; }
      for (let k = 0; k < n; k++) { const x = a[p][k], y = a[q][k]; a[p][k] = c * x - s * y; a[q][k] = s * x + c * y; }
    }
  }
  return a.map((r, i) => r[i]).sort((x, y) => x - y);
}
function hermEig(M) {   // the real embedding [[A, −B], [B, A]] doubles every eigenvalue
  const n = M.length, S = Array.from({ length: 2 * n }, () => new Array(2 * n).fill(0));
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) { const { re, im } = M[i][j]; S[i][j] = re; S[i + n][j + n] = re; S[i][j + n] = -im; S[i + n][j] = im; }
  return jacobiEig(S).filter((_, i) => i % 2 === 0);
}
const eigH = (k1, k2, m) => hermEig(sourceH(k1, k2, m));
const qInd = (k1, k2, m) => { const d = 2 + m; return (Math.sin(2 * k1) - d) ** 2 + (Math.sin(2 * k2) - d) ** 2 + 2 - d * d; };
function gridStats(m, n) { let max3 = -Infinity, min4 = Infinity, minQ = Infinity, minDist = Infinity; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) { const k1 = Math.PI * i / (n - 1), k2 = Math.PI * j / (n - 1), e = eigH(k1, k2, m); max3 = Math.max(max3, e[2]); min4 = Math.min(min4, e[3]); minQ = Math.min(minQ, qInd(k1, k2, m)); for (const x of e) minDist = Math.min(minDist, Math.abs(x - 2)); } return { max3, min4, minQ, minDist }; }
function harper(kx, ky, p, q) {   // Harper's q × q Bloch matrix in the Landau gauge
  const M = Array.from({ length: q }, () => Array.from({ length: q }, () => cx(0)));
  for (let j = 0; j < q; j++) { M[j][j] = cadd(M[j][j], cx(2 * Math.cos(ky + 2 * Math.PI * p * j / q))); const k = (j + 1) % q; M[j][k] = cadd(M[j][k], cexp(kx)); M[k][j] = cadd(M[k][j], cexp(-kx)); }
  return M;
}
let seed = 271828; const rnd = () => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed / 2147483648; };
const QUARTER = [[-2 * Math.SQRT2, -Math.sqrt(4 + 2 * Math.SQRT2)], [-Math.sqrt(4 - 2 * Math.SQRT2), 0], [0, Math.sqrt(4 - 2 * Math.SQRT2)], [Math.sqrt(4 + 2 * Math.SQRT2), 2 * Math.SQRT2]];

await page.goto(origin + BASE + 'viz/hofstadter-gap/');
await page.waitForFunction(() => window.HG_DEBUG && HG_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
check('page loads with the probe', (await D(() => document.body.dataset.vizId)) === 'hofstadter-gap');
check('starts on the mass sweep in band mode', (await state()).preset === 'sweep' && (await info()).mode === 'bands');
check('the frozen anchors are named', JSON.stringify(await D(() => [...document.querySelectorAll('.lean:not(.lit):not(.theory):not(.num) code')].map((c) => c.textContent))) === JSON.stringify(['HalfFluxHofstadterMassGap.result', 'HalfFluxHofstadterMassGap.bloch_isHermitian']));
check('…argued steps, page numbers and literature sit in separate ARGUED, NUM and LIT boxes', (await D(() => [document.querySelectorAll('.lean.theory').length, document.querySelectorAll('.lean.num').length, document.querySelectorAll('.lean.lit').length].join())) === '1,1,1' && /未形式化/.test(await D(() => document.querySelector('.lean.theory').textContent)) && /不是定理/.test(await D(() => document.querySelector('.lean.num').textContent)));

// --- the matrix and its bands
const pts = Array.from({ length: 240 }, () => [rnd() * Math.PI * 2 - Math.PI, rnd() * Math.PI * 2 - Math.PI, rnd() * 4 - 2]);
const mats = await D((pts) => pts.map(([a, b, m]) => HG_DEBUG.matrix(a, b, m)), pts);
let matErr = 0, hermErr = 0;
pts.forEach(([a, b, m], t) => { const H = sourceH(a, b, m), M = mats[t]; for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) { matErr = Math.max(matErr, Math.abs(M.re[4 * i + j] - H[i][j].re), Math.abs(M.im[4 * i + j] - H[i][j].im)); hermErr = Math.max(hermErr, Math.abs(M.re[4 * i + j] - M.re[4 * j + i]), Math.abs(M.im[4 * i + j] + M.im[4 * j + i])); } });
check('240 random (k₁, k₂, m): the page’s matrix equals the source formula entry by entry and is Hermitian', matErr < 1e-14 && hermErr < 1e-14, `${matErr.toExponential(1)} · ${hermErr.toExponential(1)}`);
const pageBands = await D((pts) => pts.map(([a, b, m]) => HG_DEBUG.bands(a, b, m)), pts);
let bandErr = 0; pts.forEach(([a, b, m], t) => { const e = eigH(a, b, m); e.forEach((x, j) => { bandErr = Math.max(bandErr, Math.abs(x - pageBands[t][j])); }); });
check('…its four bands (characteristic polynomial + Newton) equal Jacobi eigenvalues of the real embedding', bandErr < 1e-8, bandErr.toExponential(2));
const eF = eigH(Math.PI / 4, Math.PI / 4, 0);
check('Fermi point: at k_F = (π/4, π/4), m = 0 the bands are −4, 0, 2, 2 (charpoly X(X + 4)(X − 2)²), so μ = 2', [-4, 0, 2, 2].every((v, j) => near(eF[j], v, 1e-7)));
await preset('cone'); let i = await info();
check('…the m = 0 preset shows λ₃ = λ₄ = 2 at k_F and a vanishing gap', i.m === 0 && near(i.kF[2], 2, 1e-6) && near(i.kF[3], 2, 1e-6) && i.gap < 1e-6 && /相碰/.test(await text('ro5')));

// --- the theorem, rechecked numerically
const masses = [-2, -1.5, -1, -0.5, -0.25, -0.1, -0.05, 0.05, 0.1, 0.25, 0.5, 1, 1.5, 2];
const thm = masses.map((m) => { const g = gridStats(m, 49); return g.max3 <= 2 - m * m / 500 && g.min4 >= 2 + m * m / 500; });
check('14 nonzero masses × 49 × 49 momenta (Jacobi): λ₃ ≤ 2 − m²/500 and λ₄ ≥ 2 + m²/500 (the frozen statement)', thm.every(Boolean), thm.map((x) => (x ? 1 : 0)).join(''));
const randomGap = Array.from({ length: 400 }, () => { const m = (rnd() < 0.5 ? -1 : 1) * (0.02 + rnd() * 1.98), k1 = rnd() * 7 - 3.5, k2 = rnd() * 7 - 3.5, e = eigH(k1, k2, m); return e[2] <= 2 - m * m / 500 && e[3] >= 2 + m * m / 500; });
check('…and at 400 random (k, m) with m ∈ [−2, 2] \\ {0}', randomGap.every(Boolean));
await preset('sweep');
const sweepOK = [];
for (const f of [0, 0.125, 0.375, 0.625, 0.75, 1]) { await setFrac(f); i = await info(); const g = gridStats(i.m, 41); sweepOK.push(near(i.m, -2 + 4 * f, 1e-12) && near(i.max3, g.max3, 1e-8) && near(i.min4, g.min4, 1e-8) && near(i.gap, Math.min(2 - g.max3, g.min4 - 2), 1e-8) && near(i.delta, i.m * i.m / 500, 1e-15)); }
check('sweep: at m = −2, −1.5, −0.5, 0.5, 1, 2 the page’s max λ₃, min λ₄ and gap on its 41 × 41 grid equal the Jacobi grid', sweepOK.every(Boolean), sweepOK.map((x) => (x ? 1 : 0)).join(''));
check('…the readouts at m = 2 report gap 0.5359 against δ = 8.00e-3', (await text('ro3')) === '0.5359 · 8.00e-3', await text('ro3'));
const curveOK = i.curve.length === 81 && [0, 10, 30, 39, 41, 60, 80].every((t) => { const c = i.curve[t], g = gridStats(c.m, 33); return near(c.below, 2 - g.max3, 1e-8) && near(c.above, g.min4 - 2, 1e-8); });
check('…the gap-against-mass curve (81 masses, 33 × 33 grid) matches the Jacobi grid at seven sampled masses', curveOK);
const argued = [0.25, 1, 2].every((m) => near(eigH(Math.PI / 4, Math.PI / 4, m)[3], 2 + m, 1e-9));
await preset('top'); i = await info();
check('argued in the dossier: for m > 0, λ₄(k_F) = 2 + m (checked at m = 0.25, 1, 2); the m = 2 preset shows 4', argued && near(i.kF[3], 4, 1e-9) && near(i.min4, 4, 1e-9));

// --- the certificate
const certPts = Array.from({ length: 300 }, () => [rnd() * 7 - 3.5, rnd() * 7 - 3.5, (rnd() < 0.5 ? -1 : 1) * (0.02 + rnd() * 1.98)]);
let detErr = 0, inertiaOK = true, floorOK = true;
for (const [a, b, m] of certPts) { const K = eigH(a, b, m).map((x) => x - 2), det = K.reduce((s, x) => s * x, 1), q = qInd(a, b, m); detErr = Math.max(detErr, Math.abs(det + 4 * q) / (1 + Math.abs(det))); if (K.filter((x) => x > 0).length !== 1 || K.filter((x) => x < 0).length !== 3) inertiaOK = false; if (q < m * m / 2 - 1e-12) floorOK = false; }
check('300 random (k, m ≠ 0): det(H − 2) = −4q with q = (y₁ − d)² + (y₂ − d)² + 2 − d², y = sin 2k (from Jacobi eigenvalues)', detErr < 1e-8, detErr.toExponential(2));
check('…H − 2 has exactly one positive and three negative eigenvalues, and q ≥ m²/2', inertiaOK && floorOK);
await preset('cert');
const loopOK = [];
for (const f of [0, 0.1, 0.25, 0.4, 0.55, 0.7, 0.85, 1]) { await setFrac(f); i = await info(); const K = eigH(i.k1, i.k2, i.m).map((x) => x - 2); loopOK.push(i.m === 1 && i.nPos === 1 && i.nNeg === 3 && K.every((x, j) => near(x, i.K[j], 1e-8)) && near(i.det, -4 * qInd(i.k1, i.k2, 1), 1e-8) && near(i.q, qInd(i.k1, i.k2, 1), 1e-12)); }
check('certificate mode at m = 1: around the loop the page’s eigenvalues of H − 2, inertia (1, 3) and det = −4q are confirmed', loopOK.every(Boolean), loopOK.map((x) => (x ? 1 : 0)).join(''));
const kfFrac = (Math.SQRT2 / 4) / (Math.SQRT2 / 2 + 1);   // Γ → k_F has length π√2/4 of the loop's π(√2/2 + 1)
await setFrac(kfFrac); i = await info();
check('…the k_F mark of the loop (0.2071 of its length) is k_F = (π/4, π/4), where q = m² = 1', near(i.k1, Math.PI / 4, 1e-12) && near(i.k2, Math.PI / 4, 1e-12) && near(i.q, 1, 1e-12));
const gq = gridStats(1, 41);
check('…the minimum of q on the 41 × 41 grid is 1 at k_F, above the floor m²/2 = 0.5', near(i.minQ, gq.minQ, 1e-12) && near(i.minQ, 1, 1e-12) && near(i.atQ[0], Math.PI / 4, 1e-12) && /\(1, 3\)/.test(await text('ro3')));
await preset('floor'); i = await info();
check('the floor preset: m = 0.25 at k_F, q = m² = 0.0625 ≥ m²/2 = 0.03125', i.m === 0.25 && near(i.k1, Math.PI / 4, 1e-12) && near(i.k2, Math.PI / 4, 1e-12) && near(i.q, 0.0625, 1e-12) && near(i.minQ, gridStats(0.25, 41).minQ, 1e-12) && /0\.0625 · 0\.0313 · 0\.0625/.test(await text('ro5')), await text('ro5'));

// --- the bound
await preset('bound'); await setFrac(0.75); i = await info();
const g1 = gridStats(1, 41);
check('bound mode at m = 1: actual gap 0.2984 (Jacobi grid) against δ = 0.002, ratio 149', near(i.minDist, g1.minDist, 1e-8) && near(i.minDist, 0.29844, 1e-5) && near(i.delta, 0.002, 1e-15) && /0\.29844/.test(await text('ro2')) && /2\.00e-3 · 149/.test(await text('ro3')));
check('…the proof’s budget: min |det(H − 2)| ≥ 2m² and max |λ − 2| ≤ 10 on the grid', i.minAbsDet >= 2 - 1e-9 && i.maxShift <= 10 && near(i.minAbsDet, 4, 1e-8));
await preset('tiny'); i = await info();
check('the small-mass preset: m = 0.1, actual gap 0.033 against δ = 2e-5', near(i.m, 0.1, 1e-12) && near(i.minDist, gridStats(0.1, 41).minDist, 1e-8) && i.minDist > 0.03 && near(i.delta, 2e-5, 1e-15));

// --- the butterfly
let chErr = 0;
for (const [p, q] of [[1, 3], [1, 4], [2, 5], [3, 7]]) for (let t = 0; t < 6; t++) {
  const kx = rnd() * 6, ky = rnd() * 6, E = rnd() * 8 - 4, ev = hermEig(harper(kx, ky, p, q)), det = ev.reduce((s, x) => s * (E - x), 1);
  const pageP = await D(([E, p, q]) => HG_DEBUG.chambers(E, p, q), [E, p, q]);
  chErr = Math.max(chErr, Math.abs(det + 2 * Math.cos(q * kx) + 2 * Math.cos(q * ky) - pageP) / (1 + Math.abs(pageP)));
}
check('Chambers’ relation: the page’s P_q(E) equals det(E − H_Harper(k)) + 2cos(q k_x) + 2cos(q k_y) for p/q = 1/3, 1/4, 2/5, 3/7', chErr < 1e-8, chErr.toExponential(2));
await preset('harper'); i = await info();
const quarter = i.slices.find((s) => s.p === 1 && s.q === 4);
check('the α = 1/4 slice has the closed-form band edges ±2√2, ±√(4 ± 2√2), 0', quarter.intervals.length === 4 && quarter.intervals.every(([a, b], j) => near(a, QUARTER[j][0], 1e-7) && near(b, QUARTER[j][1], 1e-7)));
check('…at m = −2 the model’s four band ranges equal those edges (41 × 41 grid), the readout reports the difference', near(i.m, -2, 1e-12) && i.quarterModel.every((x, j) => near(x, QUARTER[j >> 1][j & 1], 1e-7)) && /e-/.test(await text('ro4')));
let hr = [[Infinity, -Infinity], [Infinity, -Infinity], [Infinity, -Infinity], [Infinity, -Infinity]];
for (let a = 0; a <= 32; a++) for (let b = 0; b <= 32; b++) { const e = hermEig(harper(2 * Math.PI * a / 32, 2 * Math.PI * b / 32, 1, 4)); e.forEach((x, j) => { hr[j][0] = Math.min(hr[j][0], x); hr[j][1] = Math.max(hr[j][1], x); }); }
check('…and Harper’s own 1/4 matrix, diagonalized on a 33 × 33 grid, gives the same four bands', hr.every(([a, b], j) => near(a, QUARTER[j][0], 1e-7) && near(b, QUARTER[j][1], 1e-7)));
let sliceOK = true, coverOK = true, nSlices = 0;
for (const s of i.slices) {
  nSlices++;
  if (s.intervals.length !== s.q || s.roots.length !== s.q) { sliceOK = false; continue; }
  const P = await D(([xs, p, q]) => xs.map((E) => HG_DEBUG.chambers(E, p, q)), [s.intervals.flat().concat(s.roots), s.p, s.q]);
  const edges = P.slice(0, 2 * s.q), atRoots = P.slice(2 * s.q), tol = (j) => 1e-6 + 8 / Math.max(1e-300, s.intervals[j][1] - s.intervals[j][0]) * 1e-14;   // |P| moves 8 across a band, so a thin band's edge carries a rounding error of slope × 1e-14
  if (!edges.every((v, k) => Math.abs(Math.abs(v) - 4) < tol(k >> 1)) || !atRoots.every((v, j) => Math.abs(v) < tol(j))) sliceOK = false;
  if (!s.roots.every((r, j) => r >= s.intervals[j][0] - 1e-12 && r <= s.intervals[j][1] + 1e-12)) sliceOK = false;
}
for (const [p, q] of [[1, 3], [2, 7], [3, 8], [5, 13]]) { const s = i.slices.find((t) => t.p === p && t.q === q); const Es = Array.from({ length: 4001 }, (_, k) => -4.2 + 8.4 * k / 4000); const P = await D(([Es, p, q]) => Es.map((E) => HG_DEBUG.chambers(E, p, q)), [Es, p, q]); Es.forEach((E, k) => { if (Math.abs(P[k]) < 4 - 1e-6 && !s.intervals.some(([a, b]) => E >= a - 1e-9 && E <= b + 1e-9)) coverOK = false; }); }
check(`all ${nSlices} slices (q ≤ 20): exactly q bands, each with |P_q| = 4 at both edges and one root of P_q inside`, nSlices === 129 && sliceOK);
check('…and every energy with |P_q(E)| < 4 on a 4001-point scan lies in a drawn band (1/3, 2/7, 3/8, 5/13)', coverOK);

// --- controls, keys, presets
for (const name of ['sweep', 'cone', 'top', 'harper', 'cert', 'floor', 'bound', 'tiny']) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await click('#modeChips [data-mode="cert"]');
check('the model chips switch to the certificate, show the mass slider and mark the settings custom', (await info()).mode === 'cert' && (await visible('massField')) && (await state()).preset === null);
await D(() => { const el = document.getElementById('mm'); el.value = '-0.73'; el.dispatchEvent(new Event('input', { bubbles: true })); }); await settle();
check('the mass slider snaps to steps of 0.05', near((await state()).m, -0.75, 1e-12) && near((await info()).m, -0.75, 1e-12));
await click('#modeChips [data-mode="bound"]');
check('…the bound mode hides the slider', !(await visible('massField')) && (await info()).mode === 'bound');
await setFrac(0.5); await page.keyboard.press('ArrowRight'); await settle();
check('→ moves the mass by 0.05', near((await info()).m, 0.05, 1e-9));
await page.keyboard.press('e'); await settle();
check('E jumps to m = 2 and pauses', near((await info()).m, 2, 1e-12) && (await state()).playing === false);

// --- play and toasts
await preset('sweep'); await setFrac(0.985); await click('#play');
check('the sweep toast reports the gap at m = 2', await waitToast(/m = 2.*0\.536/));
await pause();
await preset('cert'); await setFrac(0.985); await click('#play');
check('the certificate toast reports one positive, three negative', await waitToast(/一正三负/));
await pause();
await preset('harper'); await setFrac(0.985); await click('#play');
check('the butterfly toast fires at m = 2', await waitToast(/1\/4/));
await pause();
await preset('sweep'); await setFrac(0.2); await click('#play'); await waitFrames(12); const p1 = (await state()).nowFrac; await pause();
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
await click('#modeChips [data-mode="cert"]');
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
for (const m of ['bands', 'bound', 'butterfly', 'cert']) {
  await click(`#modeChips [data-mode="${m}"]`); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${m}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('HOFSTADTER//GAP · The mass gap of the π/2-flux Hofstadter model'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the source preprint and the three classic papers', (await D(() => { const h = [...document.querySelectorAll('#drawer .en a')].map((a) => a.href).join(' '); return ['fabbri-marcelli-giuliani-2026-half-flux-hofstadter-mass-gap.md', 'HalfFluxHofstadterMassGap.lean', 'arxiv.org/abs/2609.03832', '10.1103/PhysRevB.14.2239', '10.1088/0370-1298/68/10/304', '10.1103/PhysRev.140.A135'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="hofstadter-gap"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.HG_DEBUG && HG_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'hofstadter-gap');

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
