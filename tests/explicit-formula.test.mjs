#!/usr/bin/env node
// Browser regression suite for viz/explicit-formula (Playwright + Chromium with software WebGL).
//   node tests/explicit-formula.test.mjs
// Reads page state through the read-only window.EF_DEBUG probe and checks it against an independent implementation: the zero
// table decoded with BigInt and compared with Odlyzko's printed values; ζ(1/2 + it) by Euler–Maclaurin summation and θ(t) by its
// asymptotic series, so that Z(t) must change sign between consecutive zeros; φ̂ by composite Gauss–Legendre quadrature; the
// archimedean term in t-space through the digamma function (the page computes it in x-space); prime sides by trial division.
import fs from 'node:fs';
import path from 'node:path';
import { createRequire } from 'node:module';
import { createServer, BASE } from '../scripts/serve.mjs';
import { ROOT, readRegistry } from '../scripts/site.mjs';

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
  const start = await page.evaluate(() => EF_DEBUG.frames());
  await page.waitForFunction((f0) => !EF_DEBUG.pending() && EF_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => EF_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => EF_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => EF_DEBUG.info());
const state = () => D(() => EF_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => EF_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => EF_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 60000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

// --- independent implementation
// zero table: BigInt partial sums of the base-36 differences in zeros.js
const src = fs.readFileSync(path.join(ROOT, 'viz/explicit-formula/zeros.js'), 'utf8');
const body = src.match(/EF_ZEROS_B36 = '([0-9a-z,]+)'/)[1];
const Z = (() => { let acc = 0n; return body.split(',').map((d) => { acc += [...d].reduce((v, c) => v * 36n + BigInt(parseInt(c, 36)), 0n); return Number(acc) / 1e9; }); })();
const ODLYZKO = { 1: 14.134725142, 2: 21.022039639, 3: 25.010857580, 4: 30.424876126, 5: 32.935061588, 100: 236.524229666, 1000: 1419.422480946, 10000: 9877.782654004 };
// θ(t) by its asymptotic series (valid for t ≥ 10), Z(t) = Re(e^{iθ} ζ(1/2 + it)) with ζ by Euler–Maclaurin
const thetaAsym = (t) => (t / 2) * Math.log(t / (2 * Math.PI)) - t / 2 - Math.PI / 8 + 1 / (48 * t) + 7 / (5760 * t ** 3) + 31 / (80640 * t ** 5);
const B2K = [1 / 6, -1 / 30, 1 / 42, -1 / 30, 5 / 66, -691 / 2730, 7 / 6, -3617 / 510, 43867 / 798, -174611 / 330, 854513 / 138, -236364091 / 2730];
function zetaHalf(t) {
  const N = Math.ceil(t / Math.PI) + 10; let re = 0, im = 0;
  for (let n = 1; n < N; n++) { const l = Math.log(n), a = Math.exp(-0.5 * l); re += a * Math.cos(t * l); im -= a * Math.sin(t * l); }
  const lN = Math.log(N), aN = Math.exp(-0.5 * lN), cr = Math.cos(t * lN), ci = -Math.sin(t * lN);   // N^{−s} = aN (cr + i ci)
  re += 0.5 * aN * cr; im += 0.5 * aN * ci;
  // N^{1−s}/(s − 1), s − 1 = −1/2 + it
  { const nr = N * aN * cr, ni = N * aN * ci, dr = -0.5, di = t, d2 = dr * dr + di * di; re += (nr * dr + ni * di) / d2; im += (ni * dr - nr * di) / d2; }
  // Σ B_2k/(2k)! s(s+1)…(s+2k−2) N^{−s−2k+1}
  let pr = 0.5, pi = t, fact = 2, Npow = 1 / N;               // pr + i pi = s(s+1)…(s+2k−2); Npow = N^{−(2k−1)}
  for (let k = 1; k <= B2K.length; k++) {
    const c = B2K[k - 1] / fact, wr = aN * cr * Npow, wi = aN * ci * Npow;
    re += c * (pr * wr - pi * wi); im += c * (pr * wi + pi * wr);
    for (const j of [2 * k - 1, 2 * k]) { const qr = pr * (0.5 + j) - pi * t, qi = pr * t + pi * (0.5 + j); pr = qr; pi = qi; }
    fact *= (2 * k + 1) * (2 * k + 2); Npow /= N * N;
  }
  return [re, im];
}
const Zfun = (t) => { const [re, im] = zetaHalf(t), th = thetaAsym(t); return re * Math.cos(th) - im * Math.sin(th); };
// the bump and its transform by composite Gauss–Legendre on [0, 1]
const phi = (u) => (Math.abs(u) < 1 ? Math.exp(-1 / (1 - u * u)) : 0);
const GX = [-0.9602898564975363, -0.7966664774136267, -0.5255324099163290, -0.1834346424956498, 0.1834346424956498, 0.5255324099163290, 0.7966664774136267, 0.9602898564975363];
const GW = [0.1012285362903763, 0.2223810344533745, 0.3137066458778873, 0.3626837833783620, 0.3626837833783620, 0.3137066458778873, 0.2223810344533745, 0.1012285362903763];
const gl = (f, a, b, P) => { const h = (b - a) / P; let s = 0; for (let p = 0; p < P; p++) { const m = a + (p + 0.5) * h; for (let j = 0; j < 8; j++) s += GW[j] * f(m + 0.5 * h * GX[j]); } return s * h / 2; };
const PU = []; { const P = 256, h = 1 / P; for (let p = 0; p < P; p++) for (let j = 0; j < 8; j++) { const u = (p + 0.5) * h + 0.5 * h * GX[j]; PU.push([u, GW[j] * phi(u) * h / 2]); } }
const phiHat = (xi) => { let s = 0; for (const [u, w] of PU) s += w * Math.cos(xi * u); return 2 * s; };
// Re ψ(x + iy) (digamma) by recurrence to x ≥ 15 and the asymptotic series
function reDigamma(x, y) {
  let acc = 0; while (x < 15) { acc -= x / (x * x + y * y); x += 1; }
  const r2 = x * x + y * y; let re = 0.5 * Math.log(r2) - 0.5 * x / r2;
  const ir = x / r2, ii = -y / r2, w2r = ir * ir - ii * ii, w2i = 2 * ir * ii; let pr = w2r, pi = w2i;
  for (const [k, b] of [[1, 1 / 6], [2, -1 / 30], [3, 1 / 42], [4, -1 / 30], [5, 5 / 66]]) { re -= b / (2 * k) * pr; const nr = pr * w2r - pi * w2i, ni = pr * w2i + pi * w2r; pr = nr; pi = ni; }
  return re + acc;
}
const simpson = (f, a, b, n) => { const h = (b - a) / n; let s = f(a) + f(b); for (let i = 1; i < n; i++) s += (i % 2 ? 4 : 2) * f(a + i * h); return s * h / 3; };
// archimedean term (1/2π)∫ ĝ(t)(Re ψ(1/4 + it/2) − log π) dt for even real ĝ, given on [0, tMax]
const archT = (ghat, tMax, n) => simpson((t) => (reDigamma(0.25, t / 2) - Math.log(Math.PI)) * ghat(t), 0, tMax, n) / Math.PI;
// von Mangoldt by trial division
const vonMangoldt = (n) => { for (let p = 2; p * p <= n; p++) if (n % p === 0) { let m = n; while (m % p === 0) m /= p; return m === 1 ? Math.log(p) : 0; } return n >= 2 ? Math.log(n) : 0; };
const psiExact = (x) => { let s = 0; for (let n = 2; n <= x; n++) s += vonMangoldt(n); return s; };
const close = (a, b, tol) => Math.abs(a - b) <= tol;

await page.goto(origin + BASE + 'viz/explicit-formula/');
await page.waitForFunction(() => window.EF_DEBUG && EF_DEBUG.frames() > 3, null, { timeout: 120000 });
let i = await info();
check('opens on the prime detector and plays', i.mode === 'spikes' && (await state()).playing === true);
await pause();

// --- the zero data
check('the zero table decodes to 10 000 increasing values matching Odlyzko’s printed zeros', Z.length === 10000 && Z.every((g, k) => k === 0 || g > Z[k - 1]) && Object.entries(ODLYZKO).every(([n, g]) => Math.abs(Z[n - 1] - g) < 5e-10));
check('the page decodes the same table', i.nZeros === 10000 && i.zerosHead.every((g, k) => Math.abs(g - Z[k]) < 1e-12) && Math.abs(i.zeroLast - Z[9999]) < 1e-9);
let flips = 0, worst = Infinity;
for (let k = 0; k + 1 < Z.length; k++) { const a = Zfun((Z[k] + Z[k + 1]) / 2); if (k % 2 === 0 ? a > 0 : a < 0) flips++; worst = Math.min(worst, Math.abs(a)); }
check('Z(t) (Euler–Maclaurin) alternates in sign at the midpoints between consecutive zeros (positive after γ₁), so each gap holds an odd number of zeros', flips === Z.length - 1, `smallest |Z| at a midpoint ${worst.toExponential(2)}`);
const zAt = Z.slice(0, 50).map((g) => Math.abs(Zfun(g)));
check('…and |Z(γ)| is tiny at the first 50 tabulated zeros', Math.max(...zAt) < 5e-8, Math.max(...zAt).toExponential(2));
const counts = [100, 1000, 5000, 9000].map((T) => [Z.filter((g) => g <= T).length, thetaAsym(T) / Math.PI + 1]);
check('N(T) from the table stays within 1.5 of θ(T)/π + 1 at T = 100, 1000, 5000, 9000 (no missing zeros)', counts.every(([n, s]) => Math.abs(n - s) < 1.5), counts.map(([n, s]) => `${n}/${s.toFixed(2)}`).join(' '));

// --- ψ(x): von Mangoldt’s formula
await preset('psi30'); await setFrac(1); i = await info();
const psiFormula = (x, K) => { let s = x - Math.log(2 * Math.PI) - 0.5 * Math.log(1 - 1 / (x * x)); for (let k = 0; k < K; k++) { const g = Z[k], a = g * Math.log(x); s -= 2 * Math.sqrt(x) * (0.5 * Math.cos(a) + g * Math.sin(a)) / (0.25 + g * g); } return s; };
const idx = [100, 500, 999, 1500, 1990];
check('ψ ≤ 30: 600 pairs of zeros; the page’s formula curve matches an independent sum at sampled x', i.K === 600 && i.Kmax === 600 && idx.every((q) => close(i.curve[q], psiFormula(i.xs[q], 600), 2e-3)), idx.map((q) => `${i.xs[q].toFixed(2)}:${i.curve[q].toFixed(3)}`).join(' '));
check('…the exact staircase ψ(x) matches trial division', idx.every((q) => close(i.exact[q], psiExact(i.xs[q]), 1e-9)));
const meanErr = (K) => { let s = 0, c = 0; for (let q = 0; q < i.xs.length; q += 7) if (i.xs[q] >= 2) { s += Math.abs(psiFormula(i.xs[q], K) - psiExact(i.xs[q])); c++; } return s / c; };
const e40 = meanErr(40), e600 = meanErr(600);
check('…and the mean error over 2 ≤ x ≤ 30 drops from 40 to 600 pairs, below 0.06', e600 < e40 && e600 < 0.06, `${e40.toFixed(3)} → ${e600.toFixed(3)}`);
check('…the readouts name the zeros used and ψ(X)/X', /600/.test(await text('ro1')) && close(parseFloat(await text('ro5')), psiExact(30) / 30, 1e-4));
await setFrac(0.5); i = await info();
const K05 = Math.round(Math.pow(601, 0.5)) - 1;
check('half way along the rail uses K = ⌊√601⌉ − 1 pairs', i.K === K05 && close(i.curve[999], psiFormula(i.xs[999], K05), 2e-3), `K ${i.K}`);
await setRange('xx', 100); i = await info();
check('X = 100 raises the number of pairs to 2000 and marks the settings custom', i.Kmax === 2000 && i.X === 100 && (await state()).preset === null);

// --- the prime detector (Weil’s formula with bumps at ±a)
await preset('spikes'); await setFrac(1); i = await info();
const eps = 0.06, sel = [0, 101, 287, 450, 700, 899];
const J = 2 * gl((u) => phi(u) * Math.cosh(eps * u / 2), 0, 1, 64);
const poleA = (a) => 4 * eps * Math.cosh(a / 2) * J;
const primeA = (a) => { let s = 0; for (let n = 2; Math.log(n) < a + eps; n++) { const u = (Math.log(n) - a) / eps; if (u > -1) s += 2 * vonMangoldt(n) / Math.sqrt(n) * phi(u); } return s; };
check('prime detector: pole and prime terms match independent quadrature and trial division', sel.every((q) => close(i.pole[q], poleA(i.as[q]), 1e-11) && close(i.prime[q], primeA(i.as[q]), 1e-11)));
const wIndep = Z.slice(0, 50).map((g) => 4 * eps * phiHat(eps * g));
check('…the weight 4εφ̂(εγ) of each zero matches Gauss–Legendre quadrature', wIndep.every((w, k) => close(i.wHead[k], w, 1e-13)));
const wSp = Z.map((g) => (eps * g > 700 ? 0 : 4 * eps * phiHat(eps * g)));
const zeroA = (a) => { let s = 0; for (let k = 0; k < Z.length; k++) s += wSp[k] * Math.cos(a * Z[k]); return s; };
const zs = [101, 450, 899].map((q) => [i.zeroCurve[q], zeroA(i.as[q]), i.pole[q] - i.prime[q] + i.arch[q]]);
check('…with all 10⁴ zeros the zero side equals pole − prime + archimedean (frozen identity), independently summed', zs.every(([zp, zi, r]) => close(zp, zi, 1e-10) && close(zi, r, 1e-8)), zs.map(([zp, zi, r]) => (zi - r).toExponential(1)).join(' '));
check('…and the page reports the largest gap between the two sides below 10⁻⁸', i.idErr < 1e-8, i.idErr.toExponential(2));
const peak = (p) => { const q = Math.round((Math.log(p) - i.as[0]) / (i.as[1] - i.as[0])); return [i.curve[q], i.target[q]]; };
check('…the spike at a ≈ log 2 has height log 2 and at a ≈ log 3 height log 3', [2, 3].every((p) => { const [c, t] = peak(p); return close(c, t, 1e-5) && close(t, Math.log(p), 3e-3); }), [2, 3].map((p) => peak(p)[0].toFixed(4)).join(' '));
await setFrac(0.3); i = await info();
let dev = 0; for (let q = 0; q < i.curve.length; q++) dev = Math.max(dev, Math.abs(i.curve[q] - i.target[q]));
check('…with few zeros (K = ⌊10001^0.3⌉ − 1) the curve is still far from the spikes', i.K === Math.round(Math.pow(10001, 0.3)) - 1 && dev > 0.5, `K ${i.K} · max dev ${dev.toFixed(2)}`);
// archimedean term in t-space (digamma) for the wide bump, ε = 0.2
await preset('blur'); await setFrac(1); i = await info();
const e2 = 0.2, NT = 130000, TT = 2600, PH2 = Float64Array.from({ length: NT + 1 }, (_, q) => e2 * phiHat(e2 * TT * q / NT));
const archIndep = (a) => archT((t) => 2 * Math.cos(a * t) * PH2[Math.round(t / TT * NT)], TT, NT);
const aq = [120, 640];
const archPairs = aq.map((q) => [i.arch[q], archIndep(i.as[q])]);
check('blur (ε = 0.2): the page’s x-space archimedean term equals the t-space digamma integral', archPairs.every(([p, r]) => close(p, r, 1e-8)), archPairs.map(([p, r]) => `${p.toFixed(8)}/${(p - r).toExponential(1)}`).join(' '));
await setRange('eps', 0.1); i = await info();
check('the ε slider sets ε = 0.10 and the weights follow', close(i.eps, 0.1, 1e-12) && close(i.wHead[0], 4 * 0.1 * phiHat(0.1 * Z[0]), 1e-13) && (await state()).preset === null);

// --- balance: one bump g(x) = φ(x/3)
await preset('balance'); await setFrac(1); i = await info();
const L3 = 3, poleB = 2 * L3 * 2 * gl((u) => phi(u) * Math.cosh(L3 * u / 2), 0, 1, 64);
let primeB = 0; for (let n = 2; Math.log(n) < L3; n++) primeB += 2 * vonMangoldt(n) / Math.sqrt(n) * phi(Math.log(n) / L3);
const archB = archT((t) => L3 * phiHat(L3 * t), 300, 60000);
let zeroB = 0; for (const g of Z) { if (L3 * g > 700) break; zeroB += 2 * L3 * phiHat(L3 * g); }
check('balance: pole, prime and archimedean terms match independent values (archimedean via digamma)', close(i.pole, poleB, 1e-10) && close(i.prime, primeB, 1e-10) && close(i.arch, archB, 1e-8), `${i.pole.toFixed(6)} ${i.prime.toFixed(6)} ${i.arch.toFixed(6)}`);
check('…the zero side with 10⁴ zeros matches an independent sum and equals the prime side', close(i.zeroAll, zeroB, 1e-12) && close(zeroB, poleB - primeB + archB, 1e-8), `${zeroB.toExponential(6)} vs ${(poleB - primeB + archB).toExponential(6)}`);
check('…the three terms are each a few units but the two sides are only −0.00148', i.pole > 3 && i.prime > 1.5 && i.arch < -1 && close(i.rhs, -0.00148107, 1e-8));
check('…the readouts show both sides and a difference below 10⁻¹⁰', /-1\.48107e-3|−1\.48107e-3|-0\.00148107/.test(await text('ro2')) && Math.abs(parseFloat(await text('ro4'))) < 1e-10, `${await text('ro2')} · ${await text('ro4')}`);
await setRange('ll', 1.5); i = await info();
let primeB15 = 0; for (let n = 2; Math.log(n) < 1.5; n++) primeB15 += 2 * vonMangoldt(n) / Math.sqrt(n) * phi(Math.log(n) / 1.5);
check('the L slider rebuilds the bump: L = 1.5 keeps only n ≤ e^1.5 in the prime term', close(i.L, 1.5, 1e-12) && close(i.prime, primeB15, 1e-10) && i.primeList.map((x) => x[0]).join(',') === '2,3,4', i.primeList.map((x) => x[0]).join(','));

// --- Weil square g = f ∗ f, f(x) = φ(x)
await preset('square'); await setFrac(1); i = await info();
const fhat1 = (t) => phiHat(t);
const fi = 2 * gl((u) => phi(u) * Math.cosh(u / 2), 0, 1, 64), poleS = 2 * fi * fi;
const conv1 = (y) => gl((x) => phi(x) * phi(y - x), Math.max(-1, y - 1), Math.min(1, y + 1), 128);
let primeS = 0; for (let n = 2; Math.log(n) < 2; n++) primeS += 2 * vonMangoldt(n) / Math.sqrt(n) * conv1(Math.log(n));
const archS = archT((t) => fhat1(t) ** 2, 300, 60000);
let zeroS = 0; for (const g of Z) { if (g > 700) break; zeroS += 2 * fhat1(g) ** 2; }
check('Weil square: every one of the 10⁴ zero terms is ≥ 0', i.wNonneg === true && i.wHead.every((w) => w >= 0));
check('…the zero side equals the prime side, both positive, matching independent values', close(i.zeroAll, zeroS, 1e-13) && close(i.rhs, poleS - primeS + archS, 1e-9) && i.rhs > 0 && close(zeroS, poleS - primeS + archS, 1e-9), `${zeroS.toExponential(5)} vs ${(poleS - primeS + archS).toExponential(5)}`);
await setFrac(0.5); const iHalf = await info(); let part = 0; for (let k = 0; k < 99; k++) part += 2 * fhat1(Z[k]) ** 2;
check('…half way (K = 99) the partial zero sum matches an independent one and is no larger than the full sum', iHalf.K === 99 && close(iHalf.zeroSide, part, 1e-13) && iHalf.zeroSide <= i.zeroAll, `${iHalf.zeroSide.toExponential(6)} ≤ ${i.zeroAll.toExponential(6)}`);

// --- the hypothetical off-line pair
await preset('offline'); await setFrac(0); i = await info();
const g1 = Z[0], L = 3, fo = (x) => x * Math.sin(g1 * x) * phi(x / L);
const fhatO = (zr, zi) => { let re = 0, im = 0; const f = (x) => [fo(x) * Math.cos(zr * x) * Math.cosh(zi * x), fo(x) * Math.sin(zr * x) * Math.sinh(zi * x)]; const P = 384, h = L / P; for (let p = 0; p < P; p++) { const m = (p + 0.5) * h; for (let j = 0; j < 8; j++) { const [a, b] = f(m + 0.5 * h * GX[j]); re += GW[j] * a; im += GW[j] * b; } } return [re * h, im * h]; };
const pairO = (d) => { const [a, b] = fhatO(g1, d); return 4 * (a * a - b * b); };
let Son = 0; for (const g of Z) { if (Math.abs(g - g1) * L > 700) break; const [a] = fhatO(g, 0); Son += 2 * a * a; }
check('off-line: at δ = 0 the real zeros give a positive sum, matching an independent sum and the prime side', close(i.Son, Son, 1e-12) && i.Son > 0 && close(i.Son, i.rhs, 1e-11), `${i.Son.toExponential(4)} · rhs ${i.rhs.toExponential(4)}`);
let lo = 0, hi = 0.05; for (let it = 0; it < 50; it++) { const m = (lo + hi) / 2; if (Son - i.own + pairO(m) > 0) lo = m; else hi = m; }
check('…the zero sum of the hypothetical set turns negative at the same δ, independently bisected (about 0.0048)', i.cross !== null && close(i.cross, lo, 1e-6) && close(lo, 0.00477, 1e-4), `${i.cross === null ? 'none' : i.cross.toFixed(6)} vs ${lo.toFixed(6)}`);
await setFrac(Math.sqrt(0.0125 / 0.05)); i = await info();
check('…at δ = 0.0125 the pair contributes 4 Re f̂(γ₁ − iδ)² < 0 and W(δ) < 0', close(i.d, 0.0125, 1e-9) && close(i.P, pairO(0.0125), 1e-10) && i.W < 0 && close(i.W, Son - i.own + pairO(0.0125), 1e-10), `${i.P.toExponential(3)} · ${i.W.toExponential(3)}`);
check('…and the note says it violates Weil positivity and is not in the real data', /违反 Weil 正性/.test(await text('roNote')) && /没有这样的零点/.test(await text('roNote')));

// --- counting zeros
await preset('count'); await setFrac(0.6); i = await info();
const Tc = 9877.782654004 * 0.36;
check('count: N(T) at T = 0.36·γ₁₀₀₀₀ matches the table and θ(T)/π + 1 matches the asymptotic series', close(i.t, Tc, 1e-6) && i.N === Z.filter((g) => g <= Tc).length && close(i.smooth, thetaAsym(Tc) / Math.PI + 1, 1e-9), `N ${i.N} · ${i.smooth.toFixed(4)}`);
const th = await D(() => [20, 100, 1000, 9000].map((t) => EF_DEBUG.theta(t)));
check('…the page’s θ (recurrence + Stirling) agrees with the asymptotic series at 20, 100, 1000, 9000', th.every((v, k) => close(v, thetaAsym([20, 100, 1000, 9000][k]), 1e-9)));
const dyad = []; for (let j = 4; j <= 12; j++) { const a = 2 ** j; dyad.push(Z.filter((g) => g > a && g <= 2 * a).length); }
check('…the dyadic counts N(T, 2T) for T = 16 … 4096 are the independent ones and keep growing', (await text('ro5')) === dyad.join(' · ') && dyad.every((n, k) => k === 0 || n > dyad[k - 1]), dyad.join(' '));
await setFrac(1); i = await info();
check('…at the end of the rail all 10 000 zeros are counted', i.N === 10000);

// --- controls, keys, presets
for (const name of ['psi30', 'psi100', 'spikes', 'blur', 'balance', 'square', 'offline', 'count']) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await click('#modeChips [data-mode="psi"]');
check('the formula chips switch the mode, show the x field and mark the settings custom', (await info()).mode === 'psi' && (await visible('xField')) && !(await visible('epsField')) && !(await visible('lField')) && (await state()).preset === null && /自定义/.test(await text('presetNote')));
await click('#modeChips [data-mode="square"]');
check('…the square mode shows the L field with its own range 0.3–3 and default L = 1', (await visible('lField')) && (await D(() => [document.getElementById('ll').min, document.getElementById('ll').max].join('-'))) === '0.3-3' && (await info()).L === 1);
await preset('spikes'); await setFrac(0.2);
await page.keyboard.press('ArrowRight'); await settle();
check('→ moves one step along the rail', close((await state()).nowFrac, 0.2 + 1 / 400, 1e-9));
await page.keyboard.press('e'); await settle();
check('E jumps to the end (all zeros) and pauses', (await info()).K === 10000 && (await state()).playing === false);
check('the rail is marked in numbers of zeros', /10000/.test(await D(() => document.getElementById('marks').textContent)));

// --- play and toasts
await preset('offline'); await setFrac(0.25); await click('#play');
check('the off-line toast fires when the zero sum turns negative', await waitToast(/零点和变负/));
await pause();
await preset('balance'); await setFrac(0.99); await click('#play');
check('the balance toast reports zero side = prime side at the end', await waitToast(/零点一侧 = 素数一侧/));
await pause();
await preset('count'); await setFrac(0.99); await click('#play');
check('the count toast reports all 10 000 zeros', await waitToast(/10000/));
await pause();
await preset('spikes'); await setFrac(0.3); await click('#play'); await waitFrames(12); const p1 = (await state()).nowFrac; await pause();
check('play advances along the rail', p1 > 0.3);
await click('#rev'); await waitFrames(12); const p2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', p2 < p1);
await page.click('#rev'); await pause();
await page.focus('#eps'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await setRange('eps', 0.12);
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /PRIME SIDE/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('EXPLICIT//FORMULA · Rebuilding the primes'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
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
await page.click('.card:has(a[href*="explicit-formula"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.EF_DEBUG && EF_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'explicit-formula');

// --- narrow layouts in both languages
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await waitFrames(3);
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await waitFrames(6);
    check(`no horizontal scroll at ${w}px (${lang})`, (await D(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 }); await waitFrames(3);
}
check('no script errors during the whole session', errors.length === 0, errors.join(' | '));

const failed = results.filter(r => !r.ok);
console.log(`\n${results.length - failed.length}/${results.length} passed`);
await browser.close(); server.close();
if (failed.length) process.exit(1);
