#!/usr/bin/env node
// Browser regression suite for viz/lindblad-zero (Playwright + Chromium with software WebGL).
//   node tests/lindblad-zero.test.mjs
// Reads page state through the read-only window.LZ_DEBUG probe and checks it against an independent implementation: the
// Lindblad matrix entry is evaluated literally (every sum written out over a window) on unit kernels, the truncated trace is
// assembled from it, the ring generator is built as one full N² × N² matrix with periodic indices (no momentum blocks), and
// the page's eigenvalues are checked by LU factorisation of (M − λI), by power sums against traces of M^p, and against the
// closed form g(e^{−iq} − 1) of the right-jump generator. Only the generator's defining tables are read from the page.
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
  const start = await page.evaluate(() => LZ_DEBUG.frames());
  await page.waitForFunction((f0) => !LZ_DEBUG.pending() && LZ_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => LZ_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => LZ_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => LZ_DEBUG.info());
const state = () => D(() => LZ_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => LZ_DEBUG.frames()); await page.waitForFunction((t) => LZ_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- independent implementation ---------- */
const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]], cadd = (a, b) => [a[0] + b[0], a[1] + b[1]];
const cconj = (a) => [a[0], -a[1]], cnorm = (a) => Math.hypot(a[0], a[1]);
/* tables → functions; on a ring the differences are taken modulo N into (−N/2, N/2] */
function generator(tab, g, N = 0) {
  const rep = (d) => { if (!N) return d; let e = ((d % N) + N) % N; if (e > N / 2) e -= N; return e; };
  const H = new Map(tab.h.map(([d, re, im]) => [d, [re, im]])), Lm = new Map(tab.l.map(([a, b, re, im]) => [`${a},${b}`, [re, im]]));
  return { r: tab.r, g, N, h: (x, y) => H.get(rep(y - x)) || [0, 0], l: (k, x, y) => Lm.get(`${rep(x - k)},${rep(y - k)}`) || [0, 0] };
}
/* (tρ)(x, y) for a sparse kernel ρ (Map "u,v" → complex), every sum written out literally over a window around the support */
function entry(G, rho, x, y) {
  const { g, h, l } = G, R = G.r, get = (u, v) => rho.get(`${u},${v}`) || [0, 0], lo = Math.min(x, y) - 3 * R - 1, hi = Math.max(x, y) + 3 * R + 1;
  const rng = (a, b) => { const out = []; for (let i = a; i <= b; i++) out.push(i); return out; };
  const Z = rng(lo - 2 * R, hi + 2 * R);
  let s = [0, 0];
  for (const z of Z) s = cadd(s, cmul(h(x, z), get(z, y)));
  for (const z of Z) s = cadd(s, cmul(get(x, z), h(z, y)).map((v) => -v));
  let out = cmul([0, -1], s), diss = [0, 0];
  for (const k of rng(lo, hi)) {
    let a = [0, 0];
    for (const u of Z) for (const v of Z) { const lu = l(k, x, u); if (!lu[0] && !lu[1]) continue; a = cadd(a, cmul(cmul(lu, get(u, v)), cconj(l(k, y, v)))); }
    for (const z of Z) { let w = [0, 0]; for (const ww of Z) w = cadd(w, cmul(cconj(l(k, ww, x)), l(k, ww, z))); a = cadd(a, cmul(w, get(z, y)).map((v) => -v / 2)); }
    for (const z of Z) { let w = [0, 0]; for (const ww of Z) w = cadd(w, cmul(cconj(l(k, ww, z)), l(k, ww, y))); a = cadd(a, cmul(get(x, z), w).map((v) => -v / 2)); }
    diss = cadd(diss, a);
  }
  return cadd(out, [diss[0] * g, diss[1] * g]);
}
/* coefficients of Σ_{|x| ≤ n} (tρ)(x, x) by evaluating on unit kernels e_p over a window that surely contains the support */
function truncatedTrace(G, n) {
  const W = n + 4 * G.r + 2, out = new Map();
  for (let u = -W; u <= W; u++) for (let v = u - 4 * G.r - 1; v <= u + 4 * G.r + 1; v++) {
    const rho = new Map([[`${u},${v}`, [1, 0]]]); let s = [0, 0];
    for (let x = -n; x <= n; x++) if (Math.abs(x - u) <= 2 * G.r + 1) s = cadd(s, entry(G, rho, x, x));
    if (cnorm(s) > 1e-12) out.set(`${u},${v}`, s);
  }
  return out;
}
/* the ring generator on ℤ_N with every sum taken over the N sites, evaluated on the unit kernel at (u0, v0) */
function entryRingUnit(G, u0, v0, x, y) {
  const { g, h, l, N } = G, md = (a) => ((a % N) + N) % N, eq = (a, b) => md(a - b) === 0;
  let out = [0, 0];
  if (eq(v0, y)) out = cadd(out, cmul([0, -1], h(x, u0)));                 // −i Σ_z h(x, z) ρ(z, y)
  if (eq(u0, x)) out = cadd(out, cmul([0, 1], h(v0, y)));                  // + i Σ_z ρ(x, z) h(z, y)
  let diss = [0, 0];
  for (let k = 0; k < N; k++) {
    diss = cadd(diss, cmul(l(k, x, u0), cconj(l(k, y, v0))));
    if (eq(v0, y)) { let w = [0, 0]; for (let ww = 0; ww < N; ww++) w = cadd(w, cmul(cconj(l(k, ww, x)), l(k, ww, u0))); diss = cadd(diss, [-w[0] / 2, -w[1] / 2]); }
    if (eq(u0, x)) { let w = [0, 0]; for (let ww = 0; ww < N; ww++) w = cadd(w, cmul(cconj(l(k, ww, v0)), l(k, ww, y))); diss = cadd(diss, [-w[0] / 2, -w[1] / 2]); }
  }
  return cadd(out, [diss[0] * g, diss[1] * g]);
}
/* one full ring matrix M[(x, y), (u, v)], row-major complex */
function ringMatrix(G, N) {
  const D2 = N * N, Mr = new Float64Array(D2 * D2), Mi = new Float64Array(D2 * D2);
  for (let u = 0; u < N; u++) for (let v = 0; v < N; v++) for (let x = 0; x < N; x++) for (let y = 0; y < N; y++) {
    const e = entryRingUnit(G, u, v, x, y), row = x * N + y, col = u * N + v; Mr[row * D2 + col] = e[0]; Mi[row * D2 + col] = e[1];
  }
  return { D2, Mr, Mi };
}
/* growth of the solution of (M − λI)z = b through LU with partial pivoting: large growth means λ is (nearly) an eigenvalue */
function luGrowth(n, Mr, Mi, lam) {
  const Ar = Float64Array.from(Mr), Ai = Float64Array.from(Mi);
  for (let i = 0; i < n; i++) { Ar[i * n + i] -= lam[0]; Ai[i * n + i] -= lam[1]; }
  /* a generic right-hand side: a constant vector would sit in one momentum sector and miss the others */
  let seed = 12345; const rnd = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648) - 0.5;
  const br = Float64Array.from({ length: n }, rnd), bi = Float64Array.from({ length: n }, rnd);
  for (let k = 0; k < n; k++) {
    let p = k, best = -1; for (let i = k; i < n; i++) { const a = Math.hypot(Ar[i * n + k], Ai[i * n + k]); if (a > best) { best = a; p = i; } }
    if (best < 1e-300) return Infinity;
    if (p !== k) { for (let j = 0; j < n; j++) { [Ar[k * n + j], Ar[p * n + j]] = [Ar[p * n + j], Ar[k * n + j]]; [Ai[k * n + j], Ai[p * n + j]] = [Ai[p * n + j], Ai[k * n + j]]; } [br[k], br[p]] = [br[p], br[k]]; [bi[k], bi[p]] = [bi[p], bi[k]]; }
    const pr = Ar[k * n + k], pi = Ai[k * n + k], d = pr * pr + pi * pi;
    for (let i = k + 1; i < n; i++) {
      const fr = (Ar[i * n + k] * pr + Ai[i * n + k] * pi) / d, fi = (Ai[i * n + k] * pr - Ar[i * n + k] * pi) / d;
      if (!fr && !fi) continue;
      for (let j = k; j < n; j++) { const ar = Ar[k * n + j], ai = Ai[k * n + j]; Ar[i * n + j] -= fr * ar - fi * ai; Ai[i * n + j] -= fr * ai + fi * ar; }
      br[i] -= fr * br[k] - fi * bi[k]; bi[i] -= fr * bi[k] + fi * br[k];
    }
  }
  const zr = new Float64Array(n), zi = new Float64Array(n);
  for (let i = n - 1; i >= 0; i--) {
    let sr = br[i], si = bi[i]; for (let j = i + 1; j < n; j++) { sr -= Ar[i * n + j] * zr[j] - Ai[i * n + j] * zi[j]; si -= Ar[i * n + j] * zi[j] + Ai[i * n + j] * zr[j]; }
    const pr = Ar[i * n + i], pi = Ai[i * n + i], d = pr * pr + pi * pi; zr[i] = (sr * pr + si * pi) / d; zi[i] = (si * pr - sr * pi) / d;
  }
  let z = 0; for (let i = 0; i < n; i++) z += zr[i] ** 2 + zi[i] ** 2;
  return Math.sqrt(z / n);
}
/* traces of M, M², M³ against the power sums of the eigenvalues */
function powerSums(n, Mr, Mi, ev) {
  let Pr = Float64Array.from(Mr), Pi = Float64Array.from(Mi), worst = 0;
  for (let p = 1; p <= 3; p++) {
    let tr = [0, 0]; for (let i = 0; i < n; i++) { tr[0] += Pr[i * n + i]; tr[1] += Pi[i * n + i]; }
    let s = [0, 0]; for (const e of ev) { let z = [1, 0]; for (let k = 0; k < p; k++) z = cmul(z, e); s = cadd(s, z); }
    worst = Math.max(worst, cnorm([tr[0] - s[0], tr[1] - s[1]]) / Math.max(1, cnorm(tr)));
    if (p === 3) break;
    const Qr = new Float64Array(n * n), Qi = new Float64Array(n * n);
    for (let i = 0; i < n; i++) for (let k = 0; k < n; k++) { const ar = Pr[i * n + k], ai = Pi[i * n + k]; if (!ar && !ai) continue; for (let j = 0; j < n; j++) { const br = Mr[k * n + j], bi = Mi[k * n + j]; if (!br && !bi) continue; Qr[i * n + j] += ar * br - ai * bi; Qi[i * n + j] += ar * bi + ai * br; } }
    Pr = Qr; Pi = Qi;
  }
  return worst;
}
const sameMap = (pageA, mine) => { if (pageA.length !== mine.size) return false; for (const [u, v, re, im] of pageA) { const m = mine.get(`${u},${v}`); if (!m || Math.hypot(m[0] - re, m[1] - im) > 1e-11) return false; } return true; };
const normOf = (m) => Math.sqrt([...m.values()].reduce((s, c) => s + c[0] ** 2 + c[1] ** 2, 0));

/* ---------- open ---------- */
await page.goto(origin + BASE + 'viz/lindblad-zero/');
await page.waitForFunction(() => window.LZ_DEBUG && LZ_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
/* state and info read in one evaluation: the page autoplays, so n may already have moved off 0 */
const [s0, i0] = await D(() => [LZ_DEBUG.state(), LZ_DEBUG.info()]); let i = i0;
check('opens on Klausen’s example (dephased hopping, g = 1, ring ℤ₂₄) at the start of the n axis and plays', s0.preset === 'deph' && i.gen === 'deph' && i.g === 1 && i.N === 24 && s0.nowFrac < 0.25 && i.n === Math.round(s0.nowFrac * 16) && s0.playing === true, `n = ${i.n}`);
await pause();
const tabs = { deph: await D(() => LZ_DEBUG.genData('deph')), jump: await D(() => LZ_DEBUG.genData('jump')), rand: await D(() => LZ_DEBUG.genData('rand')) };
check('the dephasing and jump tables are the stated generators: h(x, x ± 1) = 1, ℓ(k, k, k) = 1; ℓ(k, k + 1, k) = 1 and h = 0', JSON.stringify(tabs.deph.h.sort((a, b) => a[0] - b[0])) === '[[-1,1,0],[1,1,0]]' && JSON.stringify(tabs.deph.l) === '[[0,0,1,0]]' && tabs.jump.h.length === 0 && JSON.stringify(tabs.jump.l) === '[[1,0,1,0]]' && tabs.deph.r === 1 && tabs.jump.r === 1);
const randH0 = new Map(tabs.rand.h.map(([d, re, im]) => [d, [re, im]])), randH = { get: (d) => randH0.get(d) || [NaN, NaN] };
const randRank = (() => { const M = [-1, 0, 1].map((a) => [-1, 0, 1].map((b) => { const e = tabs.rand.l.find((t) => t[0] === a && t[1] === b); return e ? [e[2], e[3]] : [0, 0]; })); const det = (m) => cadd(cadd(cmul(m[0][0], cadd(cmul(m[1][1], m[2][2]), cmul(m[1][2], m[2][1]).map((v) => -v))), cmul(m[0][1], cadd(cmul(m[1][0], m[2][2]), cmul(m[1][2], m[2][0]).map((v) => -v))).map((v) => -v)), cmul(m[0][2], cadd(cmul(m[1][0], m[2][1]), cmul(m[1][1], m[2][0]).map((v) => -v)))); return cnorm(det(M)); })();
check('the random generator has range 1, a Hermitian h and jump blocks of full rank 3', tabs.rand.r === 1 && Math.hypot(randH.get(1)[0] - randH.get(-1)[0], randH.get(1)[1] + randH.get(-1)[1]) < 1e-15 && randH.get(0)[1] === 0 && tabs.rand.l.every((t) => Math.max(Math.abs(t[0]), Math.abs(t[1])) <= 1) && randRank > 1e-3, `|det| = ${randRank.toFixed(4)}`);

/* ---------- the truncated trace ---------- */
const cases = [['deph', 1], ['jump', 1], ['rand', 0.5], ['deph', -1], ['jump', 0.7]];
let ttOK = true, ttBad = [], edgeOK = true, countOK = true, cancelOK = true;
for (const [gen, g] of cases) {
  await click(`#genChips [data-gen="${gen}"]`);
  await D((g) => { const el = document.getElementById('gSlider'); el.value = g; el.dispatchEvent(new Event('input', { bubbles: true })); }, g); await settle();
  const G = generator(tabs[gen], g);
  for (const n of [0, 1, 2, 5, 16]) {
    await setFrac(n / 16); const x = await info(), mine = truncatedTrace(G, n);
    if (x.gen !== gen || x.g !== g || x.n !== n || !sameMap(x.a, mine) || Math.abs(x.norm - normOf(mine)) > 1e-11) { ttOK = false; ttBad.push(`${gen}/${g}/n=${n}`); }
    for (const [u, v] of x.a) if (!((Math.abs(u - n) <= 2 || Math.abs(u + n) <= 2) && Math.abs(v - u) <= 4)) edgeOK = false;
    if (x.a.length > 2 * 5 * 9 || x.bound !== 90) countOK = false;
  }
  /* trace_single_zero: the full trace of t applied to a matrix unit vanishes */
  for (const [u, v] of [[0, 0], [2, 3], [-1, 1], [4, 4], [0, 2]]) { const rho = new Map([[`${u},${v}`, [1, 0]]]); let s = [0, 0]; for (let x = u - 4; x <= u + 4; x++) s = cadd(s, entry(G, rho, x, x)); if (cnorm(s) > 1e-12) cancelOK = false; }
}
check('for five generators and n = 0, 1, 2, 5, 16 the page’s truncated-trace coefficients and norm equal the literal sum of matrix entries', ttOK, ttBad.join(' '));
check('every surviving coefficient lies in the Lean edge region (u within 2r of ±n, v within 4r of u), at most 2(4r + 1)(8r + 1) = 90 of them', edgeOK && countOK);
check('the full trace of t applied to a matrix unit is 0 for every generator (trace_single_zero, checked on 25 units)', cancelOK);
await preset('deph'); await setFrac(7 / 16); i = await info();
const dephA = new Map(i.a.map(([u, v, re, im]) => [`${u},${v}`, [re, im]])), dA = (k) => dephA.get(k) || [NaN, NaN];
check('dephasing: the truncated trace is −i[ρ(n+1, n) − ρ(−n, −n−1) + ρ(−n−1, −n) − ρ(n, n+1)], norm exactly 2', i.n === 7 && dephA.size === 4 && Math.hypot(dA('8,7')[1] + 1, dA('8,7')[0]) < 1e-12 && Math.hypot(dA('-7,-8')[1] - 1, dA('-7,-8')[0]) < 1e-12 && Math.hypot(dA('-8,-7')[1] + 1, dA('-8,-7')[0]) < 1e-12 && Math.hypot(dA('7,8')[1] - 1, dA('7,8')[0]) < 1e-12 && Math.abs(i.norm - 2) < 1e-12);
await preset('jump'); await setFrac(1); i = await info();
check('right jumps: the truncated trace is g(ρ(−n−1, −n−1) − ρ(n, n)), norm g√2', i.a.length === 2 && i.a.some(([u, v, re, im]) => u === -17 && v === -17 && Math.abs(re - 1) < 1e-12 && Math.abs(im) < 1e-12) && i.a.some(([u, v, re, im]) => u === 16 && v === 16 && Math.abs(re + 1) < 1e-12 && Math.abs(im) < 1e-12) && Math.abs(i.norm - Math.SQRT2) < 1e-12);
await preset('rand'); i = await info();
const randNorms = i.norms;
check('random generator: the norm changes only up to n = 2r = 2 and is constant from there on (K = its maximum)', randNorms.slice(2).every((v) => Math.abs(v - randNorms[2]) < 1e-12) && Math.abs(i.K - Math.max(...randNorms)) < 1e-15 && Math.abs(randNorms[0] - randNorms[2]) > 1e-3, randNorms.slice(0, 4).map((v) => v.toFixed(4)).join(' '));
check('‖P_n‖² = 2n + 1 and the bound √(2n + 1)/K appear in the readouts', /n = 8 · 17/.test(await text('ro2')) && new RegExp(`K = ${i.K.toFixed(4)} · ${(Math.sqrt(17) / i.K).toFixed(4)}`).test(await text('ro4')));

/* ---------- the ring spectrum ---------- */
let specBad = [];
for (const [gen, g] of [['deph', 1], ['rand', 0.5], ['deph', -1]]) {
  await click(`#genChips [data-gen="${gen}"]`);
  await D((g) => { const el = document.getElementById('gSlider'); el.value = g; el.dispatchEvent(new Event('input', { bubbles: true })); }, g);
  await click('#ringChips [data-ring="12"]');
  const x = await info(), ev = (await D(() => LZ_DEBUG.spectrum())).map((e) => [e[0], e[1]]), { D2, Mr, Mi } = ringMatrix(generator(tabs[gen], g, 12), 12);
  const growth = ev.map((e) => luGrowth(D2, Mr, Mi, e)), weakest = Math.min(...growth), ps = powerSums(D2, Mr, Mi, ev);
  const probe = luGrowth(D2, Mr, Mi, [0.123, 0.456]);
  if (x.N !== 12 || ev.length !== 144 || weakest < 1e6 || ps > 1e-9 || probe > 1e3) specBad.push(`${gen}/${g}: n=${ev.length} weakest growth ${weakest.toExponential(1)} power-sum err ${ps.toExponential(1)} control ${probe.toFixed(1)}`);
  if (x.zeros !== 1 || Math.abs(Math.min(...ev.map((e) => cnorm(e)))) > 1e-9) specBad.push(`${gen}/${g}: zero eigenvalues ${x.zeros}`);
}
check('ring ℤ₁₂: each of the 144 page eigenvalues makes the independently built 144 × 144 matrix M − λI singular (LU growth > 10⁶), power sums match tr M, tr M², tr M³, and exactly one eigenvalue is 0', specBad.length === 0, specBad.join(' | '));
await preset('jump'); await click('#ringChips [data-ring="24"]');
const jev = await D(() => LZ_DEBUG.spectrum()); let jumpOK = jev.length === 576;
for (let j = 0; j < 24; j++) {
  const q = 2 * Math.PI * j / 24, mine = [[Math.cos(q) - 1, -Math.sin(q)], ...Array(23).fill([-1, 0])], got = jev.filter((e) => e[2] === j).map((e) => [e[0], e[1]]);
  const used = new Set(); for (const m of mine) { let b = -1, bd = Infinity; got.forEach((e, k) => { if (used.has(k)) return; const d = Math.hypot(e[0] - m[0], e[1] - m[1]); if (d < bd) { bd = d; b = k; } }); if (bd > 1e-9) jumpOK = false; used.add(b); }
}
check('right jumps on ℤ₂₄: the spectrum is exactly g(e^{−iq} − 1) once per momentum plus −g with multiplicity 23 each', jumpOK);
await preset('ring'); i = await info();
const gaps = {};
for (const N of [12, 24, 48]) { await click(`#ringChips [data-ring="${N}"]`); gaps[N] = (await info()).gap; }
check('dephased hopping: the smallest nonzero |λ| on the ring shrinks as N grows (12 → 24 → 48), as the page says', gaps[12] > gaps[24] && gaps[24] > gaps[48] && gaps[48] < 0.05, Object.entries(gaps).map(([N, g]) => `${N}:${g.toFixed(4)}`).join(' '));

/* ---------- presets, controls, timeline ---------- */
for (const p of ['deph', 'jump', 'rand', 'neg', 'ring', 'edge']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
await preset('neg'); i = await info();
check('neg preset: g = −1 at n = 16, the same truncated trace as g = 1', i.g === -1 && i.n === 16 && Math.abs(i.norm - 2) < 1e-12);
await preset('edge'); i = await info();
check('edge preset: n = 12 from above, 4 coefficients against the bound 90', i.n === 12 && i.a.length === 4 && i.bound === 90 && (await D(() => document.querySelector('#camChips [aria-pressed="true"]')?.dataset.cam)) === 'top' && /4 \(≤ 90\)/.test(await text('ro3')));
await click('#genChips [data-gen="rand"]');
check('generator chips mark the settings custom', (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')) && (await info()).gen === 'rand');
await D(() => { const el = document.getElementById('gSlider'); el.value = 1.37; el.dispatchEvent(new Event('input', { bubbles: true })); }); await settle();
check('the g slider rounds to one decimal and is shown next to it', (await info()).g === 1.4 && (await text('gVal')) === '1.4');
await preset('deph');
check('the rail marks n = 0, the step where ‖P_n‖ passes 2K, and n = 16', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 'n = 0 | ‖P_n‖ > 2K（n = 8） | n = 16');
await setFrac(0.5);
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps n by one', (await info()).n === 9);
await page.keyboard.press('e'); await settle();
check('E jumps to n = 16 and pauses', (await info()).n === 16 && (await state()).playing === false);
await setFrac(0.9); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing to the end reports the lower bound an inverse would need', await waitToast(/n = 16.*√33.*至少 2\.87/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
const noteText = await text('roNote');
check('the readout note writes the four surviving terms at n = 16', ['ρ(17, 16)', 'ρ(-16, -17)', 'ρ(-17, -16)', 'ρ(16, 17)'].every((t) => (noteText).includes(t)), noteText.slice(0, 120));
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['deph', 'edge']) {
  await preset(p);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#ringChips [data-ring="48"]');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('LINDBLAD//ZERO · Zero in the spectrum of a lattice Lindbladian'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, arXiv and the DOI', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['klausen-2025-lattice-lindbladian-zero-spectrum.md', 'D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.lean', 'Blueprint/D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.md', 'Library/HilbertOperators/klausen2025spectragenerators.md', 'arxiv.org/abs/2206.09879v3', 'doi.org/10.48550/arXiv.2206.09879'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="lindblad-zero"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.LZ_DEBUG && LZ_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'lindblad-zero');

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
