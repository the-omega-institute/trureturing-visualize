#!/usr/bin/env node
// Browser regression suite for viz/robin-lattice (Playwright + Chromium with software WebGL).
//   node tests/robin-lattice.test.mjs
// Reads page state through the read-only window.RL_DEBUG probe and checks it against an independent implementation:
// trial-division factorization, σ(n)/n as an exact BigInt fraction from the divisor sum, the evidence rules re-derived
// from scratch (smoothness, compression and an exact replay of every prime swap, the 5040 optimum by an exact sieve of
// σ(m)/m for m ≤ 5040, the edge rule), the κ fibre, the excess 1/(q·σ(q^a)) of a prime fibre, the face identity
// Z(n)Z(npq) = Z(np)Z(nq), the continuous relaxation, the prefix constants and a full recount of the coverage.
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
  const start = await page.evaluate(() => RL_DEBUG.frames());
  await page.waitForFunction((f0) => !RL_DEBUG.pending() && RL_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); };
const state = () => D(() => RL_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 30000 }); return true; } catch { return false; }
};
const near = (a, b, tol = 1e-9) => Math.abs(a - b) <= tol * Math.max(1, Math.abs(b));

// --- independent implementation
const GAMMA = 0.5772156649015329, EG = Math.exp(GAMMA);
function tdFactor(n) { const f = []; let m = n; for (let p = 2; p * p <= m; p += (p === 2 ? 1 : 2)) { if (m % p === 0) { let a = 0; while (m % p === 0) { m /= p; a++; } f.push([p, a]); } } if (m > 1) f.push([m, 1]); return f; }
const isPrime = (p) => p >= 2 && tdFactor(p).length === 1 && tdFactor(p)[0][1] === 1;
const gcd = (a, b) => { while (b) [a, b] = [b, a % b]; return a; };
function sigmaBrute(n) { let s = 0n; const N = BigInt(n); for (let d = 1n; d * d <= N; d++) if (N % d === 0n) { s += d; if (d * d !== N) s += N / d; } return s; }
const frac = (n) => { const s = sigmaBrute(n), N = BigInt(n), g = gcd(s, N); return `${s / g}/${N / g}`; };
const Zf = (f) => f.reduce((z, [p, a]) => z * (1 - p ** -(a + 1)) / (1 - 1 / p), 1);
const cap = (n) => EG * Math.log(Math.log(n));
const PRIMES30 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113];
const compress = (f) => f.reduce((c, [, a], i) => c * PRIMES30[i] ** a, 1);
const testEdge = (M, p, b, r) => { const z = (q, a) => (1 - q ** -(a + 1)) / (1 - 1 / q); const lhs = (z(p, b + r) / z(p, b) - 1) * Math.log(Math.log(M)); return lhs <= Math.log1p(r * Math.log(p) / Math.log(M)); };
// exact maximum of σ(m)/m over m ≤ 5040, by a divisor-sum sieve
const SIG = new Array(5041).fill(0n); for (let d = 1; d <= 5040; d++) for (let m = d; m <= 5040; m += d) SIG[m] += BigInt(d);
let best = [1n, 1n, 1]; for (let m = 1; m <= 5040; m++) if (SIG[m] * best[1] > best[0] * BigInt(m)) best = [SIG[m], BigInt(m), m];
function indepClass(n, memo = new Map(), depth = 0) {
  if (memo.has(n)) return memo.get(n);
  const f = tdFactor(n), w = f.length, Z = Zf(f); let c;
  if (n <= 5040) c = n >= 16 && Z >= cap(n) ? 'viol' : 'out';
  else if (f[w - 1][0] <= 11) c = 'lean';
  else if (w <= 5 && compress(f) > 5040) c = 'chain';
  else if (w <= 5 && n >= 5600) c = 'bound';
  else {
    if (depth < 4) for (const [p, a] of f) { let pr = 1; for (let r = 1; r <= a && !c; r++) { pr *= p; const M = n / pr; if (M > 5040 && ['lean', 'chain', 'bound', 'edge'].includes(indepClass(M, memo, depth + 1)) && testEdge(M, p, a - r, r)) c = 'edge'; } if (c) break; }
    if (!c) c = Z < cap(n) ? 'num' : 'fail';
  }
  if (depth === 0 || c !== 'num') memo.set(n, c);
  return c;
}
let seed = 20261011; const rnd = () => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed / 2147483648; };
const rint = (lo, hi) => lo + Math.floor(rnd() * (hi - lo + 1));

// --- load
await page.goto(`${origin}${BASE}viz/robin-lattice/?lang=zh`);
await page.waitForFunction(() => window.RL_DEBUG && RL_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
check('the page loads with the 5040 preset and a WebGL canvas', (await state()).preset === 'core' && (await state()).n === 5040 && (await D(() => !!document.querySelector('#gl'))));

// --- arithmetic: factorization and the exact divisor ratio
const samples = []; for (let i = 0; i < 120; i++) samples.push(rint(2, 2e7)); for (let i = 0; i < 30; i++) samples.push(rint(1e9, 1e12));
let facOK = 0, fracOK = 0, fracN = 0;
for (const n of samples) {
  const f = await D((n) => RL_DEBUG.factor(n), n);
  if (f.reduce((m, [p, a]) => m * p ** a, 1) === n && f.every(([p, a], i) => isPrime(p) && a >= 1 && (i === 0 || f[i - 1][0] < p))) facOK++;
  if (n <= 2e7) { fracN++; if ((await D((n) => RL_DEBUG.info(n).frac, n)) === frac(n)) fracOK++; }
}
check('150 random n up to 10¹²: the page’s factorization multiplies back to n, in increasing primes', facOK === samples.length, `${facOK}/${samples.length}`);
check('…and σ(n)/n matches the brute-force divisor sum as an exact reduced fraction', fracOK === fracN, `${fracOK}/${fracN}`);
check('5040 has σ(n)/n = 403/105, and 403/105 is the exact maximum of σ(m)/m over m ≤ 5040 (sieve), attained only there', (await D(() => RL_DEBUG.info(5040).frac)) === '403/105' && best[2] === 5040 && `${best[0] / gcd(best[0], best[1])}/${best[1] / gcd(best[0], best[1])}` === '403/105');
check('the threshold 5600: e^γ log log 5600 > 403/105; the exact crossing lies between 5582 and 5583', cap(5600) > 403 / 105 && cap(5583) > 403 / 105 && cap(5582) < 403 / 105);

// --- evidence classes
const named = await D(() => [5040, 10080, 15840, 18720, 10007, 5041, 30030, 2520].map((n) => RL_DEBUG.info(n)));
check('named points: 5040 and 2520 are outside the criterion with the inequality failing (red), 10080 is 7-smooth, 15840 is 11-smooth',
  named[0].cat === 'viol' && named[7].cat === 'viol' && named[1].cat === 'lean' && named[1].rule === 'seven' && named[2].cat === 'lean' && named[2].rule === 'eleven');
check('…18720 = 2⁵·3²·5·13 is a prime-swap chain from its compression 10080, swapping 7 → 13 on the 7-smooth theorem', named[3].cat === 'chain' && named[3].c === 10080 && named[3].base === 'seven' && JSON.stringify(named[3].steps) === JSON.stringify([[7, 13, 1]]));
check('…the prime 10007 uses the 5040 optimum (compression 2), 5041 = 71² has numbers only, 30030 = 2·3·5·7·11·13 has numbers only',
  named[4].cat === 'bound' && named[4].c === 2 && named[5].cat === 'num' && named[6].cat === 'num');
const memo = new Map(); let clsOK = 0, chainOK = 0, chainN = 0, edgeOK = 0, edgeN = 0; const clsBad = [];
const pool = []; for (let i = 0; i < 260; i++) pool.push(rint(5041, 3e6)); for (let i = 0; i < 60; i++) { const k = rint(6, 7); let m = 1; for (let j = 0; j < k; j++) m *= PRIMES30[j]; pool.push(m * rint(1, 12)); }
for (let i = 0; i < 40; i++) pool.push(2 ** rint(3, 8) * 3 ** rint(1, 4) * 5 ** rint(0, 2) * [13, 17, 19, 23, 29][rint(0, 4)] ** rint(1, 2));
for (const n of pool) {
  const I = await D((n) => RL_DEBUG.info(n), n), mine = indepClass(n, memo);
  if (I.cat === mine) clsOK++; else clsBad.push(`${n}:${I.cat}/${mine}`);
  if (I.cat === 'chain') {   // replay the swaps exactly: start from the compression, each step p ≤ q with both prime to the rest
    chainN++; let cur = I.c, ok = I.c > 5040 && I.c === compress(tdFactor(n));
    for (const [p, q, a] of I.steps) { const pa = p ** a; if (cur % pa !== 0 || (cur / pa) % p === 0 || (cur / pa) % q === 0 || p > q || !isPrime(p) || !isPrime(q)) ok = false; cur = cur / pa * q ** a; }
    if (ok && cur === n) chainOK++;
  }
  if (I.cat === 'edge') { edgeN++; const M = I.from, pr = I.p ** I.r; if (M * pr === n && ['lean', 'chain', 'bound', 'edge'].includes(indepClass(M, memo)) && testEdge(M, I.p, tdFactor(n).find(([p]) => p === I.p)[1] - I.r, I.r)) edgeOK++; }
}
check(`${pool.length} random n (including integers with six and seven distinct primes): the page’s evidence class equals the independent rules`, clsOK === pool.length, `${clsOK}/${pool.length} ${clsBad.slice(0, 4).join(' ')}`);
check('…every prime-swap certificate replays exactly from its compression to n', chainOK === chainN && chainN > 20, `${chainOK}/${chainN}`);
check('…every edge certificate starts at a coloured divisor M = n/p^r and passes the edge test', edgeOK === edgeN, `${edgeOK}/${edgeN}`);

// --- the κ fibre
const kf = await D(() => RL_DEBUG.kappaFibre(7560));
check('the κ fibre at (4, 3, 2): 10800, 7560, 5292 with margins 0.4101, 0.0901, 0.8112', JSON.stringify(kf.base) === '[4,3,2]' && JSON.stringify(kf.members.map((m) => m.n)) === '[10800,7560,5292]' && near(kf.members[0].M, 0.4101243, 1e-6) && near(kf.members[1].M, 0.0901103, 1e-6) && near(kf.members[2].M, 0.8111684, 1e-6));
let kOK = true;
for (let i = 0; i < 40; i++) {
  const n = 2 ** rint(0, 6) * 3 ** rint(0, 3) * 5 ** rint(0, 3) * 7 ** rint(0, 3) * [1, 11, 13, 143][rint(0, 3)];
  const F = await D((n) => RL_DEBUG.kappaFibre(n), n), f = tdFactor(n), v = (p) => (f.find(([q]) => q === p) || [0, 0])[1];
  const U = v(2) + v(7), W = v(5) + v(7);
  if (F.members.length !== Math.min(U, W) + 1 || !F.members.some((m) => m.n === n)) kOK = false;
  for (let j = 0; j + 1 < F.members.length; j++) if (F.members[j + 1].n * 10 !== F.members[j].n * 7) kOK = false;
  for (const m of F.members) { const g = tdFactor(m.n), w = (p) => (g.find(([q]) => q === p) || [0, 0])[1]; if (w(2) + w(7) !== U || w(3) !== v(3) || w(5) + w(7) !== W || w(7) !== m.kappa) kOK = false; }
}
check('40 random κ fibres: min(U, W) + 1 members, same (U, V, W), κ = a₇, consecutive members in ratio 7/10', kOK);

// --- prime fibres
let exOK = true, closureOK = true, closureN = 0;
for (let i = 0; i < 160; i++) {
  const n = rint(21, 5e6), q = PRIMES30[rint(0, 7)], F = await D(([n, q]) => RL_DEBUG.primeFibre(n, q), [n, q]), a = (tdFactor(n).find(([p]) => p === q) || [0, 0])[1];
  if (F.a !== a) exOK = false;
  F.layers.forEach((l) => { const exact = (q - 1) / (q * (q ** (a + l.k + 1) - 1)); if (!near(l.excess, exact, 1e-9) || !near(l.excessExact, exact, 1e-12)) exOK = false; if (l.pass !== testEdge(Math.exp(l.L), q, a + l.k, 1)) exOK = false; });
  if (F.layers[0].pass) { closureN++; if (!F.layers.every((l) => l.pass)) closureOK = false; }
}
check('160 random fibres n·qᵏ: the excess is (q − 1)/(q(q^{a+k+1} − 1)) = 1/(q·σ(q^{a+k})) and every layer’s test agrees', exOK);
check('…whenever the first layer passes (log n ≥ 3), every later layer passes (the frozen fibre theorem, rechecked)', closureOK && closureN > 30, `${closureN} fibres with a passing first layer`);
await preset('fibre'); let F = await D(() => RL_DEBUG.primeFibre());
check('the fibre preset 10080·11ᵏ: first layer 0.2019 ≤ 0.2313, the start is coloured, the fibre theorem applies', F.theorem && near(F.layers[0].lhs, 0.20194, 1e-3) && near(F.layers[0].rhs, 0.23134, 1e-3) && /robinAt_mul_prime_pow/.test(await text('certNote')));
await preset('fail'); F = await D(() => RL_DEBUG.primeFibre());
const r301840 = Zf(tdFactor(301840)) / cap(301840);
check('the failing preset 27440 → ×11: 0.2113 > 0.2108, no fibre theorem, yet 301840 has Robin ratio 0.6551', !F.layers[0].pass && !F.theorem && near(F.layers[0].lhs, 0.211302, 1e-4) && near(F.layers[0].rhs, 0.210774, 1e-4) && near(r301840, 0.65509, 1e-4) && /用不上/.test(await text('certNote')));

// --- faces
let faceOK = true;
for (let i = 0; i < 80; i++) {
  const n = rint(6000, 5e6), p = [2, 3, 5, 7][rint(0, 3)], q = [3, 5, 7, 11].filter((x) => x !== p)[rint(0, 2)];
  const Fc = await D(([n, p, q]) => RL_DEBUG.face(n, p, q), [n, p, q]);
  const C = (m) => Math.log(cap(m) / Zf(tdFactor(m))), g = (x) => Math.log(Math.log(x)), L = Math.log(n), h = Math.log(p), k = Math.log(q);
  const mix = C(n * p * q) - C(n * p) - C(n * q) + C(n), gm = g(L + h + k) - g(L + h) - g(L + k) + g(L);
  if (!near(Fc.mixed, mix, 1e-7) || !near(Fc.gmix, gm, 1e-9) || !near(Fc.mixed, Fc.gmix, 1e-7) || !(Fc.loss > 0) || !(Fc.lo <= Fc.loss && Fc.loss <= Fc.hi) || Math.abs(Fc.product) > 1e-12 * Fc.Z[0] * Fc.Z[3]) faceOK = false;
}
check('80 random faces: the mixed difference of C equals the mixed difference of log log, is negative, and lies within hk·K bounds', faceOK);
await preset('face'); const fc = await D(() => RL_DEBUG.face());
check('the face preset 10080, ×2, ×3: face loss 0.0046373', near(fc.loss, 0.00463734556, 1e-6) && /0\.004637/.test(await text('c1Meta')));

// --- continuous relaxation and prefix families
const rx = await D(() => RL_DEBUG.relaxation([2, 3, 5, 7], Math.log(6000)));
const T6 = (6000 * 210) ** 0.25;
check('the relaxation over {2, 3, 5, 7} at log 6000: T = (6000·210)^{1/4} = 33.5037 and max Z = (1 − 1/T)⁴·35/8 = 3.8756 > 3.8529', near(rx.T, T6, 1e-9) && rx.active === 4 && near(rx.R, (1 - 1 / T6) ** 4 * 35 / 8, 1e-9) && rx.R > cap(6000) && near(cap(6000), 3.85293563, 1e-7));
const pf = await D(() => RL_DEBUG.prefix());
let Mk = 1, lp = 0, pfOK = true;
pf.forEach((r, i) => { Mk *= PRIMES30[i] / (PRIMES30[i] - 1); lp += Math.log(PRIMES30[i]); if (!near(r.M, Mk, 1e-12) || !near(r.llT, Mk / EG, 1e-12) || !near(r.llN, Math.log(lp), 1e-12)) pfOK = false; });
check('prefix constants M_k = ∏ p/(p − 1) for the first 30 primes; e^{−γ}M_k stays above log log p_k# (numbers only)', pfOK && pf.every((r) => r.gap > 0));

// --- coverage
const cov5 = await D(() => RL_DEBUG.coverage(100000));
const cnt = { lean: 0, chain: 0, bound: 0, edge: 0, num: 0, fail: 0 }, m5 = new Map();
for (let n = 5041; n <= 100000; n++) cnt[indepClass(n, m5)]++;
check('coverage of (5040, 10⁵]: every class count equals an independent recount', Object.keys(cnt).every((k) => cov5.counts[k] === cnt[k]) && cov5.total === 100000 - 5040, JSON.stringify(cov5.counts));
await preset('cover'); const cov6 = await D(() => RL_DEBUG.coverage(1000000));
check('coverage of (5040, 10⁶]: Lean 2037, chain 32033, optimum 958055, edge 2191, numbers only 644, no failure', JSON.stringify(cov6.counts) === JSON.stringify({ lean: 2037, chain: 32033, bound: 958055, edge: 2191, num: 644, fail: 0 }));
check('…numbers only with ω ≤ 5: 542, all in 5041–5599; with ω ≥ 6: 102, the smallest 30030', cov6.stats.numLe5 === 542 && cov6.stats.numGe6 === 102 && cov6.firstOmega6Num === 30030 && cov6.frontier.filter((n) => tdFactor(n).length <= 5).every((n) => n >= 5041 && n <= 5599));
check('…the readouts report 99.935% certified and the frontier 102', /99\.935%/.test(await text('ro2')) && /99\.935%/.test(await text('pillB')) && /102/.test(await text('pillC')));

// --- the lattice
await preset('core'); let lat = await D(() => RL_DEBUG.lattice());
const pos = (U, V, W, k) => [(U - 5) * 0.62 + k * -0.2, (V - 2) * 0.9 + k * 0.3, (W - 3) * 0.62 + k * 0.2];
check('the lattice box has 8·5·4·4 = 640 vertices at (a₂ + a₇, a₃, a₅ + a₇) offset by κ = a₇, each n = 2^a₂3^a₃5^a₅7^a₇',
  lat.verts.length === 640 && lat.verts.every((v) => v.n === 2 ** v.e[0] * 3 ** v.e[1] * 5 ** v.e[2] * 7 ** v.e[3] && v.U === v.e[0] + v.e[3] && v.V === v.e[1] && v.W === v.e[2] + v.e[3] && v.kappa === v.e[3] && pos(v.U, v.V, v.W, v.kappa).every((x, i) => near(x, v.pos[i], 1e-12))));
check('…its edges multiply by 2, 3, 5 or 7 inside the box, and vertex colours equal the independent classes', lat.edges.length === 7 * 5 * 4 * 4 + 8 * 4 * 4 * 4 + 8 * 5 * 3 * 4 + 8 * 5 * 4 * 3 && lat.edges.every((e) => e.b === e.a * e.p) && lat.verts.every((v) => v.cat === indepClass(v.n, memo)));
await click('#sliceChips [data-slice="2"]'); lat = await D(() => RL_DEBUG.lattice());
check('the slice chip a₁₁ = 2 multiplies every vertex by 121 and recolours: 7·121 is still outside (≤ 5040), 5040·121 is 11-smooth (Lean)', lat.slice === 2 && lat.verts.every((v) => v.n % 121 === 0) && lat.verts.find((v) => v.n === 5040 * 121).cat === 'lean' && (await state()).preset === null);
await click('#sliceChips [data-slice="0"]');
await click('#edgeChips [data-edge="test"]');
check('the edge-colour chip switches to the edge test and records each edge’s verdict', (await state()).edge === 'test' && (await D(() => RL_DEBUG.lattice().edges.filter((e) => e.pass === false).length)) > 0);
await click('#edgeChips [data-edge="grad"]');
const sp = await D(() => RL_DEBUG.screenOf(10080));
if (sp) { await page.mouse.click(sp.x, sp.y); await settle(); }
check('clicking the vertex 10080 in the 3D view selects it', sp !== null && (await state()).n === 10080 && /10080/.test(await text('pillA')));
await D(() => { document.getElementById('nInput').value = '18720'; }); await click('#nGo');
check('typing 18720 selects it, and the lattice highlights its compression 10080', (await state()).n === 18720 && (await D(() => RL_DEBUG.selectedVertex())) === 10080 && /压缩数/.test(await text('certNote')));
await D(() => { document.getElementById('nInput').value = '12ab'; }); await click('#nGo');
check('an invalid entry shows an error and keeps the selection', (await state()).n === 18720 && /10¹²/.test(await text('nErr')));
await page.fill('#nInput', '999983'); await page.press('#nInput', 'Enter'); await settle();
check('Enter in the field selects the prime 999983 (5040 optimum)', (await state()).n === 999983 && (await D(() => RL_DEBUG.info().cat)) === 'bound' && (await text('nErr')) === '');

// --- modes and fields
const fieldsShown = async () => { const out = []; for (const id of ['qField', 'faceField', 'xField']) if (await visible(id)) out.push(id); return out.join(','); };
for (const [m, fields] of [['lattice', ''], ['kappa', ''], ['fibre', 'qField'], ['face', 'faceField'], ['cover', 'xField']]) {
  await click(`#modeChips [data-mode="${m}"]`);
  check(`the ${m} chip switches the view and shows ${fields || 'no extra field'}`, (await state()).mode === m && (await fieldsShown()) === fields && (await D(() => document.querySelector(`#modeChips [data-mode="${CSS.escape('x')}"]`) === null)));
}
await click('#modeChips [data-mode="fibre"]'); await click('#qChips [data-q="13"]');
check('the q chip sets the fibre direction', (await state()).q === 13 && (await D(() => RL_DEBUG.primeFibre().layers.length)) === 10);
await click('#modeChips [data-mode="face"]'); await click('#pChips [data-p="3"]'); await click('#fqChips [data-fq="3"]');
let s = await state();
check('the face chips never pick p = q: choosing q = 3 with p = 3 moves p to 2', s.fq === 3 && s.p === 2);
await click('#modeChips [data-mode="cover"]');
await D(() => { const el = document.getElementById('xx'); el.value = '5'; el.dispatchEvent(new Event('input', { bubbles: true })); }); await settle();
check('the X slider sets the coverage bound to 10⁵', (await state()).xExp === 5 && (await text('oX')) === '100,000');
await page.keyboard.press('ArrowRight'); await settle();
check('→ cycles the views (cover → lattice)', (await state()).mode === 'lattice');
await page.keyboard.press('ArrowLeft'); await settle();
check('← cycles back', (await state()).mode === 'cover');
await click('#camChips [data-cam="top"]');
check('the camera chips are exclusive', (await D(() => [...document.querySelectorAll('#camChips .chip')].filter((b) => b.getAttribute('aria-pressed') === 'true').map((b) => b.dataset.cam).join())) === 'top');

// --- presets and toasts
for (const name of ['core', 'kappa', 'fibre', 'fail', 'face', 'replace', 'cover']) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await preset('fibre'); check('the fibre toast names the fibre 10080·11ᵏ', await waitToast(/10080·11ᵏ/));
await preset('fail'); check('the failing-test toast names 301840', await waitToast(/301840/));

// --- language
await page.click('[data-lang-set="en"]'); await settle();
for (const m of ['lattice', 'kappa', 'fibre', 'face', 'cover']) {
  await click(`#modeChips [data-mode="${m}"]`);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${m}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('ROBIN//LATTICE · Robin certificate colouring'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the two theory volumes, the four Lean files, the Robin library card and Nicolas 1983', (await D(() => { const h = [...document.querySelectorAll('#drawer a')].map((a) => a.href).join(' '); return ['AURIC_FIB_ROBIN_DIVISOR_SCALE_GEOMETRY', 'AURIC_FIB_ATOM_KAPPA_CHARGE', 'SevenSmooth.lean', 'ElevenSmooth.lean', 'PrimeFiberPropagation.lean', 'GoldenResourceOptimalInteger.lean', 'choie2006robincriterion', '0022-314X(83)90055-0'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="robin-lattice"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.RL_DEBUG && RL_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'robin-lattice');

// --- narrow layouts in both languages
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await settle();
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await settle();
    check(`no horizontal scroll at ${w}px (${lang})`, (await D(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 });
}
check('no script errors during the whole session', errors.length === 0, errors.slice(0, 3).join(' | '));

await browser.close(); server.close();
const failed = results.filter(r => !r.ok).length;
console.log(`\n${results.length - failed}/${results.length} passed`);
process.exit(failed ? 1 : 0);
