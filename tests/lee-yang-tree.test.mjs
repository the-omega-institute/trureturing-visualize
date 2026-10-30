#!/usr/bin/env node
// Browser regression suite for viz/lee-yang-tree (Playwright + Chromium with software WebGL).
//   node tests/lee-yang-tree.test.mjs
// Reads page state through the read-only window.LY_DEBUG probe and checks it against an independent implementation: the
// source polynomial built by enumerating every spin state with its τ-weight (the page multiplies one factor per vertex), the
// physical weights written literally from the Lean definition, exact rational arithmetic throughout, the reciprocal reduction
// by subtracting binomial expansions of (x + 1/x)^j, and Sturm sequences that count the real roots of R(y) in [−2, 2] (the
// page uses Aberth iteration). Fixed reference data come from the dossier and the Lean sources: P₃₁, the cubic q and its
// discriminant −16404, F(y) of QuiverTreePhysicalE8, 400P at τ = −19/20, M = 60, and the double-hub closed form R(m).
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
  const start = await page.evaluate(() => LY_DEBUG.frames());
  await page.waitForFunction((f0) => !LY_DEBUG.pending() && LY_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => LY_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => LY_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => LY_DEBUG.info());
const state = () => D(() => LY_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const slide = async (id, v) => { await D(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input')); }, [id, v]); await settle(); };
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => LY_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => LY_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};
const clickEdge = async (i) => { const p = await D((i) => LY_DEBUG.edgeScreen(i), i); await page.mouse.click(p.x, p.y); await settle(); };

/* ---------- independent exact arithmetic ---------- */
const g = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const Q = (n, d = 1n) => { if (d < 0n) { n = -n; d = -d; } const k = g(n, d) || 1n; return [n / k, d / k]; };
const qa = (x, y) => Q(x[0] * y[1] + y[0] * x[1], x[1] * y[1]);
const qm = (x, y) => Q(x[0] * y[0], x[1] * y[1]);
const qd = (x, y) => Q(x[0] * y[1], x[1] * y[0]);
const qneg = (x) => [-x[0], x[1]];
const qsign = (x) => (x[0] > 0n ? 1 : x[0] < 0n ? -1 : 0);
const F = (n) => { let r = 1n; for (let i = 2n; i <= BigInt(n); i++) r *= i; return r; };
const C = (n, k) => F(n) / (F(k) * F(n - k));
function primInt(R) {   // rational coefficients → primitive integer polynomial with positive leading coefficient
  while (R.length > 1 && R[R.length - 1][0] === 0n) R = R.slice(0, -1);
  let L = 1n; for (const [, d] of R) L = L / g(L, d) * d;
  let P = R.map(([n, d]) => n * (L / d)); const c = P.reduce((t, x) => g(t, x), 0n) || 1n; P = P.map((x) => x / c);
  return P[P.length - 1] < 0n ? P.map((x) => -x) : P;
}
const eqPoly = (A, B) => !!A && !!B && A.length === B.length && A.every((x, i) => BigInt(x) === BigInt(B[i]));
// the source polynomial: Σ over splits k and over all 2^V spin states of ρ(k) τ^{#opposite edges} x^{Σ up masses}
function sourcePoly(V, edges, n, rho, tau) {
  const acc = []; const k = new Array(edges.length).fill(1);
  const rec = (i) => {
    if (i < edges.length) { for (let s = 1; s < n[i]; s++) { k[i] = s; rec(i + 1); } return; }
    const mass = new Array(V).fill(0); edges.forEach(([a, b], e) => { mass[a] += k[e]; mass[b] += n[e] - k[e]; });
    const w = rho(k, mass), poly = new Map();
    for (let st = 0; st < 2 ** V; st++) {
      let opp = 0, ex = 0; for (const [a, b] of edges) if (((st >> a) & 1) !== ((st >> b) & 1)) opp++;
      for (let v = 0; v < V; v++) if ((st >> v) & 1) ex += mass[v];
      const key = `${ex}|${opp}`; poly.set(key, (poly.get(key) || 0) + 1);
    }
    for (const [key, cnt] of poly) { const [ex, opp] = key.split('|').map(Number); let t = [BigInt(cnt), 1n]; for (let j = 0; j < opp; j++) t = qm(t, tau); while (acc.length <= ex) acc.push([0n, 1n]); acc[ex] = qa(acc[ex], qm(w, t)); }
  };
  rec(0); return acc;
}
const sumPolys = (list) => { const R = []; for (const P of list) P.forEach((c, i) => { while (R.length <= i) R.push([0n, 1n]); R[i] = qa(R[i], c); }); return R; };
// the physical weight ρ_phys of QuiverTreePhysicalE8: ∏ choose(2n, 2k) · ∏_v cVert(mass_v, deg_v) · fEnd at every endpoint
function physRho(V, edges, n) {
  const deg = new Array(V).fill(0); for (const [a, b] of edges) { deg[a]++; deg[b]++; }
  const fEnd = (a) => [F(2 * a), F(a - 1) * F(a)], cVert = (d, a) => [F(d - 1), F(d - a + 2)];
  return (k, mass) => {
    let w = [1n, 1n]; edges.forEach((_, i) => { w = qm(w, [C(2 * n[i], 2 * k[i]), 1n]); });
    for (let v = 0; v < V; v++) {
      w = qm(w, Q(...cVert(mass[v], deg[v])));
      edges.forEach(([a, b], i) => { if (a === v) w = qm(w, Q(...fEnd(k[i]))); if (b === v) w = qm(w, Q(...fEnd(n[i] - k[i]))); });
    }
    return w;
  };
}
const physPoly = (V, edges, n) => sourcePoly(V, edges, n, physRho(V, edges, n), [-1n, 1n]);
function pairPoly(V, edges) { const L = []; for (let a = 0; a < edges.length; a++) for (let b = a + 1; b < edges.length; b++) L.push(physPoly(V, edges, edges.map((_, i) => (i === a || i === b ? 3 : 2)))); return sumPolys(L); }
// rational polynomials for Sturm sequences
const rtrim = (P) => { const R = P.slice(); while (R.length > 1 && R[R.length - 1][0] === 0n) R.pop(); return R; };
const rIsZero = (P) => P.length === 1 && P[0][0] === 0n;
function rrem(A, B) { A = rtrim(A); B = rtrim(B); let R = A.slice(); const db = B.length - 1; while (R.length - 1 >= db && !rIsZero(R)) { const c = qd(R[R.length - 1], B[db]), sh = R.length - 1 - db; for (let i = 0; i <= db; i++) R[i + sh] = qa(R[i + sh], qneg(qm(c, B[i]))); R = rtrim(R.slice(0, -1).length ? R.slice(0, -1) : [[0n, 1n]]); } return R; }
const rder = (P) => (P.length > 1 ? P.slice(1).map((c, i) => qm(c, [BigInt(i + 1), 1n])) : [[0n, 1n]]);
function rgcd(A, B) { A = rtrim(A); B = rtrim(B); while (!rIsZero(B)) [A, B] = [B, rrem(A, B)]; return A; }
const rEval = (P, x) => P.reduceRight((t, c) => qa(qm(t, x), c), [0n, 1n]);
function sturmIn(P, a, b) {   // distinct real roots in (a, b]
  const seq = [rtrim(P), rder(rtrim(P))]; while (!rIsZero(seq[seq.length - 1])) { const r = rrem(seq[seq.length - 2], seq[seq.length - 1]); if (rIsZero(r)) break; seq.push(r.map(qneg)); }
  const V = (x) => { let n = 0, prev = 0; for (const s of seq) { const v = qsign(rEval(s, x)); if (v && prev && v !== prev) n++; if (v) prev = v; } return n; };
  return V(a) - V(b);
}
function reduceY(P) {   // x^{−d}P(x) = R(x + 1/x) for a self-reciprocal P of degree 2d, by peeling binomial expansions of (x + 1/x)^j
  P = P.map((c) => [BigInt(c), 1n]); const n = P.length - 1, d = n / 2, R = new Array(d + 1).fill(null).map(() => [0n, 1n]); const W = P.slice();
  for (let j = d; j >= 0; j--) { const c = W[d + j]; R[j] = c; for (let i = 0; i <= j; i++) W[d + j - 2 * i] = qa(W[d + j - 2 * i], qneg(qm(c, [C(j, i), 1n]))); }
  return R;
}
function circleCount(Pint) {   // exact: [roots off the circle (simple roots assumed off it), all roots on the circle?]
  let P = Pint.map(BigInt); if ((P.length - 1) % 2) { const Qp = new Array(P.length - 1).fill(0n); let r = 0n; for (let i = P.length - 1; i >= 1; i--) { r = P[i] - r; Qp[i - 1] = r; } P = Qp; }   // drop the root −1 of odd degree
  const R = reduceY(P), sq = rgcd(R, rder(R)), distinct = (R.length - 1) - (sq.length - 1);
  const eps = [1n, 10n ** 9n], inside = sturmIn(R, qa([-2n, 1n], qneg(eps)), qa([2n, 1n], eps));   // distinct real roots in [−2, 2] (a margin of 1e-9)
  return { off: 2 * (distinct - inside), on: inside === distinct };
}
const evalI = (P) => { let re = 0n, im = 0n; P.forEach((c, k) => { c = BigInt(c); [[re, im]] = [[re + [c, 0n, -c, 0n][k % 4], im + [0n, c, 0n, -c][k % 4]]]; }); return [re, im]; };
const mul = (A, B) => { const r = new Array(A.length + B.length - 1).fill(0n); A.forEach((a, i) => B.forEach((b, j) => { r[i + j] += a * b; })); return r; };
const add = (...Ps) => { const r = new Array(Math.max(...Ps.map((p) => p.length))).fill(0n); for (const p of Ps) p.forEach((c, i) => { r[i] += c; }); return r; };
const sc = (c, P) => P.map((x) => x * c);
const prim = (P) => primInt(P.map((c) => [BigInt(c), 1n]));
// the double-hub closed form R(m) = (1 − x)^h(d) Q(d), d = m + 1, from FiolDoubleHubSource
function closedR(m) {
  const d = m + 1, x = BigInt(d), odd = d % 2 === 1;
  const H = (r) => { const p = new Array(r + 1).fill(0n); p[0] = 1n; p[r] = 1n; return p; }, Sx = (r) => new Array(r).fill(1n);
  const U = odd ? Sx(d) : H(d), Vv = odd ? Sx(d + 1) : H(d + 1), W = odd ? Sx(d + 2) : H(d + 2), Lx = [1n, 1n];
  const inner = add(sc(2n * x ** 4n, mul(Vv, Vv)), sc(3n * x * x * (x * x - 1n) / 2n, mul(U, W)), sc(4n * x * (x - 1n) * (2n * x - 1n), mul(Lx, mul(U, Vv))), sc(2n * (x - 1n) * (2n * x - 3n), mul(mul(Lx, Lx), mul(U, U))));
  const Qd = add(mul(H(2), inner), mul(H(3), add(sc(8n * x * (2n * x - 1n), mul(U, Vv)), sc(16n * (x - 1n), mul(Lx, mul(U, U))))), sc(9n, mul(H(4), mul(U, U))));
  const h = odd ? 2 * d : 2 * d - 2; let R = Qd; for (let i = 0; i < h; i++) R = mul(R, [1n, -1n]);
  return R;
}
const near = (a, b, tol = 1e-9) => Math.abs(a - b) <= tol;
const dh = (m) => { const e = [[1, 0], [2, 0]]; let v = 3; for (let j = 0; j < m; j++) e.push([v++, 1]); for (let j = 0; j < m; j++) e.push([v++, 2]); return [v, e]; };
const PATH3 = [[0, 1], [2, 1]];
const Wm = (c, M) => [[1, 1, 1], [1, c, 1], [1, 1, M]];
const mixInd = (c, M, tau) => primInt(sourcePoly(3, PATH3, [4, 4], (k) => [BigInt(Wm(c, M)[k[0] - 1][k[1] - 1]), 1n], tau));

await page.goto(origin + BASE + 'viz/lee-yang-tree/');
await page.waitForFunction(() => window.LY_DEBUG && LY_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info();

/* ---------- joint weights: the frozen counterexample ---------- */
check('the page opens on the W₃₁ preset: joint weights, c = 10, M = 31, τ = −1, paused', i.mode === 'mix' && i.c === 10 && i.M === 31 && i.j === -20 && (await state()).preset === 'w31');
await pause(); i = await info();
const p31 = mixInd(10, 31, [-1n, 1n]);
check('W₃₁: the page’s polynomial equals the state enumeration and the dossier’s P₃₁ / 2 = 24 − 3x + 4x² − 31x³ + 12x⁴ − …', eqPoly(i.coeffs, p31) && eqPoly(p31, [24n, -3n, 4n, -31n, 12n, -31n, 4n, -3n, 24n]), i.coeffs.join(' '));
check('…x⁻⁴P = (y − 2)q(y) with q = 24y³ + 45y² − 2y − 26 and disc q = −16404, as in the Lean proof', eqPoly(i.q, [-26n, -2n, 45n, 24n]) && i.disc === '-16404' && /−16404/.test(await text('ro4')));
const c31 = circleCount(p31);
check('…four roots leave the circle (Sturm count on R) and the page finds the same four, x = 1 double', i.nOff === 4 && c31.off === 4 && i.mult1 === 2 && i.deg === 8, `${i.nOff} · ${c31.off}`);
check('…the verdict names the frozen counterexample', /冻结的反例 W₃₁/.test(await text('ro5')));
check('…every root the page reports satisfies |P(x)| ≤ 1e-9 · Σ|c_k||x|^k (backward error)', i.roots.every((r) => { let re = 0, im = 0, scale = 0; const ax = Math.hypot(r.re, r.im); for (let k = i.coeffs.length - 1; k >= 0; k--) { [re, im] = [re * r.re - im * r.im + Number(i.coeffs[k]), re * r.im + im * r.re]; scale = scale * ax + Math.abs(Number(i.coeffs[k])); } return Math.hypot(re, im) <= 1e-9 * scale; }));
const offIdx = i.offByM.map((x, M) => (x > 0 ? M : null)).filter((x) => x !== null);
check('…with c = 10 the page finds M ≤ 30 on the circle and every M from 31 to 80 off it', offIdx.length === 50 && offIdx[0] === 31 && offIdx[49] === 80);
const sweepInd = [30, 31, 45, 80].map((M) => circleCount(mixInd(10, M, [-1n, 1n])));
check('…independently: M = 30 on the circle, M = 31, 45, 80 off it', sweepInd[0].on && !sweepInd[1].on && !sweepInd[2].on && !sweepInd[3].on);
await preset('lone'); await setFrac(1); i = await info();
check('c = 1: the page keeps every M up to 80 on the circle, and the state enumeration agrees at M = 80', i.offByM.slice(1).every((x) => x === 0) && circleCount(mixInd(1, 80, [-1n, 1n])).on && eqPoly(i.coeffs, mixInd(1, 80, [-1n, 1n])));
await preset('interior'); i = await info();
const p60 = mixInd(10, 60, [-19n, 20n]);
check('τ = −19/20, M = 60: the page’s polynomial equals the enumeration and the dossier’s 400P = (30800, −2280, 12901, −45676, 8664, …)', eqPoly(i.coeffs, p60) && eqPoly(p60, [30800n, -2280n, 12901n, -45676n, 8664n, -45676n, 12901n, -2280n, 30800n]));
check('…and R(y) = 30800y⁴ − 2280y³ − 110299y² − 38836y + 44462, with four roots off the circle', eqPoly(i.R, [44462n, -38836n, -110299n, -2280n, 30800n]) && i.nOff === 4 && circleCount(p60).off === 4);
await slide('tt', '-0.5'); i = await info();
check('the τ slider: τ = −0.5 at c = 10, M = 60 matches the enumeration, and the settings become custom', i.j === -10 && eqPoly(i.coeffs, mixInd(10, 60, [-1n, 2n])) && (await state()).preset === null);
await slide('cc', '1'); i = await info();
check('the c slider: c = 1 matches the enumeration', i.c === 1 && eqPoly(i.coeffs, mixInd(1, 60, [-1n, 2n])) && i.nOff === circleCount(mixInd(1, 60, [-1n, 2n])).off);
await slide('zz', '2'); i = await info();
check('the magnification slider sets ×100', near(i.zoom, 100, 1e-9) && (await text('oZ')) === '×100');
check('joint-weight mode shows the c, τ and magnification fields only', (await visible('cField')) && (await visible('tauField')) && (await visible('zoomField')) && !(await visible('treeField')) && !(await visible('totField')));

/* ---------- physical weights with fixed totals ---------- */
await preset('e8'); await setFrac(0.85); i = await info();
const [V8, E8] = dh(3), pe8 = primInt(physPoly(V8, E8, new Array(8).fill(3)));
check('the nine-vertex double hub, all totals 3: the page’s polynomial equals the enumeration with the Lean weights', eqPoly(i.coeffs, pe8) && i.tree.V === 9 && i.tree.edges.length === 8 && i.splits === 256);
const p_ = [26n, -281n, -40n, 112n], q_ = [686n, -788n, -1543n, 264n, 400n];
const F2 = add(mul([0n, 2n], mul(q_, q_)), mul(mul([-16n, 8n, 8n], p_), q_), mul([-36n, -18n, 18n, 9n], mul(p_, p_)));   // 2F(y) of QuiverTreePhysicalE8
check('…after (1 − x)⁶, the reduction is F(y) = yq² + 4(y + 2)(y − 1)pq + 9/2 (y + 2)(y² − 2)p² of the Lean proof', eqPoly(i.reduction, prim(F2)) && i.mult1 === 6);
const ce8 = circleCount(pe8);
check('…four roots off the circle (Sturm count) and the page finds the same four, about 0.00195 away', i.nOff === 4 && ce8.off === 4 && near(i.maxDev, 0.00195, 2e-5), String(i.maxDev));
check('…a root inside the circle and its reciprocal outside', i.roots.some((r) => r.off && Math.hypot(r.re, r.im) < 1) && i.roots.some((r) => r.off && Math.hypot(r.re, r.im) > 1));
check('…the verdict names the frozen physical counterexample, the time axis is the magnification', /冻结的物理反例/.test(await text('ro5')) && near(i.zoom, 10 ** 2.55, 1e-6) && i.e8 === true);
check('fixed-total mode shows the tree, size and totals fields, not the sliders of the other modes', (await visible('treeField')) && (await visible('sizeField')) && (await visible('totField')) && !(await visible('zoomField')) && !(await visible('cField')));
await clickEdge(0); await clickEdge(0); await clickEdge(0); i = await info();
check('clicking an edge three times cycles its total 3 → 4 → 5 → 2, and the polynomial follows', i.totals.join(',') === '2,3,3,3,3,3,3,3' && eqPoly(i.coeffs, primInt(physPoly(V8, E8, [2, 3, 3, 3, 3, 3, 3, 3]))) && (await state()).preset === null);
check('…with one total lowered to 2 the roots are back on the circle', i.nOff === 0 && circleCount(i.coeffs).on);
let scan = 0, scanOff = [];
for (let mask = 0; mask < 256; mask++) { const n = E8.map((_, e) => ((mask >> e) & 1 ? 3 : 2)); const c = circleCount(primInt(physPoly(V8, E8, n))); scan++; if (!c.on) scanOff.push(mask); }
check('independently: among all 256 assignments of totals {2, 3} only the all-3 one leaves the circle', scan === 256 && scanOff.length === 1 && scanOff[0] === 255);
await preset('hub4'); i = await info();
const [V10, E10] = dh(4);
check('eleven vertices, all totals 3: the page and the Sturm count keep every root on the circle', i.nOff === 0 && circleCount(primInt(physPoly(V10, E10, new Array(10).fill(3)))).on && i.tree.edges.length === 10 && i.mult1 === 10);
await click('#totChips [data-tot="4"]');
check('the cap: all totals 4 on ten edges (3¹⁰ splits) is refused with a toast and the totals stay', (await waitToast(/4096/)) && (await info()).totals.every((t) => t === 3));
await click('#treeChips [data-tree="path"]'); await slide('ee', '2'); await click('#totChips [data-tot="2"]');
let twoEdge = true; const twoBad = [];
for (let a = 2; a <= 5; a++) for (let b = 2; b <= 5; b++) {
  for (let t = 0; t < 4 && (await info()).totals[0] !== a; t++) await clickEdge(0);
  for (let t = 0; t < 4 && (await info()).totals[1] !== b; t++) await clickEdge(1);
  i = await info(); const ind = primInt(physPoly(3, [[1, 0], [2, 1]], [a, b]));
  if (!(i.totals[0] === a && i.totals[1] === b && i.nOff === 0 && eqPoly(i.coeffs, ind) && circleCount(ind).on)) { twoEdge = false; twoBad.push(`${a},${b}`); }
}
check('two-edge path, all totals a, b ≤ 5 set by clicking: every root on the circle, the page matching the enumeration', twoEdge, twoBad.join(' '));

/* ---------- the pair coefficient ---------- */
await preset('pair'); await setFrac(1); i = await info();
const [V9] = dh(3), pp9 = primInt(pairPoly(V9, E8));
check('pair coefficient on the nine-vertex tree: the page’s sum of 28 placements equals the enumeration', i.k === 28 && i.N === 28 && eqPoly(i.coeffs, pp9));
check('…degree 2E + 2 = 18, x = 1 of multiplicity 6 = the odd-degree vertices, all roots on the circle (Sturm)', i.deg === 18 && i.mult1 === 6 && i.tree.odd === 6 && i.nOff === 0 && circleCount(pp9).on);
check('…the verdict cites the frozen theorem', /冻结定理/.test(await text('ro5')));
check('pair mode shows the tree, size and magnification fields', (await visible('treeField')) && (await visible('sizeField')) && (await visible('zoomField')) && !(await visible('totField')));
const placements = i.placementCoeffs; let placeOK = true; { let idx = 0; for (let a = 0; a < 8; a++) for (let b = a + 1; b < 8; b++) { if (!eqPoly(placements[idx], primInt(physPoly(V9, E8, E8.map((_, e) => (e === a || e === b ? 3 : 2)))))) placeOK = false; idx++; } }
check('…each of the 28 placements the page lists equals its own enumeration', placements.length === 28 && placeOK);
const classOK = []; for (let m = 1; m <= 5; m++) {
  await slide('ee', String(2 * m + 2)); await setFrac(1); i = await info();
  const [Vm, Em] = dh(m), P = primInt(pairPoly(Vm, Em)), R = prim(closedR(m)), h = m % 2 ? 2 * m : 2 * m + 2, [ire, iim] = evalI(P);
  const simple = i.roots.every((r) => (r.re === 1 && r.im === 0) || r.mult === 1);
  classOK.push(eqPoly(i.coeffs, P) && eqPoly(P, R) && i.deg === 4 * m + 6 && i.mult1 === h && simple && i.nOff === 0 && circleCount(P).on && ((ire === 0n && iim === 0n) === (m % 4 === 1)));
}
check('double hubs m = 1 … 5: the page’s sum equals the enumeration and the closed form 200·12²ᵐ·(1 − x)ʰQ_{m+1} up to scale; degree 4m + 6, x = 1 of multiplicity 2m + 2 or 2m, other roots simple and on the circle, ±i roots exactly when m ≡ 1 (mod 4)', classOK.every(Boolean), classOK.map((x) => (x ? 1 : 0)).join(''));
await preset('hub5'); i = await info();
check('hub5: the placement with both central edges at total 3 is the only one off the circle, and with it alone four roots leave', JSON.stringify(i.offPlacements) === '[[0,1]]' && i.k === 1 && i.nOff === 4 && !circleCount(primInt(physPoly(13, dh(5)[1], dh(5)[1].map((_, e) => (e < 2 ? 3 : 2))))).on);
const partialOff = await D(() => { const r = []; for (let k = 1; k <= 66; k++) { LY_DEBUG.setFrac(k / 66); r.push(LY_DEBUG.info().nOff); } return r; });
check('…from the second partial sum on, every partial sum in the page’s order is on the circle', partialOff[0] === 4 && partialOff.slice(1).every((x) => x === 0), partialOff.slice(0, 6).join(','));
const trees = [['path', 6], ['star', 7], ['spider', 9], ['random', 8]];
const anyTree = [];
for (const [t, E] of trees) {
  await click(`#treeChips [data-tree="${t}"]`); await slide('ee', String(E)); await setFrac(1); i = await info();
  const P = primInt(pairPoly(i.tree.V, i.tree.edges));
  anyTree.push(i.tree.edges.length === E && eqPoly(i.coeffs, P) && i.deg === 2 * E + 2 && i.mult1 === i.tree.odd && circleCount(P).on && i.nOff === 0 && i.coeffs[0] === i.coeffs[i.coeffs.length - 1]);
}
check('the pair theorem on a path, a star, a spider and a random tree: the page matches the enumeration, degree 2E + 2, x = 1 of multiplicity = odd-degree vertices, every root on the circle', anyTree.every(Boolean), anyTree.map((x) => (x ? 1 : 0)).join(''));
const before = JSON.stringify((await info()).tree.edges); await click('#treeChips [data-tree="random"]'); i = await info();
check('clicking “random” again draws a different tree of the same size', JSON.stringify(i.tree.edges) !== before && i.tree.edges.length === 8 && i.tree.V === 9);

/* ---------- play, keys and toasts ---------- */
await preset('sweep'); await setFrac(0.985); await click('#play');
check('the sweep toast reports that the roots left the circle at M = 31', await waitToast(/M = 31/));
await pause();
await preset('e8'); await setFrac(0.985); await click('#play');
check('the magnification toast reports four roots off the circle', await waitToast(/4 个根离开圆/));
await pause();
await preset('pair'); await setFrac(0.985); await click('#play');
check('the pair toast reports all 18 roots on the circle with x = 1 sixfold', await waitToast(/18 个根都在单位圆上.*6 重根/));
await pause();
await preset('sweep'); await setFrac(0.2); await click('#play'); await waitFrames(12); const t1 = (await state()).nowFrac; await pause();
check('play advances along the rail', t1 > 0.2);
await click('#rev'); await waitFrames(12); const t2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', t2 < t1);
await page.click('#rev'); await pause();
await page.focus('#now'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with the rail focused', playing === true);
await pause();
await page.keyboard.press('e'); await settle();
check('E jumps to M = 80 and pauses', (await info()).M === 80 && (await state()).playing === false);
await setFrac(fracOf(30)); await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps the weight by one', (await info()).M === 31);

/* ---------- language ---------- */
await click('#modeChips [data-mode="sum"]');
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
for (const m of ['mix', 'fixed', 'sum']) {
  await click(`#modeChips [data-mode="${m}"]`); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${m}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('LEE-YANG//TREE · The unit circle on trees'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the five Lean files and the three papers', (await D(() => { const h = [...document.querySelectorAll('#drawer .en a')].map((a) => a.href).join(' '); return ['fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang.md', 'QuiverTreeIsingRefutation.lean', 'QuiverTreePhysicalE8.lean', 'TreePairTheorem.lean', 'FiolDoubleHubPhysical.lean', 'FiolDoubleHubCoefficient.lean', '10.1007/JHEP08(2020)161', '10.1103/PhysRev.87.410', '10.1007/s10474-012-0225-4'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="lee-yang-tree"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.LY_DEBUG && LY_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'lee-yang-tree');

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
function fracOf(M) { return (M - 1) / 79; }
