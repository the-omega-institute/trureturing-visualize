#!/usr/bin/env node
// Browser regression suite for viz/roc-fidelity (Playwright + Chromium with software WebGL).
//   node tests/roc-fidelity.test.mjs
// Reads page state through the read-only window.ROC_DEBUG probe and checks it against an independent implementation: exact
// rational arithmetic (BigInt fractions) for the Lean witness — the states, D ρ D = σ, Sylvester minors, the likelihood order,
// the cumulative point and the competing projector — and, for the optimal ROC, eigenvalues from the closed-form cubic,
// a ternary-search dual, weak-duality certificates and a direct maximization over the ring of projectors.
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
  const start = await page.evaluate(() => ROC_DEBUG.frames());
  await page.waitForFunction((f0) => !ROC_DEBUG.pending() && ROC_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => ROC_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D((t) => ROC_DEBUG.setT(t), t); await settle(); };
const info = () => D(() => ROC_DEBUG.info());
const state = () => D(() => ROC_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => ROC_DEBUG.frames()); await page.waitForFunction((t) => ROC_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const Q = (n, d = 1n) => { n = BigInt(n); d = BigInt(d); if (d < 0n) { n = -n; d = -d; } const g = gcd(n, d) || 1n; return { n: n / g, d: d / g }; };
const add = (a, b) => Q(a.n * b.d + b.n * a.d, a.d * b.d), sub = (a, b) => Q(a.n * b.d - b.n * a.d, a.d * b.d), mul = (a, b) => Q(a.n * b.n, a.d * b.d);
const eq = (a, b) => a.n === b.n && a.d === b.d, pos = (a) => a.n > 0n, num = (a) => Number(a.n) / Number(a.d);
const I3 = [0, 1, 2];
const qmm = (A, B) => I3.map((i) => I3.map((j) => I3.reduce((s, k) => add(s, mul(A[i][k], B[k][j])), Q(0))));
const qtr = (A) => add(add(A[0][0], A[1][1]), A[2][2]);
const qdet2 = (A) => sub(mul(A[0][0], A[1][1]), mul(A[0][1], A[1][0]));
const qdet3 = (A) => add(sub(mul(A[0][0], sub(mul(A[1][1], A[2][2]), mul(A[1][2], A[2][1]))), mul(A[0][1], sub(mul(A[1][0], A[2][2]), mul(A[1][2], A[2][0])))), mul(A[0][2], sub(mul(A[1][0], A[2][1]), mul(A[1][1], A[2][0]))));
const qquad = (A, v) => I3.reduce((s, i) => I3.reduce((t, j) => add(t, mul(mul(v[i], A[i][j]), v[j])), s), Q(0));
const RHOQ = [[2, 1, 1], [1, 10, 1], [1, 1, 8]].map((r) => r.map((v) => Q(v, 20)));
const SIGQ = [[16, 4, 2], [4, 20, 1], [2, 1, 4]].map((r) => r.map((v) => Q(v, 40)));
const DQ = I3.map((i) => I3.map((j) => (i === j ? [Q(2), Q(1), Q(1, 2)][i] : Q(0))));

/* ---------- floating point, independent of the page ---------- */
const det3 = (A) => A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0]) + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]);
/* eigenvalues of a symmetric 3 × 3 matrix by the trigonometric solution of the characteristic cubic, ascending */
function ev3(A) {
  const p1 = A[0][1] ** 2 + A[0][2] ** 2 + A[1][2] ** 2, q = (A[0][0] + A[1][1] + A[2][2]) / 3;
  if (p1 < 1e-30) return [A[0][0], A[1][1], A[2][2]].sort((a, b) => a - b);
  const p = Math.sqrt(((A[0][0] - q) ** 2 + (A[1][1] - q) ** 2 + (A[2][2] - q) ** 2 + 2 * p1) / 6);
  const B = A.map((r, i) => r.map((v, j) => (v - (i === j ? q : 0)) / p)), r = det3(B) / 2;
  const phi = r <= -1 ? Math.PI / 3 : r >= 1 ? 0 : Math.acos(r) / 3;
  const e1 = q + 2 * p * Math.cos(phi), e3 = q + 2 * p * Math.cos(phi + 2 * Math.PI / 3);
  return [e3, 3 * q - e1 - e3, e1];
}
const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
const norm = (v) => Math.hypot(...v), unit = (v) => v.map((x) => x / norm(v)), dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
/* a unit eigenvector for the eigenvalue l: the longest cross product of two rows of A − l I */
function evec(A, l) { const M = A.map((r, i) => r.map((v, j) => v - (i === j ? l : 0))); const c = [cross(M[0], M[1]), cross(M[0], M[2]), cross(M[1], M[2])].sort((a, b) => norm(b) - norm(a))[0]; return unit(c); }
const quad = (A, v) => I3.reduce((s, i) => s + v[i] * I3.reduce((t, j) => t + A[i][j] * v[j], 0), 0);
const lin = (A, a, B, b) => A.map((r, i) => r.map((v, j) => a * v + b * B[i][j]));
const lamPlus = (H) => ev3(H).reduce((s, l) => s + Math.max(0, l), 0);
function family(eps, d0, d2) {
  const rho = I3.map((i) => I3.map((j) => (i === j ? [2, 10, 8][i] : eps) / 20)), d = [d0, 1, d2];
  const s0 = I3.map((i) => I3.map((j) => d[i] * rho[i][j] * d[j])), c2 = s0[0][0] + s0[1][1] + s0[2][2];
  return { rho, sigma: s0.map((r) => r.map((v) => v / c2)), c: Math.sqrt(c2), d };
}
/* the dual y*(x) = min_t λ₊(σ − tρ) + t x, by ternary search on [0, 50] */
function dualT(P, x) { const f = (t) => lamPlus(lin(P.sigma, 1, P.rho, -t)) + t * x; let a = 0, b = 50; for (let i = 0; i < 260; i++) { const m1 = a + (b - a) / 3, m2 = b - (b - a) / 3; if (f(m1) <= f(m2)) b = m2; else a = m1; } return f((a + b) / 2); }
/* the ring of unit vectors u with uᵀρu = c, then the best (or worst) value of uᵀσu on it, refined by golden section */
function ringExt(P, c, sign) {
  const w = ev3(P.rho), V = w.map((l) => evec(P.rho, l)), at = (a) => {
    const ca = Math.cos(a), sa = Math.sin(a);
    if (c <= w[1]) { const la = w[1] * ca * ca + w[2] * sa * sa, r2 = Math.max(0, (c - w[0]) / (la - w[0])), r = Math.sqrt(r2), h = Math.sqrt(1 - r2); return I3.map((k) => h * V[0][k] + r * ca * V[1][k] + r * sa * V[2][k]); }
    const la = w[0] * ca * ca + w[1] * sa * sa, r2 = Math.max(0, (w[2] - c) / (w[2] - la)), r = Math.sqrt(r2), h = Math.sqrt(1 - r2); return I3.map((k) => h * V[2][k] + r * ca * V[0][k] + r * sa * V[1][k]);
  };
  const g = (a) => sign * quad(P.sigma, at(a)); let bi = 0, bv = -Infinity; const n = 7200;
  for (let i = 0; i < n; i++) { const v = g(2 * Math.PI * i / n); if (v > bv) { bv = v; bi = i; } }
  let a = 2 * Math.PI * (bi - 1) / n, b = 2 * Math.PI * (bi + 1) / n; const gr = (Math.sqrt(5) - 1) / 2;
  for (let i = 0; i < 100; i++) { const c1 = b - gr * (b - a), c2 = a + gr * (b - a); if (g(c1) >= g(c2)) b = c2; else a = c1; }
  const u = at((a + b) / 2); return { u, v: quad(P.sigma, u), x: quad(P.rho, u) };
}
const deg = (u, v) => 180 / Math.PI * Math.acos(Math.min(1, Math.abs(dot(unit(u), unit(v)))));
const close = (a, b, tol) => Math.abs(a - b) <= tol;
const LEANP = family(1, 2, 0.5);

await page.goto(`${origin}${BASE}viz/roc-fidelity/`);
await page.waitForFunction(() => window.ROC_DEBUG && ROC_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();

/* ---------- the Lean witness, exactly ---------- */
check('opens on Lean’s counterexample at x = Q₁ = 1/10, paused', st.preset === 'lean' && st.playing === false && i.eps === 1 && i.d.join() === '2,1,0.5' && close(i.x, 0.1, 1e-12) && i.lean && i.comp !== null);
const DRD = qmm(qmm(DQ, RHOQ), DQ);
check('exactly: σ = DρD, tr ρ = tr σ = 1, and both are positive definite by their leading minors', I3.every((a) => I3.every((b) => eq(DRD[a][b], SIGQ[a][b]))) && eq(qtr(RHOQ), Q(1)) && eq(qtr(SIGQ), Q(1))
  && [RHOQ, SIGQ].every((A) => pos(A[0][0]) && pos(qdet2(A)) && pos(qdet3(A))) && I3.every((a) => I3.every((b) => close(i.rho[a][b], num(RHOQ[a][b]), 1e-15) && close(i.sigma[a][b], num(SIGQ[a][b]), 1e-15))));
const Mres = Math.max(...I3.flatMap((a) => I3.map((b) => Math.abs(i.M[a][b] - (a === b ? [2, 1, 0.5][a] : 0)))));
check('the page’s fidelity observable, computed from its definition, is D = diag(2, 1, ½) (Lean’s sqrt_observable)', Mres < 1e-10, `max |M − D| = ${Mres.toExponential(1)}`);
const qv = I3.map((k) => RHOQ[k][k]), pv = I3.map((k) => SIGQ[k][k]);
const ordered = [[0, 1], [0, 2], [1, 2]].every(([a, b]) => !pos(sub(mul(pv[b], qv[a]), mul(pv[a], qv[b]))));
check('exactly: the coordinate basis has q = (1/10, 1/2, 2/5), p = (2/5, 1/2, 1/10), cross-multiplied order a₀ = e₀, a₁ = e₁, a₂ = e₂; the page uses this basis', ordered
  && eq(qv[0], Q(1, 10)) && eq(pv[0], Q(2, 5)) && i.basis.every((b, k) => close(Math.abs(b.a[k]), 1, 1e-9)));
check('the page’s cumulative points are (0, 0), (1/10, 2/5), (3/5, 9/10), (1, 1)', [0, 0.1, 0.6, 1].every((v, k) => close(i.Q[k], v, 1e-12)) && [0, 0.4, 0.9, 1].every((v, k) => close(i.P[k], v, 1e-12)));
const vq = [Q(37), Q(2), Q(-3)], n2 = add(add(mul(vq[0], vq[0]), mul(vq[1], vq[1])), mul(vq[2], vq[2]));
const FQ = I3.map((a) => I3.map((b) => mul(mul(vq[a], vq[b]), Q(1n, n2.n))));
const F2 = qmm(FQ, FQ), fx = qtr(qmm(FQ, RHOQ)), fy = qtr(qmm(FQ, SIGQ));
check('exactly: F = vv†/1382 with v = (37, 2, −3) is a projector (so 0 ≤ F ≤ I), tr Fρ = 1/10, tr Fσ = 5539/13820 = 2/5 + 11/13820', eq(n2, Q(1382)) && I3.every((a) => I3.every((b) => eq(F2[a][b], FQ[a][b])))
  && eq(fx, Q(1, 10)) && eq(fy, Q(5539, 13820)) && eq(sub(fy, Q(2, 5)), Q(11, 13820)) && close(i.comp.x, 0.1, 1e-15) && close(i.comp.y, 5539 / 13820, 1e-15));

/* ---------- the optimal ROC ---------- */
const certify = (x, P, page) => { const H = lin(P.sigma, 1, P.rho, -page.tstar), U = lamPlus(H) + page.tstar * x; return U; };
const U1 = certify(0.1, LEANP, i), bu = i.best.u, Lb1 = quad(LEANP.sigma, bu);
check('a weak-duality certificate brackets the optimum at x = 1/10: the page’s best vector gives a lower bound, its t* an upper bound (test eigenvalues)', close(quad(LEANP.rho, bu), 0.1, 1e-12) && U1 - Lb1 < 1e-8 && i.ystar >= Lb1 - 1e-9 && i.ystar <= U1 + 1e-9, `${Lb1.toFixed(10)} ≤ y* ≤ ${U1.toFixed(10)}`);
const r1 = ringExt(LEANP, 0.1, 1);
check('maximizing uᵀσu over the ring uᵀρu = 1/10 independently gives y*(1/10) ≈ 0.402031, gap ≈ 0.00203 (the dual ternary search agrees)', close(r1.v, i.ystar, 1e-9) && close(dualT(LEANP, 0.1), i.ystar, 1e-9) && i.ystar.toFixed(6) === '0.402031' && close(i.gap, 0.0020305, 1e-7), `${r1.v.toFixed(10)}`);
check('the optimal direction at Q₁ is 3.19° from a₀ (page tilt against the test’s ring maximizer); rank 1', close(deg(r1.u, [1, 0, 0]), i.tilt, 0.02) && i.tilt.toFixed(2) === '3.19' && i.rank === 1, `${deg(r1.u, [1, 0, 0]).toFixed(3)}°`);
const Hl = lin(LEANP.sigma, 1, LEANP.rho, -i.tstar);
check('the amber axes are eigenvectors of σ − t*ρ with the page’s eigenvalues, one positive', i.HV.every((v, k) => I3.every((r) => close(I3.reduce((s, c) => s + Hl[r][c] * v[c], 0), i.Hw[k] * v[r], 1e-9))) && i.Hw.filter((l) => l > 0).length === 1);
check('the ring samples are unit vectors with uᵀρu = x, and the share beating the polyline matches', i.ring.every((u) => close(norm(u), 1, 1e-12) && close(quad(LEANP.rho, u), 0.1, 1e-12)) && close(i.ring.filter((u) => quad(LEANP.sigma, u) > 0.4 + 1e-12).length / i.ring.length, i.arcFrac, 2 / 60), `${(100 * i.arcFrac).toFixed(1)}%`);
const curveBad = i.curve.filter(([x, y]) => !close(y, dualT(LEANP, x), 1e-8));
const polyL = (x) => (x <= 0.1 ? 4 * x : x <= 0.6 ? 0.4 + (x - 0.1) : 0.9 + 0.25 * (x - 0.6));
check('the page’s optimal curve agrees with the test’s dual at every sampled x and never lies below the polyline', curveBad.length === 0 && i.curve.every(([x, y]) => y >= polyL(x) - 1e-12), `${i.curve.length} samples`);
const Gm = (() => { let best = 0; for (let k = 1; k <= 2000; k++) { const x = 0.1 * k / 2000; best = Math.max(best, dualT(LEANP, x) - 4 * x); } return best; })();
check('between 0 and Q₁ the polyline is a mixture and the optimum lies higher, by up to ≈ 0.019 (as the NUM box says)', Gm.toFixed(3) === '0.019', `${Gm.toFixed(5)}`);

/* ---------- presets ---------- */
await preset('second'); i = await info();
const r2 = ringExt(LEANP, 0.4, -1), y2 = 1 - r2.v;
check('second preset: x = Q₂ = 3/5, rank-2 optimum I − ww† with y* ≈ 0.900880 (ring minimizer and dual agree), gap ≈ 8.80 × 10⁻⁴, w 2.88° from a₂', close(i.x, 0.6, 1e-12) && i.mode === 'two' && i.rank === 2 && close(y2, i.ystar, 1e-9) && close(dualT(LEANP, 0.6), i.ystar, 1e-9) && i.ystar.toFixed(6) === '0.900880' && close(i.gap, 8.7994e-4, 1e-7) && close(deg(r2.u, [0, 0, 1]), i.tilt, 0.02), `${y2.toFixed(10)}`);
await preset('commute'); i = await info();
const PC = family(0, 2, 0.5);
check('commute preset: the gaps at Q₁ and Q₂ vanish (test dual) and the page reports 0', [0.1, 0.6].every((x, k) => close(dualT(PC, x), [0.4, 0.9][k], 1e-12)) && i.gaps.every((g) => Math.abs(g) < 1e-12) && i.tilt === 0);
await preset('small'); i = await info();
const gS = dualT(family(0.25, 2, 0.5), 0.1) - 0.4, gH = dualT(family(0.5, 2, 0.5), 0.1) - 0.4;
check('small preset: gap ≈ 1.2 × 10⁻⁴ at ε = 1/4, about a quarter of ≈ 4.9 × 10⁻⁴ at ε = 1/2', close(i.gap, gS, 1e-9) && gS.toFixed(5) === '0.00012' && gH.toFixed(5) === '0.00049' && gS / gH > 0.2 && gS / gH < 0.3, `ratio ${(gS / gH).toFixed(3)}`);
await preset('strong'); i = await info();
const P3 = family(3, 2, 0.5), r3 = ringExt(P3, 0.1, 1);
check('strong preset: ρ’s smallest eigenvalue ≈ 0.021, gap ≈ 0.0214, optimal direction ≈ 11° from a₀', close(i.rhoEig[0], ev3(P3.rho)[0], 1e-12) && ev3(P3.rho)[0].toFixed(3) === '0.021' && close(i.gap, dualT(P3, 0.1) - 0.4, 1e-9) && i.gap.toFixed(4) === '0.0214' && close(deg(r3.u, [1, 0, 0]), i.tilt, 0.02) && Math.round(i.tilt) === 11);
await preset('reversed'); i = await info();
const PR = family(1, 0.5, 2), P1R = Q(64, 85);
/* exactly: tr(DρD) = (¼ · 2 + 10 + 4 · 8)/20 = 85/40, and the first outcome e₂ has p = d₂² ρ₂₂ / tr(DρD) = 4 · (8/20) · (40/85) = 64/85 */
const trR = add(add(mul(Q(1, 4), Q(2, 20)), Q(10, 20)), mul(Q(4), Q(8, 20)));
check('reversed preset: a₀ = e₂, a₁ = e₁, a₂ = e₀, first point (2/5, 64/85), M = D/√2.125, gap ≈ 5.1 × 10⁻⁴', i.basis[0].a[2] ** 2 > 0.999 && i.basis[2].a[0] ** 2 > 0.999 && close(i.Q[1], 0.4, 1e-12) && close(i.P[1], num(P1R), 1e-12) && eq(trR, Q(85, 40)) && eq(mul(mul(Q(4), Q(8, 20)), Q(trR.d, trR.n)), P1R)
  && I3.every((k) => close(i.m.slice().sort((a, b) => a - b)[k], [0.5, 1, 2][k] / Math.sqrt(2.125), 1e-10)) && close(i.gap, dualT(PR, 0.4) - num(P1R), 1e-9) && i.gap.toFixed(5) === '0.00051');
for (const p of ['lean', 'second', 'commute', 'small', 'strong', 'reversed']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }

/* ---------- readouts and controls ---------- */
await preset('lean');
check('the readouts give the basis, the cumulative points, the optimum and Lean’s effect', /a₀ = e₀, a₁ = e₁, a₂ = e₂/.test(await text('ro2')) && /\(0\.1, 0\.4\) · \(0\.6, 0\.9\)/.test(await text('ro3')) && /y\* = 0\.402031/.test(await text('ro4')) && /5539\/13820/.test(await text('ro5')) && /11\/13820/.test(await text('ro5')));
check('the rail marks x = 0, Q₁ = 0.1, Q₂ = 0.6 and x = 1', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 'x = 0 | Q₁ = 0.1 | Q₂ = 0.6 | x = 1');
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ moves x by 0.005 and marks the settings custom', close((await info()).x, 0.105, 1e-12) && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await page.keyboard.press('e'); await settle();
check('E jumps to x = 1 and pauses', (await info()).x === 1 && (await state()).playing === false);
await click('#jumpChips [data-k="2"]');
check('the Q₂ chip jumps to x = 3/5', close((await info()).x, 0.6, 1e-12));
await click('#jumpChips [data-k="1"]');
await D(() => { const e = document.getElementById('epsIn'); e.value = 2; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the ε slider sets ε = 2; the page’s gap at Q₁ matches the test’s dual (≈ 0.0088)', i.eps === 2 && close(i.gap, dualT(family(2, 2, 0.5), 0.1) - 0.4, 1e-9) && i.gap.toFixed(4) === '0.0088');
await D(() => { const e = document.getElementById('d0In'); e.value = 0.5; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
const P05 = family(2, Math.SQRT2, 0.5);
check('the d₀ slider sets d₀ = √2; the fidelity observable is D/c with the test’s c', close(i.d[0], Math.SQRT2, 1e-12) && I3.every((k) => close(i.M[k][k], P05.d[k] / P05.c, 1e-10)) && close(i.Q[1], 0.1, 1e-9));
await preset('lean'); await setT(0.05); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('sweeping x reports the gap at Q₁', await waitToast(/Q₁ = 0\.1.*0\.00203/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['focus', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso' && (await D(() => ROC_DEBUG.cam())) === 'iso');
await preset('lean');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'second']) {
  await preset(p);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('ROC//FIDELITY · The fidelity measurement need not give optimal ROC points'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['bodor-koniorczyk-2017-fidelity-measurement-roc-refutation.md', 'D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.lean', 'Blueprint/D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.md', 'Library/Observer/bodorkoniorczyk2017quantumroc.md', 'doi.org/10.1007/s10946-017-9629-5', 'arxiv.org/abs/1603.06801'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="roc-fidelity"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.ROC_DEBUG && ROC_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'roc-fidelity');

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
