#!/usr/bin/env node
// Browser regression suite for viz/error-disturbance (Playwright + Chromium with software WebGL).
//   node tests/error-disturbance.test.mjs
// Reads page state through the read-only window.ED_DEBUG probe and checks it against an independent implementation: exact
// rational arithmetic (BigInt fractions) for the Lean instance — orthogonality, the 36 certificates by principal minors and the
// witness states — and, along the paths, quaternion rotations with eigenvalues from the closed-form cubic.
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
  const start = await page.evaluate(() => ED_DEBUG.frames());
  await page.waitForFunction((f0) => !ED_DEBUG.pending() && ED_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => ED_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D((t) => ED_DEBUG.setT(t), t); await settle(); };
const info = () => D(() => ED_DEBUG.info());
const state = () => D(() => ED_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => ED_DEBUG.frames()); await page.waitForFunction((t) => ED_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const Q = (n, d = 1n) => { n = BigInt(n); d = BigInt(d); if (d < 0n) { n = -n; d = -d; } const g = gcd(n, d) || 1n; return { n: n / g, d: d / g }; };
const qadd = (a, b) => Q(a.n * b.d + b.n * a.d, a.d * b.d), qsub = (a, b) => Q(a.n * b.d - b.n * a.d, a.d * b.d), qmul = (a, b) => Q(a.n * b.n, a.d * b.d);
const qneg = (a) => Q(-a.n, a.d), qsgn = (a) => (a.n > 0n ? 1 : a.n < 0n ? -1 : 0), qcmp = (a, b) => qsgn(qsub(a, b)), qnum = (a) => Number(a.n) / Number(a.d);
const qabs = (a) => (a.n < 0n ? qneg(a) : a);
const Z = Q(0), ONE = Q(1);
const qmat = (rows, den) => rows.map((r) => r.map((v) => Q(v, den)));
const qmm = (A, B) => A.map((r, i) => B[0].map((_, j) => [0, 1, 2].reduce((s, k) => qadd(s, qmul(A[i][k], B[k][j])), Z)));
const qT = (A) => A[0].map((_, j) => A.map((r) => r[j]));
const qplus = (A, B, s = 1) => A.map((r, i) => r.map((v, j) => (s > 0 ? qadd(v, B[i][j]) : qsub(v, B[i][j]))));
const qcol = (M, i) => [M[0][i], M[1][i], M[2][i]];
const qouter = (x) => x.map((a) => x.map((b) => qmul(a, b)));
const qquad = (H, x) => x.reduce((s, xi, a) => qadd(s, qmul(xi, H[a].reduce((u, h, b) => qadd(u, qmul(h, x[b])), Z))), Z);
const det2 = (a, b, c, d) => qsub(qmul(a, d), qmul(b, c));
const det3 = (M) => qadd(qsub(qmul(M[0][0], det2(M[1][1], M[1][2], M[2][1], M[2][2])), qmul(M[0][1], det2(M[1][0], M[1][2], M[2][0], M[2][2]))), qmul(M[0][2], det2(M[1][0], M[1][1], M[2][0], M[2][1])));
/* a symmetric 3 × 3 matrix is positive semidefinite iff all seven principal minors are ≥ 0 */
const psdExact = (M) => [M[0][0], M[1][1], M[2][2], det2(M[0][0], M[0][1], M[1][0], M[1][1]), det2(M[0][0], M[0][2], M[2][0], M[2][2]), det2(M[1][1], M[1][2], M[2][1], M[2][2]), det3(M)].every((m) => qsgn(m) >= 0);
const UQ = qmat([[312, -25, 0], [25, 312, 0], [0, 0, 313]], 313), VQ = qmat([[32976, -3757, -1020], [3893, 31824, 8640], [0, -8700, 32045]], 33205);
const IQ = [0, 1, 2].map((i) => [0, 1, 2].map((j) => (i === j ? ONE : Z)));
const projQ = (M) => [0, 1, 2].map((i) => qouter(qcol(M, i)));
function partsQ(Ap) {
  const P = projQ(IQ), Qp = projQ(Ap), R = projQ(VQ);
  return { E: P.map((p, i) => qplus(p, Qp[i], -1)), D: R.map((r) => qplus(r, Qp.reduce((s, q) => qplus(s, qmm(qmm(q, r), q)), [0, 1, 2].map(() => [Z, Z, Z])), -1)) };
}

/* ---------- floating point: quaternion rotations and closed-form eigenvalues ---------- */
const U = UQ.map((r) => r.map(qnum)), V = VQ.map((r) => r.map(qnum)), I3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
const mm = (A, B) => A.map((r, i) => B[0].map((_, j) => r.reduce((s, _, k) => s + A[i][k] * B[k][j], 0)));
const tr = (A) => A[0].map((_, j) => A.map((r) => r[j]));
function quat(R) { /* Shepperd: rotation matrix → unit quaternion (w, x, y, z) */
  const t = R[0][0] + R[1][1] + R[2][2];
  if (t > 0) { const s = 2 * Math.sqrt(1 + t); return [s / 4, (R[2][1] - R[1][2]) / s, (R[0][2] - R[2][0]) / s, (R[1][0] - R[0][1]) / s]; }
  throw new Error('rotation angle too large for this test');
}
function rotQ([w, x, y, z]) { return [[1 - 2 * (y * y + z * z), 2 * (x * y - w * z), 2 * (x * z + w * y)], [2 * (x * y + w * z), 1 - 2 * (x * x + z * z), 2 * (y * z - w * x)], [2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x * x + y * y)]]; }
function qpow(q, s) { const [w, x, y, z] = q, h = Math.acos(Math.min(1, w)), n = Math.hypot(x, y, z); if (n < 1e-15) return [1, 0, 0, 0]; const k = Math.sin(s * h) / n; return [Math.cos(s * h), x * k, y * k, z * k]; }
const TH = Math.atan2(25, 312), QVU = quat(mm(V, tr(U))), QV = quat(V);
const Rz = (a) => [[Math.cos(a), -Math.sin(a), 0], [Math.sin(a), Math.cos(a), 0], [0, 0, 1]];
const pathRef = (p, t) => (p === 'direct' ? rotQ(qpow(QV, t)) : t <= 0.5 ? Rz(2 * t * TH) : mm(rotQ(qpow(QVU, 2 * t - 1)), U));
function eigSym(A) { /* closed-form eigenvalues of a symmetric 3 × 3 matrix (trigonometric cubic) */
  const p1 = A[0][1] ** 2 + A[0][2] ** 2 + A[1][2] ** 2, q = (A[0][0] + A[1][1] + A[2][2]) / 3;
  const p2 = (A[0][0] - q) ** 2 + (A[1][1] - q) ** 2 + (A[2][2] - q) ** 2 + 2 * p1, p = Math.sqrt(p2 / 6);
  if (p < 1e-300) return [q, q, q];
  const B = A.map((r, i) => r.map((v, j) => (v - (i === j ? q : 0)) / p));
  const r = (B[0][0] * (B[1][1] * B[2][2] - B[1][2] * B[2][1]) - B[0][1] * (B[1][0] * B[2][2] - B[1][2] * B[2][0]) + B[0][2] * (B[1][0] * B[2][1] - B[1][1] * B[2][0])) / 2;
  const phi = Math.acos(Math.max(-1, Math.min(1, r))) / 3, e1 = q + 2 * p * Math.cos(phi), e3 = q + 2 * p * Math.cos(phi + 2 * Math.PI / 3);
  return [e3, 3 * q - e1 - e3, e1];
}
const nrm = (H) => { const e = eigSym(H); return Math.max(Math.abs(e[0]), Math.abs(e[2])); };
const outer = (x) => x.map((a) => x.map((b) => a * b));
const proj = (M) => [0, 1, 2].map((i) => outer([M[0][i], M[1][i], M[2][i]]));
const madd = (A, B, s = 1) => A.map((r, i) => r.map((v, j) => v + s * B[i][j]));
function ref(Ap) {
  const P = proj(I3), Qp = proj(Ap), R = proj(V);
  const E = P.map((p, i) => madd(p, Qp[i], -1)), Dj = R.map((r) => madd(r, Qp.reduce((s, q) => madd(s, mm(mm(q, r), q)), [[0, 0, 0], [0, 0, 0], [0, 0, 0]]), -1));
  let Delta = 0; const cert = [];
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
    for (const s of [1, -1]) Delta = Math.max(Delta, nrm(madd(E[i], Dj[j], s)));
    for (const a of [1, -1]) for (const b of [1, -1]) cert.push(eigSym(madd(I3.map((r) => r.map((v) => v * 71 / 250)), madd(E[i].map((r) => r.map((v) => v * a)), Dj[j], b), -1))[0]);
  }
  return { Delta, eps: Math.max(...E.map(nrm)), eta: Math.max(...Dj.map(nrm)), cert, E, D: Dj };
}
const PERMS = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
const Rb = proj(V), Pa = proj(I3);
const epsLabelRef = PERMS.map((p) => Math.max(...p.map((k, i) => nrm(madd(Pa[i], Rb[k], -1)))));
const ETA = ref(I3).eta, EPS_REL = Math.min(...epsLabelRef), F = Math.min(ETA, EPS_REL);
const near = (a, b, tol = 1e-9) => Math.abs(a - b) <= tol;
const s = Q(71, 250), r = Q(57, 200);

await page.goto(`${origin}${BASE}viz/error-disturbance/`);
await page.waitForFunction(() => window.ED_DEBUG && ED_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();

/* ---------- Lean's instance, in exact arithmetic ---------- */
check('opens on Lean’s counterexample: A′ = U at t = ½ on the path through U, paused', st.preset === 'lean' && st.playing === false && i.t === 0.5 && i.path === 'viaU' && i.Ap.every((row, a) => row.every((v, b) => near(v, U[a][b], 1e-12))));
const orth = (M) => qmm(qT(M), M).every((row, a) => row.every((v, b) => qcmp(v, a === b ? ONE : Z) === 0));
const pU = await D(() => ED_DEBUG.U()), pV = await D(() => ED_DEBUG.V());
check('U and V are the dossier’s matrices and exactly orthogonal (UᵀU = VᵀV = I in rationals)', orth(UQ) && orth(VQ) && pU.every((row, a) => row.every((v, b) => v === U[a][b])) && pV.every((row, a) => row.every((v, b) => v === V[a][b])));
const PQ = partsQ(UQ);
check('at A′ = U the error operators satisfy the dossier’s table: E₁ = −E₀ and E₂ = 0', PQ.E[2].every((row) => row.every((v) => qsgn(v) === 0)) && PQ.E[1].every((row, a) => row.every((v, b) => qcmp(v, qneg(PQ.E[0][a][b])) === 0)));
let certOK = true, certCount = 0;
for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) for (const x of [1, -1]) for (const y of [1, -1]) {
  const H = qplus(PQ.E[a].map((row) => row.map((v) => (x > 0 ? v : qneg(v)))), PQ.D[b], y);
  const M = IQ.map((row, u) => row.map((v, w) => qsub(qmul(s, v), H[u][w]))); certCount++; if (!psdExact(M)) certOK = false;
}
check('exact certificates: all 36 matrices (71/250)I − (±Eᵢ ± Dⱼ) at A′ = U have nonnegative principal minors, so Δ(I, U, V) ≤ 71/250', certOK && certCount === 36);
const R0 = ref(U);
check('Δ(I, U, V) on the page matches an independent eigenvalue computation (0.283676) and lies below 71/250', near(i.Delta, R0.Delta) && near(i.Delta, 0.283676, 5e-7) && i.Delta < 0.284);
check('the page’s 36 certificate eigenvalues match, all ≥ 0 at U, smallest about 0.000324', i.cert.length === 36 && i.cert.every((v, k) => near(v, R0.cert[k], 1e-9)) && i.certMin >= 0 && near(i.certMin, 0.000324, 5e-7));
const wv = i.worst, ws = Math.max(...[0, 1, 2].map((a) => Math.abs(wv.reduce((t, xa, u) => t + xa * R0.E[a][u].reduce((w2, h, v) => w2 + h * wv[v], 0), 0)))) + Math.max(...[0, 1, 2].map((b) => Math.abs(wv.reduce((t, xa, u) => t + xa * R0.D[b][u].reduce((w2, h, v) => w2 + h * wv[v], 0), 0))));
check('the worst state the page shows is a unit vector that attains Δ: ε_x + η_x = Δ', near(Math.hypot(...wv), 1, 1e-9) && near(ws, i.Delta, 1e-9), `ε_x + η_x = ${ws.toFixed(9)}`);
/* disturbance witness at A′ = I: D_j = R_j − diag(R_j) */
const PI = partsQ(IQ), xd = [-5, 11, -10].map((v) => Q(v)), nd = Q(246);
const distW = PI.D.map((Dj) => qabs(qquad(Dj, xd))).reduce((m, v) => (qcmp(v, m) > 0 ? v : m), Z);
check('exact witness: x = (−5, 11, −10)/√246 has disturbance > 57/200 at A′ = A, so η(I, V) > 57/200', qcmp(qmul(distW, Q(1)), qmul(r, nd)) > 0 && near(qnum(distW) / 246, 0.285112, 5e-7));
const Rq = projQ(VQ), Pq = projQ(IQ), errAt = (pi, x, n) => pi.map((k, a) => qabs(qquad(qplus(Pq[a], Rq[k], -1), x))).reduce((m, v) => (qcmp(v, m) > 0 ? v : m), Z);
const xe = [-5, -16, -11].map((v) => Q(v)), xu = [0, 1, 0].map((v) => Q(v));
const wOK = PERMS.every((pi) => (pi[1] === 1 ? qcmp(errAt(pi, xe), qmul(r, Q(402))) > 0 : qcmp(errAt(pi, xu), r) > 0));
check('exact witnesses for all 6 relabelings: (−5, −16, −11)/√402 when π(1) = 1, (0, 1, 0) otherwise, each with error > 57/200', wOK);
check('η(I, V), all six labelled errors, ε_rel and f match independent values (f = η(I, V) ≈ 0.285229 > 57/200)', near(i.etaAB, ETA) && i.epsLabel.every((v, k) => near(v, epsLabelRef[k])) && near(i.epsRel, EPS_REL) && near(i.f, F) && near(F, 0.285229, 5e-7) && F > 0.285 && near(EPS_REL, 0.285395, 5e-7));
check('the five other relabelings give errors between 0.966 and 1, as the endB note says', epsLabelRef.slice(1).every((v) => v > 0.9655 && v <= 1 + 1e-12));
check('f − Δ ≈ 0.001553 > 0 at U, and the readout and note say the second inequality fails there', near(i.gap, F - R0.Delta) && near(i.gap, 0.001553, 5e-7) && /0\.001553/.test(await text('ro4')) && /不成立/.test(await text('roNote')) && /Lean/.test(await text('roNote')));
check('the first inequality is not refuted here: ε(I, U) + η(U, V) ≈ 0.336408 ≥ f, as the readout shows', near(i.eps + i.eta, R0.eps + R0.eta) && R0.eps + R0.eta >= F && /0\.336408/.test(await text('ro2')));
check('the witness readouts match: disturbance 0.285112 at A′ = A, error 0.285337 at A′ = B', near(i.wErr, 0.285337, 5e-7) && near(i.wErr, Math.max(...ref(V).E.map((Ei) => { const x = [-5, -16, -11].map((v) => v / Math.sqrt(402)); return Math.abs(x.reduce((t, xa, u) => t + xa * Ei[u].reduce((w2, h, v) => w2 + h * x[v], 0), 0)); }))));

/* ---------- the paths ---------- */
let pathOK = true; const bad = [];
for (const p of ['viaU', 'direct']) {
  const cv = await D((p) => ED_DEBUG.curve(p), p);
  for (const [t, d, e, h] of cv) { const R1 = ref(pathRef(p, t)); if (!near(d, R1.Delta, 1e-8) || !near(e, R1.eps, 1e-8) || !near(h, R1.eta, 1e-8)) { pathOK = false; bad.push(`${p}@${t}`); } }
}
check('Δ, ε and η along both paths (201 samples each) match quaternion rotations with closed-form eigenvalues', pathOK, bad.slice(0, 4).join(' '));
let apOK = true;
for (const p of ['viaU', 'direct']) for (const t of [0.13, 0.37, 0.5, 0.71, 0.96]) {
  await D((p) => document.querySelector(`#pathChips [data-path="${p}"]`).click(), p); await setT(t); const x = await info(), A = pathRef(p, t);
  if (!x.Ap.every((row, a) => row.every((v, b) => near(v, A[a][b], 1e-9)))) apOK = false;
}
check('A′ on the page equals the independent path at t = 0.13, 0.37, 0.5, 0.71, 0.96 on both paths', apOK);
const cvU = await D(() => ED_DEBUG.curve('viaU')), cvD = await D(() => ED_DEBUG.curve('direct'));
const lowU = cvU.filter(([, d]) => d < F).map(([t]) => t);
check('through U, Δ < f from the first sample after A up to t = 0.54, and Δ(0.001) < f too', lowU[0] === 0.005 && lowU[lowU.length - 1] === 0.54 && lowU.length === 108 && ref(pathRef('viaU', 0.001)).Delta < F);
let lo = 0.4, hi = 0.5; const g = (t) => ref(pathRef('viaU', t)).Delta;
for (let k = 0; k < 80; k++) { const m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3; if (g(m1) < g(m2)) hi = m2; else lo = m1; }
await D(() => document.querySelector('#pathChips [data-path="viaU"]').click()); await settle(); i = await info();
check('the lowest Δ through U is about 0.283674 at t ≈ 0.4835, just before U; the page’s sample minimum agrees', near(g(lo), 0.283674, 5e-7) && Math.abs(lo - 0.4835) < 5e-4 && Math.abs(i.minPt[0] - lo) <= 0.005 && near(i.minPt[1], g(i.minPt[0]), 1e-9) && i.below[0] === 0.005 && i.below[1] === 0.54);
check('along the direct geodesic Δ ≥ f everywhere, lowest at A′ = A', cvD.every(([, d]) => d >= F - 1e-12) && near(cvD[0][1], F, 1e-12));
await setT(0); i = await info();
check('at t = 0 (A′ = A): ε = 0 and Δ = η(I, V)', near(i.eps, 0, 1e-12) && near(i.Delta, ETA));
await setT(1); i = await info();
check('at t = 1 (A′ = B): η = 0 and Δ = ε(I, V) with the original labels', near(i.eta, 0, 1e-12) && near(i.Delta, epsLabelRef[0]));
let sgnOK = true;
for (const t of [0, 0.25, 0.5, 0.75, 1]) { await setT(t); const x = await info(); const R1 = ref(pathRef('viaU', t)); if ((x.certMin >= 0) !== (R1.Delta <= 0.284) || (await D(() => document.getElementById('pillD').textContent.includes('✓'))) !== (x.certMin >= 0)) sgnOK = false; }
check('the certificate pill is ✓ exactly where Δ ≤ 71/250 (checked at t = 0, ¼, ½, ¾, 1)', sgnOK);

/* ---------- presets ---------- */
await preset('sweep'); i = await info();
check('sweep preset: starts at A′ = A and its note gives the minimum near t ≈ 0.48 and the crossing at t ≈ 0.54', i.t < 0.05 && i.path === 'viaU' && /0\.48/.test(await text('presetNote')) && /0\.54/.test(await text('presetNote')));
await preset('endB'); i = await info();
check('endB preset: A′ = B, the note gives ε ≈ 0.285395 and the other relabelings 0.966 to 1', i.t === 1 && /0\.285395/.test(await text('presetNote')) && /0\.966/.test(await text('presetNote')));
await preset('direct'); i = await info();
check('direct preset: the direct geodesic, with no stretch below f', i.path === 'direct' && i.below === null);
await preset('witness'); i = await info();
const wd = [-5, 11, -10].map((v) => v / Math.sqrt(246));
check('witness preset: the 3D ray is the witness (−5, 11, −10)/√246, while the first readout still shows the worst state', i.state.every((v, k) => near(v, wd[k], 1e-12)) && !(await text('ro1')).includes('-0.319, 0.701, -0.638') && /0\.285112/.test(await text('ro5')) && /0\.285337/.test(await text('ro5')));
for (const p of ['lean', 'sweep', 'endA', 'endB', 'direct', 'witness']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }

/* ---------- controls ---------- */
check('the rail marks A′ = A, U (Lean) at the midpoint and A′ = B', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => `${m.textContent}@${parseFloat(m.style.left)}`).join(' | '))) === 'A′ = A@0 | U（Lean）@50 | A′ = B@100');
await preset('lean');
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps t by 0.05 and marks the settings custom', near((await info()).t, 0.55, 1e-12) && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await page.keyboard.press('e'); await settle();
check('E jumps to A′ = B and pauses', (await info()).t === 1 && (await state()).playing === false);
await D(() => { const e = document.getElementById('now'); e.value = 0.3; e.dispatchEvent(new Event('input')); }); await settle();
check('the slider sets t', near((await info()).t, 0.3, 1e-12));
await D(() => document.querySelector('#pathChips [data-path="direct"]').click()); await settle();
check('the path chips switch to the direct geodesic and the rail drops the U mark', (await info()).path === 'direct' && (await D(() => document.querySelectorAll('#marks i').length)) === 2);
await preset('sweep'); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('walking A → U → B reports where Δ is below f and its lowest value', await waitToast(/Δ 在 t ≈ 0 到 0\.54 之间低于 f，最低 0\.28367\d 在 t ≈ 0\.4\d/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await preset('lean');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'witness']) {
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
check('English title', (await D(() => document.title)).startsWith('ERROR//DISTURB · An intermediate measurement beats both endpoints'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['zhou-wu-chau-2016-error-disturbance-endpoint-refutation.md', 'D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.lean', 'Blueprint/D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.md', 'Library/Estimation/zhouwuchau2016errordisturbance.md', 'doi.org/10.1016/j.physleta.2016.03.046', 'arxiv.org/abs/1509.03812'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="error-disturbance"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.ED_DEBUG && ED_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'error-disturbance');

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
