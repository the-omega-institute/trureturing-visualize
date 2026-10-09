#!/usr/bin/env node
// Browser regression suite for viz/whole-parts (Playwright + Chromium with software WebGL).
//   node tests/whole-parts.test.mjs
// Reads page state through the read-only window.WP_DEBUG probe and checks it against an independent implementation:
// two-qubit state vectors and mixtures as nested complex arrays, explicit partial traces and Pauli products, closed-form trace
// distances, conditional states after Alice's projective measurement, and a state-vector simulation of the teleportation
// protocol (mixed resources as averages of pure runs) with a numerical sphere average of the fidelity.
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
  const start = await page.evaluate(() => WP_DEBUG.frames());
  await page.waitForFunction((f0) => !WP_DEBUG.pending() && WP_DEBUG.frames() >= f0 + 2, start, { timeout: 30000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => WP_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => WP_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => WP_DEBUG.info());
const state = () => D(() => WP_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => WP_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => WP_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 60000 }); return true; } catch { return false; }
};

// --- independent implementation: complex numbers as [re, im], matrices as nested arrays
const c = (re, im = 0) => [re, im];
const cadd = (a, b) => [a[0] + b[0], a[1] + b[1]], cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]], conj = (a) => [a[0], -a[1]];
const outerV = (v) => v.map((x) => v.map((y) => cmul(x, conj(y))));
const madd = (A, B, s = 1) => A.map((r, i) => r.map((x, j) => [x[0] + s * B[i][j][0], x[1] + s * B[i][j][1]]));
const msc = (A, s) => A.map((r) => r.map((x) => [x[0] * s, x[1] * s]));
const mmul = (A, B) => A.map((r) => B[0].map((_, j) => r.reduce((s, x, k) => cadd(s, cmul(x, B[k][j])), c(0))));
const kron = (A, B) => { const n = A.length, m = B.length; return Array.from({ length: n * m }, (_, I) => Array.from({ length: n * m }, (_, J) => cmul(A[Math.floor(I / m)][Math.floor(J / m)], B[I % m][J % m]))); };
const tr = (A) => A.reduce((s, r, i) => cadd(s, r[i]), c(0));
const I2 = [[c(1), c(0)], [c(0), c(1)]], X = [[c(0), c(1)], [c(1), c(0)]], Y = [[c(0), c(0, -1)], [c(0, 1), c(0)]], Z = [[c(1), c(0)], [c(0), c(-1)]];
const PAU = [X, Y, Z];
const s2 = Math.SQRT1_2;
const vec = { phiP: [c(s2), c(0), c(0), c(s2)], phiM: [c(s2), c(0), c(0), c(-s2)], psiM: [c(0), c(s2), c(-s2), c(0)], prod: [c(1), c(0), c(0), c(0)] };
const phaseVec = (phi) => [c(s2), c(0), c(0), c(s2 * Math.cos(phi), s2 * Math.sin(phi))];
const partialVec = (th) => [c(Math.cos(th)), c(0), c(0), c(Math.sin(th))];
const basis = (k) => Array.from({ length: 4 }, (_, i) => c(i === k ? 1 : 0));
const I4 = kron(I2, I2);
const mixRho = madd(msc(outerV(basis(0)), 0.5), msc(outerV(basis(3)), 0.5));
const wernerRho = (p) => madd(msc(outerV(vec.phiP), p), msc(I4, (1 - p) / 4));
const trA = (R) => [0, 1].map((i) => [0, 1].map((j) => cadd(R[i][j], R[2 + i][2 + j])));          // trace out Alice → Bob
const trB = (R) => [0, 1].map((i) => [0, 1].map((j) => cadd(R[2 * i][2 * j], R[2 * i + 1][2 * j + 1])));   // trace out Bob → Alice
const bloch = (r) => PAU.map((P) => tr(mmul(r, P))[0] / tr(r)[0]);
const ex = (R, A, B) => tr(mmul(R, kron(A, B)))[0];
const near = (a, b, e = 1e-9) => a.length === b.length && a.every((x, i) => Math.abs(x - b[i]) < e);
const flatPage = (P) => Array.from({ length: 4 }, (_, i) => Array.from({ length: 4 }, (_, j) => c(P.re[i * 4 + j], P.im[i * 4 + j])));

await page.goto(origin + BASE + 'viz/whole-parts/');
await page.waitForFunction(() => window.WP_DEBUG && WP_DEBUG.frames() > 2, null, { timeout: 30000 });
await settle();

// --- the opening preset: Φ⁺ against Φ⁻
check('opens on the Φ⁺ / Φ⁻ comparison and plays', (await state()).preset === 'bellpair' && (await state()).playing === true && (await state()).mode === 'compare');
await pause(); await setFrac(1);
let i = await info();
const RA = flatPage(i.A.R), RB = flatPage(i.B.R);
check('whole A is |Φ⁺⟩⟨Φ⁺| and whole B is |Φ⁻⟩⟨Φ⁻| entry by entry', RA.every((r, p) => r.every((x, q) => Math.hypot(x[0] - outerV(vec.phiP)[p][q][0], x[1] - outerV(vec.phiP)[p][q][1]) < 1e-15)) && RB.every((r, p) => r.every((x, q) => Math.hypot(x[0] - outerV(vec.phiM)[p][q][0], x[1] - outerV(vec.phiM)[p][q][1]) < 1e-15)));
check('Φ⁺ is pure (Tr ρ² = 1) while each half is I/2 (purity ½, Bloch vector 0)', Math.abs(i.A.purity - 1) < 1e-12 && near(bloch(trB(RA)), [0, 0, 0]) && near(bloch(trA(RA)), [0, 0, 0]) && near(i.A.a, [0, 0, 0]) && near(i.A.b, [0, 0, 0]));
check('both halves of Φ⁺ and Φ⁻ agree exactly: local trace distances 0', i.locA < 1e-12 && i.locB < 1e-12 && near(bloch(trB(RA)), bloch(trB(RB))) && near(bloch(trA(RA)), bloch(trA(RB))));
check('the wholes are orthogonal: global trace distance 1', Math.abs(i.glob - 1) < 1e-9, i.glob.toFixed(12));
let Tok = true; for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) if (Math.abs(i.A.T[a][b] - ex(RA, PAU[a], PAU[b])) > 1e-12 || Math.abs(i.B.T[a][b] - ex(RB, PAU[a], PAU[b])) > 1e-12) Tok = false;
check('correlation tensors match Tr ρ(σ_a ⊗ σ_b): diag(1, −1, 1) and diag(−1, 1, 1)', Tok && near(i.A.T.flat(), [1, 0, 0, 0, -1, 0, 0, 0, 1]) && near(i.B.T.flat(), [-1, 0, 0, 0, 1, 0, 0, 0, 1]));
check('every local Pauli direction agrees, the difference lives only in the 9 correlation cells', [1, 2, 3].every((k) => Math.abs(i.A.P[k][0] - i.B.P[k][0]) < 1e-12 && Math.abs(i.A.P[0][k] - i.B.P[0][k]) < 1e-12) && Math.abs(i.A.P[1][1] - i.B.P[1][1] - 2) < 1e-12);
check('readouts: local 0 / 0, global 1, one-side guess ½ against 1', /0\.000 \/ 0\.000/.test(await text('roLoc')) && /1\.000/.test(await text('roGlob')) && /0\.500 \/ 1\.000/.test(await text('roGuess')) && /9\/15/.test(await text('roShare')));
// sampling: shared random numbers, Born probabilities, statistics
const born = (R, a, b) => [[1, 1], [1, -1], [-1, 1], [-1, -1]].map(([s, t]) => ex(R, madd(I2, PAU[a], s).map((r) => r.map((x) => [x[0] / 2, x[1] / 2])), madd(I2, PAU[b], t).map((r) => r.map((x) => [x[0] / 2, x[1] / 2]))));
const pA = born(RA, 0, 0), pB = born(RB, 0, 0);
check('Born probabilities for X ⊗ X: Φ⁺ gives (½, 0, 0, ½), Φ⁻ gives (0, ½, ½, 0)', near(i.A.p, pA, 1e-12) && near(i.B.p, pB, 1e-12) && near(pA, [0.5, 0, 0, 0.5], 1e-12) && near(pB, [0, 0.5, 0.5, 0], 1e-12));
const pick = (p, u) => { let k = 0, acc = p[0]; while (k < 3 && u >= acc) { k++; acc += p[k]; } return k; };
check('both wholes are sampled with the same random numbers by inverse CDF', i.u.length === 400 && i.A.out.every((k, n) => k === pick(pA, i.u[n])) && i.B.out.every((k, n) => k === pick(pB, i.u[n])));
const statsOf = (out, N) => { let ap = 0, bp = 0, E = 0; for (let n = 0; n < N; n++) { const s = out[n] < 2 ? 1 : -1, t = out[n] % 2 === 0 ? 1 : -1; if (s > 0) ap++; if (t > 0) bp++; E += s * t; } return { pa: ap / N, pb: bp / N, E: E / N }; };
const sA = statsOf(i.A.out, 400), sB = statsOf(i.B.out, 400);
check('after 400 shots the one-sided rates match each other shot by shot, the X⊗X correlation is +1 against −1', i.N === 400 && sA.pa === sB.pa && Math.abs(sA.E - 1) < 1e-12 && Math.abs(sB.E + 1) < 1e-12 && Math.abs(i.stats.A.pa - sA.pa) < 1e-12 && Math.abs(i.stats.B.E - sB.E) < 1e-12, `pa ${sA.pa.toFixed(3)}`);
check('the one-sided rate stays within sampling noise of ½', Math.abs(sA.pa - 0.5) < 0.1 && Math.abs(sA.pb - 0.5) < 0.1);
// steering: Bob's state after Alice gets ± along her axis
const condBob = (R, a, s) => { const P = madd(I2, PAU[a], s).map((r) => r.map((x) => [x[0] / 2, x[1] / 2])); return bloch(trA(mmul(kron(P, I2), R))); };
check('steering: when Alice gets ± along X, Bob holds ±X for Φ⁺ and ∓X for Φ⁻', near(i.steerA[0], condBob(RA, 0, 1)) && near(i.steerA[1], condBob(RA, 0, -1)) && near(i.steerB[0], condBob(RB, 0, 1)) && near(i.steerA[0], [1, 0, 0]) && near(i.steerB[0], [-1, 0, 0]));

// --- other comparisons against closed forms
await preset('classical'); i = await info();
let R2 = flatPage(i.B.R);
check('classical mixture: the same halves as Φ⁺, the same Z⊗Z = +1, but X⊗X = 0 and global distance ½', i.locA < 1e-12 && i.locB < 1e-12 && Math.abs(i.B.T[2][2] - 1) < 1e-12 && Math.abs(i.B.T[0][0]) < 1e-12 && Math.abs(i.glob - 0.5) < 1e-9 && R2.every((r, p) => r.every((x, q) => Math.abs(x[0] - mixRho[p][q][0]) < 1e-15)), i.glob.toFixed(9));
check('the mixture is not pure: Tr ρ² = ½', Math.abs(i.B.purity - 0.5) < 1e-12);
check('Bob’s steering for the mixture collapses onto the Z axis: Alice’s X result leaves him at I/2', near(i.steerB[0], [0, 0, 0]) && near(i.steerB[1], [0, 0, 0]));
await preset('werner'); i = await info();
check('Werner p = 0.6 against p = 0: same halves, correlations 0.6·diag(1, −1, 1), global distance ¾·0.6', i.locA < 1e-12 && near(i.A.T.flat(), [0.6, 0, 0, 0, -0.6, 0, 0, 0, 0.6], 1e-12) && near(i.B.T.flat(), [0, 0, 0, 0, 0, 0, 0, 0, 0], 1e-12) && Math.abs(i.glob - 0.45) < 1e-9, i.glob.toFixed(9));
await setRange('parA', 0.2); i = await info();
R2 = flatPage(i.A.R);
check('dragging p to 0.2 leaves the halves untouched and matches pΦ⁺ + (1 − p)I/4', i.locA < 1e-12 && Math.abs(i.glob - 0.15) < 1e-9 && R2.every((r, p) => r.every((x, q) => Math.abs(x[0] - wernerRho(0.2)[p][q][0]) < 1e-15)));
await preset('phase'); i = await info();
check('phase φ = 90° against Φ⁺: X⊗X = cos φ = 0, X⊗Y = sin φ = 1, global distance |sin(φ/2)|', i.locA < 1e-12 && Math.abs(i.A.T[0][0]) < 1e-12 && Math.abs(i.A.T[0][1] - 1) < 1e-12 && Math.abs(i.glob - Math.sin(Math.PI / 4)) < 1e-9);
await setRange('parA', 0.5); i = await info();
check('φ = 180° turns the phase state into Φ⁻: orthogonal to Φ⁺ with equal halves', i.locA < 1e-12 && Math.abs(i.glob - 1) < 1e-9);
await preset('product'); i = await info();
check('control |00⟩ against Φ⁺: the halves differ (distance ½ on both sides), Z⊗Z agrees at +1, global distance √½', Math.abs(i.locA - 0.5) < 1e-12 && Math.abs(i.locB - 0.5) < 1e-12 && Math.abs(i.A.T[2][2] - 1) < 1e-12 && Math.abs(i.B.T[2][2] - 1) < 1e-12 && Math.abs(i.glob - Math.SQRT1_2) < 1e-9);
check('…and one side alone now guesses right with probability ¾', /0\.750/.test(await text('roGuess')));
await click('#famA [data-fam="partial"]'); await setRange('parA', 0.6); i = await info();
const th = Math.PI / 4 * 0.6, Rp = outerV(partialVec(th));
check('partial entanglement cos θ|00⟩ + sin θ|11⟩: halves have Bloch length cos 2θ, steering from a pure entangled state reaches the sphere', near(i.A.a, [0, 0, Math.cos(2 * th)], 1e-12) && near(i.A.b, bloch(trA(Rp)), 1e-12) && Math.abs(Math.hypot(...i.steerA[0]) - 1) < 1e-9);
await click('#famA [data-fam="psiM"]'); i = await info();
check('the singlet Ψ⁻ has T = −I and equal halves with Φ⁺', near(i.A.T.flat(), [-1, 0, 0, 0, -1, 0, 0, 0, -1], 1e-12) && i.locA < 1e-12 && Math.abs(i.glob - 1) < 1e-9);
await click('#axA [data-ax="1"]'); await click('#axB [data-ax="2"]');
i = await info(); const RY = flatPage(i.A.R);
check('choosing Y ⊗ Z resamples with the Born probabilities of that pair', near(i.A.p, born(RY, 1, 2), 1e-12) && /Y⊗Z/.test(await text('roCorrL')) && (await state()).preset === null);

// --- teleportation
await preset('teleport'); await setFrac(1); i = await info();
const psiOf = (thD, phD) => { const t = thD * Math.PI / 180, f = phD * Math.PI / 180; return [c(Math.cos(t / 2)), c(Math.sin(t / 2) * Math.cos(f), Math.sin(t / 2) * Math.sin(f))]; };
const BELLV = [[s2, 0, 0, s2], [0, s2, s2, 0], [0, s2, -s2, 0], [s2, 0, 0, -s2]];
const CORR = [I2, X, mmul(Z, X), Z];
// state-vector teleportation for a pure resource: returns per outcome {p, bloch before, bloch after}
function tpPure(psi, res) {
  const full = []; for (let cc = 0; cc < 2; cc++) for (let k = 0; k < 4; k++) full.push(cmul(psi[cc], res[k]));       // index 4c + 2a + b
  return BELLV.map((bv, k) => {
    const bob = [0, 1].map((b) => { let s = c(0); for (let ca = 0; ca < 4; ca++) if (bv[ca]) s = cadd(s, cmul(c(bv[ca]), full[2 * ca + b])); return s; });
    const p = bob[0][0] ** 2 + bob[0][1] ** 2 + bob[1][0] ** 2 + bob[1][1] ** 2;
    const rb = outerV(bob), U = CORR[k], Ud = U[0].map((_, j) => U.map((r) => conj(r[j]))), rc = mmul(mmul(U, rb), Ud);
    return { p, pre: p > 1e-15 ? bloch(rb) : [0, 0, 0], post: p > 1e-15 ? bloch(rc) : [0, 0, 0], w: p };
  });
}
function tpMixed(psi, parts) {           // parts: [[weight, pure resource vector]]; average unnormalized Bob states per outcome
  const out = [0, 1, 2, 3].map(() => ({ p: 0, pre: [0, 0, 0], post: [0, 0, 0] }));
  for (const [w, v] of parts) tpPure(psi, v).forEach((q, k) => { out[k].p += w * q.p; for (let d = 0; d < 3; d++) { out[k].pre[d] += w * q.p * q.pre[d]; out[k].post[d] += w * q.p * q.post[d]; } });
  return out.map((q) => ({ p: q.p, pre: q.pre.map((x) => x / q.p), post: q.post.map((x) => x / q.p) }));
}
const blochPsi = (thD, phD) => { const t = thD * Math.PI / 180, f = phD * Math.PI / 180; return [Math.sin(t) * Math.cos(f), Math.sin(t) * Math.sin(f), Math.cos(t)]; };
const fid = (r, n) => (1 + r[0] * n[0] + r[1] * n[1] + r[2] * n[2]) / 2;
let ind = tpPure(psiOf(60, 40), vec.phiP), n0 = blochPsi(60, 40);
check('teleport with Φ⁺: four results with probability ¼ each', i.tp.every((q, k) => Math.abs(q.pk - 0.25) < 1e-12 && Math.abs(ind[k].p - 0.25) < 1e-12));
check('before the correction Bob holds the Pauli-twisted copies σ_k|ψ⟩ (matches the state-vector simulation)', i.tp.every((q, k) => near(q.pre, ind[k].pre, 1e-12)));
check('after the correction I, X, ZX, Z Bob holds |ψ⟩ exactly: fidelity 1 for every result', i.tp.every((q) => near(q.post, n0, 1e-12) && Math.abs(q.Fpost - 1) < 1e-12) && Math.abs(i.Fexp - 1) < 1e-12 && Math.abs(i.avg - 1) < 1e-12);
check('all 48 runs are counted and the running mean fidelity is 1', i.outc.length === 48 && i.N === 48 && Math.abs(i.stats.meanF - 1) < 1e-12 && i.stats.counts.reduce((s, x) => s + x, 0) === 48);
let pre4 = [0, 0, 0]; i.tp.forEach((q) => { for (let d = 0; d < 3; d++) pre4[d] += q.pk * q.pre[d]; });
check('averaged over the four results Bob’s uncorrected state is I/2 — his reduced state, whatever |ψ⟩ is', near(pre4, [0, 0, 0], 1e-12) && near(i.bobNoBits, [0, 0, 0], 1e-12));
await setRange('theta', 130); await setRange('phi', 250); i = await info();
ind = tpPure(psiOf(130, 250), vec.phiP);
check('a different input: the outcome probabilities stay ¼ (no signal) and the corrected state is the new |ψ⟩', i.tp.every((q, k) => Math.abs(q.pk - 0.25) < 1e-12 && near(q.post, blochPsi(130, 250), 1e-12) && near(q.pre, ind[k].pre, 1e-12)));
await preset('nobits'); i = await info();
check('withholding the bits: expected fidelity ½ = Bob guessing with I/2', Math.abs(i.Fexp - 0.5) < 1e-12 && (await state()).bits === 0 && /0\.500/.test(await text('roF')));
await preset('weak'); i = await info();
const mixParts = [[0.5, basis(0)], [0.5, basis(3)]];
let mx = tpMixed(psiOf(60, 40), mixParts);
check('classical-mixture resource: probabilities and Bob’s states match the averaged state-vector simulation', i.tp.every((q, k) => Math.abs(q.pk - mx[k].p) < 1e-12 && near(q.pre, mx[k].pre, 1e-12) && near(q.post, mx[k].post, 1e-12)));
check('classical mixture: F = ½ and the all-input average (2F + 1)/3 = 2/3, the classical limit', Math.abs(i.F - 0.5) < 1e-12 && Math.abs(i.avg - 2 / 3) < 1e-12);
// the sphere average from the independent simulation (midpoint rule in cos θ and φ)
const sphereAvg = (parts) => { let s = 0, w = 0; for (let a = 0; a < 40; a++) { const ct = -1 + (a + 0.5) * 2 / 40, thD = Math.acos(ct) * 180 / Math.PI; for (let b = 0; b < 40; b++) { const phD = (b + 0.5) * 9; const q = tpMixed(psiOf(thD, phD), parts), n = blochPsi(thD, phD); s += q.reduce((t, x) => t + x.p * fid(x.post, n), 0); w++; } } return s / w; };
const avMix = sphereAvg(mixParts);
check('independent sphere average for the mixture is 2/3 (numerical integration)', Math.abs(avMix - 2 / 3) < 2e-3 && Math.abs(avMix - i.avg) < 2e-3, avMix.toFixed(5));
await click('#famR [data-fam="werner"]'); await setRange('parR', 0.33); const iLo = await info(); await setRange('parR', 0.335); i = await info();
const pW = (await state()).parR, wParts = [[pW, vec.phiP], ...[0, 1, 2, 3].map((k) => [(1 - pW) / 4, basis(k)])];
const avW = sphereAvg(wParts);
check('Werner: the average (1 + p)/2 crosses the classical limit 2/3 at p = 1/3 (0.33 below, 0.335 above) and matches the numerical average', iLo.avg < 2 / 3 && i.avg > 2 / 3 && Math.abs(i.avg - (1 + pW) / 2) < 1e-12 && Math.abs(avW - i.avg) < 2e-3, `${iLo.avg.toFixed(5)} · ${i.avg.toFixed(5)} · numerical ${avW.toFixed(5)}`);
await setRange('parR', 0.8); i = await info();
check('Werner p = 0.8: average fidelity (1 + p)/2 = 0.9 beats 2/3', Math.abs(i.avg - 0.9) < 1e-9 && /超过/.test(await text('litNote')));
await click('#famR [data-fam="phiM"]'); i = await info();
check('Φ⁻ with the Φ⁺ correction table: F = 0 and the average drops to 1/3', Math.abs(i.F) < 1e-12 && Math.abs(i.avg - 1 / 3) < 1e-12 && /低于/.test(await text('litNote')));
await click('#famR [data-fam="product"]'); i = await info();
mx = tpMixed(psiOf(60, 40), [[1, vec.prod]]);
check('|00⟩ resource: Alice’s half is pure, so the outcome probabilities depend on the input; average 2/3', i.tp.some((q) => Math.abs(q.pk - 0.25) > 0.05) && i.tp.every((q, k) => Math.abs(q.pk - mx[k].p) < 1e-12) && Math.abs(i.avg - 2 / 3) < 1e-12);

// --- presets, mode switch and controls
const PRE = ['bellpair', 'classical', 'werner', 'phase', 'product', 'teleport', 'nobits', 'weak'];
for (const name of PRE) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await preset('bellpair');
check('compare mode shows its panel and readouts only', (await visible('cmpPanel')) && !(await visible('tpPanel')) && (await visible('roCmp')) && !(await visible('roTp')));
await click('#modeChips [data-mode="teleport"]');
check('switching to teleportation swaps panels, resets the runs, and marks the settings custom', !(await visible('cmpPanel')) && (await visible('tpPanel')) && (await visible('roTp')) && (await state()).nowFrac === 0 && (await state()).preset === null && /自定义/.test(await text('presetNote')));
check('the rail is labelled in runs 0 … 48', (await D(() => [...document.querySelectorAll('#marks i')].map(m => m.textContent).join(' '))) === '0 12 24 36 48');
await click('#modeChips [data-mode="compare"]');
check('…and back in compare mode in shots 0 … 400', (await D(() => [...document.querySelectorAll('#marks i')].map(m => m.textContent).join(' '))) === '0 100 200 300 400');
await setFrac(0.5); const u0 = (await info()).u.slice(0, 20).join(',');
await page.keyboard.press('r'); await settle();
check('R draws new random numbers', (await info()).u.slice(0, 20).join(',') !== u0);
await setFrac(0.5);
await page.keyboard.press('ArrowRight'); await settle();
check('→ adds exactly one shot', (await info()).N === 201);
await page.keyboard.press('ArrowLeft'); await page.keyboard.press('ArrowLeft'); await settle();
check('← removes shots', (await info()).N === 199);
await click('#famB [data-fam="werner"]');
check('a family with a parameter shows its slider', (await visible('parBField')) && /p/.test(await text('parBLabel')));
await click('#famB [data-fam="phiM"]');
check('…and hides it again for a fixed state', !(await visible('parBField')));

// --- rail, play, toasts
await preset('bellpair'); await setFrac(0.97); await click('#play');
check('the toast reports the one-sided rates and the correlations after 400 shots', await waitToast(/400/));
await pause();
await preset('teleport'); await setFrac(0.985); await click('#play');
check('the toast reports the mean fidelity after 48 teleportations', await waitToast(/48/));
await pause();
await preset('bellpair'); await setFrac(0.3); await click('#play'); await waitFrames(12); const f1 = (await state()).nowFrac; await pause();
check('play advances the shots', f1 > 0.3);
await click('#rev'); await waitFrames(12); const f2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', f2 < f1);
await page.click('#rev'); await pause();
await page.focus('#parA'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await click('#axB [data-ax="1"]');
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode (compare)', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /ALICE/.test(tags), tags);
await click('#modeChips [data-mode="teleport"]'); await setFrac(0.5);
const left2 = await D(() => { const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n; while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; const st = getComputedStyle(el); let hid = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hid = true; break; } if (st.display === 'none' || hid || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); } return bad; });
check('no visible Chinese left in English mode (teleportation)', left2.length === 0, left2.join(' | '));
check('English title', (await D(() => document.title)).startsWith('WHOLE//PARTS · The whole is more than its parts'));
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
await page.click('.card:has(a[href*="whole-parts"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'whole-parts');

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
