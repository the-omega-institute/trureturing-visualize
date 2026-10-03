#!/usr/bin/env node
// Browser regression suite for viz/syndrome-mend (Playwright + Chromium with software WebGL).
//   node tests/syndrome-mend.test.mjs
// Reads page state through the read-only window.QEC_DEBUG probe and checks it against an independent implementation:
// 8×8 Pauli matrices and the encoding built from scratch, the noise applied in the physical space, syndromes found by
// measuring the parities, the best phase compensation found by a brute-force scan, and the two-state witness of the
// lower-bound proof of Theorem ST30.2.
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
  const start = await page.evaluate(() => QEC_DEBUG.frames());
  await page.waitForFunction((f0) => !QEC_DEBUG.pending() && QEC_DEBUG.frames() >= f0 + 2, start, { timeout: 20000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => QEC_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setStage = async (t) => { await D((t) => QEC_DEBUG.setStage(t), t); await settle(); };
const info = () => D(() => QEC_DEBUG.info());
const state = () => D(() => QEC_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const hidden = (id) => D((id) => document.getElementById(id).hidden, id);
const toastOn = async () => (await D(() => document.getElementById('toast').style.opacity)) === '1';

// --- independent implementation: complex numbers [re, im], matrices as arrays of rows
const c = (re, im = 0) => [re, im];
const add = (a, b) => [a[0] + b[0], a[1] + b[1]];
const mul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const conj = (a) => [a[0], -a[1]];
const abs = (a) => Math.hypot(a[0], a[1]);
const sc = (a, s) => [a[0] * s, a[1] * s];
const ei = (t) => [Math.cos(t), Math.sin(t)];
const zerosM = (r, k) => Array.from({ length: r }, () => Array.from({ length: k }, () => c(0)));
function mm(A, B) { const R = zerosM(A.length, B[0].length); for (let i = 0; i < A.length; i++) for (let k = 0; k < B.length; k++) { const a = A[i][k]; if (!a[0] && !a[1]) continue; for (let j = 0; j < B[0].length; j++) R[i][j] = add(R[i][j], mul(a, B[k][j])); } return R; }
const dagM = (A) => A[0].map((_, j) => A.map((row) => conj(row[j])));
const addM = (A, B) => A.map((row, i) => row.map((x, j) => add(x, B[i][j])));
const scM = (A, s) => A.map((row) => row.map((x) => sc(x, s)));
const trM = (A) => A.reduce((s, row, i) => add(s, row[i]), c(0));
const normM = (A) => Math.sqrt(A.reduce((s, row) => s + row.reduce((t, x) => t + x[0] ** 2 + x[1] ** 2, 0), 0));
const eyeM = (n) => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => c(i === j ? 1 : 0)));
// qubit k (1, 2, 3) is bit 3 − k of the index 4·q1 + 2·q2 + q3
const bitOf = (k) => 1 << (3 - k);
function Xq(k) { const M = zerosM(8, 8); for (let x = 0; x < 8; x++) M[x ^ bitOf(k)][x] = c(1); return M; }
function Zq(k) { const M = zerosM(8, 8); for (let x = 0; x < 8; x++) M[x][x] = c(x & bitOf(k) ? -1 : 1); return M; }
const ENC = (() => { const E = zerosM(8, 2); E[0][0] = c(1); E[7][1] = c(1); return E; })();
const Xmask = (m) => [1, 2, 3].filter((k) => m & bitOf(k)).reduce((A, k) => mm(Xq(k), A), eyeM(8));
const Vz = (z) => [[z, c(0)], [c(0), c(1)]];
// the syndrome of a state by measuring Z1Z2 and Z2Z3 (expectation ±1 on a basis vector)
function syndromeLayer(vec8) {
  const ev = (A) => { const w = mm(A, vec8); let s = 0; for (let x = 0; x < 8; x++) s += mul(conj(vec8[x][0]), w[x][0])[0]; return s; };
  const a = ev(mm(Zq(1), Zq(2))) < 0 ? 1 : 0, b = ev(mm(Zq(2), Zq(3))) < 0 ? 1 : 0;
  return a ? (b ? 2 : 1) : (b ? 3 : 0);
}
const LAYER_MASK = [0, 4, 2, 1];
const S_old = (l) => mm(Xmask(LAYER_MASK[l]), ENC);
function branches(mode, w, p, chiDeg, phis) {
  const z = phis.map((d) => ei(d * Math.PI / 180));
  if (mode === 'iid') {
    const out = [];
    for (let m = 0; m < 8; m++) {
      const k = [1, 2, 3].filter((q) => m & bitOf(q)).length, e0 = mm(Xmask(m), ENC).map((row) => [row[0]]), l = syndromeLayer(e0);
      out.push({ mask: m, layer: l, w: p ** k * (1 - p) ** (3 - k), E: mm(Xmask(m), mm(ENC, Vz(z[l]))) });
    }
    return { list: out, z };
  }
  const s = w.reduce((a, b) => a + b, 0), wn = w.map((v) => v / s);
  const list = [0, 1, 2, 3].map((j) => ({ mask: LAYER_MASK[j], layer: j, w: wn[j], amp: sc(ei(j * chiDeg * Math.PI / 180), Math.sqrt(wn[j])), E: mm(Xmask(LAYER_MASK[j]), mm(ENC, Vz(z[j]))) }));
  return { list, z };
}
const psiOf = (thDeg, phDeg) => { const th = thDeg * Math.PI / 180; return [[c(Math.cos(th / 2))], [sc(ei(phDeg * Math.PI / 180), Math.sin(th / 2))]]; };
const rhoOf = (psi) => mm(psi, dagM(psi));
function noisy(mode, B, rho) {                            // ρ_phys
  if (mode === 'coh') { const K = B.list.reduce((A, b) => addM(A, b.E.map((row) => row.map((x) => mul(x, b.amp)))), zerosM(8, 2)); return mm(mm(K, rho), dagM(K)); }
  return B.list.reduce((A, b) => (b.w > 0 ? addM(A, scM(mm(mm(b.E, rho), dagM(b.E)), b.w)) : A), zerosM(8, 8));
}
const fold = (R) => [0, 1, 2, 3].reduce((A, l) => addM(A, mm(mm(dagM(S_old(l)), R), S_old(l))), zerosM(2, 2));
const branchLogical = (b) => mm(dagM(S_old(b.layer)), b.E);   // the logical action after folding back
function recordT(rec, K, eps, z) {
  const syn = [[0, 0], [1, 0], [1, 1], [0, 1]];
  if (rec === 'full') return [0, 1, 2, 3].map((r) => [0, 1, 2, 3].map((l) => +(r === l)));
  if (rec === 'bitA') return [0, 1].map((r) => [0, 1, 2, 3].map((l) => +(syn[l][0] === r)));
  if (rec === 'bitB') return [0, 1].map((r) => [0, 1, 2, 3].map((l) => +(syn[l][1] === r)));
  if (rec === 'none') return [[1, 1, 1, 1]];
  if (rec === 'bins') { const bin = (l) => { let a = Math.atan2(z[l][1], z[l][0]); if (a < 0) a += 2 * Math.PI; return Math.min(K - 1, Math.floor(a / (2 * Math.PI / K) + 1e-9)); }; return Array.from({ length: K }, (_, r) => [0, 1, 2, 3].map((l) => +(bin(l) === r))); }
  return [0, 1, 2, 3].map((r) => [0, 1, 2, 3].map((l) => syn[r].reduce((s, v, k) => s * (v === syn[l][k] ? 1 - eps : eps), 1)));
}
const sTof = (B, T) => T.reduce((s, Tr) => s + abs(B.list.reduce((a, b) => add(a, sc(B.z[b.layer], b.w * Tr[b.layer])), c(0))), 0);
// the best phase compensation per record cell by brute force: maximize the entanglement fidelity Σ |tr(W M)|²/4
function bruteFe(B, T) {
  let Fe = 0;
  for (const Tr of T) {
    let best = -1;
    for (let k = 0; k < 7200; k++) {
      const W = Vz(ei(2 * Math.PI * k / 7200)); let f = 0;
      for (const b of B.list) { const t = b.w * Tr[b.layer]; if (t <= 0) continue; const tr = trM(mm(W, branchLogical(b))); f += t * (tr[0] ** 2 + tr[1] ** 2) / 4; }
      best = Math.max(best, f);
    }
    Fe += best;
  }
  return Fe;
}
// trace distance between the accessible outputs of |+⟩ and |−⟩ (block by block in the record): the witness of the ST30.2 lower bound
function witness(B, T) {
  const plus = rhoOf([[c(Math.SQRT1_2)], [c(Math.SQRT1_2)]]), minus = rhoOf([[c(Math.SQRT1_2)], [c(-Math.SQRT1_2)]]);
  let d = 0;
  for (const Tr of T) {
    let diff = zerosM(2, 2);
    for (const b of B.list) { const t = b.w * Tr[b.layer]; if (t <= 0) continue; const M = branchLogical(b); diff = addM(diff, scM(addM(mm(mm(M, plus), dagM(M)), scM(mm(mm(M, minus), dagM(M)), -1)), t)); }
    // eigenvalues of a 2×2 Hermitian matrix with zero trace: ±|(a−d)/2, b|
    const a = diff[0][0][0], dd = diff[1][1][0], off = diff[0][1];
    d += Math.sqrt(((a - dd) / 2) ** 2 + off[0] ** 2 + off[1] ** 2);
  }
  return d;
}
const toM = (arr) => [[arr[0], arr[1]], [arr[2], arr[3]]];
const fromInfo = (i, key) => toM(i[key].map((x) => [x[0], x[1]]));
const PHI = { none: [0, 0, 0, 0], spread: [0, 90, 180, 270], pair: [0, 180, 0, 180] };

await page.goto(origin + BASE + 'viz/syndrome-mend/');
await page.waitForTimeout(700);
check('no toast pops up at load', !(await toastOn()));
check('page loads without script errors', errors.length === 0, errors.join(' | '));
await pause();

// --- the physics against the independent implementation, preset by preset
const P = {
  flip: { mode: 'mix', w: [0, 1, 0, 0], phi: PHI.none, rec: 'full' },
  mixed: { mode: 'mix', w: [0.4, 0.2, 0.2, 0.2], phi: PHI.none, rec: 'none' },
  coh: { mode: 'coh', w: [1, 1, 1, 1], chi: 90, phi: PHI.none, rec: 'none' },
  iid: { mode: 'iid', p: 0.1, phi: PHI.none, rec: 'full' },
  twist: { mode: 'mix', w: [1, 1, 1, 1], phi: PHI.spread, rec: 'full' },
  onebit: { mode: 'mix', w: [0.5, 0.5, 0, 0], phi: PHI.pair, rec: 'none' },
  coarse: { mode: 'mix', w: [1, 1, 1, 1], phi: PHI.spread, rec: 'bitA' },
  bins: { mode: 'mix', w: [1, 1, 1, 1], phi: [10, 100, 200, 290], rec: 'bins', K: 3 }
};
for (const [name, q] of Object.entries(P)) {
  await preset(name);
  const i = await info(), s = await state();
  const B = branches(q.mode, q.w || [1, 0, 0, 0], q.p || 0, q.chi || 0, q.phi), rho = rhoOf(psiOf(s.theta, s.phase));
  const R = noisy(q.mode, B, rho), F8 = fold(R);
  const foldErr = normM(addM(F8, scM(fromInfo(i, 'fold8'), -1)));
  const T = recordT(q.rec, q.K || 3, 0.1, B.z);
  const leak = 1 - [0, 7].reduce((s2, x) => s2 + R[x][x][0], 0);
  check(`${name}: the 8-dimensional state folds back to the page’s folded state, and leakage matches`, foldErr < 1e-12 && Math.abs(leak - i.leak) < 1e-12, `‖Δ‖ ${foldErr.toExponential(1)}, λ ${leak.toFixed(4)}`);
  // Knill–Laflamme: E_a†E_c ∝ I for every pair (coherent noise is one Kraus operator)
  const Es = q.mode === 'coh' ? [B.list.reduce((A, b) => addM(A, b.E.map((row) => row.map((x) => mul(x, b.amp)))), zerosM(8, 2))] : B.list.filter((b) => b.w > 0).map((b) => scM(b.E, Math.sqrt(b.w)));
  let kl = true; for (const A of Es) for (const C2 of Es) { const G = mm(dagM(A), C2); if (abs(G[0][1]) > 1e-9 || abs(G[1][0]) > 1e-9 || abs(add(G[0][0], sc(G[1][1], -1))) > 1e-9) kl = false; }
  check(`${name}: the Knill–Laflamme verdict agrees`, kl === i.KL, `independent ${kl}, page ${i.KL}`);
  if (i.phaseType) {
    const sT = sTof(B, T), Fe = bruteFe(B, T), wit = witness(B, T);
    check(`${name}: e* = (1 − s_T)/2, the page’s compensation is the best phase compensation, and the witness equals s_T`,
      Math.abs(i.eStar - (1 - sT) / 2) < 1e-12 && Math.abs(i.Fe - Fe) < 2e-7 && Math.abs(wit - sT) < 1e-12 && Math.abs(i.Fe - (1 - i.eStar)) < 1e-12,
      `e* ${i.eStar.toFixed(4)}, F_e page ${i.Fe.toFixed(6)} scan ${Fe.toFixed(6)}, witness ${wit.toFixed(4)}`);
    // the recovered channel is exactly (1 − e)ρ + e ZρZ, so the output for any input follows
    const Z = [[c(1), c(0)], [c(0), c(-1)]], target = addM(scM(rho, 1 - i.eStar), scM(mm(mm(Z, rho), Z), i.eStar));
    check(`${name}: the recovered state is (1 − e*)ρ + e* ZρZ`, normM(addM(fromInfo(i, 'out'), scM(target, -1))) < 1e-12);
  }
}

// --- the frozen identity itself: Σ_i S_i† 𝒩_σ(ρ) S_i = tr(σ)ρ for any matrix σ, even off-diagonal and not positive
{
  const sig = [[c(0.3, 0.1), c(-0.2, 0.4), c(0.05), c(0, -0.3)], [c(0.1, 0.2), c(0.25), c(0.3, -0.1), c(-0.4)], [c(0.2), c(0, 0.5), c(0.1, -0.2), c(0.15, 0.15)], [c(-0.1, 0.1), c(0.2), c(0.3), c(0.35, -0.05)]];
  const rho = [[c(0.7), c(0.1, -0.3)], [c(0.2, 0.4), c(-0.1)]];
  let N = zerosM(8, 8); for (let j = 0; j < 4; j++) for (let k = 0; k < 4; k++) N = addM(N, mm(mm(S_old(j), rho), dagM(S_old(k))).map((row) => row.map((x) => mul(x, sig[j][k]))));
  const lhs = fold(N), rhs = rho.map((row) => row.map((x) => mul(x, trM(sig))));
  check('orthogonal_syndrome_recovery checked independently: the fold-back gives tr(σ)·ρ for an arbitrary σ', normM(addM(lhs, scM(rhs, -1))) < 1e-14);
}

// --- preset readings and notes
await preset('flip');
let i = await info();
check('flip preset: the whole state leaves the code space (λ = 1) and is recovered exactly', Math.abs(i.leak - 1) < 1e-12 && Math.abs(i.F - 1) < 1e-12 && Math.abs(i.Fbar - 1) < 1e-12 && i.eStar < 1e-12 && /λ = 1/.test(await text('presetNote')));
await preset('coh');
i = await info();
const offDiag = Math.hypot(...i.branches[0].amp) * Math.hypot(...i.branches[1].amp);   // |σ_01| = |a_0||a_1|
check('coherent preset: a superposition of errors (σ has off-diagonal entries) folds back to exactly ρ', offDiag > 0.2 && i.plainRes < 1e-12 && Math.abs(i.F - 1) < 1e-12 && /σ/.test(await text('presetNote')));
await preset('iid');
i = await info();
const p = 0.1;
check('two-flips preset: logical failure 3p² − 2p³ = 0.028, KL fails, F̄ = 1 − 2·P/3', Math.abs(i.pFail - (3 * p * p - 2 * p ** 3)) < 1e-12 && i.KL === false && i.eStar === null && Math.abs(i.Fbar - (1 - 2 * i.pFail / 3)) < 1e-12 && /0\.028/.test(await text('presetNote')) && /✗/.test(await text('roKL')));
check('two-flips preset: the comparison chart switches to logical vs physical error rate', /逻辑错误率/.test(await text('cmpTitle')) && /3p² − 2p³/.test(await text('roL7')));
await preset('onebit');
i = await info();
check('one-bit preset: no record gives e* = 1/2, one record bit gives 0', Math.abs(i.eStar - 0.5) < 1e-12 && i.recOptions.full < 1e-12 && i.recOptions.bitA < 1e-12 && Math.abs(i.recOptions.bitB - 0.5) < 1e-12 && /1\/2/.test(await text('presetNote')));
await preset('coarse');
i = await info();
check('coarse preset: e* = 0.146 with half the syndrome, between full (0) and none (0.5)', Math.abs(i.eStar - (1 - Math.SQRT1_2) / 2) < 1e-12 && i.recOptions.full < 1e-12 && Math.abs(i.recOptions.none - 0.5) < 1e-12 && /0\.146/.test(await text('presetNote')) && (await text('roErr')) === '0.146');
await preset('bins');
i = await info();
check('phase-bins preset: e* = 0.073 within the ST31.1 bound 0.25', Math.abs(i.eStar - 0.0732233) < 1e-6 && i.eStar <= (1 - Math.cos(Math.PI / 3)) / 2 && /0\.073/.test(await text('presetNote')) && (await text('ro7')) === '0.250');

// --- ST30.5: two branches, 1 − |(1 − p)u + pv|² = p(1 − p)|u − v|², through the sliders
await preset('onebit'); await click('[data-rec="none"]');
let algebraOK = true; const detail = [];
for (const tw of ['pair', 'spread']) {
  await click(`[data-twist="${tw}"]`);
  for (const pp of [0.2, 0.5, 0.8]) {
    await setRange('w2', 0); await setRange('w3', 0); await setRange('w0', 1 - pp); await setRange('w1', pp);
    i = await info();
    const u = i.z[0], v = i.z[1], s = Math.hypot((1 - pp) * u[0] + pp * v[0], (1 - pp) * u[1] + pp * v[1]);
    const lhs = 1 - s * s, rhs = pp * (1 - pp) * Math.hypot(u[0] - v[0], u[1] - v[1]) ** 2;
    if (Math.abs(lhs - rhs) > 1e-12 || Math.abs(i.eStar - (1 - s) / 2) > 1e-12) algebraOK = false;
    detail.push(`${tw} p=${pp}: e* ${i.eStar.toFixed(4)}`);
  }
}
check('ST30.5 identity holds for the page’s two-branch numbers, and e* = (1 − |(1−p)u + pv|)/2', algebraOK, detail.join(' · '));

// --- ST30.4: coarsening only raises the error; ST31.1: bins stay under the bound for every K
await preset('bins');
let monotone = true, bounded = true; const bd = [];
for (let K = 2; K <= 8; K++) { await setRange('kbins', K); i = await info(); if (i.eStar > (1 - Math.cos(Math.PI / K)) / 2 + 1e-12) bounded = false; bd.push(`K${K}:${i.eStar.toFixed(3)}`); if (i.recOptions.none + 1e-12 < i.eStar || i.recOptions.full > i.eStar + 1e-12) monotone = false; }
check('ST31.1: for K = 2…8 the binned record stays under (1 − cos(π/K))/2', bounded, bd.join(' '));
check('ST30.4: no record ≥ any record ≥ full record', monotone);
await preset('twist'); await click('[data-rec="noisy"]');
const epsCurve = [];
for (const e of [0, 0.1, 0.25, 0.5]) { await setRange('eps', e); epsCurve.push((await info()).eStar); }
check('a noisier record never helps: e* rises from 0 (ε = 0) to 1/2 (ε = 1/2)', epsCurve[0] < 1e-12 && Math.abs(epsCurve[3] - 0.5) < 1e-12 && epsCurve.every((v, k) => k === 0 || v >= epsCurve[k - 1] - 1e-12), epsCurve.map((v) => v.toFixed(3)).join(' → '));

// --- input state: phases cannot hurt the poles
await preset('coarse'); await setRange('theta', 0);
i = await info();
check('at θ = 0 the input is immune to phase twists (F = 1) while F̄ stays 0.902', Math.abs(i.F - 1) < 1e-12 && Math.abs(i.Fbar - (1 - 2 * i.eStar / 3)) < 1e-12);
await setRange('theta', 90); await setRange('phase', 0);
i = await info();
check('at θ = 90° the input sees the full damage: 1 − F = e*', Math.abs(1 - i.F - i.eStar) < 1e-12);

// --- controls
await click('[data-mode="iid"]');
check('the independent-flip mode shows p and hides the branch weights', (await hidden('pField')) === false && (await hidden('weightFields')) === true);
await click('[data-mode="coh"]');
check('the coherent mode shows the relative phase χ', (await hidden('chiField')) === false && (await hidden('pField')) === true);
await click('[data-mode="mix"]'); await click('[data-rec="bins"]');
check('phase bins show K; the noisy record shows ε', (await hidden('kField')) === false && (await hidden('epsField')) === true);
await click('[data-rec="noisy"]');
check('…and ε for the noisy record', (await hidden('epsField')) === false && (await hidden('kField')) === true);
check('changing a control marks the settings as custom', (await state()).preset === null && /自定义/.test(await text('presetNote')));
await click('[data-twist="pair"]');
check('twist chips set the branch phases', JSON.stringify((await state()).phi) === JSON.stringify(PHI.pair));

// --- dragging a branch phase on the phasor plot
await preset('coarse');
const pt = await D(() => QEC_DEBUG.phasorPoint(1));
await page.mouse.move(pt.x, pt.y); await page.mouse.down();
await page.mouse.move(pt.cx + pt.R * Math.cos(Math.PI / 4), pt.cy - pt.R * Math.sin(Math.PI / 4), { steps: 6 }); await page.mouse.up(); await settle();
const sd = await state();
check('dragging a dot on the phasor plot sets that branch’s twist', Math.abs(sd.phi[1] - 45) <= 2 && sd.twist === null && sd.preset === null, `φ₁ = ${sd.phi[1]}°`);

// --- this run
await preset('coarse');
const h0 = (await info()).hash;
let seen = new Set(), runOK = true;
for (let k = 0; k < 8; k++) {
  i = await info();
  const b = i.branches.find((x) => x.mask === i.run.mask), Wr = (() => { const cc = i.cells[i.run.r].c, a = Math.hypot(cc[0], cc[1]); return a > 1e-12 ? [cc[0] / a, -cc[1] / a] : [1, 0]; })();
  const s = await state(), psi = psiOf(s.theta, s.phase), M = toM(b.M.map((x) => [x[0], x[1]])), W = Vz(Wr), out = mm(mm(W, M), psi);
  const ov = add(mul(conj(psi[0][0]), out[0][0]), mul(conj(psi[1][0]), out[1][0])), f = ov[0] ** 2 + ov[1] ** 2;
  if (Math.abs(f - i.run.fid) > 1e-12 || i.T[i.run.r][b.layer] !== 1) runOK = false;
  seen.add(i.hash); await page.keyboard.press('r'); await settle();
}
check('R draws new runs; each run’s branch fits its record and its fidelity is |⟨ψ|W_r M_b|ψ⟩|²', runOK && seen.size > 1 && h0 !== undefined, `${seen.size} distinct runs`);

// --- stage rail, keys and the toast
await preset('coarse'); await setStage(0);
await page.keyboard.press('ArrowRight'); await settle();
const a1 = (await state()).stage;
await page.keyboard.press('ArrowRight'); await page.keyboard.press('ArrowLeft'); await settle();
check('→ and ← step one stage', a1 === 1 && (await state()).stage === 1, `${a1} → ${(await state()).stage}`);
check('the HUD names the stage', /噪声/.test(await text('hudBig')));
await setStage(4.8); await click('#play'); await page.waitForTimeout(1600);
check('the toast reports the outcome when the pipeline completes', (await toastOn()) && /0\.146/.test(await D(() => document.getElementById('toast').textContent)));
await pause();
await setStage(1.2); await click('#play'); await page.waitForTimeout(600);
const g1 = (await state()).stage; await pause();
check('play advances the stages', g1 > 1.25);
await click('#rev'); await page.waitForTimeout(500); const g2 = (await state()).stage; await pause();
check('reverse runs backwards', g2 < g1);
await page.click('#rev'); await pause();
await page.focus('#theta'); await page.keyboard.press('Space'); await page.waitForTimeout(150);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();
for (const name of Object.keys(P)) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
i = await info();
check('the ledger note reports the fold-back check', /Σ/.test(await text('ledgerNote')) && i.ledgerRes < 1e-12);

// --- language
await setRange('w0', 0.3);
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /CODE SPACE/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('SYNDROME//MEND · Quantum error correction'));
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
await page.click('.card:has(a[href*="syndrome-mend"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'syndrome-mend');

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
