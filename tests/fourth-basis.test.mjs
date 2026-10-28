#!/usr/bin/env node
// Browser regression suite for viz/fourth-basis (Playwright + Chromium with software WebGL).
//   node tests/fourth-basis.test.mjs
// Reads page state through the read-only window.MUB_DEBUG probe and checks it against an independent implementation:
// the known bases rebuilt from their definitions (Pauli bases, Fourier and quadratic-phase bases as nested complex arrays,
// qubit ⊗ qutrit products), overlap probabilities recomputed from the page's own candidates, unitarity of the candidates,
// the commutator identity Σ‖[P, Q]‖² = 2(cols − Σp²) checked on explicit projectors, the honesty of the status labels, and the
// Schmidt-number witness: the joint table rebuilt from Φ⁺ as a d²-vector and explicit product vectors, positive semidefiniteness
// by an LDLᵀ factorization (so the trace norm is the trace), the bounds, and the thresholds found by bisection.
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
  const start = await page.evaluate(() => MUB_DEBUG.frames());
  await page.waitForFunction((f0) => !MUB_DEBUG.pending() && MUB_DEBUG.frames() >= f0 + 2, start, { timeout: 60000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => MUB_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => MUB_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => MUB_DEBUG.info());
const state = () => D(() => MUB_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => MUB_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => MUB_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 60000 }); return true; } catch { return false; }
};

// --- independent implementation: vectors as arrays of [re, im]; a basis is an array of column vectors
const cexp = (t) => [Math.cos(t), Math.sin(t)];
const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const inner = (u, v) => u.reduce((s, x, k) => { const p = cmul([x[0], -x[1]], v[k]); return [s[0] + p[0], s[1] + p[1]]; }, [0, 0]);
const abs2 = (z) => z[0] * z[0] + z[1] * z[1];
const std = (d) => Array.from({ length: d }, (_, k) => Array.from({ length: d }, (_, j) => [j === k ? 1 : 0, 0]));
const four = (d, q) => Array.from({ length: d }, (_, k) => Array.from({ length: d }, (_, j) => cexp(2 * Math.PI * (j * k + q * j * j) / d).map((x) => x / Math.sqrt(d))));
const r2 = Math.SQRT1_2;
const qubit = [std(2), [[[r2, 0], [r2, 0]], [[r2, 0], [-r2, 0]]], [[[r2, 0], [0, r2]], [[r2, 0], [0, -r2]]]];
const tensor = (A, B) => A.flatMap((a) => B.map((b) => a.flatMap((x) => b.map((y) => cmul(x, y)))));     // columns a ⊗ b
const known = (d) => d === 2 ? qubit : d === 6 ? [0, 1, 2].map((r) => tensor(qubit[r], [std(3), four(3, 0), four(3, 1)][r])) : [std(d), four(d, 0), four(d, 1)];
const pageCols = (M) => { const n = Math.round(Math.sqrt(M.re.length)); return Array.from({ length: n }, (_, k) => Array.from({ length: n }, (_, j) => [M.re[j * n + k], M.im[j * n + k]])); };
const candCols = (U, d, cols) => Array.from({ length: cols }, (_, k) => Array.from({ length: d }, (_, j) => [U.re[j * cols + k], U.im[j * cols + k]]));
const maxUnbiasDev = (A, B, d) => { let m = 0; for (const a of A) for (const b of B) m = Math.max(m, Math.abs(abs2(inner(a, b)) - 1 / d)); return m; };
const defect = (Bs, V, d) => { let s = 0; for (const B of Bs) for (const b of B) for (const v of V) s += (abs2(inner(b, v)) - 1 / d) ** 2; return s; };
const orthoDev = (V) => { let m = 0; V.forEach((a, i) => V.forEach((b, j) => { const z = inner(a, b); m = Math.max(m, Math.hypot(z[0] - (i === j ? 1 : 0), z[1])); })); return m; };
// ‖[P, Q]‖² for rank-one projectors P = |a⟩⟨a|, Q = |b⟩⟨b| built as explicit matrices
const proj = (a) => a.map((x) => a.map((y) => cmul(x, [y[0], -y[1]])));
const mm = (A, B) => A.map((r) => B[0].map((_, j) => r.reduce((s, x, k) => { const p = cmul(x, B[k][j]); return [s[0] + p[0], s[1] + p[1]]; }, [0, 0])));
const commSq = (a, b) => { const P = proj(a), Q = proj(b), X = mm(P, Q), Y = mm(Q, P); let s = 0; X.forEach((r, i) => r.forEach((x, j) => { s += (x[0] - Y[i][j][0]) ** 2 + (x[1] - Y[i][j][1]) ** 2; })); return s; };

await page.goto(origin + BASE + 'viz/fourth-basis/');
await page.waitForFunction(() => window.MUB_DEBUG && MUB_DEBUG.frames() > 2, null, { timeout: 60000 });
await settle();

// --- the known bases
check('opens on the six-dimensional search and plays', (await state()).preset === 'six' && (await state()).d === 6 && (await state()).playing === true);
await pause();
for (const d of [2, 3, 5, 6, 7]) {
  await click(`#dimChips [data-dim="${d}"]`); const i = await info(), Bs = known(d);
  let same = true; i.bases.forEach((M, r) => { const C = pageCols(M); C.forEach((col, k) => col.forEach((z, j) => { if (Math.hypot(z[0] - Bs[r][k][j][0], z[1] - Bs[r][k][j][1]) > 1e-12) same = false; })); });
  const dev = Math.max(maxUnbiasDev(Bs[0], Bs[1], d), maxUnbiasDev(Bs[0], Bs[2], d), maxUnbiasDev(Bs[1], Bs[2], d));
  check(`d = ${d}: the page’s three bases match their definitions and are pairwise unbiased`, same && dev < 1e-12 && i.pairDev < 1e-12 && Bs.every((B) => orthoDev(B) < 1e-12), dev.toExponential(1));
}

// --- six dimensions: the search stalls
await preset('six'); await setFrac(1); let i = await info();
let Bs = known(6), worstD = 0, worstO = 0;
i.Ufinal.forEach((U, k) => { const V = candCols(U, 6, 6); worstD = Math.max(worstD, Math.abs(defect(Bs, V, 6) - i.finals[k])); worstO = Math.max(worstO, orthoDev(V)); });
check('d = 6: every final candidate is unitary and its defect matches an independent recomputation', worstO < 1e-10 && worstD < 1e-10, `${worstO.toExponential(1)} · ${worstD.toExponential(1)}`);
check('d = 6: no start brings the defect below 10⁻²⁰; all stall above 0.1', i.finals.every((x) => x > 0.1) && i.stats.hits === 0 && i.stats.n === 8, i.finals.map((x) => x.toFixed(3)).join(' '));
check('d = 6: the defect never increases along a run (descent)', i.hist.every((x, t) => t === 0 || x <= i.hist[t - 1] + 1e-15));
check('d = 6: the status reads OPEN and the note calls it a numerical lead, not a proof', /OPEN/.test(await text('pillOpen')) && /不是证明|数值线索/.test(await text('roNote')) && /≥ 3 \/ 7/.test(await text('roKnown')));
await setFrac(0.06); i = await info();               // mid-run, where the snapshot shown differs from the final candidate
const P0 = i.P, Vnow = candCols(i.U, 6, 6);
check('the bar heights are the overlap probabilities |⟨b|u⟩|² of the candidate shown now (mid-run)', i.pos.t > 0 && i.pos.t < 400 && P0.every((P, r) => P.every((p, q) => Math.abs(p - abs2(inner(Bs[r][Math.floor(q / 6)], Vnow[q % 6]))) < 1e-12)), `start ${i.pos.s + 1} step ${i.pos.t}`);
let cs = 0; for (const b of Bs[1]) for (const v of Vnow) cs += commSq(b, v);
const cs2 = 2 * (6 - P0[1].reduce((s, p) => s + p * p, 0));
check('commutator readout: Σ‖[P_j, Q_r]‖² from explicit projectors equals 2(d − Σp²), at most 2(d − 1) = 10', Math.abs(cs - cs2) < 1e-10 && cs2 <= 10 + 1e-12 && (await text('roComm')).split(' · ')[1] === cs2.toFixed(4), `${cs.toFixed(6)}`);

// --- prime dimensions: the same search finds a fourth basis
// with the page's default seed; other batches of starts can find none in d = 7
for (const [name, d, minHits] of [['five', 5, 1], ['three', 3, 6], ['seven', 7, 1]]) {
  await preset(name); await setFrac(1); i = await info(); Bs = known(d);
  const k = i.finals.findIndex((x) => x < 1e-20), V = k >= 0 ? candCols(i.Ufinal[k], d, d) : null;
  const ok = V && orthoDev(V) < 1e-10 && Bs.every((B) => maxUnbiasDev(B, V, d) < 1e-12);
  check(`d = ${d}: at least ${minHits} start(s) find a basis unbiased to all three, verified independently`, i.stats.hits >= minHits && ok && /EXISTS/.test(await text('pillOpen')), `hits ${i.stats.hits}/8`);
}
await preset('five'); await setFrac(1); i = await info();
const kFound = i.finals.findIndex((x) => x < 1e-20); Bs = known(5);
const Vf = candCols(i.Ufinal[kFound], 5, 5); let csF = 0; for (const b of Bs[2]) for (const v of Vf) csF += commSq(b, v);
check('d = 5: for a basis found, the commutator sum reaches its maximum 2(d − 1) = 8', Math.abs(csF - 8) < 1e-9, csF.toFixed(9));

// --- dimension two: proved impossible
await preset('two'); await setFrac(1); i = await info();
check('d = 2: the defect stalls (no fourth basis exists) and the status says proved', i.finals.every((x) => x > 0.5) && /PROVED/.test(await text('pillOpen')) && /已证/.test(await text('roNote')));

// --- single vectors
await preset('sixvec'); await setFrac(1); i = await info(); Bs = known(6);
let vOK = true; i.Ufinal.forEach((U, k) => { const v = candCols(U, 6, 1); if (Math.abs(defect(Bs, v, 6) - i.finals[k]) > 1e-10 || orthoDev(v) > 1e-10) vOK = false; });
check('d = 6, one vector: all starts stall above 0.03; the defects match an independent recomputation', vOK && i.finals.every((x) => x > 0.03) && i.stats.hits === 0 && i.cols === 1, i.finals.map((x) => x.toFixed(4)).join(' '));
check('…and the commutator readout is not shown for a single vector', (await text('roComm')) === '—');
await preset('fivevec'); await setFrac(1); i = await info(); Bs = known(5);
const v5 = candCols(i.Ufinal[i.finals.findIndex((x) => x < 1e-20)], 5, 1);
check('d = 5, one vector: found, and unbiased to all three bases by direct check', i.stats.hits >= 6 && Bs.every((B) => maxUnbiasDev(B, v5, 5) < 1e-12));

// --- the known three, pairwise
await preset('known'); i = await info();
check('known three in d = 6: every pairwise overlap is 1/6, no search is run', i.view === 'known' && i.P.every((P) => P.every((p) => Math.abs(p - 1 / 6) < 1e-12)) && !(await visible('targetChips')) && (await text('roHits')) === '—');

// --- the Schmidt-number witness with the known bases
const phiPlus = (d) => Array.from({ length: d * d }, (_, q) => (Math.floor(q / d) === q % d ? [1 / Math.sqrt(d), 0] : [0, 0]));
function witnessQ(d, m, v) {            // ⟨x ⊗ y|ρ|x ⊗ y⟩ for ρ = v|Φ⁺⟩⟨Φ⁺| + (1 − v)I/d², x from Alice's basis, y the conjugate of Bob's
  const Bs = known(d).slice(0, m), F = phiPlus(d), n = m * d, Q = [];
  for (let l = 0; l < m; l++) for (let a = 0; a < d; a++) { const row = []; for (let k = 0; k < m; k++) for (let b = 0; b < d; b++) {
    const x = Bs[l][a], y = Bs[k][b].map(([re, im]) => [re, -im]), xy = x.flatMap((xj) => y.map((yk) => cmul(xj, yk))), amp = inner(xy, F);
    row.push(v * abs2(amp) + (1 - v) / (d * d)); } Q.push(row); }
  return Q;
}
function ldlPsd(Q) {                    // LDLᵀ without pivoting; positive semidefinite when every pivot is ≥ −1e−12 (zero pivots skip their column)
  const n = Q.length, A = Q.map((r) => r.slice()); let ok = true;
  for (let k = 0; k < n; k++) { const p = A[k][k]; if (p < -1e-12) ok = false; if (Math.abs(p) < 1e-12) continue; for (let i = k + 1; i < n; i++) { const f = A[i][k] / p; for (let j = k + 1; j < n; j++) A[i][j] -= f * A[k][j]; } }
  return ok;
}
const traceOf = (Q) => Q.reduce((s, r, k) => s + r[k], 0);
const certifiedOf = (tn, m, d) => { let r = 0; for (let k = 1; k <= d; k++) if (tn > 1 + (m - 1) * k / d + 1e-12) r = k; return r + 1; };
await preset('witness6'); await setFrac(0.6); i = await info();
const Qw = witnessQ(6, 3, 0.6);
check('witness: the preset uses d = 6, m = 3, an 18 × 18 table, and every entry equals the table rebuilt from Φ⁺ and explicit product vectors', i.view === 'witness' && i.d === 6 && i.m === 3 && i.n === 18 && Qw.every((r, a) => r.every((x, b) => Math.abs(x - i.Q[a * 18 + b]) < 1e-12)));
let psdOK = true, tnOK = true;
for (const v of [0, 0.2, 0.6, 1]) { const Qv = witnessQ(6, 3, v); await setFrac(v); const j = await info(); if (!ldlPsd(Qv)) psdOK = false; if (Math.abs(j.tn - traceOf(Qv)) > 1e-9 || Math.abs(traceOf(Qv) - (3 * v + 0.5 * (1 - v))) > 1e-12) tnOK = false; }
check('…the table is positive semidefinite (LDLᵀ), so its trace norm is its trace 3v + (1 − v)/2, and the page’s trace norm agrees at four visibilities', psdOK && tnOK);
check('…the bounds are 1 + 2r/6 for r = 1 … 6', i.bounds.length === 6 && i.bounds.every((b, k) => Math.abs(b - (1 + 2 * (k + 1) / 6)) < 1e-12));
let certOK = true, certDetail = '';
for (const v of [0.3, 0.34, 0.5, 0.75, 1]) { await setFrac(v); const j = await info(), want = certifiedOf(traceOf(witnessQ(6, 3, v)), 3, 6); if (j.certified !== want) { certOK = false; certDetail += `v=${v}: ${j.certified}≠${want} `; } }
check('…the certified Schmidt number matches the independent rule at v = 0.3, 0.34, 0.5, 0.75, 1 (1, 2, 3, 5, 6)', certOK && certifiedOf(traceOf(witnessQ(6, 3, 0.34)), 3, 6) === 2 && certifiedOf(traceOf(witnessQ(6, 3, 1)), 3, 6) === 6, certDetail);
const bisect = (m, d, r) => { let lo = 0, hi = 1; for (let it = 0; it < 60; it++) { const mid = (lo + hi) / 2; if (traceOf(witnessQ(d, m, mid)) > 1 + (m - 1) * r / d) hi = mid; else lo = mid; } return hi; };
check('…the thresholds on the page match bisection on the independent trace norm: entanglement for v > 1/3, Schmidt number 6 only at v = 1', i.thresholds.slice(0, 5).every((t, k) => Math.abs(t - bisect(3, 6, k + 1)) < 1e-9) && Math.abs(i.thresholds[0] - 1 / 3) < 1e-12 && i.thresholds[5] === 1);
await setFrac(0.5);
check('…the readouts show the trace norm 1.75 and Schmidt number ≥ 3, and the rail marks v = 0, 1/3, v = 1', (await text('roWq')) === '1.750000' && /≥ 3/.test(await text('roWr')) && (await D(() => [...document.querySelectorAll('#marks i')].map(m => m.textContent).join(' '))) === 'v=0 1/3 v=1');
check('…the witness view shows the m chips and its readouts, and hides the target chips and the search readouts', (await visible('mChips')) && (await visible('roWit')) && !(await visible('targetChips')) && !(await visible('roSearch')));
await click('#mChips [data-m="1"]'); await setFrac(1); i = await info();
check('…with one basis the bound is 1 and the trace norm reaches at most 1: nothing is certified', i.m === 1 && Math.abs(i.tn - 1) < 1e-9 && i.bounds.every((b) => Math.abs(b - 1) < 1e-12) && i.certified === 1 && (await state()).preset === null);
await click('#mChips [data-m="2"]'); i = await info();
check('…with two bases the entanglement threshold is 1/2', i.m === 2 && Math.abs(i.thresholds[0] - 0.5) < 1e-12 && Math.abs(i.thresholds[0] - bisect(2, 6, 1)) < 1e-9);
await click('#dimChips [data-dim="2"]'); i = await info();
check('…in d = 2 the theorem needs m ≤ d: the m = 3 chip is disabled and m stays 2', i.d === 2 && i.m === 2 && (await D(() => document.querySelector('#mChips [data-m="3"]').disabled)) && i.n === 4);
await preset('witness6'); await setFrac(0.995); await click('#play');
check('the toast at v = 1 reports Schmidt number ≥ 6', await waitToast(/Schmidt 数 ≥ 6/));
await pause();

// --- rail, keys, controls
await preset('six');
check('the rail marks the 8 starts', (await D(() => [...document.querySelectorAll('#marks i')].map(m => m.textContent).join(' '))) === '0 1 2 3 4 5 6 7 8');
await setFrac(0);
await page.keyboard.press('ArrowRight'); await settle();
check('→ jumps to the next start', (await info()).pos.s === 1 && (await info()).pos.t === 0);
await page.keyboard.press('ArrowLeft'); await settle();
check('← jumps back', (await info()).pos.s === 0);
const f0 = (await info()).finals.join(',');
await page.keyboard.press('r'); await settle();
check('R draws new random starts', (await info()).finals.join(',') !== f0);
await click('#targetChips [data-target="vector"]');
check('changing the target marks the settings custom and resets the search', (await state()).preset === null && (await state()).nowFrac === 0 && (await info()).cols === 1 && /自定义/.test(await text('presetNote')));
await click('#viewChips [data-view="known"]');
check('the known-three view hides the target chips and blanks the rail', !(await visible('targetChips')) && (await D(() => document.getElementById('marks').children.length)) === 0);
await click('#viewChips [data-view="search"]');
const PRE = ['six', 'five', 'three', 'seven', 'two', 'sixvec', 'fivevec', 'known', 'witness6'];
for (const name of PRE) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }

// --- play and toasts
await preset('six'); await setFrac(0.995); await click('#play');
check('the toast in six dimensions says nothing was found and that this is not a proof', await waitToast(/不是证明/));
await pause();
await preset('three'); await setFrac(0.995); await click('#play');
check('the toast in three dimensions reports the starts that found it', await waitToast(/找到了/));
await pause();
await preset('five'); await setFrac(0.3); await click('#play'); await waitFrames(12); const g1 = (await state()).nowFrac; await pause();
check('play advances the search', g1 > 0.3);
await click('#rev'); await waitFrames(12); const g2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', g2 < g1);
await page.click('#rev'); await pause();
await page.focus('#now'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with the slider focused', playing === true);
await pause();

// --- language
await click('#dimChips [data-dim="7"]');
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftoverText = () => D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
const leftovers = await leftoverText();
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /vs Fourier/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('FOURTH//BASIS · A fourth mutually unbiased basis'));
await preset('witness6'); await setFrac(0.6);
const leftoversW = await leftoverText();
check('no visible Chinese left in English mode (witness view), 3D labels included', leftoversW.length === 0 && !/[一-鿿]/.test(await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' '))), leftoversW.join(' | '));
await page.click('#infoBtn'); await page.waitForTimeout(200);
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer cites Tavakoli and Morelli (DOI and arXiv) and names the frozen theorem', await D(() => { const en = document.querySelector('#drawer div.en'), h = [...en.querySelectorAll('a')].map((a) => a.href).join(' '); return h.includes('10.1103/PhysRevA.110.062417') && h.includes('arxiv.org/abs/2402.09972') && en.textContent.includes('TavakoliMorelliIncompleteMUB.result'); }));
await page.keyboard.press('Escape'); await page.waitForTimeout(150);
check('Esc closes the drawer', (await D(() => document.getElementById('drawer').hidden)) === true);
check('focus returns to the drawer button', (await D(() => document.activeElement?.id)) === 'infoBtn');

// --- index round trip
const live = readRegistry().visualizations.filter(v => v.status === 'live').length;
await page.click('.crumb'); await page.waitForLoadState('load'); await page.waitForTimeout(800);
check('language choice carries to the index', (await D(() => document.documentElement.dataset.lang)) === 'en');
check('index lists every live visualization', (await D(() => document.querySelectorAll('.card').length)) === live, `live ${live}`);
await page.click('.card:has(a[href*="fourth-basis"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'fourth-basis');

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
