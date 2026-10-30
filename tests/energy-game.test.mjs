#!/usr/bin/env node
// Browser regression suite for viz/energy-game (Playwright + Chromium with software WebGL).
//   node tests/energy-game.test.mjs
// Reads page state through the read-only window.EG_DEBUG probe and checks it against an independent implementation: graph
// energies from Householder tridiagonalization and Sturm-sequence bisection, Shapley values of K_{a,b} written as an average
// over the number of predecessors with hypergeometric weights, the frozen closed form of the scarce-side payoff for a = 2,
// brute-force enumeration of every coalition of K₂,₄, K₂,₅ and K₃,₄ with their actual adjacency matrices, and an enumeration
// of every labelled graph on at most 6 vertices. Fixed reference data: the dossier's exact interval for the deficit of K₂,₅₀
// and the Shapley value of P₃ in Example 3.9 of the paper.
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
  const start = await page.evaluate(() => EG_DEBUG.frames());
  await page.waitForFunction((f0) => !EG_DEBUG.pending() && EG_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => EG_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => EG_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => EG_DEBUG.info());
const state = () => D(() => EG_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => EG_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => EG_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 120000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
/* Householder reduction to a tridiagonal matrix, then every eigenvalue by Sturm-count bisection */
function tridiag(A) {
  const n = A.length, M = A.map((r) => r.slice());
  for (let k = 0; k < n - 2; k++) {
    let alpha = 0; for (let i = k + 1; i < n; i++) alpha += M[i][k] * M[i][k]; alpha = Math.sqrt(alpha);
    if (alpha < 1e-300) continue;
    if (M[k + 1][k] > 0) alpha = -alpha;
    const v = new Array(n).fill(0); v[k + 1] = M[k + 1][k] - alpha; for (let i = k + 2; i < n; i++) v[i] = M[i][k];
    const vv = v.reduce((s, x) => s + x * x, 0); if (vv < 1e-300) continue;
    const u = v.map((x) => x * Math.sqrt(2 / vv)), p = M.map((row) => row.reduce((s, x, j) => s + x * u[j], 0)), up = u.reduce((s, x, i) => s + x * p[i], 0), q = p.map((x, i) => x - up / 2 * u[i]);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) M[i][j] -= u[i] * q[j] + q[i] * u[j];
  }
  return { a: M.map((r, i) => r[i]), b: Array.from({ length: Math.max(0, n - 1) }, (_, i) => M[i + 1][i]) };
}
function countBelow({ a, b }, x) { let q = 1, c = 0; for (let i = 0; i < a.length; i++) { q = a[i] - x - (i ? b[i - 1] * b[i - 1] / q : 0); if (q === 0) q = -1e-300; if (q < 0) c++; } return c; }
function eigenvalues(A) {
  const n = A.length; if (n === 0) return []; if (n === 1) return [A[0][0]];
  const T = tridiag(A); let lo = Infinity, hi = -Infinity;
  for (let i = 0; i < n; i++) { const r = (i ? Math.abs(T.b[i - 1]) : 0) + (i < n - 1 ? Math.abs(T.b[i]) : 0); lo = Math.min(lo, T.a[i] - r); hi = Math.max(hi, T.a[i] + r); }
  const out = [];
  for (let k = 1; k <= n; k++) { let x0 = lo - 1e-9, x1 = hi + 1e-9; for (let it = 0; it < 100; it++) { const mid = (x0 + x1) / 2; if (countBelow(T, mid) >= k) x1 = mid; else x0 = mid; } out.push((x0 + x1) / 2); }
  return out;
}
const energyOf = (A) => eigenvalues(A).reduce((s, l) => s + Math.abs(l), 0);
const bits = (S, n) => { const o = []; for (let i = 0; i < n; i++) if (S >> i & 1) o.push(i); return o; };
function bruteGame(n, edges) {
  const adj = Array.from({ length: n }, () => new Array(n).fill(0)); for (const [i, j] of edges) adj[i][j] = adj[j][i] = 1;
  const N = 1 << n, w = new Float64Array(N);
  for (let S = 1; S < N; S++) { const idx = bits(S, n); w[S] = energyOf(idx.map((i) => idx.map((j) => adj[i][j]))); }
  const lf = (k) => { let s = 0; for (let i = 2; i <= k; i++) s += Math.log(i); return s; };
  const phi = new Array(n).fill(0);
  for (let i = 0; i < n; i++) for (let S = 0; S < N; S++) if (!(S >> i & 1)) { const s = bits(S, n).length; phi[i] += Math.exp(lf(s) + lf(n - s - 1) - lf(n)) * (w[S | 1 << i] - w[S]); }
  let best = -Infinity, arg = 0; for (let S = 1; S < N; S++) { const d = w[S] - bits(S, n).reduce((t, i) => t + phi[i], 0); if (d > best) { best = d; arg = S; } }
  return { w, phi, best, arg, adj };
}
const bipE = (a, b) => { const e = []; for (let i = 0; i < a; i++) for (let j = 0; j < b; j++) e.push([i, a + j]); return e; };
/* Shapley value of a scarce-side vertex of K_{a,b}: average over the number s of predecessors, hypergeometric in r */
const LG = (() => { const t = [0]; for (let i = 1; i <= 900; i++) t.push(t[i - 1] + Math.log(i)); return t; })();
const lC = (n, k) => (k < 0 || k > n ? -Infinity : LG[n] - LG[k] - LG[n - k]);
function hyperShapley(a, b) {
  const n = a + b; let pA = 0, pB = 0;
  for (let s = 0; s < n; s++) for (let r = 0; r <= s; r++) {
    const k = s - r;
    const hA = Math.exp(lC(a - 1, r) + lC(b, k) - lC(n - 1, s)), hB = Math.exp(lC(a, r) + lC(b - 1, k) - lC(n - 1, s));
    if (hA > 0) pA += hA / n * (2 * Math.sqrt((r + 1) * k) - 2 * Math.sqrt(r * k));
    if (hB > 0) pB += hB / n * (2 * Math.sqrt(r * (k + 1)) - 2 * Math.sqrt(r * k));
  }
  return { pA, pB };
}
function typeMax(a, b, pA, pB) { let best = -Infinity, arg = null; for (let r = 0; r <= a; r++) for (let k = 0; k <= b; k++) { if (r === a && k === b) continue; const d = 2 * Math.sqrt(r * k) - r * pA - k * pB; if (d > best) { best = d; arg = [r, k]; } } return { best, arg }; }
/* the frozen closed form of the scarce-side payoff of K₂,ₘ (private lemma scarce_payoff) */
function frozenPayoff(m) { let S1 = 0, S3 = 0; for (let k = 0; k <= m; k++) { S1 += Math.sqrt(k); S3 += k * Math.sqrt(k); } const q = Math.SQRT2; return 2 * ((m + q) * S1 + (q - 2) * S3) / ((m + 1) * (m + 2)); }
const rel = (x, y) => Math.abs(x - y) / Math.max(1e-300, Math.abs(y));

/* ---------- load ---------- */
await page.goto(origin + BASE + 'viz/energy-game/');
await page.waitForFunction(() => window.EG_DEBUG && EG_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let st = await state(), i = await info();
check('opens on the frozen counterexample K₂,₅₀ (paused at b = 50)', st.preset === 'lean' && i.mode === 'bip' && i.a === 2 && i.b === 50 && st.playing === false);
const lo50 = 1380588425475056173 / 6630000000000000000, hi50 = 1380588425475064157 / 6630000000000000000;
check('the deficit of V∖{a} at m = 50 lies in the dossier’s exact interval (to 10⁻¹²)', i.row.dLean > lo50 - 1e-12 && i.row.dLean < hi50 + 1e-12, `${i.row.dLean}`);
check('the scarce-side payoff equals the frozen closed form 2((m + √2)S₁ + (√2 − 2)S₃)/((m + 1)(m + 2)) at m = 50', rel(i.row.pA, frozenPayoff(50)) < 1e-12, `${i.row.pA} ${frozenPayoff(50)}`);

/* ---------- complete bipartite tables ---------- */
const rowsOK = (x, picks) => picks.every((b) => { const r = x.rows[b - 1], h = hyperShapley(x.a, b), t = typeMax(x.a, b, h.pA, h.pB); return r.b === b && rel(r.pA, h.pA) < 1e-10 && rel(r.pB, h.pB) < 1e-10 && Math.abs(r.maxD - t.best) < 1e-10 && (t.best <= 1e-9 || (r.argR === t.arg[0] && r.argK === t.arg[1])); });
check('a = 2: every tabulated b ≤ 60 matches the hypergeometric Shapley values and the largest type deficit', rowsOK(i, Array.from({ length: 60 }, (_, j) => j + 1)));
check('a = 2: aφ_A + bφ_B = 2√(ab) (efficiency) for every b ≤ 60', i.rows.every((r) => Math.abs(2 * r.pA + r.b * r.pB - 2 * Math.sqrt(2 * r.b)) < 1e-10));
check('a = 2: the grid at b = 50 equals 2√(rk) − rφ_A − kφ_B for all 153 types', i.grid.length === 3 && i.grid.every((row, r) => row.length === 51 && row.every((d, k) => Math.abs(d - (2 * Math.sqrt(r * k) - r * i.row.pA - k * i.row.pB)) < 1e-12)));
check('a = 2: for b ≥ 50 the payoff exceeds 2(√2 − 1)√b and V∖{a} blocks, as frozen', i.rows.filter((r) => r.b >= 50).every((r) => r.pA > 2 * (Math.SQRT2 - 1) * Math.sqrt(r.b) && r.dLean > 0 && rel(r.pA, frozenPayoff(r.b)) < 1e-12));
const fLean = Array.from({ length: 60 }, (_, j) => j + 1).find((m) => frozenPayoff(m) - 2 * (Math.SQRT2 - 1) * Math.sqrt(m) > 1e-9);
check('the page’s first b where V∖{a} blocks (11) agrees with the closed form', i.firstLean === 11 && fLean === 11, `${i.firstLean} ${fLean}`);
check('the page’s first b where K₂,b leaves the core is 5, blocked by type (1, 3)', i.firstAny === 5 && i.rows[4].argR === 1 && i.rows[4].argK === 3 && i.rows[3].maxD <= 1e-9);
await preset('sweep'); await setFrac(1); i = await info();
check('a = 2, b ≤ 400: tabulated values match at b = 100, 250, 400 and the largest deficit is positive for every b ≥ 5', rowsOK(i, [100, 250, 400]) && i.rows.every((r) => (r.b >= 5) === (r.maxD > 1e-9)), `${i.rows[399].maxD}`);
const slope = i.rows[399].dLean / Math.sqrt(400);
check('V∖{a}’s deficit divided by √b keeps rising towards (26 − 18√2)/15 without reaching it', Math.abs(i.coef - (26 - 18 * Math.SQRT2) / 15) < 1e-15 && slope < i.coef && slope > 0.03 && i.rows.slice(20).every((r, j, arr) => j === 0 || r.dLean / Math.sqrt(r.b) > arr[j - 1].dLean / Math.sqrt(arr[j - 1].b)), `${slope}`);
await preset('star'); await setFrac(1); i = await info();
check('stars K₁,b: the page finds no blocking coalition for b ≤ 400, and neither does the hypergeometric check at b = 7, 50, 400', i.a === 1 && i.firstAny === null && [7, 50, 400].every((b) => { const h = hyperShapley(1, b); return typeMax(1, b, h.pA, h.pB).best <= 1e-9; }) && rowsOK(i, [7, 50, 400]));
for (const a of [3, 4]) {
  await click(`#aChips [data-a="${a}"]`); await click('#bChips [data-bmax="60"]'); i = await info();
  const first = Array.from({ length: 60 }, (_, j) => j + 1).find((b) => { const h = hyperShapley(a, b); return typeMax(a, b, h.pA, h.pB).best > 1e-9; });
  check(`a = ${a}: the tabulated first b outside the core (${i.firstAny}) agrees with the hypergeometric check`, i.a === a && i.firstAny === first && rowsOK(i, [1, first, 60]), `${first}`);
}

/* ---------- small graphs: every coalition ---------- */
const P3 = bruteGame(3, [[0, 1], [1, 2]]);
check('P₃ (Example 3.9): the independent Shapley value is ((2√2 − 1)/3, (2 + 2√2)/3, (2√2 − 1)/3)', Math.abs(P3.phi[1] - (2 + 2 * Math.SQRT2) / 3) < 1e-12 && Math.abs(P3.phi[0] - (2 * Math.SQRT2 - 1) / 3) < 1e-12);
const graphCases = { P3: [3, [[0, 1], [1, 2]]], K24: [6, bipE(2, 4)], K25: [7, bipE(2, 5)], K34: [7, bipE(3, 4)], C6: [6, [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]]],
  petersen: [10, [[0, 1], [1, 2], [2, 3], [3, 4], [4, 0], [0, 5], [1, 6], [2, 7], [3, 8], [4, 9], [5, 7], [7, 9], [9, 6], [6, 8], [8, 5]]] };
const brute = {};
await click('#modeChips [data-mode="graph"]');
for (const [g, [n, e]] of Object.entries(graphCases)) {
  await click(`#gChips [data-g="${g}"]`);
  await setFrac(1); const x = await info(), B = bruteGame(n, e); brute[g] = { x, B };
  const okW = x.w.every((v, S) => Math.abs(v - B.w[S]) < 1e-9), okPhi = x.phi.every((p, k) => Math.abs(p - B.phi[k]) < 1e-9);
  const okD = x.order.every((S, j) => Math.abs(x.D[j] - (B.w[S] - bits(S, n).reduce((t, k) => t + B.phi[k], 0))) < 1e-9);
  check(`${g}: all ${1 << n} coalition energies, the Shapley value and every deficit match the independent enumeration`, x.g === g && x.N === 1 << n && okW && okPhi && okD && x.count === x.N);
}
const bK25 = brute.K25, bK34 = brute.K34;
check('K₂,₄ stays in the core and K₂,₅ leaves it: the independent largest deficit is ≤ 10⁻⁹ and ≈ 0.0241 by {a, three others}', brute.K24.B.best <= 1e-9 && Math.abs(bK25.B.best - 0.0241) < 5e-5 && bits(bK25.B.arg, 7).filter((k) => k < 2).length === 1 && bits(bK25.B.arg, 7).length === 4 && Math.abs(bK25.x.D[bK25.x.bestJ] - bK25.B.best) < 1e-9, `${bK25.B.best}`);
check('K₃,₄ leaves the core with a deficit ≈ 0.0021 from 2 + 3 vertices', Math.abs(bK34.B.best - 0.00206) < 2e-5 && bits(bK34.B.arg, 7).filter((k) => k < 3).length === 2 && bits(bK34.B.arg, 7).length === 5, `${bK34.B.best}`);
check('C₆, the Petersen graph and P₃ stay in the core', ['C6', 'petersen', 'P3'].every((g) => brute[g].B.best <= 1e-9 && brute[g].x.D[brute[g].x.bestJ] <= 1e-9));
check('the vertex energies sum to the energy and satisfy every coalition inequality (Theorem 3.6) on every graph tested', Object.values(brute).every(({ x, B }) => Math.abs(x.ve.reduce((s, v) => s + v, 0) - B.w[x.N - 1]) < 1e-9 && x.order.every((S) => B.w[S] - bits(S, x.n).reduce((t, k) => t + x.ve[k], 0) <= 1e-9)));
/* every labelled graph on at most 6 vertices: energies memoized by induced subgraph */
const memo = new Map();
const subKey = (adjBits, idx) => { let key = idx.length; for (let p = 0; p < idx.length; p++) for (let q = p + 1; q < idx.length; q++) key = key * 2 + (adjBits[idx[p]] >> idx[q] & 1); return key; };
let bad = 0, graphs = 0;
for (let n = 1; n <= 6; n++) {
  const pairs = []; for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) pairs.push([p, q]);
  for (let m = 0; m < 1 << pairs.length; m++) {
    graphs++;
    const adjBits = new Array(n).fill(0); pairs.forEach(([p, q], t) => { if (m >> t & 1) { adjBits[p] |= 1 << q; adjBits[q] |= 1 << p; } });
    const N = 1 << n, w = new Float64Array(N);
    for (let S = 1; S < N; S++) { const idx = bits(S, n), key = subKey(adjBits, idx); if (!memo.has(key)) memo.set(key, energyOf(idx.map((p) => idx.map((q) => adjBits[p] >> q & 1)))); w[S] = memo.get(key); }
    const fac = [1, 1, 2, 6, 24, 120, 720], phi = new Array(n).fill(0);
    for (let v = 0; v < n; v++) for (let S = 0; S < N; S++) if (!(S >> v & 1)) { const s = bits(S, n).length; phi[v] += fac[s] * fac[n - s - 1] / fac[n] * (w[S | 1 << v] - w[S]); }
    for (let S = 1; S < N; S++) if (w[S] - bits(S, n).reduce((t, v) => t + phi[v], 0) > 1e-9) { bad++; break; }
  }
}
check('every labelled graph on at most 6 vertices keeps its Shapley value in the core (tolerance 10⁻⁹), as the drawer says', bad === 0 && graphs === 1 + 2 + 8 + 64 + 1024 + 32768, `${graphs} graphs, ${bad} outside`);

/* ---------- presets, controls, timeline ---------- */
for (const p of ['lean', 'sweep', 'k25', 'k34', 'star', 'p3']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
await preset('k25');
check('graph mode shows the graph chips and hides the a and b chips', await visible('gChips') && !(await visible('aChips')) && !(await visible('bChips')));
await click('#modeChips [data-mode="bip"]');
check('bipartite mode shows the a and b chips and hides the graph chips', !(await visible('gChips')) && await visible('aChips') && await visible('bChips'));
check('custom settings are marked', (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await preset('k25'); await setFrac(0.95); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing a small graph to the end reports the verdict over all coalitions', await waitToast(/128 个联盟核对完.*离开核/));
await pause();
await preset('sweep'); await setFrac(0.97); await click('#play');
check('playing the sweep to the end reports the deficits at b = 400', await waitToast(/b = 400.*最大赤字/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
await preset('lean'); const b0 = (await info()).b;
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps b by one', (await info()).b === b0 + 1);
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await info()).b === 60 && (await state()).playing === false);
check('the rail marks b = 1, the Lean bound and the end (the mark at b = 5 is too close to the start on this scale)', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 'b = 1 | LEAN 50 | b = 60');
check('the readouts state the frozen comparison and efficiency (aφ_A + bφ_B = w(V) to six decimals)', /> 2\(√2 − 1\)√b/.test(await text('ro4')) && (await text('ro5')).split(' · ')[0] === (await text('ro5')).split(' · ')[1], await text('ro5'));
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 2000), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'k34']) {
  await preset(p); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#gChips [data-g="C6"]');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('ENERGY//GAME · The graph energy game: the Shapley value leaves the core'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['Problems/aa2012.md', 'ArizmendiEnergyGameShapleyRefutation.lean', 'Blueprint/D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.md', 'arizmendi2020energygame.md', '10.1016/j.dam.2023.01.030', 'arxiv.org/abs/2012.14114'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="energy-game"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.EG_DEBUG && EG_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'energy-game');

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
