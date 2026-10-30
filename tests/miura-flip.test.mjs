#!/usr/bin/env node
// Browser regression suite for viz/miura-flip (Playwright + Chromium with software WebGL).
//   node tests/miura-flip.test.mjs
// Reads page state through the read-only window.MF_DEBUG probe and checks it against an independent implementation: the
// dispersion as a minimum over every integer centre (the page takes a median), D(m, n) summed over the grid and compared with
// (m³ − m)/3, height functions and strict extrema read from the grid neighbours, the number of proper 3-colourings by a
// transfer matrix over rows, the whole flip graph of a small grid with all-pairs breadth-first search, a step-by-step check
// that every path move flips one strict extremum by 2, and the ramp i + j. Fixed reference data come from the dossier: the
// 1-Lipschitz counts 22979 (3 × 4) and 31307 (2 × 6).
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
  const start = await page.evaluate(() => MF_DEBUG.frames());
  await page.waitForFunction((f0) => !MF_DEBUG.pending() && MF_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => MF_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => MF_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => MF_DEBUG.info());
const state = () => D(() => MF_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const slide = async (id, v) => { await D(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input')); }, [id, v]); await settle(); };
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => MF_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => MF_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};
const clickCell = async (k) => { const p = await D((k) => MF_DEBUG.cellScreen(k), k); await page.mouse.click(p.x, p.y); await settle(); };

/* ---------- independent arithmetic ---------- */
const nb = (m, n, k) => { const i = Math.floor(k / n), j = k % n, r = []; if (i > 0) r.push(k - n); if (i < m - 1) r.push(k + n); if (j > 0) r.push(k - 1); if (j < n - 1) r.push(k + 1); return r; };
const dispAll = (f) => { let best = Infinity; for (let K = Math.min(...f) - 1; K <= Math.max(...f) + 1; K++) best = Math.min(best, f.reduce((t, x) => t + Math.abs(x - K), 0)); return best; };
const Dind = (m, n) => { let best = Infinity; for (let K = 0; K <= m + n + 2; K++) { let s = 0; for (let i = 1; i <= m; i++) for (let j = 1; j <= n; j++) s += Math.abs(i + j - K); best = Math.min(best, s); } return best; };
const lipOK = (m, n, f) => f.every((x, k) => nb(m, n, k).every((u) => Math.abs(f[u] - x) <= 1));
const heightOK = (m, n, f) => f.every((x, k) => nb(m, n, k).every((u) => Math.abs(f[u] - x) === 1));
const isMin = (m, n, h, k) => nb(m, n, k).every((u) => h[u] > h[k]), isMax = (m, n, h, k) => nb(m, n, k).every((u) => h[u] < h[k]);
function colourings(m, n) {   // proper 3-colourings of the m × n grid by a transfer matrix over rows
  const rows = []; const rec = (r) => { if (r.length === n) { rows.push(r.slice()); return; } for (let c = 0; c < 3; c++) if (!r.length || r[r.length - 1] !== c) { r.push(c); rec(r); r.pop(); } }; rec([]);
  let v = rows.map(() => 1);
  for (let i = 1; i < m; i++) v = rows.map((r) => rows.reduce((t, s, si) => t + (r.every((c, j) => c !== s[j]) ? v[si] : 0), 0));
  return v.reduce((t, x) => t + x, 0);
}
function bfsGraph(m, n) {   // every height function with h(0) = 0, flips, all-pairs breadth-first search
  const S = []; const h = new Array(m * n).fill(0);
  const rec = (k) => { if (k === m * n) { if (heightOK(m, n, h)) S.push(h.slice()); return; } if (k === 0) { h[0] = 0; rec(1); return; } const p = k % n ? h[k - 1] : h[k - n]; for (const v of [p - 1, p + 1]) { h[k] = v; if (k >= n && Math.abs(h[k - n] - v) !== 1) continue; rec(k + 1); } };
  rec(0);
  const key = (g) => { const c = g[0]; return g.map((x) => x - c).join('|'); }, idx = new Map(S.map((g, i) => [key(g), i]));
  const adj = S.map((g) => { const r = []; for (let k = 0; k < m * n; k++) { const s = isMin(m, n, g, k) ? 2 : isMax(m, n, g, k) ? -2 : 0; if (s) { const q = g.slice(); q[k] += s; r.push(idx.get(key(q))); } } return r; });
  let dia = 0; for (let s = 0; s < S.length; s++) { const d = new Map([[s, 0]]), q = [s]; for (let i = 0; i < q.length; i++) for (const w of adj[q[i]]) if (!d.has(w)) { d.set(w, d.get(q[i]) + 1); q.push(w); } for (const x of d.values()) dia = Math.max(dia, x); }
  const degrees = {}; adj.forEach((a) => { degrees[a.length] = (degrees[a.length] || 0) + 1; });
  return { states: S.length, diameter: dia, degrees };
}
function legalPath(m, n, path) {   // each step changes exactly one strict extremum by 2 in the right direction
  for (let t = 1; t < path.length; t++) { const a = path[t - 1], b = path[t], diff = a.map((x, k) => b[k] - x).map((x, k) => [x, k]).filter(([x]) => x !== 0); if (diff.length !== 1) return false; const [[dx, k]] = diff; if (!((dx === 2 && isMin(m, n, a, k)) || (dx === -2 && isMax(m, n, a, k)))) return false; if (!heightOK(m, n, b)) return false; }
  return true;
}
const rampInd = (m, n) => Array.from({ length: m * n }, (_, k) => Math.floor(k / n) + (k % n));
const eqArr = (a, b) => !!a && !!b && a.length === b.length && a.every((x, i) => x === b[i]);

await page.goto(origin + BASE + 'viz/miura-flip/');
await page.waitForFunction(() => window.MF_DEBUG && MF_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle(); await pause();
let i = await info();

/* ---------- the flip path ---------- */
check('the page opens on the 6 × 6 flip path from −A to A', i.mode === 'walk' && i.m === 6 && i.n === 6 && eqArr(i.source, rampInd(6, 6).map((x) => -x)) && eqArr(i.target, rampInd(6, 6)) && (await state()).preset === 'geo');
check('D(6, 6) = 70 from the definition and from (m³ − m)/3', i.D === 70 && Dind(6, 6) === 70 && (6 ** 3 - 6) / 3 === 70);
check('…the path has 70 steps, every step a legal flip of a strict extremum, every state a height function, ending at A (states differing by a constant are one state)', i.T === 70 && i.path.length === 71 && legalPath(6, 6, i.path) && eqArr(i.path[70].map((x) => x - i.path[70][0]), rampInd(6, 6)) && !i.stuck);
check('…70 is a lower bound for any path from −A to A: disp((−A − A)/2) = disp(A) = 70 and one flip moves the dispersion by at most 1', dispAll(rampInd(6, 6).map((x) => -x).map((x, k) => (x - rampInd(6, 6)[k]) / 2)) === 70);
await setFrac(32 / 70); i = await info();
const mins = [], maxs = []; for (let k = 0; k < 36; k++) { if (isMin(6, 6, i.h, k)) mins.push(k); if (isMax(6, 6, i.h, k)) maxs.push(k); }
check('at step 32 the distance to A is 38 and the page’s strict minima and maxima are the independent ones', i.t === 32 && i.dist === 38 && dispAll(i.h.map((x, k) => (x - i.target[k]) / 2)) === 38 && eqArr(i.minima, mins) && eqArr(i.maxima, maxs));
check('…the readouts show a, b and the degree d = a + b', (await text('ro3')) === `${mins.length} · ${maxs.length} · ${mins.length + maxs.length}`);
await preset('small'); i = await info();
const g44 = bfsGraph(4, 4);
check('4 × 4: 2604 states, equal to the proper 3-colourings / 3 (transfer matrix: 7812)', i.graph.states === 2604 && colourings(4, 4) === 7812 && g44.states === 2604);
check('…the page’s BFS diameter is 20 = D(4, 4), and the independent BFS agrees', i.graph.diameter === 20 && g44.diameter === 20 && Dind(4, 4) === 20);
check('…every one of the 2604² pairs is at flip distance disp((h₁ − h₂)/2) on the page', i.graph.mismatch === 0 && i.graph.pairs === 2604 * 2604);
check('…the degree histogram matches the independent graph (two checkerboards of degree 16)', JSON.stringify(i.graph.degrees) === JSON.stringify(g44.degrees) && i.graph.degrees['16'] === 2);
check('…the 20-step path from −A to A is legal', i.T === 20 && legalPath(4, 4, i.path));
const more = [];
for (const [m, n] of [[3, 3], [2, 5], [3, 5], [2, 7]]) {
  await slide('mm', String(m)); await slide('nn', String(n)); i = await info();
  const ind = m * n <= 12 ? bfsGraph(m, n) : null;
  more.push(i.m === m && i.n === n && i.graph && i.graph.states === colourings(m, n) / 3 && i.graph.diameter === Dind(m, n) && i.graph.mismatch === 0 && (!ind || ind.diameter === i.graph.diameter) && i.T === Dind(m, n) && legalPath(m, n, i.path));
}
check('3 × 3, 2 × 5, 3 × 5, 2 × 7: states = colourings / 3, BFS diameter = D(m, n), all pairs follow the distance formula, and the path from −A has D steps', more.every(Boolean), more.map((x) => (x ? 1 : 0)).join(''));
check('D(2, n) = ⌈n²/2⌉ for the page’s 2 × 5 and 2 × 7, D(m, m) = (m³ − m)/3 for 3 × 3', Dind(2, 5) === Math.ceil(25 / 2) && Dind(2, 7) === Math.ceil(49 / 2) && Dind(3, 3) === 8);
await slide('mm', '9'); await slide('nn', '9'); i = await info();
check('9 × 9 is too large to enumerate; the path from −A still has D(9, 9) = 240 legal steps', i.graph === null && i.D === 240 && Dind(9, 9) === 240 && i.T === 240 && legalPath(9, 9, i.path) && (await state()).preset === null);
await preset('wander'); i = await info();
check('a random 7 × 5 height function walks to A in disp((h − A)/2) legal steps, fewer than D(7, 5)', heightOK(7, 5, i.source) && i.T === dispAll(i.source.map((x, k) => (x - i.target[k]) / 2)) && i.T < i.D && legalPath(7, 5, i.path));
const before = i.source; await setFrac(0); i = await info();
const flip = i.minima[0] !== undefined ? i.minima[0] : i.maxima[0];
await clickCell(flip); i = await info();
check('clicking an extremal cell flips it: the new start differs there by 2 and the path restarts', i.source[flip] - before[flip] === (before[flip] < i.source[flip] ? 2 : -2) && i.source.filter((x, k) => x !== before[k]).length === 1 && i.t === 0 && (await state()).preset === null);
const notExt = i.source.findIndex((_, k) => !isMin(7, 5, i.source, k) && !isMax(7, 5, i.source, k));
await clickCell(notExt);
check('clicking a cell that is not an extremum is refused with a toast', await waitToast(/不是严格局部极值/));
await preset('extrema'); i = await info();
check('the 8 × 8 checkerboard: every one of the 64 cells is a strict extremum (32 + 32), so the degree is 64', i.minima.length === 32 && i.maxima.length === 32 && i.minima.every((k) => isMin(8, 8, i.h, k)) && /32 · 32 · 64/.test(await text('ro3')));
check('…its minima share no side, as the readout says', i.sides.length === 0 && /不全在同一条边上/.test(await text('ro4')));
await click('#toolChips [data-fn="random"]'); await click('#toolChips [data-fn="ramp"]'); await slide('mm', '2'); await slide('nn', '4'); await setFrac(0); i = await info();
check('2 × 4 from −A: the minima of the start lie on one side, which the readout names', i.minima.length > 0 && i.sides.length > 0 && (await text('ro4')).length > 0 && i.sides.every((sd) => ['top', 'bottom', 'left', 'right'].includes(sd)));

/* ---------- dispersion ---------- */
await preset('ramp'); i = await info();
check('the ramp on 6 × 6: dispersion 70 = D(6, 6) with best centre 5 (independent: every integer centre tried)', i.disp === 70 && dispAll(i.f) === 70 && i.bestK === 5 && eqArr(i.f, rampInd(6, 6)) && /取到上界/.test(await text('ro5')));
const costs = []; for (let K = Math.min(...i.f) - 1; K <= Math.max(...i.f) + 1; K++) costs.push(K);
let costOK = true; for (const K of costs) { await setFrac((K - (Math.min(...i.f) - 1)) / (Math.max(...i.f) - Math.min(...i.f) + 2)); const j = await info(); if (j.K !== K || j.cost !== i.f.reduce((t, x) => t + Math.abs(x - K), 0)) costOK = false; }
check('the time axis sweeps every integer centre K, with Σ|φ − K| matching', costOK);
await preset('lip'); i = await info();
check('a random 1-Lipschitz function: 1-Lipschitz, with zero differences, dispersion (independent) below D', lipOK(6, 6, i.f) && !heightOK(6, 6, i.f) && i.disp === dispAll(i.f) && i.disp < 70 && i.lip);
check('disp mode shows the size sliders and the +1 / −1 tools', (await visible('upChip')) && (await visible('downChip')) && (await visible('flatChip')));
const k0 = i.f.findIndex((x, k) => lipOK(6, 6, i.f.map((y, j) => (j === k ? y + 1 : y))));
await clickCell(k0); const i2 = await info();
check('clicking with +1 raises a cell when the result stays 1-Lipschitz, and the dispersion is recomputed', i2.f[k0] === i.f[k0] + 1 && i2.disp === dispAll(i2.f) && (await state()).preset === null);
await click('#downChip'); const kBad = i2.f.findIndex((x, k) => !lipOK(6, 6, i2.f.map((y, j) => (j === k ? y - 1 : y))));
await clickCell(kBad);
check('a change that would break the 1-Lipschitz condition is refused with a toast and the function stays', (await waitToast(/超过 1/)) && eqArr((await info()).f, i2.f));
await click('#toolChips [data-fn="flat"]'); i = await info();
check('the flat function has dispersion 0', i.disp === 0 && i.f.every((x) => x === 0));
await slide('mm', '3'); await slide('nn', '4'); i = await info();
check('3 × 4: the page enumerates all 22979 1-Lipschitz functions (dossier table) and the largest dispersion is 14 = D(3, 4)', i.lipMax && i.lipMax.count === 22979 && i.lipMax.best === 14 && Dind(3, 4) === 14);
await slide('mm', '2'); await slide('nn', '6'); i = await info();
check('2 × 6: 31307 functions and the largest dispersion 18 = D(2, 6) = ⌈36/2⌉, as in the dossier', i.lipMax && i.lipMax.count === 31307 && i.lipMax.best === 18 && Dind(2, 6) === 18);

/* ---------- rearrangement ---------- */
await preset('sortL'); i = await info();
const [f0, R, F, A] = i.stages;
const sortRowsInd = (m, n, f) => { const r = []; for (let a = 0; a < m; a++) r.push(...f.slice(a * n, a * n + n).sort((x, y) => x - y)); return r; };
const sortColsInd = (m, n, f) => { const r = f.slice(); for (let j = 0; j < n; j++) { const c = []; for (let a = 0; a < m; a++) c.push(f[a * n + j]); c.sort((x, y) => x - y); c.forEach((v, a) => { r[a * n + j] = v; }); } return r; };
check('the stages are φ, the rows sorted, then the columns sorted, then the ramp', eqArr(R, sortRowsInd(6, 6, f0)) && eqArr(F, sortColsInd(6, 6, R)) && dispAll(A) === 70);
check('…F is increasing along rows and columns and still 1-Lipschitz; the dispersion is unchanged throughout', F.every((x, k) => (k % 6 === 5 || F[k + 1] >= x) && (k >= 30 || F[k + 6] >= x)) && lipOK(6, 6, F) && lipOK(6, 6, R) && dispAll(f0) === dispAll(R) && dispAll(R) === dispAll(F) && dispAll(F) <= 70);
const st = []; for (const f of [0, 1 / 3, 2 / 3, 1]) { await setFrac(f); st.push((await info()).stage); }
check('the stage readout follows the rail: 0, 1, 2, 3 at the four marks', JSON.stringify(st) === '[0,1,2,3]');
await preset('sortH'); i = await info();
check('sorting a height function gives neighbouring differences 0 or 1: no longer a height function, still 1-Lipschitz', heightOK(6, 6, i.stages[0]) && !heightOK(6, 6, i.stages[2]) && lipOK(6, 6, i.stages[2]) && /不再是高度函数/.test(await text('roNote')));

/* ---------- play, keys and toasts ---------- */
await preset('geo'); await setFrac(0.985); await click('#play');
check('the path toast reports 70 steps, exactly D(6, 6)', await waitToast(/70 步，正好是 D\(6, 6\)/));
await pause();
await preset('lip'); await setFrac(0.985); await click('#play');
check('the dispersion toast reports the smallest cost and D', await waitToast(/D = 70/));
await pause();
await preset('sortL'); await setFrac(0.985); await click('#play');
check('the rearrangement toast reports disp(F) ≤ D', await waitToast(/disp\(F\) = \d+ ≤ D = 70/));
await pause();
await preset('geo'); await setFrac(0.2); await click('#play'); await waitFrames(12); const t1 = (await state()).nowFrac; await pause();
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
check('E jumps to the end of the path and pauses', (await info()).t === 70 && (await state()).playing === false);
await setFrac(10 / 70); await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps one flip', (await info()).t === 11);
await click('#modeChips [data-mode="disp"]');

/* ---------- language ---------- */

await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
for (const m of ['walk', 'disp', 'sort']) {
  await click(`#modeChips [data-mode="${m}"]`); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${m}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('MIURA//FLIP · Height functions on the Miura-ori flip graph'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links both dossiers, both Lean files and the four papers', (await D(() => { const h = [...document.querySelectorAll('#drawer .en a')].map((a) => a.href).join(' '); return ['gupta-2026-miura-grid-dispersion-inequality-4.md', 'gupta-2026-miura-residual-degree-conjecture-83.md', 'GuptaMiuraGridDispersion.lean', 'MiuraResolution.lean', 'arxiv.org/abs/2606.22614', 'arxiv.org/abs/2607.05567', 'arxiv.org/abs/2506.19700', '10.1007/BF01651330'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="miura-flip"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.MF_DEBUG && MF_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'miura-flip');

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
