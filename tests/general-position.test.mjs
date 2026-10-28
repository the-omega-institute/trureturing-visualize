#!/usr/bin/env node
// Browser regression suite for viz/general-position (Playwright + Chromium with software WebGL).
//   node tests/general-position.test.mjs
// Reads page state through the read-only window.GP_DEBUG probe and checks it against an independent implementation: the
// cylinder distance as a formula (the page runs breadth-first search), general position over all ordered triples, every
// 5-subset of the cylinder filtered by general position, a separate breadth-first search over robot moves, ψ(G) by
// enumerating subsets with Floyd–Warshall distances, and the outer general position number by brute force over all subsets.
// Fixed reference data come from the Lean modules and dossiers: the first route pattern, the route length, the counts
// 2r·C(s, 5) of five-vertex sets, ψ(P₃) = 1 + 3x + 3x², the edge lists and the five-colouring of the 19-vertex graph.
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
  const start = await page.evaluate(() => GP_DEBUG.frames());
  await page.waitForFunction((f0) => !GP_DEBUG.pending() && GP_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => GP_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => GP_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => GP_DEBUG.info());
const state = () => D(() => GP_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const slide = async (id, v) => { await D(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input')); }, [id, v]); await settle(); };
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => GP_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => GP_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
// cylinder distance written as a formula (the page runs breadth-first search); general position over all ordered triples;
// a brute-force enumeration of five-vertex sets over every 5-subset; a separate breadth-first search over robot moves;
// ψ by enumerating subsets with Floyd–Warshall distances; the outer number by brute force over all subsets
const cylD = (r) => (u, v) => { const dx = Math.abs((u % r) - (v % r)), d = Math.min(dx, r - dx); return d + Math.abs(Math.floor(u / r) - Math.floor(v / r)); };
const gpBy = (d, S) => S.every((a, i) => S.every((b, j) => S.every((c, k) => i === j || j === k || i === k || d(a, b) + d(b, c) !== d(a, c))));
const routeLen = (r, s) => 4 * r * (s - 1) + 4 * Math.max(0, s - 2);
function checkRoute(r, s, route) {
  const d = cylD(r), seen = new Set(); let ok = route.length === routeLen(r, s) + 1;
  route.forEach((c, t) => { c.forEach((v) => seen.add(v)); if (new Set(c).size !== 4 || !gpBy(d, c)) ok = false;
    if (t) { const p = route[t - 1], diff = c.map((v, i) => [v, p[i]]).filter(([a, b]) => a !== b); if (diff.length !== 1 || d(diff[0][0], diff[0][1]) !== 1 || p.includes(diff[0][0])) ok = false; } });
  return ok && seen.size === r * s;
}
function fiveSets(r, s) {   // every 5-subset of the r·s vertices, filtered by general position
  const d = cylD(r), n = r * s, out = [];
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) for (let c = b + 1; c < n; c++) { if (!gpBy(d, [a, b, c])) continue; for (let e = c + 1; e < n; e++) { if (!gpBy(d, [a, b, c, e])) continue; for (let f = e + 1; f < n; f++) if (gpBy(d, [a, b, c, e, f])) out.push([a, b, c, e, f]); } }
  return out;
}
function reachInd(r, s, start) {
  const d = cylD(r), key = (S) => S.slice().sort((a, b) => a - b).join(','), seen = new Set([key(start)]), q = [start], vis = new Set(start); let moves = 0, side = 0;
  while (q.length) { const S = q.shift(); for (let i = 0; i < 5; i++) for (let v = 0; v < r * s; v++) { if (d(S[i], v) !== 1 || S.includes(v)) continue; const T = S.slice(); T[i] = v; if (!gpBy(d, T)) continue; moves++; if (Math.floor(v / r) === Math.floor(S[i] / r)) side++; const k = key(T); if (!seen.has(k)) { seen.add(k); q.push(T); T.forEach((w) => vis.add(w)); } } }
  return { configs: [...seen].sort(), moves, side, cols: [...new Set([...vis].map((v) => v % r))].sort((a, b) => a - b) };
}
const C = (n, k) => { let c = 1; for (let i = 0; i < k; i++) c = c * (n - i) / (i + 1); return Math.round(c); };
function floyd(n, edges) { const D = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 0 : 1e9))); for (const [a, b] of edges) D[a][b] = D[b][a] = 1; for (let k = 0; k < n; k++) for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (D[i][k] + D[k][j] < D[i][j]) D[i][j] = D[i][k] + D[k][j]; return D; }
function psiInd(n, edges) { const D = floyd(n, edges), d = (a, b) => D[a][b], a = new Array(n + 1).fill(0); for (let m = 0; m < (1 << n); m++) { const S = []; for (let i = 0; i < n; i++) if ((m >> i) & 1) S.push(i); if (gpBy(d, S)) a[S.length]++; } while (a.length > 1 && a[a.length - 1] === 0) a.pop(); return a; }
const polyAt = (a, [x, y]) => { let re = 0, im = 0; for (let k = a.length - 1; k >= 0; k--) [re, im] = [re * x - im * y + a[k], re * y + im * x]; return Math.hypot(re, im); };
const EH = [[0, 8], [0, 17], [1, 8], [1, 17], [2, 8], [2, 17], [3, 8], [3, 17], [4, 12], [4, 13], [5, 12], [5, 13], [6, 12], [6, 13], [7, 12], [7, 13], [8, 9], [9, 10], [10, 11], [11, 12], [13, 14], [14, 15], [15, 16], [16, 17]], EG = EH.concat([[8, 18], [13, 18]]);
const COLOR = [0, 1, 2, 3, 0, 1, 2, 3, 0, 4, 0, 0, 1, 0, 4, 1, 1, 0, 2];   // the Lean module's colouring
const blocks = (D, u, w) => { for (let v = 0; v < D.length; v++) if (v !== u && v !== w && (D[u][w] + D[w][v] === D[u][v] || D[w][u] + D[u][v] === D[w][v])) return v; return -1; };
function outerInd(n, edges) { const D = floyd(n, edges), cm = Array.from({ length: n }, (_, u) => { let m = 0; for (let w = 0; w < n; w++) if (w !== u && blocks(D, u, w) >= 0) m |= 1 << w; return m; }); let best = 0; for (let m = 0; m < (1 << n); m++) { let ok = true; for (let i = 0; i < n && ok; i++) if ((m >> i) & 1 && (m & cm[i])) ok = false; if (ok) { let c = 0, x = m; while (x) { c += x & 1; x >>>= 1; } best = Math.max(best, c); } } return { D, best }; }
const sameSet = (a, b) => JSON.stringify(a.map((x) => x.slice().sort((p, q) => p - q).join(',')).sort()) === JSON.stringify(b.map((x) => x.slice().sort((p, q) => p - q).join(',')).sort());

await page.goto(origin + BASE + 'viz/general-position/');
await page.waitForFunction(() => window.GP_DEBUG && GP_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle(); await pause();
let i = await info();

/* ---------- four robots ---------- */
check('the page opens on four robots on C₇ □ P₅, a route of 4r(s − 1) + 4(s − 2) = 124 moves', i.mode === 'robots' && i.k === 4 && i.r === 7 && i.s === 5 && i.T === 124 && (await D(() => document.querySelector('.preset[aria-pressed="true"]').dataset.preset)) === 'cyl7');
check('…the route starts in the Lean pattern: columns 0, 4, 1, 5 in rows 0, 0, 1, 1', JSON.stringify(i.route[0]) === JSON.stringify([0, 4, 7 + 1, 7 + 5]));
check('…every configuration is in general position (distance formula), every move takes one robot along an edge to an empty vertex, and all 35 vertices are visited', checkRoute(7, 5, i.route));
check('…the page’s own legality and general-position flags agree', i.legal.every((x) => x >= 0) && i.gp.every(Boolean));
await setFrac(1); i = await info();
check('…at the end the readouts show 35 / 35 and the frozen verdict', i.visited === 35 && /35 \/ 35/.test(await text('ro3')) && /冻结定理/.test(await text('ro5')));
await setFrac(0.5); i = await info();
check('…halfway, the visited count equals the number of distinct vertices on the route so far', i.visited === new Set(i.route.slice(0, i.t + 1).flat()).size);
await preset('cyl10'); i = await info();
check('C₁₀ □ P₆: 216 moves, legal, in general position throughout, covering all 60 vertices', i.r === 10 && i.s === 6 && i.T === 216 && checkRoute(10, 6, i.route));
let allRoutes = true;
for (const [r, s] of [[7, 2], [7, 8], [10, 2], [10, 8]]) { await click(`#rChips [data-r="${r}"]`); await slide('ss', s); const j = await info(); if (!(j.r === r && j.s === s && checkRoute(r, s, j.route))) allRoutes = false; }
check('the route is legal and covering for r = 7, 10 and s = 2, 8 (the Lean construction works for every s ≥ 2)', allRoutes && (await state()).preset === null);

/* ---------- five robots ---------- */
await preset('five'); i = await info();
const f76 = fiveSets(7, 6);
check('five robots on C₇ □ P₆: the page counts 84 five-vertex general position sets, as the brute force over all 5-subsets does, = 2·7·C(6, 5)', i.k === 5 && i.five.count === 84 && f76.length === 84 && 2 * 7 * C(6, 5) === 84);
check('…none of them extends to six vertices (independent check of every extension)', i.five.extend === 0 && f76.every((S) => Array.from({ length: 42 }, (_, v) => v).every((v) => S.includes(v) || !gpBy(cylD(7), S.concat([v])))));
check('…every set is one of the arithmetic progressions b ± 2i in five distinct rows (the rigidity in the Lean proof)', f76.every((S) => { const rows = S.map((v) => Math.floor(v / 7)); if (new Set(rows).size !== 5) return false; const o = S.slice().sort((a, b) => Math.floor(a / 7) - Math.floor(b / 7)).map((v) => v % 7); const st = (o[1] - o[0] + 7) % 7; return (st === 2 || st === 5) && o.every((c, k) => k === 0 || (c - o[k - 1] + 7) % 7 === st); }));
const r76 = reachInd(7, 6, i.configs[0]);
check('…from the start 0, 2, 4, 6, 1 the reachable configurations, legal moves and columns equal an independent search: 6, 10, none sideways, columns 0 1 2 4 6', JSON.stringify(i.configs[0]) === JSON.stringify([0, 7 + 2, 14 + 4, 21 + 6, 28 + 1]) && sameSet(i.configs, r76.configs.map((k) => k.split(',').map(Number))) && i.moves === 10 && r76.moves === 10 && i.sideways === 0 && r76.side === 0);
await setFrac(1); i = await info();
check('…at the end only columns 0 1 2 4 6 have been reached, and the verdict says the frozen theorem', JSON.stringify(i.cols) === JSON.stringify([0, 1, 2, 4, 6]) && JSON.stringify(r76.cols) === JSON.stringify([0, 1, 2, 4, 6]) && /冻结定理/.test(await text('ro5')));
await preset('tall'); i = await info();
const r108 = reachInd(10, 8, i.configs[0]);
check('C₁₀ □ P₈: 1120 = 2·10·C(8, 5) sets, none extendable; 56 reachable configurations, only vertical moves, five of ten columns', i.five.count === 1120 && i.five.extend === 0 && i.configs.length === 56 && r108.configs.length === 56 && i.sideways === 0 && r108.side === 0 && JSON.stringify(r108.cols) === JSON.stringify([0, 2, 3, 6, 9]));
await slide('ss', 4); i = await info();
check('s = 4: no five vertices are in general position (page and brute force), and the readout says so', i.five.count === 0 && fiveSets(10, 4).length === 0 && i.configs === null && /s < 5/.test(await text('ro5')));
let counts = true;
for (const s of [5, 6, 7]) { await slide('ss', s); const j = await info(); if (j.five.count !== 2 * 10 * C(s, 5) || j.five.extend !== 0) counts = false; }
check('C₁₀ □ Pₛ for s = 5, 6, 7: 20, 120, 420 sets = 2·10·C(s, 5), none extendable (the dossier’s 20, 120)', counts);

/* ---------- the general position polynomial ---------- */
await preset('p3'); i = await info();
check('ψ(P₃) = 1 + 3x + 3x², with roots −1/2 ± (√3/6)i, on the page and by enumeration', JSON.stringify(i.a) === '[1,3,3]' && JSON.stringify(psiInd(3, [[0, 1], [1, 2]])) === '[1,3,3]' && i.roots.length === 2 && i.roots.every((z) => Math.abs(z[0] + 0.5) < 1e-9 && Math.abs(Math.abs(z[1]) - Math.sqrt(3) / 6) < 1e-9));
check('…Newton’s first inequality fails: 9 < 1·3·2·2/1 = 12, and the readout says not complete', /9 < 12\.00/.test(await text('ro4')) && /不是完全图/.test(await text('ro5')));
await preset('toK'); i = await info();
const extra = []; for (let a = 0; a < 6; a++) for (let b = a + 2; b < 6; b++) extra.push([a, b]);
let polyOK = true, newtonOK = true, rootsOK = true;
i.steps.forEach((st, t) => {
  const e = [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5]].concat(extra.slice(0, t)), a = psiInd(6, e), dd = a.length - 1;
  if (JSON.stringify(a) !== JSON.stringify(st.a) || dd !== st.d) polyOK = false;
  const lhs = a[1] ** 2, rhs = a[0] * a[2] * 2 * dd / (dd - 1); if ((lhs >= rhs - 1e-9) !== (dd === 6)) newtonOK = false;
  if ((t === i.steps.length - 1) !== (st.maxIm < 1e-9) || (t < i.steps.length - 1 && st.maxIm < 1e-3)) rootsOK = false;
});
check('P₆ → K₆: every step’s ψ equals the enumeration (lexicographic edge order), and only K₆ has ψ = (1 + x)⁶', polyOK && JSON.stringify(i.steps[i.steps.length - 1].a) === '[1,6,15,20,15,6,1]');
check('…Newton’s first inequality holds exactly when d = n, i.e. only at K₆', newtonOK);
check('…every graph before K₆ has a root with imaginary part above 10⁻³, and K₆ has only real roots', rootsOK);
await setFrac(0.6); i = await info();
check('…at an intermediate step the page’s roots are roots of ψ (|ψ(z)| < 10⁻⁸ · Σ|aₖ||z|ᵏ)', i.roots.length === i.d && i.roots.every((z) => polyAt(i.a, z) < 1e-8 * i.a.reduce((s, c, k) => s + c * Math.hypot(z[0], z[1]) ** k, 0)));
await setFrac(1); i = await info();
check('…at K₆ the readout states ψ = (1 + x)⁶ and the frozen theorem', /\(1 \+ x\)⁶/.test(await text('ro5')) && /冻结定理/.test(await text('ro5')) && i.roots.every((z) => z[0] === -1 && z[1] === 0));
await click('#startChips [data-start="star"]'); i = await info();
check('starting from the star K₁,₅: the five leaves are a largest general position set (d = 5) and ψ matches the enumeration', i.start === 'star' && i.d === 5 && JSON.stringify(i.a) === JSON.stringify(psiInd(6, [[0, 1], [0, 2], [0, 3], [0, 4], [0, 5]])) && JSON.stringify(i.best) === '[1,2,3,4,5]');
await click('#startChips [data-start="cycle"]'); await slide('nn', 7); i = await info();
check('the cycle C₇ start: ψ matches the enumeration, d < 7, and Newton fails', i.n === 7 && JSON.stringify(i.a) === JSON.stringify(psiInd(7, [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 6], [0, 6]])) && i.d < 7 && /✗/.test(await D(() => document.getElementById('pillC').textContent)));

/* ---------- outer general position ---------- */
await preset('outer'); i = await info();
const oH = outerInd(18, EH), oG = outerInd(19, EG);
check('the counterexample opens on G − x with A ∪ B selected; outer numbers by brute force: 8 without x and 5 with x, as on the page', i.mode === 'outer' && i.stage === 0 && i.graph === 'H' && JSON.stringify(i.set) === '[0,1,2,3,4,5,6,7]' && i.outerH === 8 && oH.best === 8 && i.outerG === 5 && oG.best === 5);
check('…A ∪ B is in outer general position in G − x: no pair is blocked by any third vertex', [0, 1, 2, 3, 4, 5, 6, 7].every((u) => [0, 1, 2, 3, 4, 5, 6, 7].every((w) => u === w || blocks(oH.D, u, w) < 0)));
check('…x is not a cut vertex and has degree 2, so the conjecture asks gp₀(G − x) ≤ 5 + 2 = 7 < 8', EG.filter(([a, b]) => a === 18 || b === 18).length === 2 && oH.D.every((row) => row.every((v) => v < 1e9)));
await setFrac(1.5 / 8); i = await info();
check('stage 2: with x, the page names a blocked pair of A ∪ B and a third vertex that really blocks it', i.graph === 'G' && !!i.pair && [0, 1, 2, 3, 4, 5, 6, 7].includes(i.pair[0]) && [0, 1, 2, 3, 4, 5, 6, 7].includes(i.pair[1]) && (oG.D[i.pair[0]][i.pair[1]] + oG.D[i.pair[1]][i.pair[2]] === oG.D[i.pair[0]][i.pair[2]] || oG.D[i.pair[1]][i.pair[0]] + oG.D[i.pair[0]][i.pair[2]] === oG.D[i.pair[1]][i.pair[2]]));
let classesOK = true;
for (let c = 0; c < 5; c++) { await setFrac((c + 2.5) / 8); const j = await info(); const mem = COLOR.map((x, v) => (x === c ? v : -1)).filter((v) => v >= 0); if (j.cls !== c || JSON.stringify(j.members) !== JSON.stringify(mem) || !mem.every((u) => mem.every((w) => u === w || blocks(oG.D, u, w) >= 0))) classesOK = false; }
check('stages 3–7: each colour class of the Lean colouring, every pair of which is blocked in G (independent distances)', classesOK);
await setFrac(1); i = await info();
check('the last stage shows a 5-vertex outer general position set of G, verified independently', i.set.length === 5 && i.set.every((u) => i.set.every((w) => u === w || blocks(oG.D, u, w) < 0)));
check('…the readouts state 8 > 5 + 2 and the frozen theorem', /8 > 5 \+ 2/.test(await text('ro5')) && /冻结定理/.test(await text('ro5')));

/* ---------- timeline and keys ---------- */
await preset('cyl7'); await setFrac(0.97); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing the four-robot route to the end raises the covered toast', await waitToast(/走遍/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
await setFrac(10 / 124); await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps one move', (await info()).t === 11);
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await info()).t === 124 && (await state()).playing === false);
await click('#modeChips [data-mode="outer"]'); await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps one stage of the counterexample', (await info()).stage === 1);
check('the rail marks the eight stages', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' '))) === 'G−x +x c1 c2 c3 c4 c5 max');
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }).catch(() => {}); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
for (const p of ['cyl7', 'five', 'toK', 'outer']) {
  await preset(p); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('GENERAL//POSITION · Robots, polynomials and outer sets'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the three dossiers, the three Lean files and the five sources', (await D(() => { const h = [...document.querySelectorAll('#drawer .en a')].map((a) => a.href).join(' '); return ['klavzar-et-al-2025-mobile-general-position-cylinders.md', 'rather-2026-general-position-real-rooted-complete.md', 'tian-dokyeesun-klavzar-conjecture34-refutation.md', 'CylinderSevenTen.lean', 'RatherRealRootedComplete.lean', 'TianDokyeesunKlavzarOuterGeneralPositionRefutation.lean', '10.1016/j.dam.2025.10.041', 'arxiv.org/abs/2603.06930', 'arxiv.org/abs/2510.01294', '10.1017/S0004972718000473', '10.1017/S0004972723000102'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="general-position"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.GP_DEBUG && GP_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'general-position');

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
