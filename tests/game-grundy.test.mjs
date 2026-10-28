#!/usr/bin/env node
// Browser regression suite for viz/game-grundy (Playwright + Chromium with software WebGL).
//   node tests/game-grundy.test.mjs
// Reads page state through the read-only window.GG_DEBUG probe and checks it against an independent implementation: Divisor
// Nim Grundy values with each other heap tested for divisibility (the page divides the gcd), the subtraction-game recursion,
// and the cordiality game by a separate minimax over label arrays, including the frozen proof's pairing strategy for Impish.
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
  const start = await page.evaluate(() => GG_DEBUG.frames());
  await page.waitForFunction((f0) => !GG_DEBUG.pending() && GG_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => GG_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => GG_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => GG_DEBUG.info());
const state = () => D(() => GG_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => GG_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => GG_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};
const near = (a, b, tol = 1e-12) => Math.abs(a - b) <= tol;

// --- independent implementation
const memo = new Map();
function grundyInd(heaps) {   // every other heap is tested for divisibility one by one
  const key = heaps.slice().sort((a, b) => b - a).join('/'); if (memo.has(key)) return memo.get(key);
  const followers = [];
  heaps.forEach((h, i) => { const rest = heaps.filter((_, j) => j !== i); for (let d = 1; d <= h; d++) { if (rest.some((x) => x % d !== 0)) continue; followers.push(grundyInd(h > d ? rest.concat([h - d]) : rest)); } });
  const sorted = [...new Set(followers)].sort((a, b) => a - b); let m = 0; for (const x of sorted) { if (x === m) m++; else if (x > m) break; }
  memo.set(key, m); return m;
}
const val2 = (x) => { let k = 0; while (!(x & 1)) { x >>= 1; k++; } return k; };
function probsInd(S, N) { const a = new Array(N + 1).fill(0); for (let n = 1; n <= N; n++) { const moves = S.filter((s) => s <= n); if (moves.length) a[n] = 1 - moves.map((s) => a[n - s]).reduce((x, y) => x + y, 0) / moves.length; } return a; }
function windowsInd(S, N) { const a = probsInd(S, N + 2), b = a.map((x, n) => (n % 2 === 0 ? 1 : -1) * (1 - 2 * x)), d = a.map((_, n) => (n + 1 < b.length ? b[n] + b[n + 1] : 0)), M = Math.max(...S), J = []; for (let n = M; n <= N; n++) { let t = 0; for (const s of S) for (let r = 0; r < s; r++) t += d[n - s + r]; J.push(t); } return { a, d, J }; }
function minimaxInd(n, edges) {   // labels: −1 free, 0 Admirable, 1 Impish; Admirable moves when the counts are equal
  const lab = new Array(n).fill(-1), cache = new Map();
  const go = (na, ni) => {
    const key = lab.join(''); if (cache.has(key)) return cache.get(key);
    let r;
    if (na + ni === n) { const ones = edges.filter(([u, v]) => lab[u] !== lab[v]).length; r = Math.abs(ones - (edges.length - ones)); }
    else { const adm = na === ni; r = adm ? Infinity : -Infinity; for (let v = 0; v < n; v++) if (lab[v] < 0) { lab[v] = adm ? 0 : 1; const x = adm ? go(na + 1, ni) : go(na, ni + 1); lab[v] = -1; r = adm ? Math.min(r, x) : Math.max(r, x); } }
    cache.set(key, r); return r;
  };
  return go(0, 0);
}
const WIT = [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 6], [6, 7], [0, 8], [0, 9]];
const PATHN = (n) => Array.from({ length: n - 1 }, (_, i) => [i, i + 1]);
function pairingFloor() {   // Impish answers each move with its partner (or any free vertex when the partner is taken); the worst case for Impish
  const partner = { 0: 4, 4: 0, 1: 5, 5: 1, 2: 6, 6: 2, 3: 7, 7: 3, 8: 9, 9: 8 }, lab = new Array(10).fill(-1);
  const disc = () => { const ones = WIT.filter(([u, v]) => lab[u] !== lab[v]).length; return Math.abs(2 * ones - 9); };
  const adm = () => { if (lab.every((x) => x >= 0)) return disc(); let r = Infinity; for (let v = 0; v < 10; v++) if (lab[v] < 0) { lab[v] = 0; r = Math.min(r, imp(v)); lab[v] = -1; } return r; };
  const imp = (last) => { if (lab.every((x) => x >= 0)) return disc(); const p = partner[last]; if (lab[p] < 0) { lab[p] = 1; const x = adm(); lab[p] = -1; return x; } let r = Infinity; for (let v = 0; v < 10; v++) if (lab[v] < 0) { lab[v] = 1; r = Math.min(r, adm()); lab[v] = -1; } return r; };
  return adm();
}

await page.goto(origin + BASE + 'viz/game-grundy/');
await page.waitForFunction(() => window.GG_DEBUG && GG_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
check('page loads with the probe', (await D(() => document.body.dataset.vizId)) === 'game-grundy');
check('starts on two-heap Divisor Nim', (await state()).preset === 'nim2' && (await info()).mode === 'nim' && (await info()).c === 0);
check('the frozen anchors are named', JSON.stringify(await D(() => [...document.querySelectorAll('.lean:not(.lit):not(.num) code')].map((c) => c.textContent))) === JSON.stringify(['DivisorNimBound.result', 'DivisorNimBoundOutcome.zero_iff_even_count', 'DivisorNimPeriodPropagation.singleton_grundy', 'CapitelliSommaAllOddNonconvergence.result', 'CordialityTreePathRefutation.result']));
check('…page numbers and literature sit in separate NUM and LIT boxes', (await D(() => [document.querySelectorAll('.lean.num').length, document.querySelectorAll('.lean.lit').length].join())) === '1,1' && /不是定理/.test(await D(() => document.querySelector('.lean.num').textContent)));

// --- Divisor Nim
let i = await info();
const tableOK = (tab, c) => tab.every((row, a) => row.every((g, b) => g === grundyInd(c ? [a + 1, b + 1, c] : [a + 1, b + 1])));
check('two heaps, a, b ≤ 24: all 576 Grundy values equal the independent recursion', i.table.length === 24 && tableOK(i.table, 0));
let boundOK = true, parityOK = true;
for (let a = 1; a <= 24; a++) for (let b = 1; b <= 24; b++) { const g = grundyInd([a, b]); if (g > 2 * Math.min(a, b)) boundOK = false; const k = Math.min(val2(a), val2(b)); if ((g === 0) !== ([a, b].filter((x) => val2(x) === k).length % 2 === 0)) parityOK = false; }
check('…every value is at most 2·min(a, b) (frozen bound) and g = 0 exactly when the 2-adic count is even (frozen)', boundOK && parityOK && i.viol === 0 && i.parityOK === 576);
check('…the largest ratio g/(2·h_min) with two heaps is 3/4, as the readout says', near(i.maxRatio, 0.75) && (await text('ro3')) === '0.750' && i.equal.length === 0);
check('single heaps: g({n}) = n for n ≤ 30 (frozen), and the page agrees', Array.from({ length: 30 }, (_, k) => grundyInd([k + 1]) === k + 1).every(Boolean) && (await D(() => Array.from({ length: 30 }, (_, k) => GG_DEBUG.grundy([k + 1]) === k + 1).every(Boolean))));
await preset('nim3');
const cOK = [];
for (const c of [3, 8, 12, 16]) { await setFrac(c / 16); i = await info(); let bnd = true, par = true; for (let a = 1; a <= 24; a++) for (let b = 1; b <= 24; b++) { const P = [a, b, c], g = grundyInd(P); if (g > 2 * Math.min(...P)) bnd = false; const k = Math.min(...P.map(val2)); if ((g === 0) !== (P.filter((x) => val2(x) === k).length % 2 === 0)) par = false; } cOK.push(i.c === c && tableOK(i.table, c) && bnd && par && i.viol === 0 && i.parityOK === 576); }
check('third heap c = 3, 8, 12, 16: all Grundy tables match, stay under 2·min(a, b, c) and follow the 2-adic rule', cOK.every(Boolean), cOK.map((x) => (x ? 1 : 0)).join(''));
await preset('tight'); i = await info();
check('the tight preset: c = 10, and {1, 4, 10} attains g = 2 = 2·h_min (independent recursion)', i.c === 10 && grundyInd([1, 4, 10]) === 2 && i.equal.some((P) => P.join() === '1,4,10') && /\{1, 4, 10\}/.test(await text('ro4')));
const tight = []; for (let a = 1; a <= 24; a++) for (let b = a; b <= 24; b++) if (grundyInd([a, b, 10]) === 2 * Math.min(a, b, 10)) tight.push([a, b, 10].sort((x, y) => x - y).join());
check('…the page lists exactly the boards that attain the bound at c = 10', JSON.stringify(i.equal.map((P) => P.join()).sort()) === JSON.stringify(tight.sort()), tight.join(' | '));
await preset('zeros'); i = await info();
check('the zeros preset counts the losing positions: 194 of 576 for two heaps', i.zeros === 194 && i.zeros === i.table.flat().filter((g) => g === 0).length);

// --- random subtraction games
await preset('odd35'); await setFrac(1); i = await info();
const w35 = windowsInd([3, 5], 120);
check('S = {3, 5}: a_0 … a_120 equal the independent recursion', i.a.length === 121 && i.a.every((x, n) => near(x, w35.a[n], 1e-12)));
check('…d_n ≥ 0 and the window sum J_N stays at 4 from N = max S = 5 on (≥ 2, as in the frozen proof)', i.d.every((x) => x >= -1e-12) && w35.J.every((x) => near(x, 4, 1e-9)) && i.J.every(([, x]) => near(x, 4, 1e-9)) && i.J[0][0] === 5);
check('…the even and odd terms stay apart (0.375 and 0.625 to 4 decimals) and the verdict cites the frozen theorem', Math.abs(w35.a[120] - w35.a[119]) > 0.2 && near(w35.a[120], 0.375, 1e-4) && near(w35.a[119], 0.625, 1e-4) && i.verdict === 'frozen' && /冻结定理/.test(await text('ro5')));
const odds = [[1, 3], [1, 5, 7], [3, 7, 9], [5, 9]].map((S) => { const W = windowsInd(S, 110); return W.d.slice(0, 110).every((x) => x >= -1e-12) && W.J.every((x) => near(x, W.J[0], 1e-9)) && W.J[0] >= 2 - 1e-12 && Math.abs(W.a[110] - W.a[109]) > 1e-3; });
check('…independently for S = {1, 3}, {1, 5, 7}, {3, 7, 9}, {5, 9}: d ≥ 0, a constant window ≥ 2, and adjacent terms apart', odds.every(Boolean), odds.map((x) => (x ? 1 : 0)).join(''));
await preset('even12'); await setFrac(1); i = await info();
const w12 = probsInd([1, 2], 120);
check('S = {1, 2}: the sequence matches and converges to ½, with the verdict citing the literature', i.a.every((x, n) => near(x, w12[n], 1e-12)) && near(w12[120], 0.5, 1e-9) && near(w12[119], 0.5, 1e-9) && i.verdict === 'lit' && i.Jnow < 1e-6);
await click('#setChips [data-s="2"]'); await click('#setChips [data-s="3"]'); i = await info();
check('the set chips: removing 2 and adding 3 gives S = {1, 3}, all odd, the sequence matches and the settings become custom', JSON.stringify(i.S) === '[1,3]' && i.allOdd && i.verdict === 'frozen' && i.a.every((x, n) => near(x, probsInd([1, 3], 120)[n], 1e-12)) && (await state()).preset === null);
await click('#setChips [data-s="1"]'); i = await info();
check('…S = {3} has gcd 3: the verdict cites the frozen proof’s gcd-free lemma, and a_n still alternates', JSON.stringify(i.S) === '[3]' && i.gcd === 3 && i.verdict === 'proof' && i.a.every((x, n) => near(x, probsInd([3], 120)[n], 1e-12)));
await click('#setChips [data-s="6"]'); i = await info();
check('…S = {3, 6} (gcd 3 with an even move) is covered by neither theorem', JSON.stringify(i.S) === '[3,6]' && i.verdict === 'none');

// --- the cordiality game
await preset('tree10'); i = await info();
check('the tree T: independent minimax gives c_g(T) = 3, and the page agrees', minimaxInd(10, WIT) === 3 && i.cg === 3 && i.treeValue === 3);
check('…Impish’s pairing (0, 4), (1, 5), (2, 6), (3, 7), (8, 9) alone forces a discrepancy of at least 3 against every Admirable play', pairingFloor() >= 3);
check('the path P₁₀: c_g = 1 (independent minimax), so c_g(T) > c_g(P₁₀) and Conjecture 3.2 fails', minimaxInd(10, PATHN(10)) === 1);
check('…the page’s path values P₂ … P₁₀ and the star value equal the independent minimax', JSON.stringify(i.pathValues.map(([n, v]) => [n, v])) === JSON.stringify(Array.from({ length: 9 }, (_, k) => [k + 2, minimaxInd(k + 2, PATHN(k + 2))])) && i.starValue === minimaxInd(10, Array.from({ length: 9 }, (_, k) => [0, k + 1])));
const legal = (mv) => mv.length === 10 && new Set(mv).size === 10 && mv.every((v) => v >= 0 && v < 10);
const finalDisc = (mv, E) => { const lab = []; mv.forEach((v, t) => { lab[v] = t % 2; }); const ones = E.filter(([u, v]) => lab[u] !== lab[v]).length; return Math.abs(2 * ones - E.length); };
check('…the replayed optimal game is legal, ends with discrepancy 3, and every position along it has value 3', legal(i.moves) && finalDisc(i.moves, WIT) === 3 && i.traj.every((v) => v === 3));
await setFrac(0.6); i = await info();
check('…after six moves the labels are those six moves, Admirable is to move and the value is still 3', i.t === 6 && i.A === i.moves.slice(0, 6).filter((_, t) => t % 2 === 0).reduce((m, v) => m | (1 << v), 0) && i.B === i.moves.slice(0, 6).filter((_, t) => t % 2 === 1).reduce((m, v) => m | (1 << v), 0) && i.value === 3 && /Admirable/.test(await text('ro2')));
const free = Array.from({ length: 10 }, (_, v) => v).filter((v) => !(((i.A | i.B) >> v) & 1)), pick = free.find((v) => v !== i.moves[6]);
const at = await D((u) => GG_DEBUG.vertexScreen(u), pick);
await page.mouse.click(at.x, at.y); await settle(); const j = await info();
check('clicking a free vertex plays it for the side to move; the game continues optimally and the readouts follow', at && j.moves[6] === pick && legal(j.moves) && j.t === 7 && (await state()).preset === null && j.traj[6] === 3 && j.traj[10] === finalDisc(j.moves, WIT), `clicked ${pick}`);
await preset('path10'); await setFrac(1); i = await info();
check('the path preset: the optimal game on P₁₀ ends 5 · 4 · 1', legal(i.moves) && finalDisc(i.moves, PATHN(10)) === 1 && /5 · 4 · 1/.test(await text('ro5')), await text('ro5'));

// --- controls, keys, presets
for (const name of ['nim2', 'nim3', 'zeros', 'tight', 'odd35', 'even12', 'tree10', 'path10']) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await click('#modeChips [data-mode="nim"]');
check('the game chips switch to Divisor Nim, hide both fields and mark the settings custom', (await info()).mode === 'nim' && !(await visible('setField')) && !(await visible('treeField')) && (await state()).preset === null);
await click('#modeChips [data-mode="random"]');
check('…random subtraction shows the set chips', (await visible('setField')) && !(await visible('treeField')));
await click('#modeChips [data-mode="cordial"]');
check('…the cordiality game shows the graph chips', (await visible('treeField')) && !(await visible('setField')));
await click('#treeChips [data-tree="star"]'); i = await info();
check('the graph chip switches to the star with value 1', i.tree === 'star' && i.cg === 1);
await setFrac(0); await page.keyboard.press('ArrowRight'); await settle();
check('→ plays one move', (await info()).t === 1);
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await info()).t === 10 && (await state()).playing === false);
await click('#modeChips [data-mode="nim"]'); await setFrac(0); await page.keyboard.press('ArrowRight'); await settle();
check('…and in Divisor Nim → adds one stone to the third heap', (await info()).c === 1);

// --- play and toasts
await preset('nim3'); await setFrac(0.985); await click('#play');
check('the Divisor Nim toast reports c = 16 under the bound', await waitToast(/c = 16/));
await pause();
await preset('odd35'); await setFrac(0.985); await click('#play');
check('the subtraction toast says the subsequences stay apart', await waitToast(/n = 120.*仍然分开/));
await pause();
await preset('tree10'); await setFrac(0.95); await click('#play');
check('the cordiality toast reports the final discrepancy 3', await waitToast(/= 3/));
await pause();
await preset('odd35'); await setFrac(0.2); await click('#play'); await waitFrames(12); const p1 = (await state()).nowFrac; await pause();
check('play advances along the rail', p1 > 0.2);
await click('#rev'); await waitFrames(12); const p2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', p2 < p1);
await page.click('#rev'); await pause();
await page.focus('#now'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with the rail focused', playing === true);
await pause();

// --- language
await click('#modeChips [data-mode="nim"]');
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
for (const m of ['random', 'cordial', 'nim']) {
  await click(`#modeChips [data-mode="${m}"]`); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${m}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('GAME//GRUNDY · Three games, three settled questions'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the three dossiers, the five Lean files and the three source papers', (await D(() => { const h = [...document.querySelectorAll('#drawer .en a')].map((a) => a.href).join(' '); return ['tyagi-2026-divisor-nim-sharper-sg-bound.md', 'capitelli-somma-2024-all-odd-nonconvergence.md', 'krop-mittal-wigal-2024-game-cordiality-tree-path.md', 'DivisorNimBound.lean', 'DivisorNimBoundOutcome.lean', 'DivisorNimPeriodPropagation.lean', 'CapitelliSommaAllOddNonconvergence.lean', 'CordialityTreePathRefutation.lean', 'arxiv.org/abs/2610.06925', 'arxiv.org/abs/2405.19593', '10.1007/s00373-024-02798-1'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="game-grundy"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.GG_DEBUG && GG_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'game-grundy');

// --- narrow layouts in both languages
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
