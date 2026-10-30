#!/usr/bin/env node
// Browser regression suite for viz/ku-lines (Playwright + Chromium with software WebGL).
//   node tests/ku-lines.test.mjs
// Reads page state through the read-only window.KU_DEBUG probe and checks it against an independent implementation: lines
// generated from canonical directions (first nonzero coordinate +1) and admissible start points, saturated configurations
// for k = 3 as maximal cliques of the non-collinearity graph (Bron–Kerbosch with pivoting), every subset of the 4×4 board
// checked directly, the certificates checked line by line, the 3⁴ maximum by an independent branch-and-bound search, and the
// 12 Latin squares of order 3 generated from their first row and a cyclic shift.
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
  const start = await page.evaluate(() => KU_DEBUG.frames());
  await page.waitForFunction((f0) => !KU_DEBUG.pending() && KU_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => KU_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => KU_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => KU_DEBUG.info());
const state = () => D(() => KU_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => KU_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => KU_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 120000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
function myLines(k, d) {
  const N = k ** d, coord = (i) => { const c = []; for (let j = 0; j < d; j++) { c.push(i % k); i = Math.floor(i / k); } return c; }, idx = (c) => c.reduce((s, v, j) => s + v * k ** j, 0);
  const dirs = []; for (let i = 0; i < 3 ** d; i++) { const v = []; let x = i; for (let j = 0; j < d; j++) { v.push((x % 3) - 1); x = Math.floor(x / 3); } const f = v.find((c) => c !== 0); if (f === 1) dirs.push(v); }
  const out = [];
  for (const v of dirs) for (let i = 0; i < N; i++) { const p = coord(i), end = p.map((c, j) => c + (k - 1) * v[j]); if (end.some((c) => c < 0 || c >= k)) continue; out.push(Array.from({ length: k }, (_, t) => idx(p.map((c, j) => c + t * v[j])))); }
  return out;
}
const key = (L) => L.slice().sort((a, b) => a - b).join(',');
function validSat(k, d, S, lines) {
  const inS = new Set(S), cnt = lines.map((L) => L.filter((p) => inS.has(p)).length);
  const valid = cnt.every((c) => c <= k - 2);
  let saturated = valid; if (valid) for (let p = 0; p < k ** d && saturated; p++) if (!inS.has(p) && lines.every((L, li) => !L.includes(p) || cnt[li] + 1 <= k - 2)) saturated = false;
  return { valid, saturated, cnt };
}
/* k = 3: a configuration is a set of pairwise non-collinear points; saturated = maximal clique of the non-collinearity graph */
function maximalCliques(N, lines) {
  const coll = Array.from({ length: N }, () => new Set()); for (const L of lines) for (const a of L) for (const b of L) if (a !== b) coll[a].add(b);
  const nbr = Array.from({ length: N }, (_, a) => new Set([...Array(N).keys()].filter((b) => b !== a && !coll[a].has(b))));
  const out = [];
  (function bk(R, P, X) {
    if (P.size === 0 && X.size === 0) { out.push([...R].sort((a, b) => a - b)); return; }
    let u = -1, best = -1; for (const w of [...P, ...X]) { const c = [...P].filter((q) => nbr[w].has(q)).length; if (c > best) { best = c; u = w; } }
    for (const v of [...P].filter((q) => !nbr[u].has(q))) { bk(new Set([...R, v]), new Set([...P].filter((q) => nbr[v].has(q))), new Set([...X].filter((q) => nbr[v].has(q)))); P.delete(v); X.add(v); }
  })(new Set(), new Set(Array.from({ length: N }, (_, i) => i)), new Set());
  return out;
}
function maxSize(k, d, lines) {
  const N = k ** d, lineOf = Array.from({ length: N }, () => []); lines.forEach((L, li) => L.forEach((p) => lineOf[p].push(li)));
  const cnt = new Int32Array(lines.length); let best = 0;
  const ok = (p) => lineOf[p].every((li) => cnt[li] <= k - 3);
  (function rec(start, size) {
    if (size > best) best = size;
    let room = 0; for (let p = start; p < N; p++) if (ok(p)) room++;
    if (size + room <= best) return;
    for (let p = start; p < N; p++) if (ok(p)) { lineOf[p].forEach((li) => cnt[li]++); rec(p + 1, size + 1); lineOf[p].forEach((li) => cnt[li]--); }
  })(0, 0);
  return best;
}
/* the 12 Latin squares of order 3: rows are a permutation r and its two cyclic shifts, in either order */
function latin12() { const perms = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]], out = new Set(); for (const r of perms) for (const s of [1, 2]) out.add(JSON.stringify([0, 1, 2].map((i) => [0, 1, 2].map((j) => r[(j + s * i) % 3])))); return [...out].map((x) => JSON.parse(x)); }

/* ---------- load ---------- */
await page.goto(origin + BASE + 'viz/ku-lines/');
await page.waitForFunction(() => window.KU_DEBUG && KU_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let st = await state(), i = await info();
check('opens on the largest configuration of 3×3×3 (paused)', st.preset === 'lean' && i.board === '3,3' && i.mode === 'configs' && i.i === 0 && st.playing === false);

/* ---------- lines on every board ---------- */
const boards = { '3,2': 8, '4,2': 10, '5,2': 12, '3,3': 49, '4,3': 76, '3,4': 272 };
let linesOK = true, detail = [];
for (const b of Object.keys(boards)) {
  await click(`#boardChips [data-board="${b}"]`); const x = await info(); const [k, d] = b.split(',').map(Number);
  const mine = myLines(k, d), a = new Set(x.lines.map(key)), m = new Set(mine.map(key));
  const same = a.size === m.size && [...m].every((s) => a.has(s)) && x.lines.length === a.size && a.size === boards[b];
  if (!same) linesOK = false; detail.push(`${b}:${x.lines.length}`);
}
check('every board has exactly the full lines of the independent generator (8, 10, 12, 49, 76, 272)', linesOK, detail.join(' '));
check('3×3×3 splits its 49 lines into 27 axis lines, 18 face diagonals and 4 space diagonals', await (async () => { await click('#boardChips [data-board="3,3"]'); const x = await info(); const c = [1, 2, 3].map((t) => x.kinds.filter((q) => q === t).length); return c.join() === '27,18,4'; })());

/* ---------- saturated configurations ---------- */
const lines33 = myLines(3, 3), mc33 = maximalCliques(27, lines33);
await preset('all'); const cfg33 = await D(() => KU_DEBUG.configs()); i = await info();
const setOf = (arr) => new Set(arr.map((c) => c.slice().sort((a, b) => a - b).join(',')));
const s33 = setOf(cfg33), m33 = setOf(mc33);
check('3×3×3: the page’s 305 saturated configurations are exactly the maximal cliques of the non-collinearity graph', cfg33.length === 305 && mc33.length === 305 && [...m33].every((c) => s33.has(c)), `${cfg33.length} vs ${mc33.length}`);
check('3×3×3: sizes 6 → 8, 5 → 120, 4 → 176, 1 → 1, the single one being the centre (2, 2, 2)', JSON.stringify(i.hist) === '[[1,1],[4,176],[5,120],[6,8]]' && cfg33.filter((c) => c.length === 1).length === 1 && cfg33.find((c) => c.length === 1)[0] === 13);
check('3×3×3: the largest saturated size is 6 < 8 (the Lean bound) < 9 (the conjecture)', i.best === 6 && Math.max(...mc33.map((c) => c.length)) === 6 && Math.round(i.ku) === 9);
check('every listed 3×3×3 configuration is valid and saturated by an independent check', cfg33.every((c) => { const r = validSat(3, 3, c, lines33); return r.valid && r.saturated; }));
await click('#boardChips [data-board="3,2"]'); const cfg32 = await D(() => KU_DEBUG.configs()), mc32 = maximalCliques(9, myLines(3, 2));
check('3×3: the 5 saturated configurations equal the maximal cliques, the largest having 3 = (1 − 2/3)·9 points', cfg32.length === 5 && [...setOf(mc32)].every((c) => setOf(cfg32).has(c)) && Math.max(...cfg32.map((c) => c.length)) === 3);
await click('#boardChips [data-board="4,2"]'); const cfg42 = await D(() => KU_DEBUG.configs()), lines42 = myLines(4, 2);
const brute42 = []; for (let m = 0; m < 1 << 16; m++) { const S = []; for (let p = 0; p < 16; p++) if (m >> p & 1) S.push(p); const r = validSat(4, 2, S, lines42); if (r.valid && r.saturated) brute42.push(S); }
check('4×4: the saturated configurations equal those found by checking all 65536 subsets, the largest having 8 = (1 − 2/4)·16 points', cfg42.length === brute42.length && [...setOf(brute42)].every((c) => setOf(cfg42).has(c)) && Math.max(...cfg42.map((c) => c.length)) === 8, `${cfg42.length} vs ${brute42.length}`);

/* ---------- certificates ---------- */
const certOK = async (b) => { await click(`#boardChips [data-board="${b}"]`); const x = await info(), [k, d] = b.split(',').map(Number), r = validSat(k, d, x.S, myLines(k, d)); return { x, r }; };
let c = await certOK('5,2');
check('5×5 certificate: 15 points, valid and saturated, equal to (1 − 2/5)·25', c.x.S.length === 15 && c.r.valid && c.r.saturated && c.x.valid && c.x.saturated);
c = await certOK('4,3');
const axis0 = myLines(4, 3).filter((L) => L[1] - L[0] === 1);
check('4×4×4 certificate: 32 points, valid and saturated, with exactly 2 points on each of the 16 axis lines in one direction', c.x.S.length === 32 && c.r.valid && c.r.saturated && axis0.length === 16 && axis0.every((L) => L.filter((p) => c.x.S.includes(p)).length === 2));
c = await certOK('3,4');
const max34 = maxSize(3, 4, myLines(3, 4));
check('3⁴ certificate: 11 points, valid and saturated, and an independent branch and bound confirms 11 is the maximum', c.x.S.length === 11 && c.r.valid && c.r.saturated && max34 === 11, `max ${max34}`);
check('3³ maximum 6 confirmed by the same independent branch and bound', maxSize(3, 3, lines33) === 6);

/* ---------- the Latin-square obstruction ---------- */
await preset('latin'); i = await info();
const L12 = latin12(); let latOK = i.count === 12, seenL = new Set();
for (let j = 0; j < 12; j++) {
  await setFrac(j / 11); const x = await info(); seenL.add(JSON.stringify(x.L));
  const isLatin = [0, 1, 2].every((a) => new Set(x.L[a]).size === 3 && new Set([0, 1, 2].map((b) => x.L[b][a])).size === 3);
  const S = [0, 1, 2].flatMap((a) => [0, 1, 2].map((b) => a + 3 * b + 9 * x.L[a][b]));
  const r = validSat(3, 3, S, lines33), myBad = lines33.map((L, li) => (r.cnt[li] >= 2 ? key(L) : null)).filter(Boolean).sort().join('|');
  const pageBad = x.violated.map((li) => key(x.lines[li])).sort().join('|');
  const face = x.violated.some((li) => x.kinds[li] === 2);
  const axisOne = lines33.filter((L) => [1, 3, 9].includes(Math.abs(L[1] - L[0])) && L.every((p, t) => t === 0 || p - L[t - 1] === L[1] - L[0])).every((L) => L.filter((p) => S.includes(p)).length === 1);
  if (!(isLatin && JSON.stringify(x.S.slice().sort((a, b) => a - b)) === JSON.stringify(S.slice().sort((a, b) => a - b)) && myBad === pageBad && face && axisOne && !x.valid)) latOK = false;
}
check('latin mode: 12 distinct Latin squares; each gives 9 points with one per axis line and at least one violated face diagonal', latOK && seenL.size === 12 && L12.every((L) => seenL.has(JSON.stringify(L))));
check('latin mode readout names the diagonals and the violated lines', /主 \d{3} · 副 \d{3}/.test(await text('ro5')) && /面对角线/.test(await text('ro3')));

/* ---------- presets, controls, timeline ---------- */
await preset('plane'); i = await info();
check('plane preset: 3 points (1, 1), (3, 2), (2, 3), as in the note', i.board === '3,2' && i.S.join() === '0,5,7');
await click('#boardChips [data-board="4,2"]');
check('board chips mark the settings custom and the Latin mode is disabled off 3×3×3', (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')) && (await D(() => document.querySelector('#modeChips [data-mode="latin"]').disabled)) === true);
for (const p of ['lean', 'latin', 'all', 'plane', 'k43', 'd4']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
await preset('latin'); await setFrac(0.95); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing the Latin squares to the end reports that 9 points are impossible', await waitToast(/12 个 Latin 方阵.*9 个点不可能/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
await preset('all');
check('the rail marks 1, the first size-4 configuration and 305', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === '1 | |S| = 4 | 305');
await setFrac(0.5); const i0 = (await info()).i;
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps to the next configuration', (await info()).i === i0 + 1);
await page.keyboard.press('e'); await settle();
check('E jumps to the last configuration and pauses', (await info()).i === 304 && (await state()).playing === false);
await preset('lean');
check('the readouts compare the conjecture with the page maximum and list the counts', /9 · 6/.test(await text('ro2')) && /305: 6→8, 5→120, 4→176, 1→1/.test(await text('ro5')));
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 800), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['latin', 'd4']) {
  await preset(p);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#boardChips [data-board="5,2"]');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('KU//LINES · Ku\'s near-line conjecture: a counterexample on 3×3×3'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['ku-2026-monochromatic-k-in-a-row-conjecture-5-6.md', 'KuNearLineRefutation.lean', 'Blueprint/D5/S3/Combinatorics/Geometry/KuNearLineRefutation.md', 'ku2026monochromatic.md', 'arxiv.org/abs/2606.12880'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="ku-lines"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.KU_DEBUG && KU_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'ku-lines');

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
