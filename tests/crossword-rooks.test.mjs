#!/usr/bin/env node
// Browser regression suite for viz/crossword-rooks (Playwright + Chromium with software WebGL).
//   node tests/crossword-rooks.test.mjs
// Reads page state through the read-only window.CW_DEBUG probe and checks it against independent sources: Lean's SameAcross,
// SameDown, IsRookPlacement and rookCount transcribed literally (enumerating every subset of white cells), Lean's grid family
// and candidate placements, the witness permutation, and Ryser's permanent formula on the word incidence matrix.
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
const D2 = (expr, arg) => page.evaluate(expr, arg);
const settle = async () => {
  const start = await page.evaluate(() => CW_DEBUG.frames());
  await page.waitForFunction((f0) => !CW_DEBUG.pending() && CW_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D2(() => CW_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D2((t) => CW_DEBUG.setT(t), t); await settle(); };
const info = () => D2(() => CW_DEBUG.info());
const state = () => D2(() => CW_DEBUG.state());
const text = (id) => D2((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D2(() => CW_DEBUG.frames()); await page.waitForFunction((t) => CW_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };


/* the rail position of placement i, at the middle of its slot */
const slot = (i, n) => (i + 0.5) / n;

/* ---------- Lean's definitions, transcribed ---------- */
/* SameAcross, SameDown, IsRookPlacement and rookCount over a set W of white cells "a,b", literally */
const key = (a, b) => `${a},${b}`;
const sameA = (W, c, d) => c[0] === d[0] && (() => { for (let j = Math.min(c[1], d[1]); j <= Math.max(c[1], d[1]); j++) if (!W.has(key(c[0], j))) return false; return true; })();
const sameD = (W, c, d) => c[1] === d[1] && (() => { for (let i = Math.min(c[0], d[0]); i <= Math.max(c[0], d[0]); i++) if (!W.has(key(i, c[1]))) return false; return true; })();
const cellsOfW = (W) => [...W].map((s) => s.split(',').map(Number));
function isPlacement(W, R) {
  const cells = cellsOfW(W);
  if (!R.every((c) => W.has(key(...c)))) return false;
  for (let x = 0; x < R.length; x++) for (let y = 0; y < R.length; y++) if (x !== y && (sameA(W, R[x], R[y]) || sameD(W, R[x], R[y]))) return false;
  return cells.every((c) => R.some((d) => sameA(W, c, d)) && R.some((d) => sameD(W, c, d)));
}
function rookCountLiteral(W) { const cells = cellsOfW(W); let n = 0; for (let m = 0; m < 1 << cells.length; m++) if (isPlacement(W, cells.filter((_, k) => (m >> k) & 1))) n++; return n; }
/* Lean's family: gridSize, side, tip, rowLeft, rowRight, white and candidate */
const gridSizeL = (r) => Math.max(5, 2 * r - 1), sideL = (i) => (i % 2 === 0 ? 3 : 1), tipL = (i) => (i % 2 === 0 ? 4 : 0);
const rowLeftL = (r, a) => (a % 2 === 1 ? (a % 4 === 1 ? 2 : 0) : (a === 0 || (a === 2 * r - 2 && a % 4 === 2)) ? 2 : 1);
const rowRightL = (r, a) => (a % 2 === 1 ? (a % 4 === 1 ? 4 : 2) : (a === 2 * r - 2 && a % 4 === 0) ? 2 : 3);
const whiteL = (r) => { const N = gridSizeL(r), W = new Set(); for (let a = 0; a < N; a++) for (let b = 0; b < N; b++) if (a < 2 * r - 1 && rowLeftL(r, a) <= b && b <= rowRightL(r, a)) W.add(key(a, b)); return W; };
const candidateL = (r, k) => { const N = gridSizeL(r), out = []; for (let a = 0; a < N; a++) for (let b = 0; b < N; b++) { let ok = a === 2 * k && b === 2; for (let i = 0; i + 1 < r; i++) { if (a === 2 * i + 1 && b === tipL(i)) ok = true; if (b === sideL(i) && ((i < k && a === 2 * i) || (k <= i && a === 2 * i + 2))) ok = true; } if (ok) out.push([a, b]); } return out; };
const zeroWhiteL = new Set(['0,1', '0,2', '1,0', '2,0']);
/* the permanent of the word incidence matrix by Ryser's formula, an independent count of placements */
function wordMatrix(N, W) {
  const acr = new Map(), dn = new Map(); let na = 0, nd = 0;
  for (let a = 0; a < N; a++) for (let b = 0; b < N; b++) if (W.has(key(a, b))) acr.set(key(a, b), b > 0 && W.has(key(a, b - 1)) ? acr.get(key(a, b - 1)) : na++);
  for (let b = 0; b < N; b++) for (let a = 0; a < N; a++) if (W.has(key(a, b))) dn.set(key(a, b), a > 0 && W.has(key(a - 1, b)) ? dn.get(key(a - 1, b)) : nd++);
  const B = Array.from({ length: na }, () => new Array(nd).fill(0)); for (const s of W) B[acr.get(s)][dn.get(s)] = 1;
  return { B, na, nd, acr, dn };
}
function ryser(B) { const n = B.length; if (n === 0) return 1; if (B[0].length !== n) return 0; let total = 0; for (let S = 1; S < 1 << n; S++) { let prod = 1; for (let i = 0; i < n && prod; i++) { let s = 0; for (let j = 0; j < n; j++) if ((S >> j) & 1) s += B[i][j]; prod *= s; } let bits = 0; for (let x = S; x; x >>= 1) bits += x & 1; total += ((n - bits) % 2 ? -1 : 1) * prod; } return total; }
const countRyser = (N, W) => ryser(wordMatrix(N, W).B);
const permW = (p) => { const n = p.length, W = new Set(); for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) if (p[a] - 1 !== b) W.add(key(a, b)); return W; };
const asSet = (cells) => JSON.stringify(cells.map((c) => key(...c)).sort());
const LEANWITNESS = [1, 6, 3, 7, 0, 5, 2, 4];
const fromMask = (N, m) => { const W = new Set(); for (let q = 0; q < N * N; q++) if ((m >> q) & 1) W.add(key(Math.floor(q / N), q % N)); return W; };

await page.goto(`${origin}${BASE}viz/crossword-rooks/`);
await page.waitForFunction(() => window.CW_DEBUG && CW_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();
check('starts on the first preset (r = 5), playing from the start', st.preset === 'lean' && st.playing === true && st.mode === 'family' && i.r === 5);
await pause();

/* ---------- the construction against Lean ---------- */
const fams = await D2(() => Array.from({ length: 21 }, (_, r) => CW_DEBUG.family(r)));
const whiteSet = (f) => { const W = new Set(); f.white.forEach((v, q) => { if (v) W.add(key(Math.floor(q / f.N), q % f.N)); }); return W; };
check('for r = 1 … 20 the page’s grid is Lean’s white r of side gridSize r = max(5, 2r − 1); for r = 0 it is Lean’s zeroWhite', fams.every((f, r) => r === 0 ? f.N === 3 && asSet(cellsOfW(whiteSet(f))) === asSet(cellsOfW(zeroWhiteL)) : f.N === gridSizeL(r) && asSet(cellsOfW(whiteSet(f))) === asSet(cellsOfW(whiteL(r)))));
check('the page counts exactly r placements for every r = 0 … 20', fams.every((f, r) => f.count === r));
check('Lean’s rookCount, transcribed literally (every subset of white cells), is 0, 1, 2, 3 for zeroWhite and r = 1, 2, 3', rookCountLiteral(zeroWhiteL) === 0 && [1, 2, 3].every((r) => rookCountLiteral(whiteL(r)) === r));
let ryOK = true; for (let r = 1; r <= 9; r++) if (countRyser(gridSizeL(r), whiteL(r)) !== r) ryOK = false;
check('Ryser’s permanent of the word incidence matrix is r for r = 1 … 9', ryOK);
const pageCands = await D2(() => { const o = []; for (let r = 1; r <= 20; r++) { const row = []; for (let k = 0; k < r; k++) row.push(CW_DEBUG.candidate(r, k)); o.push(row); } return o; });
let candOK = true; for (let r = 1; r <= 20; r++) for (let k = 0; k < r; k++) { const c = candidateL(r, k); if (asSet(c) !== asSet(pageCands[r - 1][k]) || !isPlacement(whiteL(r), c)) candOK = false; }
check('the page’s candidate r k equals Lean’s, and each passes Lean’s IsRookPlacement (checked literally) for every k < r ≤ 20', candOK);

/* ---------- the lean preset ---------- */
await setT(slot(3, 5)); i = await info();
check('r = 5: the page lists exactly Lean’s 5 candidates, in the order of the column-2 rook', i.n === 5 && i.list.every((p, k) => asSet(p) === asSet(candidateL(5, k))));
const wm = wordMatrix(9, whiteL(5));
check('the current placement is a perfect matching of the test’s word graph: 9 across and 9 down words, each used once', i.na === 9 && i.nd === 9 && wm.na === 9 && wm.nd === 9 && new Set(i.cur.map((c) => wm.acr.get(key(...c)))).size === 9 && new Set(i.cur.map((c) => wm.dn.get(key(...c)))).size === 9);
check('readouts: the grid and its words, the count against r, the current placement, the forced words and the family check', (await text('ro1')) === '9 × 9 · 25 · 9 · 9' && (await text('ro2')) === '5 · 5 · 相等' && (await text('ro3')) === '4 / 5 · 9 · 第 6 行' && (await text('ro4')) === '4 · 21 / 21' && (await text('hudBig')) === 'r = 5 · |RP| = 5');

/* ---------- small grids and permutation grids ---------- */
const small = await D2(() => CW_DEBUG.small());
const set2 = new Set(), set3 = new Set(); for (let m = 0; m < 16; m++) set2.add(rookCountLiteral(fromMask(2, m))); for (let m = 0; m < 512; m++) set3.add(rookCountLiteral(fromMask(3, m)));
const sorted = (s) => [...s].sort((a, b) => a - b).join(',');
check('all 2 × 2 and 3 × 3 grids, by Lean’s literal rookCount: {0, 1, 2} and {0, 1, 2, 3, 4, 6}, as the page finds', sorted(set2) === '0,1,2' && sorted(set3) === '0,1,2,3,4,6' && small.grids[0].set.join(',') === '0,1,2' && small.grids[1].set.join(',') === '0,1,2,3,4,6');
check('the 2 × 2 grid whose white cells are its first row has no placement (the dossier lists {1, 2})', rookCountLiteral(new Set(['0,0', '0,1'])) === 0);
const set4 = new Set(); for (let m = 0; m < 1 << 16; m++) set4.add(countRyser(4, fromMask(4, m)));
check('all 4 × 4 grids by Ryser’s permanent: {0 … 8, 10, 12, 14, 18, 24}, as the page and the dossier find', sorted(set4) === '0,1,2,3,4,5,6,7,8,10,12,14,18,24' && small.grids[2].set.join(',') === '0,1,2,3,4,5,6,7,8,10,12,14,18,24');
check('the readout lists the three sets', (await text('ro5')) === '2×2 {0…2} · 3×3 {0…4, 6} · 4×4 {0…8, 10, 12, 14, 18, 24}');
const permsUpTo = (n) => { const out = [], a = Array.from({ length: n }, (_, q) => q + 1), c = new Array(n).fill(0); out.push(a.slice()); let k = 0; while (k < n) { if (c[k] < k) { if (k % 2 === 0) [a[0], a[k]] = [a[k], a[0]]; else [a[c[k]], a[k]] = [a[k], a[c[k]]]; out.push(a.slice()); c[k]++; k = 0; } else { c[k] = 0; k++; } } return out; };
let permOK = true; for (let n = 1; n <= 6; n++) { const s = new Set(permsUpTo(n).map((p) => countRyser(n, permW(p)))); if (sorted(s) !== small.perms[n - 1].set.join(',')) permOK = false; }
check('permutation grids with n ≤ 6: the page’s sets of counts equal the test’s Ryser counts over all permutations', permOK);
check('the maxima for n ≤ 7 are 1, 1, 1, 5, 17, 73, 469 (the refutation dossier) and no count is ≡ 3 (mod 4)', small.perms.map((p) => p.set[p.set.length - 1]).join(',') === '1,1,1,5,17,73,469' && small.perms.every((p) => p.set.every((r) => r % 4 !== 3)) && (await text('ro6')) === '0 个（共 84 个不同值）');
check('the paper’s values: the permutation grids of 263154 and 25143 have 5 and 6 placements (page and Ryser)', (await D2(() => [CW_DEBUG.perm([2, 6, 3, 1, 5, 4]), CW_DEBUG.perm([2, 5, 1, 4, 3])])).join() === '5,6' && countRyser(6, permW([2, 6, 3, 1, 5, 4])) === 5 && countRyser(5, permW([2, 5, 1, 4, 3])) === 6);

/* ---------- other presets ---------- */
await preset('one'); i = await info();
check('r = 1: a 5 × 5 grid with a single white cell and one placement', i.N === 5 && i.white.reduce((a, b) => a + b, 0) === 1 && i.n === 1 && asSet(i.list[0]) === asSet([[0, 2]]));
await preset('three'); i = await info();
check('r = 3: three placements, Lean’s candidates; the one-cell down words (1, 4) and (3, 0) hold rooks in all of them', i.n === 3 && i.list.every((p, k) => asSet(p) === asSet(candidateL(3, k))) && i.list.every((p) => p.some((c) => c[0] === 1 && c[1] === 4) && p.some((c) => c[0] === 3 && c[1] === 0)));
await preset('zero'); i = await info();
check('r = 0: Lean’s zeroWhite has no placement; the rail and readouts say so', i.n === 0 && i.N === 3 && (await text('ro3')) === '没有放法' && (await text('clock')) === '没有放法' && (await D2(() => document.querySelectorAll('#marks i').length)) === 0);
await preset('big'); i = await info();
check('r = 12: a 23 × 23 grid with Lean’s 12 candidates', i.N === 23 && i.n === 12 && i.list.every((p, k) => asSet(p) === asSet(candidateL(12, k))));
await preset('perm'); i = await info();
const pw = permW(LEANWITNESS.map((v) => v + 1));
check('the permutation grid of Lean’s witness [1,6,3,7,0,5,2,4] (2 7 4 8 1 6 3 5) has 155 placements: page and Ryser on the 14 × 14 word matrix', i.N === 8 && asSet(i.white.flatMap((v, q) => (v ? [[Math.floor(q / 8), q % 8]] : []))) === asSet(cellsOfW(pw)) && i.n === 155 && countRyser(8, pw) === 155 && wordMatrix(8, pw).na === 14 && wordMatrix(8, pw).nd === 14);
check('every listed placement passes Lean’s IsRookPlacement (literally) and they are distinct', i.list.every((p) => isPlacement(pw, p)) && new Set(i.list.map(asSet)).size === 155);
check('155 ≡ 3 (mod 4): the readout and HUD report that Conjecture 3.10 fails', 155 % 4 === 3 && (await text('ro2')) === '155 · 3 · ≡ 3，猜想不成立' && (await text('hudBig')) === '|RP| = 155 ≡ 3 (mod 4)' && (await text('pillD')) === 'mod 4 3');

/* ---------- controls ---------- */
await D2(() => { const e = document.getElementById('rIn'); e.value = 7; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the r slider sets r = 7: a 13 × 13 grid with Lean’s 7 candidates, custom settings', i.mode === 'family' && i.N === 13 && i.n === 7 && i.list.every((p, k) => asSet(p) === asSet(candidateL(7, k))) && (await state()).preset === null && /自定义/.test(await text('presetNote')));

/* ---------- labels, rail, keys, playback ---------- */
const boxes = await D2(() => [...document.querySelectorAll('.side .lean')].map((b) => [b.className, b.querySelector('.ok').textContent, b.textContent]));
check('label boxes: two LEAN ✓, NUM, dossier ARGUED, page ARGUED (dashed), OPEN, LIT', boxes.map((b) => b[1]).join(' ') === 'LEAN ✓ LEAN ✓ NUM ARGUED ARGUED OPEN LIT' && /theory/.test(boxes[3][0]) && /page/.test(boxes[4][0]));
check('the LEAN boxes name the frozen declarations', boxes[0][2].includes('CrosswordRookCounts.result') && ['candidate_is_placement', 'placement_eq_candidate', 'candidate_injective', 'zero_rook_count', 'witness_matchingCount', 'CrosswordPermutationGridRefutation.result'].every((s) => boxes[1][2].includes(s)));
check('the NUM box states the page’s sets, the 2 × 2 difference with the dossier and the maxima', ['{0, 1, 2}', '{1, 2}', '469'].every((s) => boxes[2][2].includes(s)));
check('the LIT box cites the paper with its DOI', boxes[6][2].includes('10.48550/arXiv.2609.03081'));
await preset('lean');
check('the rail marks placement 1 and placement 5', (await D2(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === '第 1 种 | 第 5 种');
await setT(0); await D2(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await page.keyboard.press('ArrowRight'); await settle();
check('→ → advances two placements', (await info()).idx === 2 && (await text('clock')) === '第 3 / 5 种');
await page.keyboard.press('ArrowLeft'); await settle();
check('← goes back one placement', (await info()).idx === 1);
await page.keyboard.press('e'); await settle();
check('E jumps to the last placement and pauses', (await info()).idx === 4 && (await state()).playing === false);
await page.keyboard.press(' '); await settle();
check('Space toggles playback', (await state()).playing === true);
await D2(() => document.querySelector('#speedChips [data-speed="2.5"]').click());
check('playing to the end reports the number of placements', await waitToast(/5 种放法：r = 5/));
await pause(); await D2(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['side', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D2(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await setT(slot(1, 5));
const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels: the grid size and the row of the column-2 rook', tags.includes('9 × 9') && tags.includes('中央列的车：第 2 行'), tags);
const lit = await D2(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
await D2(() => window.TRV_THUMB()); await settle();
check('the thumbnail state is the paused first preset at placement 3', (await state()).preset === 'lean' && (await state()).playing === false && (await info()).idx === 2);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'perm']) {
  await preset(p); await setT(0.6);
  const leftovers = await D2(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await D2(() => { const e = document.getElementById('rIn'); e.value = 4; e.dispatchEvent(new Event('input')); }); await settle();
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D2(() => document.title)).startsWith('CROSSWORD//ROOKS · Every natural number is the rook-placement count of a crossword grid'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D2(() => document.getElementById('drawer').hidden)) === false);
check('drawer links both dossiers, both Lean files, the Blueprint, the literature note and arXiv', (await D2(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['lewis-won-crossword-rook-counts.md', 'D5/S3/Combinatorics/CrosswordRookCounts.lean', 'Blueprint/D5/S3/Combinatorics/CrosswordRookCounts.md', 'lewis-won-permutation-grid-counts-refutation.md', 'D5/S3/Combinatorics/CrosswordPermutationGridRefutation.lean', 'Library/Combinatorics/lewis2026crossword.md', 'arxiv.org/abs/2609.03081v1'].every((s) => h.includes(s)); })));
await page.keyboard.press('Escape'); await page.waitForFunction(() => document.getElementById('drawer').hidden === true, null, { timeout: 10000 }).catch(() => {});
check('Esc closes the drawer', (await D2(() => document.getElementById('drawer').hidden)) === true);
await page.waitForFunction(() => document.activeElement?.id === 'infoBtn', null, { timeout: 10000 }).catch(() => {});
check('focus returns to the drawer button', (await D2(() => document.activeElement?.id)) === 'infoBtn');

/* ---------- index round trip ---------- */
const live = readRegistry().visualizations.filter(v => v.status === 'live').length;
await page.click('.crumb'); await page.waitForLoadState('load');
await page.waitForFunction((n) => document.querySelectorAll('.card').length >= n, live, { timeout: 30000 }).catch(() => {});
check('language choice carries to the index', (await D2(() => document.documentElement.dataset.lang)) === 'en');
check('index lists every live visualization', (await D2(() => document.querySelectorAll('.card').length)) === live, `live ${live}`);
await page.click('.card:has(a[href*="crossword-rooks"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.CW_DEBUG && CW_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D2(() => document.body.dataset.vizId)) === 'crossword-rooks');

/* ---------- narrow layouts in both languages ---------- */
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await waitFrames(3);
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await waitFrames(6);
    check(`no horizontal scroll at ${w}px (${lang})`, (await D2(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 });
}
check('no script errors during the whole session', errors.length === 0, errors.slice(0, 3).join(' | '));

await browser.close(); server.close();
const failed = results.filter(r => !r.ok).length;
console.log(`\n${results.length - failed}/${results.length} passed`);
process.exit(failed ? 1 : 0);
