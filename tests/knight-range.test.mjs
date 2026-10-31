#!/usr/bin/env node
// Browser regression suite for viz/knight-range (Playwright + Chromium with software WebGL).
//   node tests/knight-range.test.mjs
// Reads page state through the read-only window.KN_DEBUG probe and checks it against independent sources: the OEIS terms of
// A309221, A326954 and A326955, Lean's move table and its symmetry maps sym / latFun transcribed, and the test's own
// enumeration of all walks as base-8 numbers with explicit sets of visited squares.
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
  const start = await page.evaluate(() => KN_DEBUG.frames());
  await page.waitForFunction((f0) => !KN_DEBUG.pending() && KN_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D2(() => KN_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D2((t) => KN_DEBUG.setT(t), t); await settle(); };
const info = () => D2(() => KN_DEBUG.info());
const state = () => D2(() => KN_DEBUG.state());
const text = (id) => D2((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D2(() => KN_DEBUG.frames()); await page.waitForFunction((t) => KN_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */

/* Lean's tables */
const MOVE = [[1, 2], [2, 1], [2, -1], [1, -2], [-1, -2], [-2, -1], [-2, 1], [-1, 2]];
const symL = (m, i) => (m % 2 === 0 ? (m + i) % 8 : ((m - i) % 8 + 8) % 8);
const latL = (m, [x, y]) => (m % 2 === 0 ? (m === 0 ? [x, y] : m === 2 ? [y, -x] : m === 4 ? [-x, -y] : [-y, x]) : (m === 1 ? [y, x] : m === 3 ? [x, -y] : m === 5 ? [-y, -x] : [-x, y]));
/* OEIS A309221 a(0..8), A326954 / A326955 E(n) numerators and denominators for n = 0..8 */
const A309221 = [1, 2, 23, 240, 2355, 22320, 205942, 1866592, 16664147];
const NUM = [1, 2, 23, 15, 2355, 1395, 102971, 58331, 16664147], DEN = [1, 1, 8, 4, 512, 256, 16384, 8192, 2097152];
/* every walk as an n-digit base-8 number; visited squares as an explicit set */
function brute(n) {
  const cls = new Array(8).fill(0), hist = new Array(n + 2).fill(0);
  for (let code = 0; code < 8 ** n; code++) {
    let c = code, x = 0, y = 0; const seen = new Set(['0,0']); let first = 0;
    for (let k = 0; k < n; k++) { const m = c % 8; c = Math.floor(c / 8); if (k === 0) first = m; x += MOVE[m][0]; y += MOVE[m][1]; seen.add(`${x},${y}`); }
    cls[first] += seen.size; hist[seen.size]++;
  }
  return { S: cls.reduce((a, b) => a + b, 0), cls, hist };
}
const posOf = (w) => { const out = [[0, 0]]; let x = 0, y = 0; for (const m of w) { x += MOVE[m][0]; y += MOVE[m][1]; out.push([x, y]); } return out; };

await page.goto(`${origin}${BASE}viz/knight-range/`);
await page.waitForFunction(() => window.KN_DEBUG && KN_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();
check('starts on the first preset (n = 6), playing from the start', st.preset === 'lean' && st.playing === true && i.n === 6);
await pause(); await setT(1); i = await info();

/* ---------- Lean's symmetry lemma ---------- */
let latOK = true, symOK = true;
for (let m = 0; m < 8; m++) { const img = new Set(); for (let k = 0; k < 8; k++) { const [a, b] = latL(m, MOVE[k]), [c, d] = MOVE[symL(m, k)]; if (a !== c || b !== d) latOK = false; img.add(symL(m, k)); } if (img.size !== 8 || symL(m, 0) !== m) symOK = false; }
check('Lean’s lat m sends move i to move (sym m i) for all 64 pairs, and sym m is a permutation with sym m 0 = m', latOK && symOK);
const pageSym = await D2(() => { const o = []; for (let m = 0; m < 8; m++) for (let k = 0; k < 8; k++) o.push([KN_DEBUG.sym(m, k), KN_DEBUG.symInv(m, KN_DEBUG.sym(m, k))]); return o; });
check('the page’s sym equals Lean’s, and symInv undoes it', pageSym.every(([s, back], q) => s === symL(Math.floor(q / 8), q % 8) && back === q % 8) && JSON.stringify(await D2(() => KN_DEBUG.MOVES)) === JSON.stringify(MOVE));

/* ---------- the eight images of the walk ---------- */
const W0 = i.walk, base = posOf(W0), firsts = i.copies.map((c) => c.w[0]);
check('the eight paths start with the eight different moves 0 … 7', firsts.join('') === '01234567');
const asLat = i.copies.every((c, m) => { const g = symL(m, 0); /* the lattice map taking the original to copy m is lat(m) ∘ lat(w₀)⁻¹; check positions via the moves */ return c.pos.every((p, k) => { const q = posOf(c.w)[k]; return p[0] === q[0] && p[1] === q[1]; }) && c.w.every((mm, k) => { const [a, b] = MOVE[mm], [x0, y0] = MOVE[W0[k]]; const L = (v) => latL(m, inverseLat(W0[0], v)); const [u, v] = L([x0, y0]); return a === u && b === v; }); });
function inverseLat(m, v) { for (const cand of [[v[0], v[1]], [v[1], -v[0]], [-v[0], -v[1]], [-v[1], v[0]], [v[1], v[0]], [v[0], -v[1]], [-v[1], -v[0]], [-v[0], v[1]]]) { const r = latL(m, cand); if (r[0] === v[0] && r[1] === v[1]) return cand; } return null; }
check('each path is the original moved by the lattice symmetry lat(m) ∘ lat(w₀)⁻¹, step by step', asLat);
check('all eight paths visit the same number of squares, equal to the original’s (independent set count)', i.copies.every((c) => c.range === new Set(base.map((p) => p.join())).size));

/* ---------- the totals ---------- */
check('S(6) = 1647536 and the eight class totals are all 205942 = a(6) (OEIS A309221)', i.S === 1647536 && i.cls.every((v) => v === 205942) && i.a === 205942 && i.oeis === '205942');
check('E(6) is reduced to 102971/16384, A326954(6)/A326955(6)', i.exact[0] === '102971' && i.exact[1] === '16384');
const pageEnum = await D2(() => [1, 2, 3, 4, 5, 6, 7].map((n) => KN_DEBUG.enumerate(n)));
let bruteOK = true;
for (let n = 1; n <= 5; n++) { const b = brute(n), p = pageEnum[n - 1]; if (b.S !== p.S || b.cls.join() !== p.cls.join() || b.hist.join() !== p.hist.join()) bruteOK = false; }
check('for n ≤ 5 the page’s totals, class totals and range distribution equal the test’s base-8 enumeration', bruteOK);
check('for n ≤ 7, S(n)/8 equals OEIS A309221 and every class total equals it', pageEnum.every((e, k) => e.S === 8 * A309221[k + 1] && e.cls.every((v) => v === A309221[k + 1])));
check('for every n ≤ 7 and every r, the number of walks visiting r squares is 8 × that among walks starting with (1, 2)', pageEnum.every((e) => e.hist.every((h, r) => h === 8 * e.hist0[r])));

/* ---------- readouts ---------- */
check('readouts: steps and walks; S(n), a(n) and OEIS; E(n); the class totals', (await text('ro1')) === '6 · 262 144' && (await text('ro2')) === '1 647 536 · 205 942 · 205 942 ✓' && (await text('ro3')) === '102971/16384 ≈ 6.284851' && (await text('ro4')) === '205 942 · 205 942');
check('the HUD states S(n) = 8 × a(n)', (await text('hudBig')) === 'n = 6 · S(n) = 1 647 536 = 8 × 205 942');

/* ---------- other presets ---------- */
await preset('two'); i = await info();
check('n = 2: 8 walks visit 2 squares, 56 visit 3, S = 184 = 8 × 23, E = 23/8', i.hist[2] === 8 && i.hist[3] === 56 && i.S === 184 && i.exact.join('/') === '23/8' && i.copies.every((c) => c.range === 2));
await preset('back'); i = await info();
check('back and forth: all eight paths visit 2 squares', i.walk.join('') === '040404' && i.copies.every((c) => c.range === 2));
await preset('star'); i = await info();
check('the star: eight straight paths of 6 squares each', i.copies.every((c, m) => c.range === 6 && c.w.every((x) => x === m)));
await preset('eight'); i = await info();
check('n = 8: S(8) = 133313176 = 8 × 16664147 = 8 × OEIS a(8); E(8) = 16664147/2097152', i.S === 133313176 && i.a === 16664147 && i.oeis === '16664147' && i.exact.join('/') === `${NUM[8]}/${DEN[8]}` && i.cls.every((v) => v === 16664147));
const exacts = await D2(() => { const out = []; for (let n = 1; n <= 7; n++) { const e = KN_DEBUG.enumerate(n); out.push(e.S); } return out; });
const g = (a, b) => { while (b) [a, b] = [b, a % b]; return a; };
check('for n ≤ 7, S(n)/8ⁿ reduces to A326954(n)/A326955(n)', exacts.every((S, k) => { const n = k + 1, d = 8 ** n, q = g(S, d); return S / q === NUM[n] && d / q === DEN[n]; }));

/* ---------- controls ---------- */
await preset('lean');
await D2(() => { const e = document.getElementById('nIn'); e.value = 3; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the n slider sets n = 3: S = 1920, a = 240, custom settings', i.n === 3 && i.walk.length === 3 && i.S === 1920 && i.a === 240 && (await state()).preset === null && /自定义/.test(await text('presetNote')));
const w1 = (await info()).walk.join('');
await click('#walkBtn'); i = await info();
check('“Another path” draws a new walk with the same n and reports its range', i.walk.length === 3 && (await state()).seed === 4 && await waitToast(new RegExp(`访问 ${i.copies[0].range} 格`)), `${w1} → ${i.walk.join('')}`);

/* ---------- labels, rail, keys, playback ---------- */
const boxes = await D2(() => [...document.querySelectorAll('.side .lean')].map((b) => [b.className, b.querySelector('.ok').textContent, b.textContent]));
check('label boxes: two LEAN ✓, NUM, dossier ARGUED, page ARGUED (dashed), OPEN, LIT', boxes.map((b) => b[1]).join(' ') === 'LEAN ✓ LEAN ✓ NUM ARGUED ARGUED OPEN LIT' && /theory/.test(boxes[3][0]) && /page/.test(boxes[4][0]));
check('the LEAN boxes name the frozen declarations', boxes[0][2].includes('KnightWalkRangeIntegrality.result') && boxes[1][2].includes('latFun') && boxes[1][2].includes('symInv'));
check('the LIT box cites A309221 and A326954 / A326955', boxes[6][2].includes('A309221') && boxes[6][2].includes('A326954'));
await preset('lean');
check('the rail marks the start and step 6', (await D2(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === '起点 | 第 6 步');
await setT(0); await D2(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await page.keyboard.press('ArrowRight'); await settle();
check('→ → advances two steps', Math.abs((await info()).j - 2) < 1e-9 && (await text('clock')) === '第 2 步');
await page.keyboard.press('ArrowLeft'); await settle();
check('← goes back one step', Math.abs((await info()).j - 1) < 1e-9);
await page.keyboard.press('e'); await settle();
check('E jumps to the last step and pauses', (await info()).j === 6 && (await state()).playing === false);
await page.keyboard.press(' '); await settle();
check('Space toggles playback', (await state()).playing === true);
await D2(() => document.querySelector('#speedChips [data-speed="2.5"]').click());
check('playing to the end reports that the eight paths visit the same number of squares', await waitToast(/八条路径各访问 6 格/));
await pause(); await D2(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['side', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D2(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await setT(0.5);
const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels mark the start and the common range', tags.includes('起点') && tags.includes('八条路径 · 各访问 6 格'), tags);
const lit = await D2(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
await D2(() => window.TRV_THUMB()); await settle();
check('the thumbnail state is the paused first preset at the last step', (await state()).preset === 'lean' && (await state()).playing === false && (await info()).j === 6);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'star']) {
  await preset(p); await setT(0.5);
  const leftovers = await D2(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#walkBtn');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D2(() => document.title)).startsWith("KNIGHT//RANGE · The expected range of a knight's random walk times 2^(3n−3) is an integer"));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D2(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note and the two OEIS entries', (await D2(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['sloane-2019-a309221-knight-walk-range-integrality.md', 'D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.lean', 'Blueprint/D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.md', 'Library/Combinatorics/sloane2019a309221.md', 'oeis.org/A309221', 'oeis.org/A326954'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="knight-range"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.KN_DEBUG && KN_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D2(() => document.body.dataset.vizId)) === 'knight-range');

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
