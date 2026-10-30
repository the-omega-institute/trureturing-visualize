#!/usr/bin/env node
// Browser regression suite for viz/carryless-pairs (Playwright + Chromium with software WebGL).
//   node tests/carryless-pairs.test.mjs
// Reads page state through the read-only window.CL_DEBUG probe and checks it against an independent implementation: the
// carryless product from its definition as a GF(2) convolution of bits, the solution sets recomputed and compared with the
// data of the OEIS entries, and the automaton states derived from prefixes of k (the carry of m·r and the high part of
// C(u, r) beyond the low bits r), not from the page's step rule.
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
  const start = await page.evaluate(() => CL_DEBUG.frames());
  await page.waitForFunction((f0) => !CL_DEBUG.pending() && CL_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => CL_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setK = async (k) => { await D((k) => CL_DEBUG.setFrac(k / (CL_DEBUG.info().K - 1)), k); await settle(); };
const info = () => D(() => CL_DEBUG.info());
const state = () => D(() => CL_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => CL_DEBUG.frames()); await page.waitForFunction((t) => CL_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- independent implementation ---------- */
/* bit t of C(u, k) is the parity of Σ_{i ≤ t} bitᵢ(u)·bit_{t−i}(k) */
function conv(u, k) {
  const U = [], K = []; for (let x = u; x > 0; x = Math.floor(x / 2)) U.push(x % 2); for (let x = k; x > 0; x = Math.floor(x / 2)) K.push(x % 2);
  let out = 0n;
  for (let t = 0; t < U.length + K.length; t++) { let s = 0; for (let i = 0; i <= t; i++) s += (U[i] || 0) * (K[t - i] || 0); if (s % 2) out += 1n << BigInt(t); }
  return out;
}
const holds = ([m, u], k) => BigInt(m) * BigInt(k) === conv(u, k);
const THEOREMS = {
  A115801: { e1: [9, 25], e2: [15, 19], kind: 'iff' }, A115770: { e1: [7, 11], e2: [5, 13], kind: 'iff' },
  A115803: { e1: [13, 29], e2: [11, 31], kind: 'imp' }, A115809: { e1: [17, 49], e2: [9, 25], kind: 'imp' }
};
/* OEIS data (fetched from oeis.org; revision numbers as stated) */
const OEIS = {
  A115801: [0, 15, 30, 31, 60, 62, 63, 120, 124, 126, 127, 240, 248, 252, 254, 255, 480, 496, 504, 508, 510, 511, 960, 992, 1008, 1016, 1020, 1022, 1023, 1920, 1984, 2016, 2032, 2040, 2044, 2046, 2047, 3840, 3855, 3968, 4032, 4064, 4080, 4088, 4092, 4094, 4095],
  A115770: [0, 7, 14, 15, 28, 30, 31, 56, 60, 62, 63, 112, 120, 124, 126, 127, 224, 240, 248, 252, 254, 255, 448, 455, 480, 496, 504, 508, 510, 511, 896, 903, 910, 911, 960, 967, 992, 1008, 1016, 1020, 1022, 1023, 1792, 1799, 1806, 1807, 1820, 1822, 1823, 1920, 1927, 1934, 1935, 1984, 1991, 2016, 2032, 2040, 2044, 2046, 2047, 3584, 3591],
  A115803: [0, 3, 6, 12, 15, 24, 27, 30, 31, 48, 51, 54, 60, 62, 63, 96, 102, 108, 120, 124, 126, 127, 192, 195, 204, 207, 216, 219, 240, 243, 248, 252, 254, 255, 384, 387, 390, 403, 408, 411, 414, 415, 432, 435, 438, 480, 486, 496, 499, 504, 508, 510, 511, 768, 771, 774, 780, 783, 806, 816, 819, 822, 828, 830, 831, 864, 870],
  A115805: [0, 3, 6, 12, 24, 48, 96, 192, 195, 384, 387, 390, 768, 771, 774, 780, 1536, 1539, 1542, 1548, 1560, 3072, 3075, 3078, 3084, 3096, 3120],
  A115809: [0, 31, 62, 63, 124, 126, 127, 248, 252, 254, 255, 496, 504, 508, 510, 511, 992, 1008, 1016, 1020, 1022, 1023, 1984, 2016, 2032, 2040, 2044, 2046, 2047, 3968, 4032, 4064, 4080, 4088, 4092, 4094, 4095]
};
/* the state after the low L bits r of k: the carry of m·r and the part of C(u, r) above bit L, or rejected if the low L bits
   of the two products differ */
function prefixState([m, u], r, L) {
  const P = BigInt(m) * BigInt(r), Q = conv(u, r), mask = (1n << BigInt(L)) - 1n;
  return (P & mask) === (Q & mask) ? `(${P >> BigInt(L)}, ${Q >> BigInt(L)})` : '∅';
}
const pairState = (T, r, L) => `${prefixState(T.e1, r, L)}|${prefixState(T.e2, r, L)}`;

/* ---------- open ---------- */
await page.goto(origin + BASE + 'viz/carryless-pairs/');
await page.waitForFunction(() => window.CL_DEBUG && CL_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
const [s0, i0] = await D(() => [CL_DEBUG.state(), CL_DEBUG.info()]); let i = i0;
check('opens on A115801 (9k = C(25, k) ⇔ 15k = C(19, k)), k < 2¹⁰, playing', s0.preset === 'nine' && i.mod === 'A115801' && i.len === 10 && s0.playing === true && JSON.stringify([i.e1, i.e2]) === '[[9,25],[15,19]]' && i.kind === 'iff');
await pause();

/* ---------- the theorems themselves ---------- */
let thmOK = true, thmBad = [];
for (const [id, T] of Object.entries(THEOREMS)) for (let k = 0; k < 65536; k++) { const a = holds(T.e1, k), b = holds(T.e2, k); if (T.kind === 'iff' ? a !== b : a && !b) { thmOK = false; thmBad.push(`${id} k=${k}`); break; } }
check('all four relations hold for every k < 2¹⁶ with the convolution definition', thmOK, thmBad.join(' '));

/* ---------- solution sets ---------- */
const OE = { A115801: ['A115801', 'A115801'], A115770: ['A115770', 'A115770'], A115803: ['A115805', 'A115803'], A115809: ['A115809', 'A115801'] };
let setOK = true, oeisOK = true, setBad = [];
for (const id of Object.keys(THEOREMS)) {
  await click(`#modChips [data-mod="${id}"]`); await click('#lenChips [data-len="12"]');
  const T = THEOREMS[id], p1 = await D(() => CL_DEBUG.members(1)), p2 = await D(() => CL_DEBUG.members(2)), x = await info();
  const m1 = [], m2 = []; for (let k = 0; k < 4096; k++) { if (holds(T.e1, k)) m1.push(k); if (holds(T.e2, k)) m2.push(k); }
  if (p1.join() !== m1.join() || p2.join() !== m2.join() || x.c1 !== m1.length || x.c2 !== m2.length || x.bad !== 0) { setOK = false; setBad.push(id); }
  /* the OEIS data below 2¹² is an initial segment of the page's sets (the second OEIS entry is the second equation) */
  const [o1, o2] = OE[id].map((o) => OEIS[o].filter((k) => k < 4096));
  if (o1.join() !== p1.slice(0, o1.length).join() || o2.join() !== p2.slice(0, o2.length).join()) { oeisOK = false; setBad.push(`${id} OEIS`); }
}
check('for k < 2¹² the page’s two solution sets equal the convolution recount in every module, with no disagreement', setOK, setBad.join(' '));
check('those sets begin with the OEIS data of A115801, A115770, A115805/A115803 and A115809/A115801', oeisOK);

/* ---------- the product automaton ---------- */
let autoOK = true, clsOK = true, autoBad = [];
for (const id of Object.keys(THEOREMS)) {
  await click(`#modChips [data-mod="${id}"]`);
  const T = THEOREMS[id], A = await D(() => CL_DEBUG.automaton()), x = await info();
  const pageSet = new Set(A.nodes.map(([a, b]) => `${a ? `(${a[0]}, ${a[1]})` : '∅'}|${b ? `(${b[0]}, ${b[1]})` : '∅'}`));
  const mine = new Set(); for (let L = 0; L <= 14; L++) for (let r = 0; r < 2 ** L; r++) mine.add(pairState(T, r, L));
  if (mine.size !== pageSet.size || [...mine].some((s) => !pageSet.has(s)) || A.edges.length !== 2 * A.nodes.length) { autoOK = false; autoBad.push(`${id}: page ${pageSet.size} mine ${mine.size}`); }
  /* classification: a side holds at the end exactly when its state is (c, c) */
  const acc = (s) => { const m = /^\((\d+), (\d+)\)$/.exec(s); return !!m && m[1] === m[2]; };
  const cls = [...pageSet].map((s) => { const [a, b] = s.split('|'); return acc(a) && acc(b) ? 'both' : acc(a) ? 'first' : acc(b) ? 'second' : a === '∅' && b === '∅' ? 'dead' : 'alive'; });
  const count = (arr) => arr.reduce((o, c) => { o[c] = (o[c] || 0) + 1; return o; }, {});
  if (JSON.stringify(Object.entries(count(cls)).sort()) !== JSON.stringify(Object.entries(x.classes).sort()) || cls.includes('first') || (T.kind === 'iff' && cls.includes('second'))) { clsOK = false; autoBad.push(`${id} classes`); }
}
check('the page’s automaton states are exactly the states reached by prefixes of up to 14 bits (29, 15, 50, 101 of them), two edges each', autoOK, autoBad.join(' | '));
check('no state accepts only the first equation, and the equivalences have no state accepting only the second', clsOK);
let sizes = []; for (const id of Object.keys(THEOREMS)) { await click(`#modChips [data-mod="${id}"]`); sizes.push((await info()).states); }
check('reachable state counts are 29, 15, 50 and 101, as the readout says (the sizes of Lean’s related sets)', sizes.join() === '29,15,50,101' && /29 · 58 · 29|15 · 30 · 15|50 · 100 · 50|101 · 202 · 101/.test(await text('ro5')), sizes.join());

/* ---------- paths and products ---------- */
let pathOK = true, pathBad = [];
for (const [id, k] of [['A115801', 15], ['A115801', 511], ['A115770', 455], ['A115803', 15], ['A115809', 248], ['A115809', 37]]) {
  await click(`#modChips [data-mod="${id}"]`); await click('#lenChips [data-len="10"]'); await setK(k);
  const x = await info(), T = THEOREMS[id], L = k === 0 ? 0 : Math.floor(Math.log2(k)) + 1;
  const mine = []; for (let l = 0; l <= L; l++) mine.push(pairState(T, k % 2 ** l, l));
  if (x.k !== k || x.path.join(' ') !== mine.join(' ') || x.p1 !== String(BigInt(T.e1[0]) * BigInt(k)) || x.cl1 !== String(conv(T.e1[1], k)) || x.p2 !== String(BigInt(T.e2[0]) * BigInt(k)) || x.cl2 !== String(conv(T.e2[1], k))) { pathOK = false; pathBad.push(`${id} k=${k}`); }
}
check('the path of k through the automaton is the sequence of its prefix states, and the four products match the convolution', pathOK, pathBad.join(' '));

/* ---------- presets ---------- */
await preset('member'); i = await info();
check('member preset: k = 15, 9·15 = 135 = C(25, 15) and 15·15 = 225 = C(19, 15), ending in a both-hold state', i.k === 15 && i.p1 === '135' && i.cl1 === '135' && i.p2 === '225' && i.cl2 === '225' && i.end === 'both' && conv(25, 15) === 135n && conv(19, 15) === 225n);
await preset('converse'); i = await info();
check('converse preset: 11·15 = 165 = C(31, 15) but 13·15 = 195 ≠ C(29, 15) = 187, ending in a second-only state', i.mod === 'A115803' && i.k === 15 && i.p1 === '195' && i.cl1 === '187' && i.p2 === '165' && i.cl2 === '165' && i.end === 'second' && conv(29, 15) === 187n && conv(31, 15) === 165n);
for (const p of ['nine', 'seven', 'member', 'contain', 'seventeen', 'converse']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
await click('#lenChips [data-len="8"]');
check('module and range chips mark the settings custom', (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')) && (await info()).K === 256);
await preset('nine');
check('the rail marks k = 0, 2⁹ and 2¹⁰ − 1', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 'k = 0 | k = 2^9 | k = 2^10 − 1');
await setK(100);
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps k by one', (await info()).k === 101);
await page.keyboard.press('e'); await settle();
check('E jumps to k = 2¹⁰ − 1 and pauses', (await info()).k === 1023 && (await state()).playing === false);
await D(() => CL_DEBUG.setFrac(0.97)); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing to the end reports the two counts and the equality', await waitToast(/2\^10.*第一条 29 个，第二条 29 个，两个集合相同/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
check('the readouts give both equations for the current k', /9·\d+ = \d+ · C\(25, \d+\) = \d+/.test(await text('ro3')) && /15·\d+ = \d+ · C\(19, \d+\) = \d+/.test(await text('ro4')));
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['nine', 'converse']) {
  await preset(p);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#lenChips [data-len="12"]');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('CARRYLESS//PAIRS · Ordinary against carryless multiplication: four OEIS conjectures'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the four dossiers, the four Lean files, the Blueprint and the OEIS entries', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['oeis-a115801-carryless-multiplier-equivalence.md', 'oeis-a115770-carryless-seven-five-equivalence.md', 'oeis-a115803-carryless-thirteen-eleven-containment.md', 'oeis-a115809-carryless-seventeen-nine-containment.md', 'CarrylessMultiplierEquivalence.lean', 'CarrylessSevenFiveEquivalence.lean', 'CarrylessThirteenElevenContainment.lean', 'CarrylessSeventeenNineContainment.lean', 'Blueprint/D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.md', 'oeis.org/A115801', 'oeis.org/A115770', 'oeis.org/A115803', 'oeis.org/A115805', 'oeis.org/A115809', 'oeis.org/A048720'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="carryless-pairs"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.CL_DEBUG && CL_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'carryless-pairs');

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
