#!/usr/bin/env node
// Browser regression suite for viz/cyclic-arrange (Playwright + Chromium with software WebGL).
//   node tests/cyclic-arrange.test.mjs
// Reads page state through the read-only window.CA_DEBUG probe and checks it against an independent implementation: both
// sides of the cyclic inequality in exact BigInt arithmetic for integer tuples, N* from exact values of sin²(π/n) where
// they are rational and from separated floating comparisons elsewhere, an independent random-direction hill climb in log
// coordinates for the largest ratio, and an exhaustive search for the integer counterexamples with the smallest largest entry.
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
  const start = await page.evaluate(() => CA_DEBUG.frames());
  await page.waitForFunction((f0) => !CA_DEBUG.pending() && CA_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => CA_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => CA_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => CA_DEBUG.info());
const state = () => D(() => CA_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => CA_DEBUG.frames()); await page.waitForFunction((t) => CA_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };
const setAB = async (a, b) => { await D(([a, b]) => { for (const [id, v] of [['aSlider', a], ['bSlider', b]]) { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); } }, [a, b]); await settle(); };

/* ---------- independent implementation ---------- */
function exact(a, b, x) {
  const c = (a + b + 1) / 2, n = x.length, X = x.map(BigInt); let s = 0n, t = 0n, u = 0n;
  for (let i = 0; i < n; i++) { s += X[i]; t += X[i] ** BigInt(a) * X[(i + 1) % n] ** BigInt(b); u += X[i] ** BigInt(c); }
  return { lhs: s * t, rhs: u * u };
}
function myRatio(a, b, x) { const c = (a + b + 1) / 2; let s = 0, t = 0, u = 0; x.forEach((v, i) => { s += v; t += Math.pow(v, a) * Math.pow(x[(i + 1) % x.length], b); u += Math.pow(v, c); }); return u > 0 ? s * t / (u * u) : 0; }
/* N*: sin²(π/n) is rational for n = 2, 3, 4, 6 (1, 3/4, 1/2, 1/4); elsewhere the two sides must differ clearly */
const SIN2 = { 2: 1, 3: 3 / 4, 4: 1 / 2, 6: 1 / 4 };
function myNstar(a, b) {
  let best = 1, ambiguous = false;
  for (let n = 2; n <= 400; n++) {
    const L = (a + b - 1) ** 2, R = 8 * a * b * (SIN2[n] ?? Math.sin(Math.PI / n) ** 2);
    if (!(n in SIN2) && Math.abs(L - R) < 1e-6) ambiguous = true;
    if (L <= R) best = n;
  }
  return { best, ambiguous };
}
/* random-direction hill climb in log coordinates, x₁ = 1 fixed */
function myMax(a, b, n, seed) {
  let s = seed; const rnd = () => ((s = (s * 1664525 + 1013904223) % 4294967296) / 4294967296);
  const f = (y) => myRatio(a, b, [1, ...y.map(Math.exp)]);
  let best = 0;
  for (let start = 0; start < 30; start++) {
    let y = Array.from({ length: n - 1 }, () => (rnd() - 0.5) * 3), fy = f(y), step = 0.5;
    for (let it = 0; it < 4000 && step > 1e-7; it++) {
      const d = y.map(() => rnd() - 0.5), nd = Math.hypot(...d), y2 = y.map((v, j) => v + step * d[j] / nd), f2 = f(y2);
      if (f2 > fy) { y = y2; fy = f2; step *= 1.3; } else step *= 0.93;
    }
    best = Math.max(best, fy);
  }
  return best;
}
/* every violating integer tuple whose largest entry is the smallest possible (≤ cap) */
function myWitnesses(a, b, n, cap) {
  for (let M = 1; M <= cap; M++) {
    const out = [], x = new Array(n).fill(0);
    const rec = (i) => { if (i === n) { if (Math.max(...x) === M) { const e = exact(a, b, x); if (e.lhs > e.rhs) out.push(x.join(',')); } return; } for (let v = 0; v <= M; v++) { x[i] = v; rec(i + 1); } };
    rec(0);
    if (out.length) return { M, set: new Set(out) };
  }
  return null;
}

/* ---------- open ---------- */
await page.goto(origin + BASE + 'viz/cyclic-arrange/');
await page.waitForFunction(() => window.CA_DEBUG && CA_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
const [s0, i0] = await D(() => [CA_DEBUG.state(), CA_DEBUG.info()]); let i = i0;
check('opens on the frozen counterexample: (a, b) = (6, 1), c = 4, playing', s0.preset === 'lean' && i.a === 6 && i.b === 1 && i.c === 4 && s0.playing === true);
await pause();

/* ---------- the frozen counterexample ---------- */
const e655 = exact(6, 1, [6, 5, 5]);
check('(6, 5, 5): left side 6482480, right side 6482116, difference 364 (exact BigInt)', e655.lhs === 6482480n && e655.rhs === 6482116n && e655.lhs - e655.rhs === 364n && i.focus.label === '(6, 5, 5)' && Math.abs(i.focus.ratio - Number(e655.lhs) / Number(e655.rhs)) < 1e-12);
check('the readout writes 6482480 − 6482116 = 364', /\(6, 5, 5\): 6482480 − 6482116 = 364/.test(await text('ro4')));
const ns = myNstar(6, 1);
check('N*(6, 1) = 3: the threshold holds with equality at n = 3 (36 = 48·3/4) and fails from n = 4 on', i.nstar === 3 && ns.best === 3 && 36 === 48 * SIN2[3] && !ns.ambiguous);

/* ---------- N* for other parameters ---------- */
let nsOK = true, nsBad = [];
for (const [a, b] of [[4, 1], [3, 0.5], [1, 1], [2, 1], [3, 1], [0, 0], [2, 0], [8, 4], [0.5, 1], [1.5, 1.5], [5, 2], [7, 0.5]]) {
  await setAB(a, b); const x = await info(), m = myNstar(a, b);
  if (m.ambiguous || x.nstar !== m.best || x.a !== a || x.b !== b) { nsOK = false; nsBad.push(`(${a},${b}) page ${x.nstar} mine ${m.best}${m.ambiguous ? ' ambiguous' : ''}`); }
}
check('N* equals the independent threshold count for 12 parameter pairs (including the equality cases (4, 1) and (2, 1))', nsOK, nsBad.join(' | '));
await setAB(0.5, 0.5); i = await info();
check('a + b = 1 is excluded, as in the conjecture', i.excluded === true && i.nstar === null && /被排除|excluded/.test(await text('ro2')));

/* ---------- the numerical search ---------- */
let srOK = true, srBad = [];
for (const [a, b] of [[6, 1], [4, 1], [3, 0.5], [1, 1]]) {
  await setAB(a, b); const x = await info();
  for (const s of x.search) {
    const back = myRatio(a, b, s.x), mine = myMax(a, b, s.n, 1000 + s.n);
    const fails = s.ratio > 1 + 1e-9, mineFails = mine > 1 + 1e-9;
    /* the reported value is attained at the reported tuple, and the independent climb agrees on failure and on the value */
    if (Math.abs(back - s.ratio) > 1e-12 || fails !== mineFails || Math.abs(mine - s.ratio) > 2e-5 * s.ratio) { srOK = false; srBad.push(`(${a},${b}) n=${s.n} page ${s.ratio.toFixed(6)} mine ${mine.toFixed(6)} at-x ${back.toFixed(6)}`); }
  }
}
check('for (6, 1), (4, 1), (3, ½), (1, 1) and n = 2 … 7 the page’s largest ratios are attained at its tuples and agree with an independent hill climb', srOK, srBad.slice(0, 3).join(' | '));
await setAB(6, 1); i = await info();
/* the inequality is invariant under cyclic rotation, so compare the maximiser with its largest entry moved to the front */
const rot = (x) => { const k = x.indexOf(Math.max(...x)); return [...x.slice(k), ...x.slice(0, k)]; }, m3 = rot(i.search[1].x);
check('(6, 1): the largest ratio at n = 3 is about 1.0177 near (1, 0.779, 0.592) up to rotation, and every n from 3 to 7 fails', Math.abs(i.search[1].ratio - 1.01773) < 1e-5 && Math.abs(m3[1] - 0.779) < 2e-3 && Math.abs(m3[2] - 0.592) < 2e-3 && i.search[0].ratio <= 1 + 1e-9 && i.search.slice(1).every((s) => s.ratio > 1) && i.numericN === 2, m3.map((v) => v.toFixed(3)).join(', '));
await setAB(4, 1); i = await info();
check('(4, 1): N* = 4 with equality, n = 3 holds numerically, n = 4 fails (largest ratio ≈ 1.000188)', i.nstar === 4 && myNstar(4, 1).best === 4 && 16 === 32 * SIN2[4] && i.search[1].ratio <= 1 + 1e-9 && Math.abs(i.search[2].ratio - 1.000188) < 2e-6 && i.numericN === 3);

/* ---------- integer counterexamples ---------- */
const wx = (x) => (x.witness && x.witness.x ? x.witness.x.join(',') : 'none');
const w61 = myWitnesses(6, 1, 3, 12), w41 = myWitnesses(4, 1, 4, 10);
await setAB(6, 1); i = await info();
check('(6, 1), n = 3: the page’s witness has the smallest possible largest entry (4) and violates the inequality by 1409', w61 && w61.M === 4 && i.witness && i.witness.n === 3 && w61.set.has(wx(i)) && i.witness.diff === String(exact(6, 1, i.witness.x || [0]).lhs - exact(6, 1, i.witness.x || [0]).rhs) && wx(i) === '2,4,3' && i.witness.diff === '1409', w61 ? `M = ${w61.M}, ${w61.set.size} tuples` : '');
await setAB(4, 1); i = await info();
check('(4, 1), n = 4: the page’s witness has the smallest possible largest entry (10) and violates the inequality by 327', w41 && w41.M === 10 && i.witness && i.witness.n === 4 && w41.set.has(wx(i)) && wx(i) === '7,7,10,9' && i.witness.diff === '327', w41 ? `M = ${w41.M}, ${w41.set.size} tuples` : '');
await setAB(3, 0.5); i = await info();
check('(3, ½): no exact search when c is not an integer, and the readout says so', i.witness && i.witness.n === 4 && i.witness.x === null && /整数|integer/.test(await text('ro5')));

/* ---------- the triangle ---------- */
await preset('lean'); i = await info();
let gridMax = 0; for (let p = 0; p <= 48; p++) for (let q = 0; p + q <= 48; q++) gridMax = Math.max(gridMax, myRatio(6, 1, [p / 48, q / 48, (48 - p - q) / 48]));
check('the 3D triangle is a 48-step grid whose largest ratio matches an independent evaluation', i.tri === 48 && Math.abs(i.triMax.r - gridMax) < 1e-12, gridMax.toFixed(6));
check('the readout note gives that grid maximum', (await text('roNote')).includes(gridMax.toFixed(5)));

/* ---------- presets, controls, timeline ---------- */
for (const p of ['lean', 'small', 'max', 'four', 'holds', 'one']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
await preset('small'); i = await info();
check('small preset: the amber point is (2, 4, 3) with ratio about 1.0113', i.focus.label === '(2, 4, 3)' && Math.abs(i.focus.ratio - myRatio(6, 1, [2, 4, 3])) < 1e-12);
await preset('max'); i = await info();
check('max preset: the amber point is the numerical maximum at n = 3', Math.abs(i.focus.ratio - i.search[1].ratio) < 1e-12);
await preset('four');
check('four preset: the readout gives (7, 7, 10, 9) · 327 at n = 4', /n = 4: \(7, 7, 10, 9\) · 327/.test(await text('ro5')));
await preset('one'); i = await info();
check('one preset: (1, 1) gives N* = 8 and nothing fails up to n = 7', i.nstar === 8 && i.numericN === 7 && i.witness === null);
await setAB(5, 2);
check('the sliders mark the settings custom', (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')) && (await text('aVal')) === '5' && (await text('bVal')) === '2');
await preset('lean'); await setFrac(0.5);
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ turns the view by 15°', Math.abs((await state()).nowFrac - 13 / 24) < 1e-9);
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await state()).nowFrac === 1 && (await state()).playing === false);
await setFrac(0.9); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing to the end reports that n = 3 already fails although N* = 3', await waitToast(/猜想说 N\* = 3.*n = 3 已经失败/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'four']) {
  await preset(p);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await setAB(2, 1);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('CYCLIC//ARRANGE · Javaheri’s cyclic arrangement conjecture fails at (6, 1)'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, arXiv and the DOI', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['javaheri-2026-cyclic-arrangement-conjecture-refutation.md', 'D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.lean', 'Blueprint/D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.md', 'Library/Certificates/javaheri2026arrangement.md', 'arxiv.org/abs/2610.33653v1', 'doi.org/10.48550/arXiv.2610.33653'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="cyclic-arrange"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.CA_DEBUG && CA_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'cyclic-arrange');

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
