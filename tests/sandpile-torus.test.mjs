#!/usr/bin/env node
// Browser regression suite for viz/sandpile-torus (Playwright + Chromium with software WebGL).
//   node tests/sandpile-torus.test.mjs
// Reads page state through the read-only window.SP_DEBUG probe and checks it against an independent implementation: the
// test's own transcription of Lean's initial, neighbours, topple, run, Legal and Stable on the n × 1 torus, A023855 from
// Lean's definition, the OEIS data terms, replays of the page's toppling sequences, and the test's own random orders.
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
  const start = await page.evaluate(() => SP_DEBUG.frames());
  await page.waitForFunction((f0) => !SP_DEBUG.pending() && SP_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => SP_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D((t) => SP_DEBUG.setT(t), t); await settle(); };
const info = () => D(() => SP_DEBUG.info());
const state = () => D(() => SP_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => SP_DEBUG.frames()); await page.waitForFunction((t) => SP_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */

/* ---------- independent implementation: Lean's definitions on the n × 1 torus ---------- */
const initial = (n) => Array.from({ length: n }, (_, i) => (i === 0 ? 0 : 4));
const neighbours = (n, p) => [(p + 1) % n, (p - 1 + n) % n, p, p];
/* topple c p q = c q − (if q = p then 4 else 0) + (if q = 0 then 0 else count of q in neighbours p) */
const toppleL = (n, c, p) => c.map((x, q) => x - (q === p ? 4 : 0) + (q === 0 ? 0 : neighbours(n, p).filter((r) => r === q).length));
/* replays a sequence: legal if every toppled cell holds ≥ 4 at its turn; returns the run, the odometer and the minimum slack v ≤ u */
function replay(n, seq) {
  let c = initial(n); const v = new Array(n).fill(0); let legal = true, lost = 0, leastAction = true;
  for (const p of seq) { if (c[p] < 4) legal = false; const before = c.reduce((s, x) => s + x, 0); c = toppleL(n, c, p); lost += before - c.reduce((s, x) => s + x, 0) - 0; v[p]++; if (v[p] > uRef(n, p)) leastAction = false; }
  return { c, v, legal, stable: c.every((x) => x < 4), lost, leastAction };
}
const a023855 = (m) => { let s = 0; for (let j = 1; j <= Math.floor((m + 1) / 2); j++) s += j * (m + 1 - j); return s; };
const uRef = (n, x) => (x * (n - x) + (n % 2 === 0 ? Math.min(x, n - x) : 0)) / 2;
/* the test's own random legal order, by a different generator from the page's */
function randomRun(n, seed) { let c = initial(n), s = seed >>> 0; const seq = []; const rnd = () => { s = (s * 1664525 + 1013904223) >>> 0; return s / 2 ** 32; };
  for (;;) { const U = []; for (let i = 1; i < n; i++) if (c[i] >= 4) U.push(i); if (!U.length) break; const p = U[Math.floor(rnd() * U.length)]; c = toppleL(n, c, p); seq.push(p); } return { seq, c }; }
const OEIS = [0, 1, 2, 7, 10, 22, 28, 50, 60, 95];

await page.goto(`${origin}${BASE}viz/sandpile-torus/`);
await page.waitForFunction(() => window.SP_DEBUG && SP_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();

/* ---------- the theorem on the page's runs ---------- */
check('opens on n = 10, leftmost order, 95 topplings', st.preset === 'lean' && i.n === 10 && i.order === 'left' && i.T === 95 && i.a === 95);
let seq = await D(() => SP_DEBUG.seq());
let R = replay(10, seq);
check('the page’s 95 topplings are a legal sequence for the test’s transcription of Lean’s topple, ending in a stable state', R.legal && R.stable && seq.length === 95);
check('the final state is 3 grains everywhere, 2 at x = 5, and every cell toppled exactly u(x) times', R.c.join('') === '0333323333' && i.final.join('') === R.c.join('') && R.v.every((v, x) => v === uRef(10, x)) && i.finalV.join() === R.v.join() && i.u.every((u, x) => u === uRef(10, x)));
check('least action along the page’s sequence: no cell ever exceeds u(x)', R.leastAction);
const sums = Array.from({ length: 79 }, (_, j) => { const n = j + 2; let s = 0; for (let k = 1; k <= Math.floor(n / 2); k++) s += k * (n - k); return s; });
check('A023855(n − 1) by Lean’s definition equals Σ_{1 ≤ j ≤ ⌊n/2⌋} j(n − j) for n = 2 … 80', sums.every((s, j) => s === a023855(j + 1)));
const colL = await D(() => SP_DEBUG.column('left'));
check('the page’s column (leftmost order) reproduces the ten OEIS data terms 0, 1, 2, 7, 10, 22, 28, 50, 60, 95', OEIS.slice(1).every((t, j) => colL[j] === t) && OEIS.every((t, j) => j === 0 ? t === 0 : t === a023855(j)));
check('the printed identity T(n,1) = A023855(n) fails at every n = 1 … 80, the corrected one holds', [0, ...colL].every((t, j) => t !== a023855(j + 1)) && colL.every((t, j) => t === a023855(j + 1)));
let colOK = true; for (const o of ['left', 'right', 'max', 'random', 'parallel']) { const col = await D((o) => SP_DEBUG.column(o), o); if (!col.every((t, j) => t === sums[j])) colOK = false; }
check('every order rule gives A023855(n − 1) for every n = 2 … 80 (page simulations)', colOK);
let ownOK = true; for (let n = 2; n <= 40; n++) for (const sd of [1, 2, 3]) { const r = randomRun(n, n * 101 + sd), rr = replay(n, r.seq); if (r.seq.length !== a023855(n - 1) || !rr.v.every((v, x) => v === uRef(n, x)) || !rr.stable) ownOK = false; }
check('three random orders of the test’s own for each n = 2 … 40 also topple A023855(n − 1) times, each cell u(x) times', ownOK);
check('grains lost into the sink: n − 1 + [n even] = 10 = 2u(1)', i.finalLost === 10 && R.lost === 10 && 2 * uRef(10, 1) === 10);
await pause(); await setT(0.4); i = await info();
const R38 = replay(10, seq.slice(0, 38));
check('at k = 38 the page’s configuration, odometer and lost grains equal the test’s replay of the first 38 topplings', i.k === 38 && i.c.join() === R38.c.join() && i.v.join() === R38.v.join() && i.lost === R38.lost && i.next === seq[38] && i.last === seq[37]);

/* ---------- presets ---------- */
const presetFacts = { shuffle: [10, 'random', 95], odd: [9, 'max', 60], even: [8, 'right', 50], printed: [5, 'left', 10], big: [40, 'parallel', 5530] };
for (const [p, [n, o, t]] of Object.entries(presetFacts)) {
  await preset(p); i = await info(); seq = await D(() => SP_DEBUG.seq()); R = replay(n, seq);
  const extra = p === 'even' ? uRef(8, 4) === 10 && 4 * (8 - 4) / 2 === 8 && R.c[4] === 2 : p === 'printed' ? a023855(5) === 22 && i.printed === 22 && a023855(4) === 10 : p === 'big' ? Math.abs(t / (n ** 3 / 12) - 1) < 0.05 : p === 'odd' ? R.c.slice(1).every((x) => x === 3) : true;
  check(`${p} preset: n = ${n}, ${o} order, a legal sequence of ${t} = A023855(${n - 1}) topplings ending stable${p === 'even' ? ', u(4) = 10, 2 grains at x = 4' : p === 'printed' ? ', while A023855(5) = 22' : p === 'big' ? ', about n³/12' : ''}`, i.n === n && i.order === o && i.T === t && t === a023855(n - 1) && R.legal && R.stable && seq.length === t && extra);
}
/* each rule step by step: leftmost, rightmost, highest (ties to the smaller index) and rounds of every cell unstable at the round's start */
function followsRule(n, order, sq) {
  let c = initial(n), k = 0;
  const unstable = () => { const U = []; for (let x = 1; x < n; x++) if (c[x] >= 4) U.push(x); return U; };
  while (k < sq.length) {
    const U = unstable(); if (!U.length) return false;
    if (order === 'parallel') { for (const x of U) { if (sq[k] !== x) return false; c = toppleL(n, c, x); k++; } continue; }
    const want = order === 'left' ? U[0] : order === 'right' ? U[U.length - 1] : U.reduce((b, x) => (c[x] > c[b] ? x : b), U[0]);
    if (sq[k] !== want) return false; c = toppleL(n, c, want); k++;
  }
  return unstable().length === 0;
}
let rulesOK = true; for (const n of [10, 13, 24]) for (const o of ['left', 'right', 'max', 'parallel']) { const sq = await D(([n, o]) => SP_DEBUG.sequence(n, o), [n, o]); if (!followsRule(n, o, sq)) rulesOK = false; }
check('each order rule is followed step by step (leftmost, rightmost, highest pile, rounds) for n = 10, 13 and 24', rulesOK);
for (const p of ['lean', 'shuffle', 'odd', 'even', 'printed', 'big']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }

/* ---------- readouts and controls ---------- */
await preset('lean'); await setT(0);
check('the readouts give the order, the counts and the grains', /10 · 最左 · 0 \/ 95/.test(await text('ro1')) && /95 · 95 ✓ · 110 ✗/.test(await text('ro4')) && /36 · 0/.test(await text('ro5')) && /4\(n − 1\) = 36/.test(await text('ro5')));
check('the rail marks k = 0, k = 48 and k = 95', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 'k = 0 | k = 48 | k = 95');
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ performs one toppling and marks the settings custom', (await info()).k === 1 && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await page.keyboard.press('e'); await settle(); i = await info();
check('E jumps to the final state and pauses', i.k === 95 && i.unstable.length === 0 && (await state()).playing === false && /终态/.test(await text('roNote')));
await D(() => { const e = document.getElementById('nIn'); e.value = 13; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the n slider sets n = 13: A023855(12) = 182 topplings', i.n === 13 && i.T === a023855(12) && i.T === 182);
await click('#orderChips [data-order="max"]'); i = await info();
check('the order chips switch to the highest pile: same count, same odometer', i.order === 'max' && i.T === 182 && i.finalV.every((v, x) => v === uRef(13, x)));
await click('#orderChips [data-order="random"]'); const s1 = await D(() => SP_DEBUG.seq()); await click('#reseed'); const s2 = await D(() => SP_DEBUG.seq());
check('“another random order” draws a different sequence with the same length', (await state()).seed === 2 && s1.join() !== s2.join() && s1.length === 182 && s2.length === 182);
await preset('printed'); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing reports the final state at k = 10 = A023855(4)', await waitToast(/k = 10.*A023855\(4\)/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['side', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await preset('lean'); await setT(0.4);
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'even']) {
  await preset(p); await setT(0.5);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('SANDPILE//TORUS · The n × 1 torus sandpile topples A023855(n − 1) times in every order'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note and the two OEIS entries', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['arndt-2017-a293452-torus-column-sandpile.md', 'D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.lean', 'Blueprint/D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.md', 'Library/Combinatorics/arndt2017a293452.md', 'oeis.org/A293452', 'oeis.org/A023855'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="sandpile-torus"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.SP_DEBUG && SP_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'sandpile-torus');

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
