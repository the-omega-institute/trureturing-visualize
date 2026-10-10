#!/usr/bin/env node
// Browser regression suite for viz/prime-gaps (Playwright + Chromium with software WebGL).
//   node tests/prime-gaps.test.mjs
// Reads page state through the read-only window.PG_DEBUG probe and checks it against an independent implementation: an odd-only
// sieve, admissibility by residue sets, minimal widths s(k) by exhaustive search, the twin-prime constant, OEIS data for record
// gaps (A002386, A005250), A079063 and A089610, a(n) of A079063 from π((√pₙ + 1)²) by binary search, and τ(n) by trial division.
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
  const start = await page.evaluate(() => PG_DEBUG.frames());
  await page.waitForFunction((f0) => !PG_DEBUG.pending() && PG_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => PG_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => PG_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => PG_DEBUG.info());
const state = () => D(() => PG_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => PG_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => PG_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 60000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

// --- independent implementation
const N = 20000000;
const odd = new Uint8Array((N >> 1) + 1);            // odd[i] = 1 ⟺ 2i + 1 is composite
odd[0] = 1; for (let i = 1; (2 * i + 1) ** 2 <= N; i++) if (!odd[i]) { const p = 2 * i + 1; for (let q = (p * p - 1) >> 1; q <= N >> 1; q += p) odd[q] = 1; }
const prime = (n) => n === 2 || (n > 2 && n <= N && n % 2 === 1 && !odd[(n - 1) >> 1]);
const P = [2]; for (let i = 1; 2 * i + 1 <= N; i++) if (!odd[i]) P.push(2 * i + 1);
const piLE = (x) => { let lo = 0, hi = P.length; while (lo < hi) { const m = (lo + hi) >> 1; if (P[m] <= x) lo = m + 1; else hi = m; } return lo; };
const admissible = (H) => { for (const p of P) { if (p > H.length) break; if (new Set(H.map((h) => h % p)).size === p) return false; } return true; };
// the least width of an admissible k-tuple, by exhaustive search over even offsets containing 0 and the width
function minimalWidth(k) {
  for (let B = 0; ; B += 2) {
    const inner = []; for (let h = 2; h < B; h += 2) inner.push(h);
    const need = k - (B === 0 ? 1 : 2); if (need < 0) continue;
    const pick = (start, chosen) => { if (chosen.length === need) return admissible([0, ...chosen, ...(B ? [B] : [])]); for (let i = start; i < inner.length; i++) { chosen.push(inner[i]); if (pick(i + 1, chosen)) return true; chosen.pop(); } return false; };
    if (B === 0 ? k === 1 : need <= inner.length && pick(0, [])) return B;
  }
}
const countTuple = (H) => { let c = 0; const out = []; for (const n of P) { if (n + H[H.length - 1] > N) break; if (H.every((h) => prime(n + h))) { c++; out.push(n); } } return [c, out]; };
const A002386 = [2, 3, 7, 23, 89, 113, 523, 887, 1129, 1327, 9551, 15683, 19609, 31397, 155921, 360653, 370261, 492113, 1349533, 1357201, 2010733, 4652353, 17051707];
const A005250 = [1, 2, 4, 6, 8, 14, 18, 20, 22, 34, 36, 44, 52, 72, 86, 96, 112, 114, 118, 132, 148, 154, 180];
const A079063 = [3, 3, 2, 3, 3, 3, 3, 2, 3, 3, 4, 4, 4, 3, 4, 4, 5, 4, 5, 4, 4, 4, 4, 5, 6, 5, 4, 4, 3, 3, 5, 5, 5, 5, 6, 5, 6, 5, 6, 7, 6, 5, 5, 4, 4, 4, 7, 7, 7, 6, 6, 6, 6, 8, 7, 7, 6, 5, 6, 6, 6, 5, 6, 6, 6, 6, 7, 7, 8, 7, 7, 7, 7, 7, 6, 7, 6, 7, 7, 8];
const A089610 = [1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 3, 2, 4, 4, 1, 2, 3, 3, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 5, 5, 6, 4, 5, 7, 3, 6, 6, 8, 5, 5, 7, 4, 6, 7, 6, 7, 6, 6, 5, 9, 7, 7, 6, 7, 7, 6, 8, 8, 7, 7, 8, 9, 11, 7, 8, 10, 8, 11, 8, 7, 7, 10, 11, 12, 4];
// a(n) of A079063: the primes after pₙ up to (√pₙ + 1)² are the ones within the unit √-window
const a079 = (n) => piLE((Math.sqrt(P[n - 1]) + 1) ** 2) - n + 1;
const tau = (n) => { let t = 1, m = n; for (let d = 2; d * d <= m; d++) { let e = 0; while (m % d === 0) { m /= d; e++; } t *= e + 1; } return m > 1 ? 2 * t : t; };

await page.goto(origin + BASE + 'viz/prime-gaps/');
await page.waitForFunction(() => window.PG_DEBUG && PG_DEBUG.frames() > 3, null, { timeout: 120000 });
let i = await info();
check('opens on the optimal 8-tuple and plays', i.mode === 'tuple' && i.H.join(',') === '0,2,6,8,12,18,20,26' && (await state()).playing === true);
await pause();
check('the sieve finds π(2·10⁷) = 1 270 607 primes, the last ones as an odd-only sieve finds them', i.nPrimes === P.length && P.length === 1270607 && i.primesTail.join(',') === P.slice(-5).join(','), i.primesTail.join(','));

// --- admissible tuples
await setFrac(1); i = await info();
const [c8, o8] = countTuple([0, 2, 6, 8, 12, 18, 20, 26]);
check('8-tuple: admissible, width 26, and all prime exactly at n = 11 and 15 760 091 below 2·10⁷', i.admissible && i.D === 26 && i.occTotal === c8 && c8 === 2 && i.occHead.join(',') === o8.join(',') && o8.join(',') === '11,15760091');
const w = [1, 2, 3, 4, 5, 6, 7, 8].map(minimalWidth);
check('exhaustive search gives the minimal widths s(1 … 8) = 0, 2, 6, 8, 12, 16, 20, 26 (s(8) = 26 is the frozen theorem)', w.join(',') === '0,2,6,8,12,16,20,26' && i.sk === 26, w.join(','));
check('…the readout calls s(8) = 26 the frozen value', /26 \(LEAN\)/.test(await text('ro5')));
const ringsOK = i.rings.every((r) => r.occ.every((o, s) => o === [0, 2, 6, 8, 12, 18, 20, 26].some((h) => h % r.p === s)) && r.full === r.occ.every(Boolean));
check('the residue rings show exactly the classes the tuple occupies, none full', ringsOK && i.rings.every((r) => !r.full) && i.rings.map((r) => r.p).join(',') === '2,3,5,7,11,13');
check('the occupancy histogram over n ≤ 10⁶ adds up to 10⁶', i.hist.reduce((a, b) => a + b, 0) === 1000000);
await preset('twin'); await setFrac(1); i = await info();
const [c2] = countTuple([0, 2]);
check('twins: 107 407 pairs below 2·10⁷ by an independent count', i.occTotal === c2 && c2 === 107407);
check('…𝔖({0, 2}) is the twin-prime constant 2C₂ = 1.3203236… (product over p < 10⁵)', Math.abs(i.sing - 1.3203236316) < 5e-6, i.sing.toFixed(8));
check('…n ≤ 10⁶ with both n and n + 2 prime: 8169 (π₂(10⁶))', i.hist[2] === 8169 && i.hist[2] === countTuple([0, 2])[1].filter((n) => n <= 1e6).length);
check('…the Hardy–Littlewood value at 2·10⁷ is within 1 % of the count (a conjecture, shown as such)', Math.abs(i.hlAtN / c2 - 1) < 0.01 && /猜想/.test(await text('ro4L')), i.hlAtN.toFixed(0));
await setFrac(0.5); i = await info();
const xHalf = Math.round(Math.exp(Math.log(100) + (Math.log(N) - Math.log(100)) * 0.5));
check('half way the scan limit is x = e^{(ln 10² + ln 2·10⁷)/2} and the count is the count up to x', i.x === xHalf && i.countAtX === countTuple([0, 2])[1].filter((n) => n <= xHalf).length, `x ${i.x} · ${i.countAtX}`);
await preset('blocked'); await setFrac(1); i = await info();
check('{0, 2, 4}: blocked mod 3, all prime only at n = 3, prediction 0', !i.admissible && i.blockers.join(',') === '3' && i.occTotal === 1 && i.occHead[0] === 3 && i.sing === 0 && i.rings.find((r) => r.p === 3).full);
check('…and the readout names the full ring', /模 3 占满/.test(await text('ro2')));
await preset('forty'); i = await info();
const F40 = [0, 2, 6, 12, 20, 26, 30, 32, 36, 42, 48, 50, 56, 60, 68, 72, 78, 86, 90, 92, 98, 102, 110, 116, 120, 126, 132, 138, 140, 146, 152, 156, 158, 162, 168, 170, 176, 180, 182, 186];
check('the 40-tuple of width 186 is admissible by an independent residue check, and s(40) = 186 (A008407)', i.H.join(',') === F40.join(',') && i.k === 40 && i.D === 186 && admissible(F40) && i.admissible && i.sk === 186);
check('…its rings run through every prime below 40', i.rings.map((r) => r.p).join(',') === '2,3,5,7,11,13,17,19,23,29,31,37');
check('…no translate is all prime below 2·10⁷, and the readouts keep DHL[40, 2] unproved', i.occTotal === 0 && countTuple(F40)[0] === 0 && /没有证明 DHL\[40, 2\]/.test(await D(() => document.querySelector('.side').textContent)));
const occ40 = (n) => F40.filter((h) => prime(n + h)).length;
await setFrac(0.6); i = await info();
let bestN = 1, bestC = -1; for (let n = 1; n <= Math.min(i.x, 1e6); n++) { const c = occ40(n); if (c > bestC) { bestC = c; bestN = n; } }
check('…the featured translate is the first n ≤ min(x, 10⁶) with the most primes in n + H, found independently', i.featured.n === bestN && !i.featured.full, `n ${bestN} · ${bestC} primes of 40`);
// the offset editor
await preset('twin'); await click('#offsets [data-off="4"]'); i = await info();
check('the offset editor adds 4 to {0, 2}: blocked mod 3, settings custom', i.H.join(',') === '0,2,4' && !i.admissible && (await state()).preset === null && /自定义/.test(await text('presetNote')));
await click('#offsets [data-off="4"]'); await click('#offsets [data-off="6"]'); i = await info();
const [c3] = countTuple([0, 2, 6]);
check('…swapping 4 for 6 gives the admissible triple {0, 2, 6} with the independent count', i.H.join(',') === '0,2,6' && i.admissible && i.occTotal === c3, `${c3}`);

// --- record gaps
await preset('records'); await setFrac(1); i = await info();
check('records below 2·10⁷ match OEIS A002386 and A005250 (23 records, the last 180 after 17 051 707)', i.records.length === 23 && i.records.every(([p, g], j) => p === A002386[j] && g === A005250[j]));
check('…and every record is an actual consecutive-prime gap that beats all earlier ones', (() => { let best = 0; for (let j = 1; j < P.length; j++) { const g = P[j] - P[j - 1]; if (g > best) { best = g; if (!i.records.some(([p, gg]) => p === P[j - 1] && gg === g)) return false; } } return true; })());
await setFrac(0.5); i = await info();
check('half way (x ≈ 44 721) only the records with p + g ≤ x are shown', i.recordsAtX === A002386.filter((p, j) => p + A005250[j] <= i.x).length, `${i.recordsAtX} records`);

// --- A079063
await preset('sqrt'); await setFrac(1); i = await info();
check('A079063: the first 80 values match OEIS', i.aHead.join(',') === A079063.join(','));
check('…a(10), a(10²), …, a(10⁶) match a(n) = π((√pₙ + 1)²) − n + 1', i.aSample.join(',') === [10, 100, 1000, 10000, 100000, 1000000].map(a079).join(','), i.aSample.join(','));
let lo = Infinity, at = 0; for (let n = 1; n <= 1000000; n++) { const r = a079(n) / Math.sqrt(n); if (r < lo) { lo = r; at = n; } }
check('…the smallest a(n)/√n for n ≤ 10⁶ is 0.4002 at n = 8548, still above 0.4 (the refutation is a proof, not this number)', Math.abs(i.minRatio - lo) < 1e-12 && i.minAt === at && at === 8548 && lo > 0.4 && lo < 0.4003, `${lo.toFixed(5)} at ${at}`);
check('…the note says the frozen theorem rules out every c > 0 and the numbers stop at 10⁶', /对任何 c &gt; 0|对任何 c > 0/.test(await D(() => document.getElementById('roNote').innerHTML)) && /10⁶/.test(await text('roNote')));

// --- A089610
await preset('square'); await setFrac(1); i = await info();
check('A089610: the first 77 values match OEIS', i.aHead.join(',') === A089610.join(','));
const hil = (n) => { let c = 0; for (let m = n * n + 1; m <= n * n + n; m++) if (prime(m)) c++; return c; };
let drops = 0; for (let n = 1; n <= 3000; n++) if (hil(n + 1) <= hil(n)) drops++;
check('…steps with a(n + 1) ≤ a(n) up to n = 3000 counted independently, and the latest is close to 3000', i.drops === drops && i.dropsHead[0] === 1, `${drops}`);
check('…a(2k) ≤ k holds for every 2k ≤ 3000 (a step of the frozen proof)', Array.from({ length: 1500 }, (_, k) => hil(2 * (k + 1)) <= k + 1).every(Boolean) && /是/.test(await text('ro5')));

// --- A049591 and 529
await preset('divisor'); i = await info();
const term = (n) => n % 2 === 1 && prime(n) && !prime(n + 2), empty = (n) => { const t = tau(n); for (let m = n + 1; m < n + t * t; m++) if (prime(m)) return false; return true; };
const mism = []; for (let n = 2; n <= 200000; n++) if (term(n) !== empty(n)) mism.push(n);
check('A049591: up to 2·10⁵ the characterization fails first at 529 and 9439 times in all, counted independently', i.mismCount === mism.length && mism.length === 9439 && i.mismHead.join(',') === mism.slice(0, 20).join(',') && mism[0] === 529);
check('…529 = 23²: τ = 3, 530 … 537 are composite, 529 is not prime', tau(529) === 3 && [530, 531, 532, 533, 534, 535, 536, 537].every((m) => !prime(m)) && !prime(529));
await setFrac((529 - 2) / (2000 - 2)); i = await info();
check('…at n = 529 the page shows an empty window and disagreement', i.n === 529 && i.empty === true && i.term === false && /不一致/.test(await text('ro4')));

// --- controls, keys, presets
for (const name of ['twin', 'blocked', 'eight', 'forty', 'records', 'sqrt', 'square', 'divisor']) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await click('#modeChips [data-mode="records"]');
check('the question chips switch the mode, hide the offset editor and mark the settings custom', (await info()).mode === 'records' && !(await visible('tupleBox')) && (await state()).preset === null);
await click('#modeChips [data-mode="tuple"]');
check('…and the tuple mode shows the offset editor again', (await visible('tupleBox')) && (await D(() => document.querySelectorAll('#offsets button').length)) === 60);
await setFrac(0.2); await page.keyboard.press('ArrowRight'); await settle();
check('→ moves one step along the rail', Math.abs((await state()).nowFrac - (0.2 + 1 / 400)) < 1e-9);
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await state()).nowFrac === 1 && (await state()).playing === false);

// --- play and toasts
await preset('divisor'); await setFrac(0.25); await click('#play');
check('the 529 toast fires when the scan reaches it', await waitToast(/529/));
await pause();
await preset('eight'); await setFrac(0.99); await click('#play');
check('the tuple toast reports the count against the prediction at the end', await waitToast(/2·10⁷ 以内.*2 次/));
await pause();
await preset('records'); await setFrac(0.99); await click('#play');
check('the records toast names the gap of 180', await waitToast(/180/));
await pause();
await preset('square'); await setFrac(0.3); await click('#play'); await waitFrames(12); const p1 = (await state()).nowFrac; await pause();
check('play advances along the rail', p1 > 0.3);
await click('#rev'); await waitFrames(12); const p2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', p2 < p1);
await page.click('#rev'); await pause();
await page.focus('#now'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with the rail focused', playing === true);
await pause();

// --- language
await click('#modeChips [data-mode="tuple"]');
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /mod 2/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('PRIME//GAPS · How close primes can crowd'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
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
await page.click('.card:has(a[href*="prime-gaps"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.PG_DEBUG && PG_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'prime-gaps');

// --- narrow layouts in both languages
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await waitFrames(3);
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await waitFrames(6);
    check(`no horizontal scroll at ${w}px (${lang})`, (await D(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 }); await waitFrames(3);
}
check('no script errors during the whole session', errors.length === 0, errors.join(' | '));

const failed = results.filter(r => !r.ok);
console.log(`\n${results.length - failed.length}/${results.length} passed`);
await browser.close(); server.close();
if (failed.length) process.exit(1);
