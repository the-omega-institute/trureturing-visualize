#!/usr/bin/env node
// Browser regression suite for viz/zeckendorf-chain (Playwright + Chromium with software WebGL).
//   node tests/zeckendorf-chain.test.mjs
// Reads page state through the read-only window.ZC_DEBUG probe and checks it against an independent implementation: the
// Zeckendorf expansion as a set of indices, verified (sum, indices ≥ 2, no two adjacent) so that uniqueness makes it the
// expansion, the chains rebuilt with Set intersections, and the defining properties checked directly
// (eligibility, leastness among unused numbers, distinctness). Fixed reference data: the data fields of the OEIS records
// A370630, A370631 and A226077.
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
  const start = await page.evaluate(() => ZC_DEBUG.frames());
  await page.waitForFunction((f0) => !ZC_DEBUG.pending() && ZC_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => ZC_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => ZC_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => ZC_DEBUG.info());
const state = () => D(() => ZC_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const seq = (a, b) => D(([a, b]) => ZC_DEBUG.seq(a, b), [a, b]);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => ZC_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => ZC_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 120000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
const OEIS_630 = [1, 4, 3, 11, 8, 9, 6, 5, 7, 2, 10, 12, 14, 13, 15, 16, 18, 17, 20, 23, 21, 22, 19, 25, 26, 24, 27, 29, 28, 30, 35, 33, 37, 32, 38, 34, 36, 31, 41, 42, 39, 43, 47, 40, 44, 48, 45, 49, 46, 52, 60, 53, 56, 51, 58, 50, 59, 55, 57, 54, 61, 63, 62, 64, 68, 65, 69];
const OEIS_631 = [1, 4, 3, 11, 8, 9, 6, 5, 7, 2, 10, 12, 14, 13, 15, 16, 17, 18, 19, 20, 23, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 34, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 57, 55, 56, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67];
const OEIS_077 = [1, 3, 2, 6, 4, 5, 9, 7, 10, 8, 11, 12, 20, 13, 17, 15, 18, 14, 19, 16, 21, 24, 22, 25, 33, 23, 34, 26, 35, 29, 36, 28, 37, 27, 38, 32, 39, 40, 30, 41, 48, 31, 65, 43, 52, 42, 49, 44, 50, 45, 67, 46, 66, 47, 68, 53, 70, 51, 69, 54, 74, 55, 73, 56, 72, 57, 71, 58, 76, 59, 80, 60, 75, 64, 77, 82, 61, 96, 62, 81, 78, 97, 84, 98, 85, 104, 83, 100, 88];
const fib = [0, 1]; while (fib.length < 46) fib.push(fib[fib.length - 1] + fib[fib.length - 2]);
/* Zeckendorf indices: the representation is the unique set of indices ≥ 2, no two adjacent, summing to m; build a candidate
   from the largest index downwards and verify the three properties, so uniqueness makes it the expansion */
const zmemo = new Map();
function zeck(m) {
  if (zmemo.has(m)) return zmemo.get(m);
  let k = 2; while (fib[k + 1] <= m) k++;
  const idx = []; let r = m;
  for (; k >= 2; k--) if (fib[k] <= r && !idx.includes(k + 1)) { idx.push(k); r -= fib[k]; }
  const ok = r === 0 && idx.every((i) => i >= 2) && idx.every((i, j) => j === 0 || idx[j - 1] - i >= 2);
  if (!ok) throw new Error('bad expansion ' + m);
  const s = new Set(idx); zmemo.set(m, s); return s;
}
const bits = (m) => { const s = new Set(); for (let j = 0; m; j++, m = Math.floor(m / 2)) if (m % 2) s.add(j); return s; };
const common = (A, B) => { let c = 0; for (const x of A) if (B.has(x)) c++; return c; };
function myChain(rule, N) {
  const D = rule === 'binary' ? bits : zeck, ok = rule === 'atleast' ? (c) => c >= 1 : (c) => c === 1;
  const a = [0, 1], used = new Set([1]); let low = 2;
  for (let n = 1; n < N; n++) {
    const z = D(a[n]); let m = low;
    while (used.has(m) || !ok(common(z, D(m)))) m++;
    a.push(m); used.add(m); while (used.has(low)) low++;
  }
  return a;
}

/* ---------- load ---------- */
await page.goto(origin + BASE + 'viz/zeckendorf-chain/');
await page.waitForFunction(() => window.ZC_DEBUG && ZC_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let st = await state(), i = await info();
check('opens on the start of the chain (A370630, n ≤ 300) and plays', st.preset === 'start' && i.rule === 'one' && i.nmax === 300 && st.playing === true);
await pause();
check('the page carries the 67 data terms of the OEIS record A370630', JSON.stringify(i.oeis) === JSON.stringify(OEIS_630));

/* ---------- the chain ---------- */
await preset('long'); i = await info();
const page30k = await seq(1, 30000), mine = myChain('one', 30000);
check('A370630: the page’s first 30000 terms equal the independent chain', page30k.length === 30000 && page30k.every((v, j) => v === mine[j + 1]));
check('…and the first 67 equal the OEIS data', OEIS_630.every((v, j) => page30k[j] === v));
let elig = true; for (let n = 1; n < 30000; n++) if (common(zeck(page30k[n - 1]), zeck(page30k[n])) !== 1) { elig = false; break; }
check('every step shares exactly one Zeckendorf term with the previous one (n < 30000)', elig);
let least = true; { const used = new Set([page30k[0]]); for (let n = 1; n < 3000 && least; n++) { const z = zeck(page30k[n - 1]); for (let m = 1; m < page30k[n]; m++) if (!used.has(m) && common(z, zeck(m)) === 1) { least = false; break; } used.add(page30k[n]); } }
check('every term is the least unused eligible number (checked for the first 3000 steps)', least);
check('the 30000 terms are distinct', new Set(page30k).size === 30000);
const mst = await D(() => ZC_DEBUG.mstarSeq(1, 30000)); let okM = true; { const seen = new Set(); let low = 1; for (let n = 0; n < 30000; n++) { seen.add(page30k[n]); while (seen.has(low)) low++; if (mst[n] !== low) { okM = false; break; } } }
check('the smallest unseen number m*(n) matches a recount at every step', okM && mst[29999] === 27670, `${mst[29999]}`);
const sh = await D(() => ZC_DEBUG.sharedSeq(2, 30000)); let okS = true, lead = 0;
for (let n = 2; n <= 30000; n++) { const z1 = zeck(page30k[n - 2]), z2 = zeck(page30k[n - 1]), c = [...z1].filter((k) => z2.has(k)); const pageK = []; for (let b = 0; b < 32; b++) if (sh[n - 2] >>> b & 1) pageK.push(b + 2); if (pageK.join() !== c.join()) { okS = false; break; } if (c[0] === Math.max(...z1) && c[0] === Math.max(...z2)) lead++; }
check('the amber shared term of every step is the actual common index', okS);
check('about 62% of consecutive pairs share the leading term of both (n ≤ 30000), as the page states', Math.abs(lead / 29999 - i.lead) < 1e-12 && Math.abs(i.lead - 0.622) < 0.001, `${(lead / 29999).toFixed(4)}`);
let md = 0, mdn = 0; page30k.forEach((v, j) => { if (Math.abs(v - (j + 1)) > md) { md = Math.abs(v - (j + 1)); mdn = j + 1; } });
check('max |a(n) − n| is 3355 at n = 29428 with a(n) = 26073, as stated', i.maxDisp === 3355 && i.dispN === 29428 && md === 3355 && mdn === 29428 && page30k[29427] === 26073);
await preset('wait'); i = await info();
const pos = new Map(); page30k.forEach((v, j) => pos.set(v, j + 1)); let wM = 0, wW = 0; for (let m = 1; m < 27670; m++) { const w = pos.get(m) - m; if (w > wW) { wW = w; wM = m; } }
check('wait preset: 26073 is the longest wait among the numbers seen, appearing at step 29428 (3355 late)', i.n === 29428 && i.a === 26073 && i.waitM === 26073 && i.wait === 3355 && wM === 26073 && wW === 3355);
await preset('two'); i = await info();
const first9 = page30k.slice(0, 9);
check('two preset: a(10) = 2, and among the first 9 terms only 7 = F(5) + F(3) contains F(3)', i.n === 10 && i.a === 2 && first9.filter((v) => zeck(v).has(3)).join() === '7' && page30k[8] === 7);
check('the expansion readout writes 2 = F(3) and its shared term with 7', /2 = F\(3\)/.test(await text('ro2')) && /F\(3\) = 2/.test(await text('ro3')));

/* ---------- neighbouring rules (numerical comparisons) ---------- */
await preset('atleast'); i = await info();
const p631 = await seq(1, 3000), m631 = myChain('atleast', 3000);
check('A370631 (at least one): the page’s 3000 terms equal the independent chain and the first 67 equal the OEIS data', i.rule === 'atleast' && p631.every((v, j) => v === m631[j + 1]) && OEIS_631.every((v, j) => p631[j] === v));
check('A370631 agrees with A370630 for exactly the first 16 terms', p631.slice(0, 16).every((v, j) => v === page30k[j]) && p631[16] !== page30k[16]);
await preset('binary'); i = await info();
const p077 = await seq(1, 3000), m077 = myChain('binary', 3000);
check('A226077 (binary, exactly one bit): the page’s 3000 terms equal the independent chain and the first 89 equal the OEIS data', i.rule === 'binary' && p077.every((v, j) => v === m077[j + 1]) && OEIS_077.every((v, j) => p077[j] === v));

/* ---------- controls, presets, timeline ---------- */
await click('#ruleChips [data-rule="one"]');
check('rule chips switch the rule and mark the settings custom', (await info()).rule === 'one' && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await click('#nChips [data-n="300"]');
check('step-count chips set the range', (await info()).nmax === 300);
for (const p of ['start', 'two', 'long', 'wait', 'atleast', 'binary']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
await preset('start'); await setFrac(0.97); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing to the end reports the smallest unseen number and the largest term', await waitToast(/300 步.*最小未出现数/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
await setFrac(0.5); const n0 = (await info()).n;
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps n by one', (await info()).n === n0 + 1);
await page.keyboard.press('e'); await settle();
check('E jumps to the last step and pauses', (await info()).n === 300 && (await state()).playing === false);
await preset('start');
check('the rail marks n = 1, the longest wait within 300 steps and the end', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 'n = 1 | 最久的等待 232 | n = 300');
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit[0] > 2000 && lit[1] > 800, `${lit}`);   // the right chart is two thin curves

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['two', 'binary']) {
  await preset(p);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#ruleChips [data-rule="atleast"]');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('ZECKENDORF//CHAIN · The one-shared-term Zeckendorf chain is a permutation'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint and the OEIS records', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['oeis-a370630-zeckendorf-greedy-permutation.md', 'ZeckendorfGreedyPermutation.lean', 'Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md', 'oeis.org/A370630', 'oeis.org/A370631', 'oeis.org/A226077'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="zeckendorf-chain"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.ZC_DEBUG && ZC_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'zeckendorf-chain');

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
