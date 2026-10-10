#!/usr/bin/env node
// Browser regression suite for viz/palindrome-cuts (Playwright + Chromium with software WebGL).
//   node tests/palindrome-cuts.test.mjs
// Reads page state through the read-only window.PC_DEBUG probe and checks it against an independent implementation: both words
// built by iterating their morphisms, a quadratic brute-force palindromic length for short prefixes, a palindromic-suffix-list
// dynamic program (no palindromic tree) for long prefixes, the signed binary weight by its recursion, and the Fibonacci numeral.
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
  const start = await page.evaluate(() => PC_DEBUG.frames());
  await page.waitForFunction((f0) => !PC_DEBUG.pending() && PC_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => PC_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => PC_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => PC_DEBUG.info());
const state = () => D(() => PC_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => PC_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => PC_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

// --- independent implementation
function morphismWord(rules, n) { let w = 'a'; while (w.length < n) w = [...w].map((c) => rules[c]).join(''); return [...w.slice(0, n)].map((c) => (c === 'a' ? 0 : 1)); }
const PDW = morphismWord({ a: 'ab', b: 'aa' }, 1 << 19), FBW = morphismWord({ a: 'ab', b: 'a' }, 100001);
function bruteP(w, n) {   // quadratic DP with a palindrome table from centre expansion
  const pal = Array.from({ length: n }, () => new Uint8Array(n + 1));
  for (let c = 0; c < 2 * n - 1; c++) { let l = Math.floor(c / 2), r = l + (c % 2); while (l >= 0 && r < n && w[l] === w[r]) { pal[l][r + 1] = 1; l--; r++; } }
  const P = new Int32Array(n + 1); for (let i = 1; i <= n; i++) { let b = 1e9; for (let j = 0; j < i; j++) if (pal[j][i] && P[j] + 1 < b) b = P[j] + 1; P[i] = b; }
  return P;
}
function suffixListP(w, n) {   // palindromic suffixes ending at i come from those ending at i − 1 extended by one letter each side
  const P = new Int32Array(n + 1); let prev = [];
  for (let i = 0; i < n; i++) {
    const cur = [1]; if (i > 0 && w[i - 1] === w[i]) cur.push(2);
    for (const L of prev) { const j = i - 1 - L; if (j >= 0 && w[j] === w[i]) cur.push(L + 2); }
    let b = 1e9; for (const L of cur) { const c = P[i + 1 - L] + 1; if (c < b) b = c; }
    P[i + 1] = b; prev = cur;
  }
  return P;
}
const swMemo = new Map();
const sw = (m) => { if (m <= 1) return m; if (swMemo.has(m)) return swMemo.get(m); const v = m % 2 === 0 ? sw(m / 2) : 1 + Math.min(sw((m - 1) / 2), sw((m + 1) / 2)); swMemo.set(m, v); return v; };
const isPal = (a) => a.every((x, i) => x === a[a.length - 1 - i]);
const sparseN = (a, b) => { let s = 0; for (let i = 0; i < a; i++) s += 2 ** (2 * b + 2 + 3 * i); for (let j = 0; j < b; j++) s += 2 ** (2 * j + 1); return s; };
const fibNumeralValue = (s) => { const W = [1, 2]; while (W.length < s.length) W.push(W[W.length - 1] + W[W.length - 2]); return [...s].reverse().reduce((v, c, i) => v + (c === '1' ? W[i] : 0), 0); };
const fibF = (k) => { let a = 0, b = 1; for (let i = 0; i < k; i++) [a, b] = [b, a + b]; return a; };

await page.goto(origin + BASE + 'viz/palindrome-cuts/');
await page.waitForFunction(() => window.PC_DEBUG && PC_DEBUG.frames() > 3, null, { timeout: 120000 });
let i = await info();
const lim = await D(() => PC_DEBUG.limits());
check('opens on the period-doubling word, cutting letter by letter, and plays', i.mode === 'cut' && i.word === 'pd' && (await state()).playing === true && lim.NPD === 299691 && lim.NFIB === 100000);
await pause();

// --- the words
const pdPage = await D(() => PC_DEBUG.letters('pd', 0, 4096)), fbPage = await D(() => PC_DEBUG.letters('fib', 0, 4096));
check('period-doubling letters equal the fixed point of a → ab, b → aa (first 4096)', pdPage.every((x, k) => x === PDW[k]));
const far = await D(() => PC_DEBUG.letters('pd', 262000, 1000));
check('…and far out (positions 262 000 … 262 999)', far.every((x, k) => x === PDW[262000 + k]));
check('Fibonacci letters equal the fixed point of a → ab, b → a (first 4096)', fbPage.every((x, k) => x === FBW[k]));
const farF = await D(() => PC_DEBUG.letters('fib', 99000, 1000));
check('…and far out (positions 99 000 … 99 999)', farF.every((x, k) => x === FBW[99000 + k]));

// --- palindromic length
const BR = 1500, bp = bruteP(PDW, BR), bf = bruteP(FBW, BR);
const pagePd = await D((n) => Array.from({ length: n + 1 }, (_, m) => PC_DEBUG.P('pd', m)), BR), pageFb = await D((n) => Array.from({ length: n + 1 }, (_, m) => PC_DEBUG.P('fib', m)), BR);
check(`P(n) for n ≤ ${BR} matches a quadratic brute force on both words`, pagePd.every((v, m) => v === bp[m]) && pageFb.every((v, m) => v === bf[m]));
const LP = suffixListP(PDW, 299691), LF = suffixListP(FBW, 100000);
const pick = [1000, 5000, 4778, 10922, 43691, 76458, 174762, 250000, 299690, 299691];
const pagePick = await D((ns) => ns.map((m) => PC_DEBUG.P('pd', m)), pick);
check('…long prefixes of the period-doubling word match a palindromic-suffix-list program', pagePick.every((v, k) => v === LP[pick[k]]), pagePick.join(','));
const fpick = [17, 305, 5473, 23182, 50000, 98209, 100000], fPagePick = await D((ns) => ns.map((m) => PC_DEBUG.P('fib', m)), fpick);
check('…and of the Fibonacci word', fPagePick.every((v, k) => v === LF[fpick[k]]), fPagePick.join(','));

// --- cuts
await preset('pdcut'); await setFrac((42 - 1) / 255); i = await info();
const cover = i.blocks.every(([a, b], k) => (k === 0 ? a === 0 : a === i.blocks[k - 1][1]) && b > a) && i.blocks[i.blocks.length - 1][1] === 42;
check('n = 42: the drawn cut has P(42) blocks, covers the prefix and every block is a palindrome', i.n === 42 && i.P === LP[42] && i.blocks.length === i.P && cover && i.blocks.every(([a, b]) => isPal(PDW.slice(a, b))), i.blocks.map(([a, b]) => b - a).join('+'));
const sufTrue = []; for (let L = 1; L <= 42; L++) if (isPal(PDW.slice(42 - L, 42))) sufTrue.push(L);
check('…the palindromic suffixes ending at letter 42 are exactly the listed ones', JSON.stringify([...i.suffixes].sort((a, b) => a - b)) === JSON.stringify(sufTrue), sufTrue.join(','));
check('…the readout shows the prefix and the lower bound F(42)', (await text('ro5')).startsWith('abaaabababaaabaa') && (await text('ro2')).includes(`· ${sw(21)}`));
await click('#wordChips [data-word="fib"]'); await setFrac((17 - 1) / 255); i = await info();
check('the word chip switches to Fibonacci: the prefix of length 17 needs 3 palindromes (Frid, k = 1)', i.word === 'fib' && i.n === 17 && i.P === 3 && i.blocks.every(([a, b]) => isPal(FBW.slice(a, b))) && (await state()).preset === null);

// --- the signed-binary lower bound and the sparse family
let lbOK = true, mx = 0, first = -1;
for (let n = 0; n <= 299691; n++) { const e = LP[n] - sw(Math.floor((n + 1) / 2)); if (e < 0) lbOK = false; if (e > mx) { mx = e; first = n; } }
await preset('lower'); i = await info();
check('P(n) ≥ F(n) = sw(⌊(n + 1)/2⌋) for every n ≤ 299 691 (the frozen bound, recomputed independently)', lbOK);
const pageF = await D(() => Array.from({ length: 4001 }, (_, m) => PC_DEBUG.F(m)));
check('the page’s F(n) equals the independently computed signed weight of ⌊(n + 1)/2⌋ for every n ≤ 4000', pageF.every((f, m) => f === sw(Math.floor((m + 1) / 2))));
check('…P − F is at most 2 on this range and first equals 2 at n = 72, as the page reports', mx === 2 && first === 72 && i.excessMax === 2 && i.excessFirst === 72 && i.n === 72 && i.P === 4 && i.F === 2, `P(72) = ${LP[72]}, F(72) = ${sw(36)}`);
check('…the readout calls P ≤ F + 2 open', /开放问题/.test(await text('roNote')) || /开放问题/.test(await text('presetNote')));
const fams = [[1, 1], [1, 3], [1, 5], [1, 7], [3, 5]];
check('sparse addresses N(a, b) computed independently: 18, 298, 4778, 76458, 299690', JSON.stringify(fams.map(([a, b]) => sparseN(a, b))) === JSON.stringify([18, 298, 4778, 76458, 299690]) && JSON.stringify(i.family.map((f) => f.N)) === JSON.stringify([18, 298, 4778, 76458, 299690]));
check('…P(N(a, 2a − 1)) = 3a and P(N(a, b)) = a + b at all five (the frozen exact values), recomputed', fams.every(([a, b], k) => LP[sparseN(a, b)] === (b === 2 * a - 1 ? 3 * a : a + b) && i.family[k].P === LP[sparseN(a, b)]), fams.map(([a, b]) => LP[sparseN(a, b)]).join(','));
await preset('diag'); i = await info();
check('the diagonal preset lands on N(3, 5) = 299 690 with P = 9 = 3a', i.n === 299690 && i.P === 9 && /3a = 9 · 9/.test(await text('ro5')));
await preset('offdiag'); i = await info();
check('the off-diagonal preset lands on N(1, 5) = 4778 with P = 6 = a + b and F computed from signed binary', i.n === 4778 && i.P === 6 && i.F === sw(2389) && i.naf.reduce((s, d, k) => s + d * 2 ** k, 0) === 2389);
check('…the readout pairs the frozen value a + b = 6 with the computed 6', /N\(1, 5\) = 4 778 · a \+ b = 6 · 6/.test(await text('ro5')), await text('ro5'));

// --- the 2-kernel
const dseq = Array.from({ length: 299690 }, (_, n) => LP[n + 1] - LP[n]);
const kcount = (seq) => { const seen = new Set(), out = []; for (let e = 0; e <= 9; e++) { for (let r = 0; r < 2 ** e; r++) seen.add(Array.from({ length: 64 }, (_, n) => seq[2 ** e * n + r]).join(',')); out.push(seen.size); } return out; };
await preset('kernel'); await setFrac(1); i = await info();
check('2-kernel: distinct subsequences d(2ᵉn + r) on a 64-term window, e ≤ 9, recomputed', JSON.stringify(i.dCounts) === JSON.stringify(kcount(dseq)) && i.e === 9, i.dCounts.join(' '));
check('…the word itself gives a constant 4 from e = 2 on', JSON.stringify(i.uCounts) === JSON.stringify(kcount(PDW)) && i.uCounts.slice(2).every((c) => c === 4));
check('…d takes only the values −1, 0, 1', dseq.every((x) => x === -1 || x === 0 || x === 1));
check('…and the readout says finite counts are only circumstantial', /证明不了无穷多/.test(await text('roNote')));

// --- Frid's Fibonacci prefixes
await preset('frid'); i = await info();
check('Frid: (100)^(2k−1)101 in Fibonacci numeration equals F(6k + 3)/2 = 17, 305, 5473, 98209 (recomputed)', [1, 2, 3, 4].every((k) => fibNumeralValue('100'.repeat(2 * k - 1) + '101') === fibF(6 * k + 3) / 2) && JSON.stringify(i.frid.map((f) => f.N)) === JSON.stringify([17, 305, 5473, 98209]) && i.frid.every((f) => f.numeralValue === f.N));
check('…each Frid prefix needs exactly 2k + 1 palindromes (frozen), recomputed independently', [1, 2, 3, 4].every((k) => LF[fibF(6 * k + 3) / 2] === 2 * k + 1) && i.frid.every((f) => f.P === 2 * f.k + 1) && i.n === 98209 && i.P === 9);
const recF = []; { let cur = 0; for (let n = 1; n <= 100000; n++) if (LF[n] > cur) { cur = LF[n]; recF.push([n, cur]); } }
check('…first prefixes with P = 1 … 9 match the independent count, and P = 7, 9 first appear at N(3), N(4)', JSON.stringify(i.records) === JSON.stringify(recF) && recF[6][0] === 5473 && recF[8][0] === 98209, recF.map(([n]) => n).join(','));
check('…the readout reports the frozen value and the computed one together', /N\(4\) = 98 209 · 9 · 9/.test(await text('ro3')));

// --- controls, keys, presets
for (const name of ['pdcut', 'fibcut', 'lower', 'offdiag', 'diag', 'kernel', 'frid', 'fridsweep']) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await click('#modeChips [data-mode="cut"]');
check('the model chips switch to cutting, show the word chips and mark the settings custom', (await info()).mode === 'cut' && (await visible('wordField')) && (await state()).preset === null);
await click('#modeChips [data-mode="kernel"]');
check('…and the kernel mode hides them', !(await visible('wordField')) && (await info()).mode === 'kernel');
await setFrac(0); await page.keyboard.press('ArrowRight'); await settle();
check('→ moves one kernel level', (await info()).e === 1);
await click('#modeChips [data-mode="cut"]'); await setFrac(0); await page.keyboard.press('ArrowRight'); await settle();
check('…and one letter in the cut mode', (await info()).n === 2);
await page.keyboard.press('e'); await settle();
check('E jumps to n = 256 and pauses', (await info()).n === 256 && (await state()).playing === false);

// --- play and toasts
await preset('pdcut'); await setFrac(0.985); await click('#play');
check('the cut toast fires at n = 256', await waitToast(/n = 256/));
await pause();
await preset('lower'); await setFrac(0.985); await click('#play');
check('the bound toast fires at the end of the range', await waitToast(/299 691/));
await pause();
await preset('kernel'); await setFrac(0.97); await click('#play');
check('the kernel toast fires at e = 9', await waitToast(/e = 9/));
await pause();
await preset('fridsweep'); await setFrac(0.985); await click('#play');
check('the Fibonacci toast names N(4) = 98 209', await waitToast(/98 209/));
await pause();
await preset('fibcut'); await setFrac(0.2); await click('#play'); await waitFrames(12); const p1 = (await state()).nowFrac; await pause();
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
await click('#modeChips [data-mode="pd"]');
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
await setFrac(1);
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /N\(3, 5\)/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('PALINDROME//CUTS · How few palindromes a prefix splits into'));
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
await page.click('.card:has(a[href*="palindrome-cuts"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.PC_DEBUG && PC_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'palindrome-cuts');

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
