#!/usr/bin/env node
// Browser regression suite for viz/factorial-steps (Playwright + Chromium with software WebGL).
//   node tests/factorial-steps.test.mjs
// Reads page state through the read-only window.FS_DEBUG probe and checks it against an independent implementation: half-integer
// factorials through double factorials (the page uses (2k)!/(4ᵏk!)), third-index factorials as products of exact fractions,
// the auxiliaries as direct products, factorizations by trial division, and the step functions evaluated with integer floors
// on a common denominator. Fixed reference data come from the OEIS data sections of A347854–A347858 and from the dossiers:
// a(3n + 1) = 3³ⁿ⁺¹·b(n), a(3n + 2) = 3³ⁿ⁺²·c(n), the powers 2²ⁿ, 2⁸ⁿ and 3ⁿ, and A347854(2m) = u(m).
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
  const start = await page.evaluate(() => FS_DEBUG.frames());
  await page.waitForFunction((f0) => !FS_DEBUG.pending() && FS_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => FS_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => FS_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => FS_DEBUG.info());
const state = () => D(() => FS_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const slide = async (id, v) => { await D(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input')); }, [id, v]); await settle(); };
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => FS_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => FS_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
// half-integer factorials through double factorials, (m/2)! = m!!·√π / 2^((m+1)/2) for odd m (the page uses (2k)!/(4ᵏk!));
// third-index factorials as the product ∏ⱼ (n/3 + j) of exact fractions; factorizations by trial division of the page's own
// decimal strings; the staircases evaluated on a common denominator with integer floors
const OEIS = {   // OEIS data sections, fixed reference data
  A347854: '1,40,4620,622336,89237148,13236695040,2005604901300,308350245273600,47913489552349980,7505566011722039296,1183237138556438547120,187495217080545878999040,29836408028165719837829700,4764790302634058161217077248',
  A347855: '1,9,189,4620,120285,3241134,89237148,2493521172,70429218525,2005604901300,57481750139814,1656023714623980,47913489552349980,1391243084942932620,40519970408738302020,1183237138556438547120',
  A347856: '1,20,990,56576,3432198,215147520,13768454700,893768826880,58626071754822,3876225891958784,257898242928604740,17245961314149335040,1158088115444301759900,78040346182201091555328',
  A347857: '1,24,1386,91392,6374082,458625024,33660501840,2504739913728,188276393811330,14262358156247040,1087036407409838886,83262603737872465920,6403774152656100209808,494217792537649867653120',
  A347858: '1,512,1021020,2399141888,6016814703900,15626259253952512,41477110789150966020,111745115394167694950400,304331361887290342345862940,835666006020766806513664655360,2309513382640863232775760738593520,6416034331756986890806503962421755904'
};
const big = (n) => { let r = 1n; for (let i = 2n; i <= BigInt(n); i++) r *= i; return r; };
const dfact = (m) => { let r = 1n; for (let i = BigInt(m); i > 1n; i -= 2n) r *= i; return r; };
const gcdB = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const fr = (p, q) => { const g = gcdB(p, q) || 1n; return [p / g, q / g]; };
const halfInd = (m) => (m % 2 === 0 ? [big(m / 2), 1n] : [dfact(m), 2n ** BigInt((m + 1) / 2)]);   // (m/2)! without √π
const SPEC = {
  A347854: { int: [[6, 1], [3, -1], [2, -1]], half: [[1, 1], [3, -1]] }, A347856: { int: [[6, 1], [4, -1], [1, -1]], half: [[1, 1], [3, -1]] },
  A347857: { int: [[6, 1], [3, -1], [2, -1]], half: [[3, 1], [5, -1]] }, A347858: { int: [[9, 1], [3, -1], [2, -1]], half: [[1, 1], [9, -1]] },
  A347855: { int: [[4, 1], [2, -1], [1, -1]], third: true }
};
function aInd(id, n) {
  const S = SPEC[id]; let p = 1n, q = 1n;
  for (const [c, s] of S.int) if (s > 0) p *= big(c * n); else q *= big(c * n);
  if (S.half) for (const [c, s] of S.half) { const [a, b] = halfInd(c * n); if (s > 0) { p *= a; q *= b; } else { p *= b; q *= a; } }
  if (S.third) for (let j = 1; j <= n; j++) { p *= 3n; q *= BigInt(n + 3 * j); }   // (n/3)!/(4n/3)! = 1/∏ (n/3 + j)
  return fr(p, q);
}
function bInd(n) { let d = big(6 * n + 2) * big(3 * n + 1); for (let k = 0; k <= 3 * n; k++) d *= BigInt(3 * n + 3 * k + 4); return fr(big(12 * n + 4), d); }
function cInd(n) { let d = big(6 * n + 4) * big(3 * n + 1); for (let k = 0; k <= 3 * n + 2; k++) d *= BigInt(3 * n + 3 * k + 2); return fr(big(12 * n + 8), d); }
const vpB = (x, p) => { let v = 0; const P = BigInt(p); while (x % P === 0n) { x /= P; v++; } return v; };
function trial(x) { const out = []; for (let p = 2n; p * p <= x || x > 1n; p++) { if (p * p > x && x > 1n) { out.push([Number(x), 1]); break; } let v = 0; while (x % p === 0n) { x /= p; v++; } if (v) out.push([Number(p), v]); if (x === 1n) break; } return out; }
function Lexact(id, num, den, odd) {   // the step function at x = num/den with integer floors
  const S = SPEC[id], fl = (a, b) => Math.floor(a / b);
  return S.int.reduce((t, [a, s]) => t + s * fl(a * num, den), 0) + S.half.reduce((t, [c, s]) => t + s * (odd ? fl(c * num + den, 2 * den) : fl(c * num, 2 * den)), 0);
}
const lg10 = (c) => c * Math.log10(c);

await page.goto(origin + BASE + 'viz/factorial-steps/');
await page.waitForFunction(() => window.FS_DEBUG && FS_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle(); await pause();
let i = await info();

/* ---------- exact values ---------- */
check('the page opens on the A347854 skyline with n = 0 … 30', i.mode === 'skyline' && i.seq === 'A347854' && i.N === 30 && (await D(() => document.querySelector('.preset[aria-pressed="true"]').dataset.preset)) === 'a854');
const agree = (id, terms, n0 = 0) => terms.every((t) => { const [p, q] = aInd(id, t.n); return t.num === p.toString() && t.den === q.toString() && q === 1n; });
check('…every term a(0 … 30) equals the double-factorial computation and has denominator 1', agree('A347854', i.terms));
check('…the first 14 terms equal the OEIS data', OEIS.A347854.split(',').every((x, n) => i.terms[n].num === x));
check('…every factorization equals trial division of the page’s own number', i.terms.every((t) => JSON.stringify(t.fac) === JSON.stringify(trial(BigInt(t.num)))));
check('…the Stirling slope is 6 log 6 − 3 log 3 − 2 log 2 + ½ log ½ − 3/2 log 3/2 (base 10)', Math.abs(i.slope - (lg10(6) - lg10(3) - lg10(2) + lg10(0.5) - lg10(1.5))) < 1e-12);
check('…the readouts show the exact term, denominator 1 and the frozen verdict', /1 · \d+ · \d+/.test(await text('ro4')) && /冻结定理/.test(await text('ro5')) && /位/.test(await text('ro2L')));
let allSeq = true;
for (const id of ['A347855', 'A347856', 'A347857', 'A347858']) {
  await click(`#seqChips [data-seq="${id}"]`); const j = await info();
  if (!(j.seq === id && agree(id, j.terms) && OEIS[id].split(',').every((x, n) => j.terms[n].num === x))) allSeq = false;
}
check('A347855, A347856, A347857, A347858: every term to n = 30 matches the independent computation and the OEIS data', allSeq && (await state()).preset === null);
await click('#seqChips [data-seq="B"]'); i = await info();
const bOK = i.terms.every((t) => { const [p, q] = bInd(t.n); return t.num === p.toString() && q === 1n; });
await click('#seqChips [data-seq="C"]'); const ic = await info();
const cOK = ic.terms.every((t) => { const [p, q] = cInd(t.n); return t.num === p.toString() && q === 1n; });
check('the auxiliaries b(n), c(n) to n = 30 equal the independent products and are integers', bOK && cOK);
check('…and A347855(3n + 1) = 3³ⁿ⁺¹·b(n), A347855(3n + 2) = 3³ⁿ⁺²·c(n) for n ≤ 12', [...Array(13).keys()].every((n) => aInd('A347855', 3 * n + 1)[0] === 3n ** BigInt(3 * n + 1) * BigInt(i.terms[n].num) && aInd('A347855', 3 * n + 2)[0] === 3n ** BigInt(3 * n + 2) * BigInt(ic.terms[n].num)));
check('…the slope of b and c is 3·(slope of A347855 − log₁₀ 3)', Math.abs(i.slope - 3 * (lg10(4) - lg10(2) - lg10(1) + lg10(1 / 3) - lg10(4 / 3) - Math.log10(3))) < 1e-12 && Math.abs(ic.slope - i.slope) < 1e-15);

/* ---------- the powers of 2 and 3 (the dossier's consequences, checked numerically) ---------- */
await preset('a858'); i = await info();
check('A347858 at odd n: v₂(a(n)) ≥ 8n for every odd n ≤ 24', i.terms.filter((t) => t.n % 2).every((t) => vpB(BigInt(t.num), 2) >= 8 * t.n));
await setFrac(9 / 24);
check('…the note reports v₂ ≥ 72 at n = 9', /v₂ = \d+ ≥ 72/.test(await D(() => document.getElementById('roNote').textContent)));
let half2 = true;
for (const id of ['A347854', 'A347856', 'A347857']) for (let n = 1; n <= 29; n += 2) if (vpB(aInd(id, n)[0], 2) < 2 * n) half2 = false;
check('A347854, A347856, A347857 at odd n ≤ 29: v₂ ≥ 2n (independent computation)', half2);
await preset('a855'); i = await info();
check('A347855 with 3 ∤ n: v₃(a(n)) ≥ n for n ≤ 30', i.terms.filter((t) => t.n % 3).every((t) => vpB(BigInt(t.num), 3) >= t.n));
await preset('sporadic'); i = await info();
check('even terms: A347854(2m) = (12m)!m!/((6m)!(4m)!(3m)!) for m ≤ 15, and the note confirms it at n = 20', i.terms.filter((t) => t.n % 2 === 0).every((t) => { const m = t.n / 2; return BigInt(t.num) * big(6 * m) * big(4 * m) * big(3 * m) === big(12 * m) * big(m); }) && i.n === 20 && /✓/.test(await D(() => document.getElementById('roNote').textContent)));

/* ---------- the staircases ---------- */
await preset('stairs'); i = await info();
check('the staircase preset: A347854, p = 5, eight staircases for the four half-index sequences', i.mode === 'stairs' && i.seq === 'A347854' && i.p === 5 && i.stairs.length === 4 && i.stairs.map((s) => s.id).join() === 'A347854,A347856,A347857,A347858');
let stairOK = true, values = new Set();
for (const st of i.stairs) for (const odd of [false, true]) {
  for (let k = 0; k < 360; k++) values.add(Lexact(st.id, 2 * k + 1, 360, odd));   // every breakpoint is a multiple of 1/180
  for (const [a, b, v] of st[odd ? 'odd' : 'even']) for (let q = 1; q <= 9; q++) { const k = Math.round((a + (b - a) * q / 10) * 14400); if (Lexact(st.id, k, 14400, odd) !== v) stairOK = false; }   // constant on the whole interval
}
check('…every page staircase step equals the exact step function at nine points across its interval (no breakpoint is missing)', stairOK);
check('…at the odd multiples of 1/360 in [0, 2), one inside every interval (all breakpoints are multiples of 1/180), every staircase takes only the values 0 and 1', values.size === 2 && values.has(0) && values.has(1));
let sumOK = true;
for (const id of ['A347854', 'A347856', 'A347857', 'A347858']) for (const p of [3, 5, 7, 11, 13]) for (let n = 1; n <= 30; n++) { let s = 0; for (let pe = p; pe <= 9 * n; pe *= p) s += Lexact(id, n, pe, n % 2 === 1); if (s !== vpB(aInd(id, n)[0], p)) sumOK = false; }
check('Legendre: for p = 3, 5, 7, 11, 13 and n ≤ 30, Σₑ L(n/pᵉ) equals the exact vₚ(a(n)) for all four half-index sequences', sumOK);
await setFrac(12 / 30); i = await info();
check('…at n = 12 the page’s contributions are L(12/5ᵉ), and they add up to the page’s exact v₅', i.n === 12 && JSON.stringify(i.d.slice(0, 2)) === JSON.stringify([Lexact('A347854', 12, 5, false), Lexact('A347854', 12, 25, false)]) && i.d.reduce((a, b) => a + b, 0) === i.vp && i.vp === vpB(aInd('A347854', 12)[0], 5));
await preset('seven'); i = await info();
check('the A347856, p = 7, n = 25 preset: contributions [1, 0], v₇ = 1, matching the exact value', i.seq === 'A347856' && i.p === 7 && i.n === 25 && JSON.stringify(i.d) === '[1,0]' && i.vp === vpB(aInd('A347856', 25)[0], 7) && /✓/.test(await text('ro4')));
await preset('odd'); i = await info();
check('the A347857, p = 3, n = 17 preset uses the odd staircase: each contribution is L_odd(17/3ᵉ), [1, 1, 0, 0], summing to v₃ = 2', i.n === 17 && JSON.stringify(i.d) === JSON.stringify(i.pes.map((pe) => Lexact('A347857', 17, pe, true))) && JSON.stringify(i.d) === '[1,1,0,0]' && vpB(aInd('A347857', 17)[0], 3) === 2);
check('…in staircase mode the third-index chips are hidden', (await D(() => ['A347855', 'B', 'C'].every((s) => document.querySelector(`#seqChips [data-seq="${s}"]`).hidden))) && (await visible('pChips')));
await click('#pChips [data-p="11"]'); i = await info();
check('choosing p = 11 recomputes the contributions', i.p === 11 && i.d.reduce((a, b) => a + b, 0) === i.vp && i.vp === vpB(aInd('A347857', 17)[0], 11));
await slide('nn', 40); i = await info();
check('the largest n slider extends the terms to n = 40, all matching', i.N === 40 && agree('A347857', i.terms));

/* ---------- timeline and keys ---------- */
await click('#modeChips [data-mode="skyline"]'); await setFrac(0.95); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing the skyline to the end raises the toast that every denominator is 1', await waitToast(/分母都是 1/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
await setFrac(10 / 40); await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps n by one', (await info()).n === 11);
await page.keyboard.press('e'); await settle();
check('E jumps to the last n and pauses', (await info()).n === 40 && (await state()).playing === false);
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }).catch(() => {}); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
for (const p of ['a854', 'a855', 'stairs', 'odd']) {
  await preset(p); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('FACTORIAL//STEPS · Integer ratios of fractional factorials'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the seven dossiers, the Lean files, the OEIS entries, Blanco Gómez and Bober', (await D(() => { const h = [...document.querySelectorAll('#drawer .en a')].map((a) => a.href).join(' '); return ['oeis-a347854-bala-half-index-integrality.md', 'oeis-a347855-bala-third-index-integrality.md', 'oeis-a347855-bala-aux-b-integrality.md', 'oeis-a347855-bala-aux-c-integrality.md', 'oeis-a347856-bala-half-index-integrality.md', 'oeis-a347857-bala-half-index-integrality.md', 'oeis-a347858-bala-half-index-integrality.md', 'OeisA347854BalaHalfIndexIntegral.lean', 'OeisA347855BalaThirdIndexIntegral.lean', 'oeis.org/A347854', 'oeis.org/A347858', '10.5281/zenodo.23426707', '10.1112/jlms/jdn078'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="factorial-steps"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.FS_DEBUG && FS_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'factorial-steps');

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
