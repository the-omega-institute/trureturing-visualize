#!/usr/bin/env node
// Browser regression suite for viz/book-roots (Playwright + Chromium with software WebGL).
//   node tests/book-roots.test.mjs
// Reads page state through the read-only window.BK_DEBUG probe and checks it against an independent implementation: the book
// built from Lean's pageForward relation, dominating sets counted vertex by vertex, exact BigInt coefficients, and Sturm
// sequences that count the real roots of D/x² exactly in (−∞, −2), (−2, −1/2) and (−1/2, 0).
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
  const start = await page.evaluate(() => BK_DEBUG.frames());
  await page.waitForFunction((f0) => !BK_DEBUG.pending() && BK_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => BK_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setN = async (n) => { await D((n) => BK_DEBUG.setN(n), n); await settle(); };
const info = () => D(() => BK_DEBUG.info());
const state = () => D(() => BK_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => BK_DEBUG.frames()); await page.waitForFunction((t) => BK_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- the book from Lean's pageForward: 0–1, 1–(2i+2), (2i+2)–(2i+3), (2i+3)–0 ---------- */
function book(n) {
  const N = 2 * n + 2, adj = Array.from({ length: N }, () => new Set());
  const fwd = (u, v) => (u === 0 && v === 1) || [...Array(n).keys()].some((i) => (u === 1 && v === 2 * i + 2) || (u === 2 * i + 2 && v === 2 * i + 3) || (u === 2 * i + 3 && v === 0));
  for (let u = 0; u < N; u++) for (let v = 0; v < N; v++) if (u !== v && (fwd(u, v) || fwd(v, u))) adj[u].add(v);
  return adj;
}
const dominates = (adj, mask) => adj.every((nb, v) => ((mask >> v) & 1) || [...nb].some((u) => (mask >> u) & 1));
function enumerate(n) { const adj = book(n), N = adj.length, c = new Array(N + 1).fill(0); for (let m = 0; m < 1 << N; m++) if (dominates(adj, m)) { let k = 0; for (let x = m; x; x &= x - 1) k++; c[k]++; } while (c.length > 1 && !c[c.length - 1]) c.pop(); return c; }
/* exact coefficients of D/x² (constant term first) as BigInt, by expanding (1 + x)^{2n} + (2x + 1)x^{n−2}(x + 2)^n − 2x^{n−2} for n ≥ 2 */
const bmul = (a, b) => { const r = new Array(a.length + b.length - 1).fill(0n); a.forEach((x, i) => b.forEach((y, j) => { r[i + j] += x * y; })); return r; };
const bpow = (a, k) => { let r = [1n]; for (let i = 0; i < k; i++) r = bmul(r, a); return r; };
const badd = (a, b) => { const r = new Array(Math.max(a.length, b.length)).fill(0n); a.forEach((x, i) => { r[i] += x; }); b.forEach((x, i) => { r[i] += x; }); return r; };
function pExact(n) {
  if (n === 1) return [6n, 4n, 1n];
  let p = bpow([1n, 1n], 2 * n);
  p = badd(p, [...new Array(n - 2).fill(0n), ...bmul([1n, 2n], bpow([2n, 1n], n))]);
  p = badd(p, [...new Array(n - 2).fill(0n), -2n]);
  while (p.length > 1 && p[p.length - 1] === 0n) p.pop();
  return p;
}
/* Sturm sequence with primitive pseudo-remainders; sign variations at rational points */
const babs = (x) => (x < 0n ? -x : x), bgcd = (a, b) => { a = babs(a); b = babs(b); while (b) [a, b] = [b, a % b]; return a; };
const trimB = (p) => { const r = p.slice(); while (r.length > 1 && r[r.length - 1] === 0n) r.pop(); return r; };
const deriv = (p) => p.slice(1).map((c, i) => c * BigInt(i + 1));
function prem(a, b) {
  let r = a.slice(); const db = b.length - 1, lb = b[db]; const sgn = lb < 0n ? -1n : 1n; let flips = 0;
  while (r.length - 1 >= db && !(r.length === 1 && r[0] === 0n)) {
    const lr = r[r.length - 1], sh = r.length - 1 - db;
    r = r.map((x) => x * lb); flips++;
    for (let i = 0; i <= db; i++) r[i + sh] -= lr * b[i];
    r = trimB(r); if (r.length - 1 < db) break; if (r.length === 1 && r[0] === 0n) break;
  }
  /* we multiplied by lb `flips` times; undo its sign so that r is a positive multiple of the true remainder */
  if (sgn < 0n && flips % 2) r = r.map((x) => -x);
  const g = r.reduce((s, x) => bgcd(s, x), 0n) || 1n; return r.map((x) => x / g);
}
function sturm(p) { const seq = [p, deriv(p)]; while (seq[seq.length - 1].length > 1) { const r = prem(seq[seq.length - 2], seq[seq.length - 1]).map((x) => -x); if (r.length === 1 && r[0] === 0n) break; seq.push(r); } return seq; }
/* the sign of p(num/den), den > 0, from den^deg·p(num/den) */
const evalSign = (p, num, den) => { let v = 0n; p.forEach((c, k) => { v += c * num ** BigInt(k) * den ** BigInt(p.length - 1 - k); }); return v > 0n ? 1 : v < 0n ? -1 : 0; };
const signAtNegInf = (p) => { const lc = p[p.length - 1]; return (lc > 0n ? 1 : -1) * ((p.length - 1) % 2 ? -1 : 1); };
const variations = (signs) => { const s = signs.filter((x) => x !== 0); let v = 0; for (let i = 1; i < s.length; i++) if (s[i] !== s[i - 1]) v++; return v; };
const V = (seq, num, den) => variations(seq.map((q) => evalSign(q, num, den)));
const Vinf = (seq) => variations(seq.map(signAtNegInf));
/* exact real-root counts of D/x² in (−∞, −2), (−2, −1/2), (−1/2, 0); squarefree when the sequence ends in a constant */
function rootCounts(n) {
  const p = pExact(n), seq = sturm(p), last = seq[seq.length - 1];
  const a = Vinf(seq), b = V(seq, -2n, 1n), c = V(seq, -1n, 2n), d = V(seq, 0n, 1n);
  return { below2: a - b, mid: b - c, near0: c - d, squarefree: last.length === 1, at2: evalSign(p, -2n, 1n), atHalf: evalSign(p, -1n, 2n) };
}

/* ---------- open ---------- */
await page.goto(origin + BASE + 'viz/book-roots/');
await page.waitForFunction(() => window.BK_DEBUG && BK_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let [s0, i] = await D(() => [BK_DEBUG.state(), BK_DEBUG.info()]);
check('opens on Lean’s counterexample n = 1, paused', s0.preset === 'lean' && i.n === 1 && s0.playing === false);

/* ---------- n = 1 ---------- */
const b1 = book(1), cyc = [[0, 1], [1, 2], [2, 3], [3, 0]];
check('B₁ built from Lean’s relation is the four-cycle 0–1–2–3–0', b1.every((nb) => nb.size === 2) && cyc.every(([u, v]) => b1[u].has(v)));
const e1 = enumerate(1);
check('C₄ has 11 dominating sets — 6 pairs, 4 triples, the whole set — so D = 6x² + 4x³ + x⁴, as the page enumerates', e1.join() === '0,0,6,4,1' && i.enumCoeffs.join() === '0,0,6,4,1' && i.coeffs.join() === '0,0,6,4,1' && i.domCount === 11);
const r1 = rootCounts(1);
check('x² + 4x + 6 = (x + 2)² + 2 has no real root (Sturm), the page reports none, and its complex roots are −2 ± i√2', r1.below2 + r1.mid + r1.near0 === 0 && i.realRoots.length === 0 && i.complexRoots.length === 2 && i.complexRoots.every(([a, b]) => Math.abs(a + 2) < 1e-9 && Math.abs(Math.abs(b) - Math.SQRT2) < 1e-9) && /恒正/.test(await text('roNote')));

/* ---------- coefficients ---------- */
let enOK = true, enBad = [];
for (let n = 1; n <= 8; n++) { await setN(n); const x = await info(), e = enumerate(n); if (x.enumCoeffs.join() !== e.join() || x.coeffs.join() !== e.join()) { enOK = false; enBad.push(n); } }
check('for n = 1 … 8 an independent vertex-by-vertex count of dominating sets equals the page’s enumeration and its closed form', enOK, enBad.join(' '));
let cfOK = true, cfBad = [];
for (let n = 2; n <= 20; n++) { await setN(n); const x = await info(), p = pExact(n); if (x.coeffs.slice(2).join() !== p.map(String).join() || x.coeffs[0] !== 0 || x.coeffs[1] !== 0) { cfOK = false; cfBad.push(n); } }
check('for n = 2 … 20 the page’s coefficients are exactly x² times the BigInt expansion of (1 + x)^{2n} + (2x + 1)x^{n−2}(x + 2)^n − 2x^{n−2}', cfOK, cfBad.join(' '));
check('every book has smallest dominating set 2 (the spine): no constant or linear term, x² coefficient 6, 3, 1, 1, … for n = 1, 2, 3, 4', [1, 2, 3, 4].every((n, k) => enumerate(n)[2] === [6, 3, 1, 1][k] && enumerate(n)[1] === 0));

/* ---------- the roots, exactly ---------- */
const all = await D(() => BK_DEBUG.allReal());
let stOK = true, stBad = [];
for (let n = 2; n <= 20; n++) {
  const r = rootCounts(n), pg = all[n - 1];
  const want = n % 2 === 0 ? [1, 0, 1] : [0, 0, 2], got = [r.below2, r.mid, r.near0];
  const pageCounts = [pg.filter((x) => x < -2).length, pg.filter((x) => x > -2 && x < -0.5).length, pg.filter((x) => x > -0.5 && x < 0).length];
  if (got.join() !== want.join() || !r.squarefree || r.at2 === 0 || r.atHalf === 0 || pageCounts.join() !== want.join()) { stOK = false; stBad.push(`${n}: ${got} / page ${pageCounts}`); }
}
check('Sturm sequences in exact arithmetic: for n = 2 … 20, D/x² has exactly the conjectured real roots, all simple, and the page finds the same ones in each interval', stOK, stBad.join(' '));
let brOK = true;
for (const n of [2, 3, 7, 16, 20]) for (const r of all[n - 1]) {
  const den = 10n ** 9n, lo = BigInt(Math.floor((r - 1e-6) * 1e9)), hi = BigInt(Math.ceil((r + 1e-6) * 1e9)), p = pExact(n);
  if (evalSign(p, lo, den) * evalSign(p, hi, den) !== -1) brOK = false;
}
check('each root the page reports for n = 2, 3, 7, 16, 20 is bracketed within ±10⁻⁶ by an exact sign change', brOK);
await setN(12); i = await info();
const resid = i.complexRoots.map(([a, b]) => { let re = 0, im = 0; const p = pExact(12).map(Number); for (let k = p.length - 1; k >= 0; k--) { const nr = re * a - im * b + p[k], ni = re * b + im * a; re = nr; im = ni; } return Math.hypot(re, im) / Math.max(1, Math.hypot(a, b) ** 24); });
check('n = 12: the page gives 24 complex roots, each nearly a root of the exact polynomial, with the two real ones among them', i.complexRoots.length === 24 && resid.every((x) => x < 1e-6) && i.complexRoots.filter(([, b]) => b === 0).length === 2, `max scaled residual ${Math.max(...resid).toExponential(1)}`);

/* ---------- presets and their numbers ---------- */
await preset('two'); i = await info();
check('two preset: roots ≈ −2.2113 and −0.2343, as the note says', i.n === 2 && Math.abs(i.realRoots[0] + 2.211299) < 1e-5 && Math.abs(i.realRoots[1] + 0.234349) < 1e-5 && /−2\.2113/.test(await text('presetNote')) && /−0\.2343/.test(await text('presetNote')));
await preset('three'); i = await info();
check('three preset: roots ≈ −0.2451 and −0.1563, both in (−1/2, 0)', i.n === 3 && Math.abs(i.realRoots[0] + 0.245122) < 1e-5 && Math.abs(i.realRoots[1] + 0.156266) < 1e-5 && i.verdict.holds);
await preset('edge'); i = await info();
check('edge preset: n = 16, roots ≈ −2.5352 and −0.4985', i.n === 16 && Math.abs(i.realRoots[0] + 2.535199) < 1e-5 && Math.abs(i.realRoots[1] + 0.498502) < 1e-5);
await preset('sets');
const seen = new Set(); let domOK = true; const adj4 = book(4);
for (let k = 0; k < 4; k++) { const x = await info(); seen.add(x.domSet); if (!dominates(adj4, x.domSet)) domOK = false; await page.waitForFunction((m) => BK_DEBUG.info().domSet !== m, x.domSet, { timeout: 10000 }).catch(() => {}); }
check('sets preset: the lit vertex sets change over time and every one dominates B₄', domOK && seen.size >= 3 && (await info()).setsTotal === enumerate(4).reduce((s, v) => s + v, 0), `${seen.size} sets seen`);
for (const p of ['lean', 'sweep', 'two', 'three', 'edge', 'sets']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }

/* ---------- controls ---------- */
check('the rail marks n = 1 (Lean), n = 10 and n = 20', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 'n = 1（Lean） | n = 10 | n = 20');
await preset('two');
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ adds a page and marks the settings custom', (await info()).n === 3 && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await page.keyboard.press('e'); await settle();
check('E jumps to n = 20 and pauses', (await info()).n === 20 && (await state()).playing === false);
await D(() => { const e = document.getElementById('nIn'); e.value = 5; e.dispatchEvent(new Event('input')); }); await settle();
check('the page slider sets n', (await info()).n === 5);
await preset('sweep'); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('leafing through to n = 20 reports that only n = 1 breaks the pattern', await waitToast(/与猜想不符的只有 n = 1——/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await preset('two');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'sets']) {
  await preset(p);
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
check('English title', (await D(() => document.title)).startsWith('BOOK//ROOTS · The book-graph domination root conjecture fails at the square'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['rather-2026-book-domination-root-conjecture.md', 'D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.lean', 'Blueprint/D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.md', 'Library/Geometry/rather2026bookroots.md', 'doi.org/10.48550/arXiv.2604.08998', 'arxiv.org/abs/2604.08998'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="book-roots"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.BK_DEBUG && BK_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'book-roots');

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
