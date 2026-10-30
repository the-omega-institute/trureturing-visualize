#!/usr/bin/env node
// Browser regression suite for viz/leggett-six (Playwright + Chromium with software WebGL).
//   node tests/leggett-six.test.mjs
// Reads page state through the read-only window.LG_DEBUG probe and checks it against an independent implementation in exact
// rational arithmetic: the pair tables of Lean's example, the polygon and three-time LG inequalities as quadratic forms
// sᵀ(I + tC)s, the eigenvalues in closed form 1 ± t√5/2, the 16-point joint law at t = 0.8 checked table by table, and the
// weight W = Σ bᵢxᵢ over all 64 sign vectors.
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
  const start = await page.evaluate(() => LG_DEBUG.frames());
  await page.waitForFunction((f0) => !LG_DEBUG.pending() && LG_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => LG_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D((t) => LG_DEBUG.setT(t), t); await settle(); };
const info = () => D(() => LG_DEBUG.info());
const state = () => D(() => LG_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => LG_DEBUG.frames()); await page.waitForFunction((t) => LG_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const Q = (n, d = 1n) => { n = BigInt(n); d = BigInt(d); if (d < 0n) { n = -n; d = -d; } const g = gcd(n, d) || 1n; return [n / g, d / g]; };
const qadd = (a, b) => Q(a[0] * b[1] + b[0] * a[1], a[1] * b[1]), qmul = (a, b) => Q(a[0] * b[0], a[1] * b[1]);
const qcmp = (a, b) => { const x = a[0] * b[1] - b[0] * a[1]; return x > 0n ? 1 : x < 0n ? -1 : 0; };
const qnum = (a) => Number(a[0]) / Number(a[1]);
/* Lean's correlations: index 5 is time 6; C(4, 5) = −1/2, C(i, 5) = 1/2 otherwise, everything else 0 (scaled by t) */
const corr = (t, i, j) => { const [a, b] = i < j ? [i, j] : [j, i]; if (b !== 5 || a === b) return Q(0); return qmul(t, a === 4 ? Q(-1, 2) : Q(1, 2)); };
const quad = (t, s) => { let v = Q(0); for (let i = 0; i < 6; i++) for (let j = 0; j < 6; j++) v = qadd(v, qmul(Q(s[i] * s[j]), i === j ? Q(1) : corr(t, i, j))); return v; };
const signs = (n) => Array.from({ length: 2 ** n }, (_, m) => Array.from({ length: n }, (_, k) => ((m >> k) & 1 ? -1 : 1)));
function myNgon(t) { let best = null; for (const s of signs(6)) { const v = quad(t, s); if (!best || qcmp(v, best) < 0) best = v; } return best; }
function mySub(t) {
  let best = null;
  for (let m = 0; m < 64; m++) {
    const idx = [0, 1, 2, 3, 4, 5].filter((i) => (m >> i) & 1); if (idx.length < 3) continue;
    for (const s of signs(idx.length)) { let v = Q(idx.length - (idx.length % 2)); for (let p = 0; p < idx.length; p++) for (let q = p + 1; q < idx.length; q++) v = qadd(v, qmul(Q(2 * s[p] * s[q]), corr(t, idx[p], idx[q]))); if (!best || qcmp(v, best) < 0) best = v; }
  }
  return best;
}
function myLG(t) { let best = null; for (let i = 0; i < 6; i++) for (let j = i + 1; j < 6; j++) for (let k = j + 1; k < 6; k++) for (const [a, b, c] of signs(3)) { const v = qadd(qadd(qadd(Q(1), qmul(Q(a * b), corr(t, i, j))), qmul(Q(a * c), corr(t, i, k))), qmul(Q(b * c), corr(t, j, k))); if (!best || qcmp(v, best) < 0) best = v; } return best; }
const Bv = [1, 1, 1, 1, -1, -2];

/* ---------- open ---------- */
await page.goto(origin + BASE + 'viz/leggett-six/');
await page.waitForFunction(() => window.LG_DEBUG && LG_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(); const s0 = await state();
check('opens on Lean’s example (t = 1), paused', s0.preset === 'lean' && i.t === 1 && s0.playing === false);

/* ---------- Lean's instance, exactly ---------- */
const T1 = Q(1);
check('the page’s t = 1 correlations are Lean’s: C(i, 6) = 1/2 for i ≤ 4, C(5, 6) = −1/2, all others 0', i.C.every((r, a) => r.every((v, b) => (a === b ? v === 0 : v === qnum(corr(T1, a, b))))));
check('every pair table (1 + ab·C)/4 is nonnegative and normalized, with one-time marginals 1/2', [0, 1, 2, 3, 4, 5].every((a) => [0, 1, 2, 3, 4, 5].every((b) => a === b || [[1, 1], [1, -1], [-1, 1], [-1, -1]].every(([x, y]) => qcmp(qmul(qadd(Q(1), qmul(Q(x * y), corr(T1, a, b))), Q(1, 4)), Q(0)) >= 0))));
check('the 6-gon minimum is exactly 1, every subset polygon holds (minimum slack 0) and the three-time LG minimum is exactly 0', qcmp(myNgon(T1), Q(1)) === 0 && qcmp(mySub(T1), Q(0)) === 0 && qcmp(myLG(T1), Q(0)) === 0 && i.ngon === 1 && Math.abs(i.sub) < 1e-12 && Math.abs(i.lg) < 1e-12);
const Wsq = signs(6).map((x) => Bv.reduce((s, b, k) => s + b * x[k], 0) ** 2);
let bRb = Q(0); for (let a = 0; a < 6; a++) for (let b = 0; b < 6; b++) bRb = qadd(bRb, qmul(Q(Bv[a] * Bv[b]), a === b ? Q(1) : corr(T1, a, b)));
check('W(x)² ≥ 1 for all 64 sign vectors, while bᵀ(I + C)b = −1 exactly, and the page reports −1', Wsq.every((w) => w >= 1) && Math.min(...Wsq) === 1 && qcmp(bRb, Q(-1)) === 0 && i.avgW2 === -1 && i.mu === null);
check('the eigenvalues of I + C are 1 − √5/2, 1, 1, 1, 1, 1 + √5/2', i.eig.length === 6 && [1 - Math.sqrt(5) / 2, 1, 1, 1, 1, 1 + Math.sqrt(5) / 2].every((v, k) => Math.abs(i.eig[k] - v) < 1e-12), i.eig.map((v) => v.toFixed(4)).join(', '));

/* ---------- the scaled family ---------- */
let scOK = true, scBad = [];
for (const [num, den] of [[0, 1], [1, 2], [4, 5], [17, 20], [9, 10], [1, 1], [11, 10], [6, 5]]) {
  const t = Q(num, den); await setT(num / den); const x = await info();
  const ng = qnum(myNgon(t)), sb = qnum(mySub(t)), lg = qnum(myLG(t)), lam = 1 - (num / den) * Math.sqrt(5) / 2, avg = 9 - 10 * num / den;
  if (Math.abs(x.ngon - ng) > 1e-12 || Math.abs(x.sub - sb) > 1e-12 || Math.abs(x.lg - lg) > 1e-12 || Math.abs(x.eig[0] - Math.min(1, lam)) > 1e-12 || Math.abs(x.avgW2 - avg) > 1e-12) { scOK = false; scBad.push(`${num}/${den}`); }
}
check('for t = 0, 1/2, 4/5, 17/20, 9/10, 1, 11/10, 6/5 the page’s polygon, subset-polygon and LG minima, smallest eigenvalue and bᵀ(I + tC)b match exact recomputation', scOK, scBad.join(' '));
check('the conditions are affine in t: 6-gon minimum 6 − 5t, LG minimum 1 − t (checked exactly at the same points)', [[0, 1], [1, 2], [4, 5], [1, 1], [6, 5]].every(([n, d]) => qcmp(myNgon(Q(n, d)), qadd(Q(6), qmul(Q(-5), Q(n, d)))) === 0 && qcmp(myLG(Q(n, d)), qadd(Q(1), qmul(Q(-1), Q(n, d)))) === 0));

/* ---------- the joint law ---------- */
const mu08 = await D(() => LG_DEBUG.mu08());
let exactOK = mu08.length === 16 && mu08.every(([, w]) => w === 0.1 || w === 0.05);
const W08 = mu08.map(([x, w]) => [x, w === 0.1 ? Q(1, 10) : Q(1, 20)]);
let total = Q(0); for (const [, w] of W08) total = qadd(total, w);
for (let a = 0; a < 6; a++) for (let b = a + 1; b < 6; b++) for (const [p, q] of [[1, 1], [1, -1], [-1, 1], [-1, -1]]) {
  let s = Q(0); for (const [x, w] of W08) if (x[a] === p && x[b] === q) s = qadd(s, w);
  if (qcmp(s, qmul(qadd(Q(1), qmul(Q(p * q), corr(Q(4, 5), a, b))), Q(1, 4))) !== 0) exactOK = false;
}
check('the 16-point law at t = 0.8 matches all 60 pair tables exactly (weights 1/10 and 1/20, total mass 1)', exactOK && qcmp(total, Q(1)) === 0);
let mixOK = true;
for (const t of [0, 0.25, 0.5, 0.8]) {
  await setT(t); const x = await info();
  if (!x.mu || x.mu.some((v) => v < 0) || Math.abs(x.mu.reduce((s, v) => s + v, 0) - 1) > 1e-12 || x.muErr > 1e-12) { mixOK = false; continue; }
  /* recount the pair marginals from the page's law independently */
  for (let a = 0; a < 6; a++) for (let b = a + 1; b < 6; b++) for (const [p, q] of [[1, 1], [1, -1], [-1, 1], [-1, -1]]) {
    let s = 0; x.mu.forEach((v, k) => { const xa = (k >> a) & 1 ? -1 : 1, xb = (k >> b) & 1 ? -1 : 1; if (xa === p && xb === q) s += v; });
    if (Math.abs(s - (1 + p * q * t * qnum(corr(Q(1), a, b))) / 4) > 1e-12) mixOK = false;
  }
}
check('for t = 0, 0.25, 0.5, 0.8 the page’s law is a probability vector whose 60 pair marginals equal the tables', mixOK);
await setT(0.81); i = await info();
check('just above 0.8 the page reports no joint law, and W² cannot average to 9 − 8.1 = 0.9 < 1', i.mu === null && Math.abs(i.avgW2 - 0.9) < 1e-12 && Wsq.every((w) => w >= 1));
await preset('psd'); i = await info();
check('psd preset: at t = 0.85 every condition holds and I + C is positive semidefinite (λmin ≈ 0.0497), yet no joint law', i.t === 0.85 && i.ngon > 0 && i.sub > 0 && i.lg > 0 && Math.abs(i.eig[0] - (1 - 0.85 * Math.sqrt(5) / 2)) < 1e-12 && i.eig[0] > 0 && i.mu === null && /半正定|positive semidefinite/.test(await text('roNote')));

/* ---------- presets, controls, timeline ---------- */
for (const p of ['lean', 'sweep', 'edge', 'psd', 'half', 'beyond']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
await preset('edge'); i = await info();
check('edge preset: t = 0.8, the law exists and its average of W² is exactly 1', i.t === 0.8 && i.mu !== null && Math.abs(i.avgW2 - 1) < 1e-12 && /存在|exists/.test(await text('ro5')));
await preset('beyond'); i = await info();
check('beyond preset: at t = 1.1 the LG minimum is −0.1, so the conditions fail', Math.abs(i.lg + 0.1) < 1e-12 && /不是反例|not a counterexample/.test(await text('roNote')));
check('the rail marks t = 0, 0.8, 2/√5, 1 (Lean) and 1.2', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 't = 0 | 0.8 | 2/√5 | 1（Lean） | 1.2');
await preset('half');
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ raises t by 0.05 and marks the settings custom', Math.abs((await info()).t - 0.55) < 1e-12 && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await page.keyboard.press('e'); await settle();
check('E jumps to t = 1.2 and pauses', (await info()).t === 1.2 && (await state()).playing === false);
await preset('sweep'); await setT(1.1); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('the sweep reports at the end that the joint law vanishes at 0.8 while the conditions last until 1', await waitToast(/0\.8 消失.*撑到 1/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'edge']) {
  await preset(p);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowLeft'); await settle();
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('LG//SIX · Six-time Leggett–Garg inequalities do not suffice'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['halliwell-mawby-2019-leggett-garg-six-time-sufficiency.md', 'D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.lean', 'Blueprint/D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.md', 'Library/Observer/halliwellmawby2019finentimes.md', 'doi.org/10.1103/PhysRevA.100.042103', 'arxiv.org/abs/1906.04865'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="leggett-six"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.LG_DEBUG && LG_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'leggett-six');

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
