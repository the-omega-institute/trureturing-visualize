#!/usr/bin/env node
// Browser regression suite for viz/yb-automaton (Playwright + Chromium with software WebGL).
//   node tests/yb-automaton.test.mjs
// Reads page state through the read-only window.YB_DEBUG probe and checks it against an independent implementation: all
// solutions for q = 4 and 8 by Heap's algorithm, the test's own transcription of Lean's rmat, carry and step, step^q = id on
// every small state, and exhaustive period counts for every preset.
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
  const start = await page.evaluate(() => YB_DEBUG.frames());
  await page.waitForFunction((f0) => !YB_DEBUG.pending() && YB_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => YB_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D((t) => YB_DEBUG.setT(t), t); await settle(); };
const info = () => D(() => YB_DEBUG.info());
const state = () => D(() => YB_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => YB_DEBUG.frames()); await page.waitForFunction((t) => YB_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- independent implementation ---------- */
const fyb = (f, q) => { for (let x = 0; x < q; x++) for (let y = 0; y < q; y++) if ((f[x] ^ f[x ^ f[y]]) !== f[x ^ f[y ^ f[x]]]) return false; return true; };
const viol = (f, q) => { let v = 0; for (let x = 0; x < q; x++) for (let y = 0; y < q; y++) if ((f[x] ^ f[x ^ f[y]]) !== f[x ^ f[y ^ f[x]]]) v++; return v; };
/* every permutation by Heap's algorithm (a different order from the page's lexicographic one) */
function heap(q) { const a = Array.from({ length: q }, (_, i) => i), c = new Array(q).fill(0), out = [a.slice()]; let i = 0; while (i < q) { if (c[i] < i) { const j = i % 2 ? c[i] : 0; [a[j], a[i]] = [a[i], a[j]]; out.push(a.slice()); c[i]++; i = 0; } else { c[i] = 0; i++; } } return out; }
const hx = (f) => f.map((v) => v.toString(16)).join('');
/* Lean's rmat and carry: carry 0 = b, carry (i + 1) = (rmat f x_i (carry i)).2; the new cell i is (rmat f x_i (carry i)).1 */
const rmat = (f, x, y) => [y ^ f[x ^ y], x ^ f[x ^ y]];
function stepL(f, xs, b) { const carry = [b]; for (let i = 0; i < xs.length; i++) carry.push(rmat(f, xs[i], carry[i])[1]); return [xs.map((x, i) => rmat(f, x, carry[i])[0]), carry[xs.length]]; }
const eqS = (a, b) => a[1] === b[1] && a[0].every((v, i) => v === b[0][i]);
function minPeriod(f, xs, b, cap = 1000) { let s = [xs, b]; for (let k = 1; k <= cap; k++) { s = stepL(f, s[0], s[1]); if (eqS(s, [xs, b])) return k; } return Infinity; }
const states = (q, N) => { const out = []; const total = q ** (N + 1); for (let c = 0; c < total; c++) { let r = c; const xs = []; for (let i = 0; i < N; i++) { xs.push(r % q); r = Math.floor(r / q); } out.push([xs, r]); } return out; };
const transl = (f, q) => { const u = []; for (let t = 1; t < q; t++) if (f.every((v, x) => f[x ^ t] === (v ^ t))) u.push(t); return u; };
const histRef = (f, q, N) => { const m = new Map(); for (const [xs, b] of states(q, N)) { const p = minPeriod(f, xs, b); m.set(p, (m.get(p) || 0) + 1); } return [...m.entries()].sort((a, b) => a[0] - b[0]); };
const SOL = { 4: heap(4).filter((f) => fyb(f, 4)), 8: heap(8).filter((f) => fyb(f, 8)) };

await page.goto(`${origin}${BASE}viz/yb-automaton/`);
await page.waitForFunction(() => window.YB_DEBUG && YB_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();

/* ---------- the solutions ---------- */
check('opens on the q = 16 preset: map 0, N = 2, initial state (12, 3; 5), period 16, playing', st.preset === 'lean' && i.q === 16 && i.fi === 0 && i.N === 2 && i.xs.join() === '12,3' && i.b === 5 && i.p === 16);
const pg4 = await D(() => YB_DEBUG.solutions(4)), pg8 = await D(() => YB_DEBUG.solutions(8));
check('the page’s bijective solutions for q = 4 and 8 are exactly those found by Heap’s algorithm: 16 and 736', pg4.length === 16 && pg8.length === 736 && [...pg4].sort().join() === SOL[4].map(hx).sort().join() && [...pg8].sort().join() === SOL[8].map(hx).sort().join());
const norm = (q) => SOL[q].filter((f) => f[0] === 0);
const shiftOK = (q) => SOL[q].every((f) => { const a = f.indexOf(0), g = f.map((_, x) => f[x ^ a]); return g[0] === 0 && fyb(g, q); });
check('with f(0) = 0 there are 4 and 92 solutions, and translating any solution to f(0) = 0 keeps the equation (so all = q × normalized)', norm(4).length === 4 && norm(8).length === 92 && SOL[4].length === 4 * 4 && SOL[8].length === 8 * 92 && shiftOK(4) && shiftOK(8));
const pg16 = await D(() => YB_DEBUG.solutions(16));
check('the 8 embedded maps for q = 16 are bijections solving the equation', pg16.length === 8 && pg16.every((s) => { const f = [...s].map((c) => parseInt(c, 16)); return new Set(f).size === 16 && fyb(f, 16); }));
const allSol = [...SOL[4].map((f) => [f, 4]), ...SOL[8].map((f) => [f, 8]), ...pg16.map((s) => [[...s].map((c) => parseInt(c, 16)), 16])];
check('every solution (16 + 736 + 8) has a translation u ≠ 0 with f(x + u) = f(x) + u, as in Lean’s exists_translation', allSol.every(([f, q]) => transl(f, q).length > 0));

/* ---------- step^q = id ---------- */
let idOK = true, idCount = 0;
for (const [f, q] of allSol) for (const N of q === 16 ? [1, 2] : [1, 2]) for (const [xs, b] of states(q, N)) { let s = [xs, b]; for (let k = 0; k < q; k++) s = stepL(f, s[0], s[1]); idCount++; if (!eqS(s, [xs, b])) idOK = false; }
check('step^q = id on every initial state for N = 1, 2 and every solution above', idOK, `${idCount} states`);
let id3 = true; for (const f of SOL[8].filter((_, k) => k % 23 === 0)) for (const [xs, b] of states(8, 3)) { let s = [xs, b]; for (let k = 0; k < 8; k++) s = stepL(f, s[0], s[1]); if (!eqS(s, [xs, b])) id3 = false; }
check('step^8 = id on all 4096 states with N = 3 for every 23rd solution of q = 8', id3);
const rowsRef = [[[12, 3], 5]]; const f0 = [...pg16[0]].map((c) => parseInt(c, 16)); for (let k = 0; k < 32; k++) rowsRef.push(stepL(f0, rowsRef[k][0], rowsRef[k][1]));
check('the page’s 33 space-time rows for the q = 16 preset match stepping Lean’s definitions', i.rows.length === 33 && i.rows.every((r, k) => eqS(r, rowsRef[k])) && minPeriod(f0, [12, 3], 5) === 16);

/* ---------- histograms ---------- */
const histMatch = async (p, ref) => { await preset(p); const x = await info(); return x.hist.exhaustive && JSON.stringify(x.hist.counts) === JSON.stringify(ref); };
const F8 = [7, 6, 5, 4, 2, 1, 0, 3];
check('q = 16 preset: all 16³ = 4096 initial states have period 16 (independent count)', await histMatch('lean', histRef(f0, 16, 2)) && JSON.stringify(histRef(f0, 16, 2)) === '[[16,4096]]');
check('even preset (q = 8, N = 4): all 32768 initial states have period 8', await histMatch('even', histRef(F8, 8, 4)) && JSON.stringify(histRef(F8, 8, 4)) === '[[8,32768]]');
check('odd preset (q = 8, N = 3): 2560 states of period 2 and 1536 of period 4', await histMatch('odd', histRef(F8, 8, 3)) && JSON.stringify(histRef(F8, 8, 3)) === '[[2,2560],[4,1536]]');
check('four preset (q = 4, f = 1230, N = 6): all 16384 initial states have period 4', await histMatch('four', histRef([1, 2, 3, 0], 4, 6)) && (await info()).f.join('') === '1230' && JSON.stringify(histRef([1, 2, 3, 0], 4, 6)) === '[[4,16384]]');
const BR = [4, 2, 5, 0, 7, 6, 3, 1];
check('broken preset: a bijection with 44 violating pairs; its 512 states have periods 6 and 10, neither dividing 8', await histMatch('broken', histRef(BR, 8, 2)) && viol(BR, 8) === 44 && (await info()).viol === 44 && JSON.stringify(histRef(BR, 8, 2)) === '[[6,192],[10,320]]');
await preset('linear'); i = await info();
const fl = i.f;
check('linear preset: an additive involution; the all-zero state has period 1 and the sampled states period 2', i.additive && fl.every((v, a) => fl.every((w, b) => fl[a ^ b] === (v ^ w))) && fl.every((v, x) => fl[v] === x) && minPeriod(fl, [0, 0, 0, 0, 0, 0], 0) === 1 && !i.hist.exhaustive && i.hist.n === 4096 && JSON.stringify(i.hist.counts) === '[[2,4096]]');
let perOK = true;
for (const p of ['lean', 'even', 'odd', 'four', 'broken']) { await preset(p); const x = await info(); if (x.p !== minPeriod(x.f, x.xs, x.b)) perOK = false; }
check('for every preset the page’s period of the shown initial state equals the minimal period by stepping', perOK);
for (const p of ['lean', 'even', 'odd', 'four', 'linear', 'broken']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }

/* ---------- readouts and controls ---------- */
await preset('lean'); await pause(); await setT(0); i = await info();
check('the readouts give the map, its translations, the state, the period and the histogram', /a869bfce2d315740 · \{b\} · 否 · 0/.test(await text('ro2')) && /p = 16 整除 16/.test(await text('ro3')) && /16: 4096/.test(await text('ro4')));
check('the rail marks t = 0, p = 16 and t = 32', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 't = 0 | p = 16 | t = 32');
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ advances one time step and marks the settings custom', (await info()).tk === 1 && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await page.keyboard.press('e'); await settle();
check('E jumps to the last step and pauses', (await info()).tk === 32 && (await state()).playing === false);
await click('#qChips [data-q="8"]'); i = await info();
check('the q chips switch to q = 8 with the first solution', i.q === 8 && i.fi === 0 && i.count === 736);
await D(() => { const e = document.getElementById('fIn'); e.value = 100; e.dispatchEvent(new Event('input')); const g = document.getElementById('nIn'); g.value = 3; g.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the sliders choose solution 100 and N = 3', i.fi === 100 && i.N === 3 && i.f.join() === pg8[100].split('').map((c) => parseInt(c, 16)).join());
const before = JSON.stringify([i.xs, i.b]); await click('#reseed'); i = await info();
check('“new initial state” draws another state', JSON.stringify([i.xs, i.b]) !== before && (await state()).seed === 2);
await preset('lean'); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing reports the return to the initial state at t = 16', await waitToast(/t = 16.*回到初态/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await preset('lean');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'broken']) {
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
check('English title', (await D(() => document.title)).startsWith('YB//AUTOMATON · Yang–Baxter automata over a field of order 2ⁿ have period dividing 2ⁿ'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['araoka-2026-yang-baxter-automaton-period.md', 'D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.lean', 'Blueprint/D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.md', 'Library/StatisticalMechanics/araoka2026integrable.md', 'doi.org/10.1007/s11040-026-09569-9', 'arxiv.org/abs/2602.17148'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="yb-automaton"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.YB_DEBUG && YB_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'yb-automaton');

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
