#!/usr/bin/env node
// Browser regression suite for viz/modes-eighteen (Playwright + Chromium with software WebGL).
//   node tests/modes-eighteen.test.mjs
// Reads page state through the read-only window.MD_DEBUG probe and checks it against an independent implementation: the
// eighteen modes and the set S as written in the dossier, the nine contexts rebuilt from them, an exhaustive solver for the
// conservation equations (N ≤ 6, no parity argument used), the rook's-graph layout pair by pair, and replays of the page's
// runs with the test's own context sums.
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
const D2 = (expr, arg) => page.evaluate(expr, arg);
const settle = async () => {
  const start = await page.evaluate(() => MD_DEBUG.frames());
  await page.waitForFunction((f0) => !MD_DEBUG.pending() && MD_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D2(() => MD_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D2((t) => MD_DEBUG.setT(t), t); await settle(); };
const info = () => D2(() => MD_DEBUG.info());
const state = () => D2(() => MD_DEBUG.state());
const text = (id) => D2((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D2(() => MD_DEBUG.frames()); await page.waitForFunction((t) => MD_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */

/* ---------- independent implementation ---------- */
/* the eighteen modes and the set S of Lean's even_assignment, as printed in the dossier */
const MODES = [[1, 2], [1, 6], [1, 7], [1, 8], [2, 3], [2, 8], [2, 9], [3, 4], [3, 7], [3, 9], [4, 5], [4, 7], [4, 8], [5, 6], [5, 8], [5, 9], [6, 7], [6, 9]];
const SSET = [[1, 2], [1, 6], [2, 8], [3, 7], [3, 9], [4, 7], [4, 8], [5, 6], [5, 9]];
const key = ([a, b]) => `${a},${b}`;
const CTX = Array.from({ length: 10 }, (_, i) => MODES.map((p, e) => (p[0] === i || p[1] === i ? e : -1)).filter((e) => e >= 0));
const ctxSum = (v, i) => CTX[i].reduce((s, e) => s + v[e], 0);
const D = (v, N) => { let d = 0; for (let i = 1; i <= 9; i++) d += Math.abs(ctxSum(v, i) - N); return d; };
const valid = (v, N) => v.length === 18 && v.every((x) => Number.isInteger(x) && x >= 0) && [1, 2, 3, 4, 5, 6, 7, 8, 9].every((i) => ctxSum(v, i) === N);
/* exhaustive search for an assignment: always fill the context with the fewest free modes, every composition of what is left */
function solve(N) {
  const v = new Array(18).fill(-1); let nodes = 0;
  function rec() {
    nodes++;
    let best = -1, free = null;
    for (let i = 1; i <= 9; i++) { const f = CTX[i].filter((e) => v[e] < 0); if (f.length && (best < 0 || f.length < free.length)) { best = i; free = f; } }
    if (best < 0) return [1, 2, 3, 4, 5, 6, 7, 8, 9].every((i) => ctxSum(v, i) === N);
    const left = N - CTX[best].filter((e) => v[e] >= 0).reduce((s, e) => s + v[e], 0); if (left < 0) return false;
    const comp = (j, rest) => { if (j === free.length - 1) { v[free[j]] = rest; const ok = rec(); if (!ok) v[free[j]] = -1; return ok; } for (let x = 0; x <= rest; x++) { v[free[j]] = x; if (comp(j + 1, rest - x)) return true; } v[free[j]] = -1; return false; };
    return comp(0, left);
  }
  const found = rec(); return { found, v: found ? v.slice() : null, nodes };
}
const replayRun = (moves) => { const v = new Array(18).fill(0), traj = [D(v, 0)]; let nonneg = true; for (const [e, d] of moves) { v[e] += d; if (v[e] < 0) nonneg = false; } return { v, nonneg }; };

await page.goto(`${origin}${BASE}viz/modes-eighteen/`);
await page.waitForFunction(() => window.MD_DEBUG && MD_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();

/* ---------- the modes, the contexts and the theorem ---------- */
check('opens on N = 2 with Lean’s cycle construction', st.preset === 'lean' && i.N === 2 && i.method === 'lean' && i.T === 9);
const pm = await D2(() => MD_DEBUG.modes());
check('the page’s 18 modes are Lean’s modes; each context has 4 modes and each mode lies in exactly two contexts', pm.map(key).join(' ') === MODES.map(key).join(' ') && [1, 2, 3, 4, 5, 6, 7, 8, 9].every((c) => CTX[c].length === 4) && MODES.every(([a, b]) => a !== b && a >= 1 && b <= 9));
let dc = true; const rnd = (() => { let s = 12345; return () => { s = (s * 1103515245 + 12345) % 2147483648; return s / 2147483648; }; })();
for (let t = 0; t < 200; t++) { const v = MODES.map(() => Math.floor(rnd() * 20)); const lhs = [1, 2, 3, 4, 5, 6, 7, 8, 9].reduce((s, c) => s + ctxSum(v, c), 0); if (lhs !== 2 * v.reduce((a, b) => a + b, 0)) dc = false; }
check('double counting (Lean’s incidence_double_count) on 200 random occupations: Σ of the nine context sums = 2 × Σ occupations', dc);
const sol = [0, 1, 2, 3, 4, 5, 6].map((N) => solve(N));
check('an exhaustive search, without the parity argument, finds assignments for N = 0, 2, 4, 6 and proves none exist for N = 1, 3, 5', sol.every((r, N) => r.found === (N % 2 === 0) && (!r.found || valid(r.v, N))), sol.map((r, N) => `${N}:${r.found ? '✓' : '✗'}`).join(' '));
const pc = await D2(() => MD_DEBUG.cycle());
const sAdj = new Map(); SSET.forEach(([a, b]) => { sAdj.set(a, [...(sAdj.get(a) || []), b]); sAdj.set(b, [...(sAdj.get(b) || []), a]); });
let walk = [1], prev = 0; while (walk.length < 10) { const cur = walk[walk.length - 1], nxt = sAdj.get(cur).find((x) => x !== prev); prev = cur; walk.push(nxt); }
check('the page’s cycle is the dossier’s S: every context meets two of its modes, and S is the single cycle 1, 2, 8, 4, 7, 3, 9, 5, 6', pc.map(key).sort().join(' ') === SSET.map(key).sort().join(' ') && [1, 2, 3, 4, 5, 6, 7, 8, 9].every((c) => SSET.filter(([a, b]) => a === c || b === c).length === 2) && walk.join(',') === '1,2,8,4,7,3,9,5,6,1');
const grid = await D2(() => MD_DEBUG.grid());
let rook = true; for (let a = 1; a <= 9; a++) for (let b = a + 1; b <= 9; b++) { const share = MODES.some(([x, y]) => x === a && y === b), same = grid[a][0] === grid[b][0] || grid[a][1] === grid[b][1]; if (share !== same) rook = false; }
check('the page’s torus layout is a 3 × 3 rook’s graph: two contexts share a mode exactly when they share a row or a column (all 36 pairs)', rook && new Set(Object.values(grid).map((g) => g.join())).size === 9);

/* ---------- the page's runs ---------- */
let runsOK = true, parityOK = true; const bad = [];
for (let N = 0; N <= 12; N++) for (const [m, sd] of [['lean', 1], ['greedy', 1], ['greedy', 2], ['greedy', 3]]) {
  const r = await D2(([N, m, sd]) => MD_DEBUG.run(N, m, sd), [N, m, sd]), rr = replayRun(r.moves);
  const v = new Array(18).fill(0); for (const [e, d] of r.moves) { v[e] += d; if (D(v, N) % 2 !== N % 2) parityOK = false; }
  const ok = rr.nonneg && rr.v.join() === r.final.join() && (N % 2 === 0 ? valid(r.final, N) : D(r.final, N) === 1);
  if (!ok) { runsOK = false; bad.push(`${N}/${m}/${sd}`); }
}
check('for N = 0 … 12, Lean’s construction and three local searches end in valid assignments for even N and at D = 1 for odd N (test sums)', runsOK, bad.join(' '));
check('along every one of those runs D keeps the parity of N', parityOK);
i = await info();
check('the lean preset’s final assignment is 1 on each mode of S and 0 elsewhere, every context summing to 2', i.final.every((x, e) => x === (SSET.some((p) => key(p) === key(MODES[e])) ? 1 : 0)) && valid(i.final, 2));

/* ---------- presets ---------- */
const facts = { one: [1, 'greedy', 1], three: [3, 'greedy', 1], six: [6, 'greedy', 0], ten: [10, 'lean', 0], nine: [9, 'lean', 1] };
for (const [p, [N, m, d]] of Object.entries(facts)) {
  await preset(p); i = await info();
  const extra = p === 'ten' ? i.final.every((x, e) => x === (SSET.some((q) => key(q) === key(MODES[e])) ? 5 : 0)) : p === 'nine' ? [1, 2, 3, 4, 5, 6, 7, 8, 9].filter((c) => ctxSum(i.final, c) !== 9).join() === '6' && ctxSum(i.final, 6) === 8 : true;
  check(`${p} preset: N = ${N}, ${m}, ending at D = ${d}${p === 'ten' ? ' with 5 on each mode of S' : p === 'nine' ? ' with only context 6 one short' : ''}`, i.N === N && i.method === m && D(i.final, N) === d && i.finalD === d && extra);
}
await preset('three'); await setT(0.5); i = await info();
const r3 = await D2(() => MD_DEBUG.run(3, 'greedy', 1)), v3 = new Array(18).fill(0); for (let k = 0; k < i.k; k++) v3[r3.moves[k][0]] += r3.moves[k][1];
check('mid-run, the page’s occupations, context sums and D equal the test’s replay of its first moves', i.v.join() === v3.join() && i.s.slice(1).join() === [1, 2, 3, 4, 5, 6, 7, 8, 9].map((c) => ctxSum(v3, c)).join() && i.D === D(v3, 3) && i.k === Math.round(0.5 * i.T));
for (const p of ['lean', 'one', 'three', 'six', 'ten', 'nine']) { await preset(p); const pressed = await D2((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }

/* ---------- readouts and controls ---------- */
await preset('lean'); await setT(1);
check('the readouts give the method, the sums, the defect and the verdict', /2 · Lean 的环构造 · 9 \/ 9/.test(await text('ro1')) && (await text('ro2')) === '2 2 2 2 2 2 2 2 2' && /0 · 18 = 2 × 9 · 18/.test(await text('ro3')) && /\(1,2\):1/.test(await text('ro4')) && /N = 2 是偶数/.test(await text('ro5')));
check('the rail marks the empty start and move 9', (await D2(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === '空 | 第 9 步');
await setT(0); await D2(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ performs one move and marks the settings custom', (await info()).k === 1 && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await info()).k === 9 && (await state()).playing === false);
await D2(() => { const e = document.getElementById('nIn'); e.value = 7; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the N slider sets N = 7: Lean’s rounds plus the matching end at D = 1', i.N === 7 && i.method === 'lean' && i.T === 9 * 3 + 4 && i.finalD === 1);
await click('#methodChips [data-method="greedy"]'); i = await info();
check('the method chips switch to the local search', i.method === 'greedy' && i.finalD === 1 && (await state()).seed === 1);
await click('#reseed'); i = await info();
const runs12 = await D2(() => [MD_DEBUG.run(7, 'greedy', 1), MD_DEBUG.run(7, 'greedy', 2)]);
check('“another search” draws a different run', (await state()).seed === 2 && i.final.join() === runs12[1].final.join() && JSON.stringify(runs12[0].moves) !== JSON.stringify(runs12[1].moves));
await preset('one'); await D2(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing N = 1 reports that D stops at 1', await waitToast(/D = 1.*N = 1 是奇数/));
await pause(); await D2(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['side', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D2(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await preset('three'); await setT(0.5);
const lit = await D2(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'three']) {
  await preset(p); await setT(0.5);
  const leftovers = await D2(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await D2(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D2(() => document.title)).startsWith('MODES//EIGHTEEN · Eighteen-mode boson occupations can be assigned exactly for even particle numbers'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D2(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D2(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['kurzynski-2017-eighteen-mode-bosonic-assignment-parity.md', 'D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.lean', 'Blueprint/D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.md', 'Library/Observer/kurzynski2017contextualityidentical.md', 'doi.org/10.1103/PhysRevA.95.012133', 'arxiv.org/abs/1609.01250'].every((s) => h.includes(s)); })));
await page.keyboard.press('Escape'); await page.waitForFunction(() => document.getElementById('drawer').hidden === true, null, { timeout: 10000 }).catch(() => {});
check('Esc closes the drawer', (await D2(() => document.getElementById('drawer').hidden)) === true);
await page.waitForFunction(() => document.activeElement?.id === 'infoBtn', null, { timeout: 10000 }).catch(() => {});
check('focus returns to the drawer button', (await D2(() => document.activeElement?.id)) === 'infoBtn');

/* ---------- index round trip ---------- */
const live = readRegistry().visualizations.filter(v => v.status === 'live').length;
await page.click('.crumb'); await page.waitForLoadState('load');
await page.waitForFunction((n) => document.querySelectorAll('.card').length >= n, live, { timeout: 30000 }).catch(() => {});
check('language choice carries to the index', (await D2(() => document.documentElement.dataset.lang)) === 'en');
check('index lists every live visualization', (await D2(() => document.querySelectorAll('.card').length)) === live, `live ${live}`);
await page.click('.card:has(a[href*="modes-eighteen"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.MD_DEBUG && MD_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D2(() => document.body.dataset.vizId)) === 'modes-eighteen');

/* ---------- narrow layouts in both languages ---------- */
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await waitFrames(3);
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await waitFrames(6);
    check(`no horizontal scroll at ${w}px (${lang})`, (await D2(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 });
}
check('no script errors during the whole session', errors.length === 0, errors.slice(0, 3).join(' | '));

await browser.close(); server.close();
const failed = results.filter(r => !r.ok).length;
console.log(`\n${results.length - failed}/${results.length} passed`);
process.exit(failed ? 1 : 0);
