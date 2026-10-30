#!/usr/bin/env node
// Browser regression suite for viz/imitate-cycle (Playwright + Chromium with software WebGL).
//   node tests/imitate-cycle.test.mjs
// Reads page state through the read-only window.IM_DEBUG probe and checks it against an independent implementation: the graph
// K₄ without the edge 0–2 as neighbour lists, the payoffs as M[agent][own][opponent], the imitation rule by the set of
// strategies used by the best-paid neighbours (a tie keeps the current strategy), the best response by comparing the two
// deviations, and replays of the activation sequence the page reports. Fixed reference data come from the Lean module: the
// witness schedule and the eight-state orbit BABB → … → AABB.
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
  const start = await page.evaluate(() => IM_DEBUG.frames());
  await page.waitForFunction((f0) => !IM_DEBUG.pending() && IM_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => IM_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => IM_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => IM_DEBUG.info());
const state = () => D(() => IM_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const slide = async (id, v) => { await D(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input')); }, [id, v]); await settle(); };
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => IM_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => IM_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
const nbr = (i) => [[1, 3], [0, 2, 3], [1, 3], [0, 1, 2]][i];   // K₄ without 0–2
const M = [[[1, 0], [0, 4]], [[3, 2], [2, 3]], [[4, 1], [0, 4]], [[4, 3], [3, 4]]];   // M[i][own][opp], 0 = A, 1 = B
const ut = (s, i) => nbr(i).reduce((t, j) => t + M[i][s[i]][s[j]], 0);
function next(s, i, roles) {   // roles[i] = 'I' or 'R'
  if (roles[i] === 'I') { const u = nbr(i).map((j) => ut(s, j)), top = Math.max(...u), used = new Set(nbr(i).filter((j, k) => u[k] === top).map((j) => s[j])); return used.size === 1 ? [...used][0] : s[i]; }
  const a = ut(s.map((x, k) => (k === i ? 0 : x)), i), b = ut(s.map((x, k) => (k === i ? 1 : x)), i); return a > b ? 0 : b > a ? 1 : s[i];
}
const str = (s) => s.map((x) => 'AB'[x]).join(''), parse = (w) => w.split('').map((c) => (c === 'B' ? 1 : 0));
const stable = (s, roles) => [0, 1, 2, 3].every((i) => next(s, i, roles) === s[i]);
const run = (s0, acts, roles) => { const out = [str(s0)]; let s = s0.slice(); for (const a of acts) { s = s.slice(); s[a] = next(s, a, roles); out.push(str(s)); } return out; };
const ORBIT = ['BABB', 'BABA', 'BBBA', 'BBAA', 'ABAA', 'ABAB', 'AAAB', 'AABB'];   // `orbit` of the Lean module
const IRII = ['I', 'R', 'I', 'I'];

await page.goto(origin + BASE + 'viz/imitate-cycle/');
await page.waitForFunction(() => window.IM_DEBUG && IM_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle(); await pause();
let i = await info();

/* ---------- the counterexample ---------- */
check('the page opens on the counterexample: network view, rules I R I I, the schedule 2, 0, 3, 1 repeated', i.mode === 'net' && i.imitator.join() === 'true,false,true,true' && i.sched === 'witness' && i.acts.slice(0, 8).join() === '2,0,3,1,2,0,3,1' && (await state()).preset === 'cycle');
check('every agent satisfies the coordination condition max{pay(B, A), pay(A, B)} < min{pay(A, A), pay(B, B)}', M.every((m) => Math.max(m[1][0], m[0][1]) < Math.min(m[0][0], m[1][1])));
check('the schedule is persistent: every agent appears in every window of 4 consecutive steps', i.acts.every((_, t) => t + 4 > i.acts.length || [0, 1, 2, 3].every((a) => i.acts.slice(t, t + 4).includes(a))));
const ind = run(parse('BABB'), i.acts, IRII);
check('the page’s 34-step trajectory equals the independent rules step by step', JSON.stringify(i.states) === JSON.stringify(ind) && i.T === 34);
check('…it is BABB for t < 2 and orbit((t − 2) mod 8) after, the Lean formula, for every t ≤ 34', i.states.every((w, t) => w === (t < 2 ? 'BABB' : ORBIT[(t - 2) % 8])));
check('…no state on it is an equilibrium, and the page reports a cycle of length 8 from step 2 with no settling', i.states.every((w) => !stable(parse(w), IRII)) && JSON.stringify(i.cycle) === '[2,8]' && i.settled === -1 && /冻结的反例/.test(await text('ro5')));
const eqInd = []; for (let s = 0; s < 16; s++) { const st = [3, 2, 1, 0].map((b) => (s >> b) & 1); if (stable(st, IRII)) eqInd.push(str(st)); }
check('only AAAA and BBBB are equilibria among the 16 states (page and independent enumeration)', JSON.stringify(i.equilibria) === JSON.stringify(eqInd) && eqInd.join() === 'AAAA,BBBB');
let movesOK = true; const movesInd = []; for (let s = 0; s < 16; s++) { const st = [3, 2, 1, 0].map((b) => (s >> b) & 1); for (let a = 0; a < 4; a++) { const y = next(st, a, IRII); if (y !== st[a]) { const t2 = st.slice(); t2[a] = y; movesInd.push([s, parseInt(t2.join(''), 2), a]); } } }
movesOK = JSON.stringify(i.moves) === JSON.stringify(movesInd);
check('the state-space moves (state, next state, agent) equal the independent ones; AAAA and BBBB have none', movesOK && !movesInd.some(([s]) => s === 0 || s === 15));
await setFrac(3 / 34); i = await info();
check('at step 3 the best responder (agent 1) is activated; the state and the four utilities match the independent ones', i.t === 3 && i.active === 1 && i.x === ind[3] && JSON.stringify(i.u) === JSON.stringify([0, 1, 2, 3].map((k) => ut(parse(ind[3]), k))));
const why = await text('ro3');
const ua = ut(parse(ind[3]).map((x, k) => (k === 1 ? 0 : x)), 1), ub = ut(parse(ind[3]).map((x, k) => (k === 1 ? 1 : x)), 1);
check('…the explanation gives agent 1’s utilities with A and with B and the choice', why.includes(`选 A 得 ${ua}，选 B 得 ${ub} → ${ua > ub ? 'A' : ub > ua ? 'B' : ind[3][1]}`), why);

/* ---------- rules and schedules ---------- */
const sweep = i.sweep; let sweepOK = sweep.length === 16;
for (const r of sweep) { const roles = r.roles.split(''), acts = Array.from({ length: 200 }, (_, t) => [2, 0, 3, 1][t % 4]), tr = run(parse('BABB'), acts, roles); const first = tr.findIndex((w) => stable(parse(w), roles)); if ((first < 0 ? -1 : first) !== r.settled) sweepOK = false; }
check('all 16 rule assignments under the schedule: the page’s settling steps equal the independent ones, and only I R I I never settles', sweepOK && sweep.filter((r) => r.settled < 0).map((r) => r.roles).join() === 'IRII');
await preset('imit'); i = await info();
const indImit = run(parse('BABB'), i.acts, ['I', 'I', 'I', 'I']);
check('all imitators: the trajectory follows the rules and settles in AAAA at step 6', JSON.stringify(i.states) === JSON.stringify(indImit) && i.settled === 6 && indImit[6] === 'AAAA' && /第 6 步停在均衡 AAAA/.test(await text('ro5')));
await preset('best'); i = await info();
check('all best responders: settles in AAAA at step 6', i.settled === 6 && JSON.stringify(i.states) === JSON.stringify(run(parse('BABB'), i.acts, ['R', 'R', 'R', 'R'])));
await preset('swap'); i = await info();
check('agent 0 best-responds instead: settles in AAAA at step 6', i.imitator.join() === 'false,true,true,true' && i.settled === 6);
await preset('cycle'); await click('#roleChips [data-agent="1"]'); i = await info();
check('clicking agent 1’s rule makes everyone an imitator, and the settings become custom', i.imitator.every(Boolean) && i.settled === 6 && (await state()).preset === null);
await click('#roleChips [data-agent="1"]'); i = await info();
check('…clicking again restores the cycle', JSON.stringify(i.cycle) === '[2,8]' && i.settled === -1);
await preset('random'); i = await info();
const indRand = run(parse('BABB'), i.acts.slice(0, i.T), IRII);
check('random activation: the trajectory follows the rules and stops at its first equilibrium', i.sched === 'random' && JSON.stringify(i.states) === JSON.stringify(indRand) && stable(parse(i.states[i.T]), IRII) && i.states.slice(0, -1).every((w) => !stable(parse(w), IRII)) && i.settled === i.T);
const h = i.hist;
check('…2000 random runs all settle; the histogram sums to 2000 and its mean matches the counts', h && h.all && h.counts.reduce((a, b) => a + b, 0) === 2000 && Math.abs(h.mean - h.counts.reduce((a, c, t) => a + c * t, 0) / 2000) < 1e-9 && h.counts.length - 1 === h.maxT);
const acts0 = JSON.stringify(i.acts); await click('#schedChips [data-sched="random"]'); i = await info();
check('clicking “random” again draws a different schedule', JSON.stringify(i.acts) !== acts0 && i.sched === 'random');
await click('#schedChips [data-sched="witness"]'); i = await info();
check('the schedule chips return to 2, 0, 3, 1', i.sched === 'witness' && JSON.stringify(i.cycle) === '[2,8]');
await click('#modeChips [data-mode="space"]'); i = await info();
check('the state-space view keeps the same trajectory', i.mode === 'space' && i.states[10] === 'BABB');

/* ---------- play, keys and toasts ---------- */
await preset('cycle'); await setFrac(0.985); await click('#play');
check('the cycle toast reports that the state returns every 8 steps', await waitToast(/每 8 步回到同一个状态/));
await pause();
await preset('imit'); await setFrac(0.985); await click('#play');
check('the settling toast names AAAA at step 6', await waitToast(/第 6 步到达 AAAA/));
await pause();
await preset('cycle'); await setFrac(0.2); await click('#play'); await waitFrames(12); const t1 = (await state()).nowFrac; await pause();
check('play advances along the rail', t1 > 0.2);
await click('#rev'); await waitFrames(12); const t2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', t2 < t1);
await page.click('#rev'); await pause();
await page.focus('#now'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with the rail focused', playing === true);
await pause();
await page.keyboard.press('e'); await settle();
check('E jumps to step 34 and pauses', (await info()).t === 34 && (await state()).playing === false);
await setFrac(10 / 34); await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps one activation', (await info()).t === 11);
await click('#modeChips [data-mode="space"]');

/* ---------- language ---------- */

await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
for (const m of ['net', 'space']) {
  await click(`#modeChips [data-mode="${m}"]`); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${m}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('IMITATE//CYCLE · Imitation and best response: a cycle that never settles'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file and the two papers', (await D(() => { const h = [...document.querySelectorAll('#drawer .en a')].map((a) => a.href).join(' '); return ['hasheminejad-ramazi-2023-mixed-imitation-best-response-nonequilibration.md', 'MixedImitationBestResponseCycle.lean', '10.1109/LCSYS.2023.3292049', '10.1109/TAC.2023.3343820'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="imitate-cycle"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.IM_DEBUG && IM_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'imitate-cycle');

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
