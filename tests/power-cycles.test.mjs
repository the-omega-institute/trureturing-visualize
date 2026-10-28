#!/usr/bin/env node
// Browser regression suite for viz/power-cycles (Playwright + Chromium with software WebGL).
//   node tests/power-cycles.test.mjs
// Reads page state through the read-only window.PC_DEBUG probe and checks it against an independent implementation: the
// affine group AGL(1, p) as permutations of ℤ/p (the page multiplies coefficient pairs), the 14-cycle words read from the
// Lean digit encoding, the unused edge type at each position, the visit count through port u on every translate, the
// replacement graph built from the Lean edge list of H₁₅ and the port map τ, and a depth-first enumeration of the gadget's
// port-to-port paths. Fixed reference data come from the Lean modules: the sixteen words, the histograms (6, 4, 4) and
// (2, 6, 6), the edge list of H₁₅ and the port numbers u = 14, v = 7, w = 0.
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
const slide = async (id, v) => { await D(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input')); }, [id, v]); await settle(); };
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => PC_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => PC_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};


/* ---------- independent implementation ---------- */
// AGL(1, p) as permutations of ℤ/p: an element is the array of images of 0 … p − 1, and the product f·h applies h first
// (the Lean semidirect product); the words are read from the Lean digit encoding (0 = t, 1 = g, 2 = r); a visit passes
// through u when σ is the incoming or the outgoing type; the replacement graph is built from the Lean edge list of H₁₅ and
// the port map τ; the gadget's port-to-port paths are enumerated by depth-first search
const LEAN = {   // word4 and word6 of ErdosGyarfasGarciaOrientation (p = 29) and …ThirtyOne (p = 31)
  29: { 3: [[0, 1, 0, 1, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2], [0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2, 0, 2]],
    8: [[0, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2], [0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2]],
    10: [[0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2]],
    11: [[0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2], [0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2]] },
  31: { 11: [[0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2]],
    17: [[0, 1, 0, 1, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2], [0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2, 0, 2]],
    22: [[0, 1, 0, 1, 0, 2, 2, 2, 2, 2, 0, 1, 1, 1], [0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 2, 2, 0, 2]],
    24: [[0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 2, 2], [0, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2]] }
};
const LET = 'tgr', INVL = { t: 't', g: 'r', r: 'g' };
const wordOf = (d) => d.map((x) => LET[x]).join('');
const mod = (x, p) => ((x % p) + p) % p;
const sum = (a) => a.reduce((s, x) => s + x, 0);
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
function agl(p, a) {
  const g = Array.from({ length: p }, (_, x) => mod(a * x + 1, p)), r = new Array(p);
  g.forEach((y, x) => { r[y] = x; });
  const gen = { t: Array.from({ length: p }, (_, x) => mod(-x, p)), g, r };
  const compose = (f, h) => h.map((y) => f[y]);
  const idOf = (f) => (mod(f[1] - f[0], p) - 1) * p + f[0];   // x ↦ m·x + b has index (m − 1)·p + b
  const elem = (k) => { const m = Math.floor(k / p) + 1, b = k % p; return Array.from({ length: p }, (_, x) => mod(m * x + b, p)); };
  return { p, N: p * (p - 1), gen, compose, idOf, elem, one: Array.from({ length: p }, (_, x) => x) };
}
function walk(G, w) {   // prefix products, closure and distinctness of a word
  const pref = [G.one]; for (const c of w) pref.push(G.compose(pref[pref.length - 1], G.gen[c]));
  const ids = pref.map(G.idOf);
  return { pref: pref.slice(0, 14), closes: ids[14] === G.idOf(G.one), distinct: new Set(ids.slice(0, 14)).size === 14 };
}
const unusedOf = (w) => [...w].map((c, i) => LET.replace(c, '').replace(INVL[w[(i + 13) % 14]], ''));
const hist = (u) => [...LET].map((s) => u.filter((e) => e === s).length);
function countsInd(G, w, sigma) {
  const W = walk(G, w), out = [];
  for (let k = 0; k < G.N; k++) {
    const x = G.elem(k); let n = 0;
    for (let i = 0; i < 14; i++) { const v = G.idOf(G.compose(x, W.pref[i])); if (sigma[v] === w[i] || sigma[v] === INVL[w[(i + 13) % 14]]) n++; }
    out.push(n);
  }
  return out;
}
const H7E = [[1, 3], [3, 4], [4, 2], [5, 1], [2, 6], [3, 5], [5, 0], [0, 6], [6, 4]];   // h7Edges of the Lean base module
const H15E = new Set(H7E.concat(H7E.map(([a, b]) => [a + 7, b + 7]), [[1, 8], [2, 14], [14, 9]]).flatMap(([a, b]) => [`${a},${b}`, `${b},${a}`]));
const PORTN = { u: 14, v: 7, w: 0 };
function adjacent(G, tau, A, B) {   // an edge of the Lean `replacement` graph
  if (A[0] === B[0]) return H15E.has(`${A[1]},${B[1]}`);
  const x = G.elem(A[0]);
  return [...LET].some((j) => G.idOf(G.compose(x, G.gen[j])) === B[0] && PORTN[tau[A[0]][j]] === A[1] && PORTN[tau[B[0]][INVL[j]]] === B[1]);
}
function cycleInd(G, tau, cyc) {
  if (!cyc) return { len: 0, distinct: false, edges: false };
  let edges = true; for (let i = 0; i < cyc.length; i++) if (!adjacent(G, tau, cyc[i], cyc[(i + 1) % cyc.length])) edges = false;
  return { len: cyc.length, distinct: new Set(cyc.map(([v, j]) => v * 15 + j)).size === cyc.length, edges };
}
function gadgetPaths(s, t) {   // lengths of all simple paths from s to t in H₁₅
  const nb = (v) => [...Array(15).keys()].filter((y) => H15E.has(`${v},${y}`)), lens = new Set(), seen = new Set([s]);
  const dfs = (v, d) => { if (v === t) { lens.add(d); return; } for (const y of nb(v)) if (!seen.has(y)) { seen.add(y); dfs(y, d + 1); seen.delete(y); } };
  dfs(s, 0); return [...lens].sort((a, b) => a - b);
}
const tauOK = (j) => j.sigma.length === j.N && j.tau.length === j.N && j.sigma.every((s, v) => j.tau[v][s] === 'u' && [...LET].map((e) => j.tau[v][e]).sort().join('') === 'uvw');
function pickInd(c4, c6, w4, w6) { const f = c4.findIndex((x) => x >= 10); return f >= 0 ? { k: f, word: w4, count: c4[f] } : { k: c6.findIndex((x) => x >= 10), word: w6, count: Math.max(...c6) }; }

await page.goto(origin + BASE + 'viz/power-cycles/');
await page.waitForFunction(() => window.PC_DEBUG && PC_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle(); await pause();
let i = await info();

/* ---------- the Cayley graph and the averaging identity ---------- */
let G = agl(29, 3);
const w29 = [wordOf(LEAN[29][3][0]), wordOf(LEAN[29][3][1])];
check('opens on the sweep preset: AGL(1, 29), a = 3, N = 29·28 = 812, a random orientation, the four-t family', i.mode === 'base' && i.p === 29 && i.a === 3 && i.N === 812 && G.N === 812 && i.sigmaMode === 'random' && i.fam === 4);
check('the page’s two words are the Lean words for p = 29, a = 3', i.words[0].word === w29[0] && i.words[1].word === w29[1], i.words.map((w) => w.word).join(' '));
const W29 = w29.map((w) => walk(G, w));
check('…both close up and visit 14 distinct elements (as permutations of ℤ/29), as the page reports', W29.every((W) => W.closes && W.distinct) && i.words.every((w) => w.closes && w.distinct));
check('…the unused type at each position matches, with histograms (6, 4, 4) and (2, 6, 6) over t, g, r', same(i.words[0].unused, unusedOf(w29[0])) && same(i.words[1].unused, unusedOf(w29[1])) && same(hist(unusedOf(w29[0])), [6, 4, 4]) && same(hist(unusedOf(w29[1])), [2, 6, 6]));
check('σ and τ: every vertex sends its σ-edge to port u and the other two edge types to v and w', tauOK(i));
const c4 = countsInd(G, w29[0], i.sigma), c6 = countsInd(G, w29[1], i.sigma), T0 = i.sigma.filter((s) => s === 't').length;
check('the visit counts through u on all 812 translates of both words match the independent count', same(c4, i.c4) && same(c6, i.c6));
check('S₄ = 10N − 2T and S₆ = 8N + 4T, with T counted independently', i.T === T0 && sum(c4) === 10 * 812 - 2 * T0 && sum(c6) === 8 * 812 + 4 * T0 && i.S4 === sum(c4) && i.S6 === sum(c6), `T ${T0} S4 ${sum(c4)} S6 ${sum(c6)}`);
check('2S₄ + S₆ = 28N > 27N, so some translate passes through u at least 10 times', 2 * sum(c4) + sum(c6) === 28 * 812 && Math.max(...c4, ...c6) >= 10);
check('…the readouts show S₄, S₆, 28N and the frozen theorem', (await text('ro3')).includes(`${sum(c4)} = ${10 * 812 - 2 * T0} · ${sum(c6)} = ${8 * 812 + 4 * T0}`) && (await text('ro4')).startsWith(`${28 * 812} = ${28 * 812}`) && /冻结定理/.test(await text('ro5')));
await setFrac(0.5); i = await info();
check('the time axis picks a translate: at 0.5 it is #407 (k = 406), with the independent count in the readout', i.k === 406 && i.count === c4[406] && (await text('clock')) === '#407' && (await text('ro4')).endsWith(` · ${c4[406]}`));
await click('#famChips [data-fam="6"]'); i = await info();
check('the six-t chip sweeps the other family: the same translate now shows its six-t count, and the settings become custom', i.fam === 6 && i.count === c6[406] && (await state()).preset === null && /自定义/.test(await text('presetNote')));
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps to the next translate', (await info()).k === 407);
await page.keyboard.press('e'); await settle();
check('E jumps to the last translate and pauses', (await info()).k === 811 && (await state()).playing === false);
check('the rail marks the first, middle and last translate', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' '))) === '#1 #406 #812');

/* ---------- all eight instances, expanded ---------- */
await click('#modeChips [data-mode="cycle"]');
check('in cycle mode the family chips are hidden and the rail counts edges', !(await visible('famChips')) && (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' '))) === '0 14 32 64');
for (const [p, a] of [[29, 3], [29, 8], [29, 10], [29, 11], [31, 11], [31, 17], [31, 22], [31, 24]]) {
  await click(`#instChips [data-inst="${p}-${a}"]`); const j = await info(), H = agl(p, a), [w4, w6] = LEAN[p][a].map(wordOf);
  const Wa = walk(H, w4), Wb = walk(H, w6), k4 = countsInd(H, w4, j.sigma), k6 = countsInd(H, w6, j.sigma), T = j.sigma.filter((s) => s === 't').length;
  check(`AGL(1, ${p}), a = ${a}: the Lean words close on 14 distinct elements with histograms (6, 4, 4) and (2, 6, 6), the page uses them, its counts match, and 2S₄ + S₆ = 28N`,
    j.mode === 'cycle' && j.p === p && j.a === a && j.N === p * (p - 1) && j.words[0].word === w4 && j.words[1].word === w6 && Wa.closes && Wa.distinct && Wb.closes && Wb.distinct
    && same(hist(unusedOf(w4)), [6, 4, 4]) && same(hist(unusedOf(w6)), [2, 6, 6]) && tauOK(j) && same(k4, j.c4) && same(k6, j.c6) && j.T === T && 2 * sum(k4) + sum(k6) === 28 * H.N);
  const pk = pickInd(k4, k6, w4, w6), cy = cycleInd(H, j.tau, j.cycle);
  check(`…its 64-cycle starts from the first translate with ≥ 10 u-visits and is a simple cycle of length 64 in the independently built replacement graph`,
    !!j.pick && j.pick.k === pk.k && j.pick.word === pk.word && j.pick.count === pk.count && pk.count >= 10 && cy.len === 64 && cy.distinct && cy.edges, JSON.stringify(cy));
}

/* ---------- presets ---------- */
await preset('six'); i = await info();
const wn = await text('wordNote');
check('six-t preset: AGL(1, 31), a = 24, sweeping the six-t family; the word note lists the unused types 6, 4, 4 and 2, 6, 6', i.mode === 'base' && i.p === 31 && i.a === 24 && i.fam === 6 && /6、4、4/.test(wn) && /2、6、6/.test(wn) && wn.includes(wordOf(LEAN[31][24][0])) && wn.includes(wordOf(LEAN[31][24][1])));
await preset('noT'); i = await info(); G = agl(29, 10);
const n4 = countsInd(G, wordOf(LEAN[29][10][0]), i.sigma);
check('never-t preset: no vertex has σ = t, so T = 0 and S₄ = 10N; the four-t translates average exactly 10', i.sigmaMode === 'noT' && i.sigma.every((s) => s !== 't') && i.T === 0 && sum(n4) === 10 * 812 && i.S4 === 10 * 812 && Math.max(...n4) >= 10);
await preset('allT'); i = await info(); G = agl(29, 8);
const a4 = countsInd(G, wordOf(LEAN[29][8][0]), i.sigma), a6 = countsInd(G, wordOf(LEAN[29][8][1]), i.sigma);
check('always-t preset: T = N, every six-t translate passes through u exactly 12 times (S₆ = 12N), and S₄ = 8N', i.sigma.every((s) => s === 't') && i.T === 812 && i.fam === 6 && a6.every((x) => x === 12) && same(a6, i.c6) && sum(a4) === 8 * 812 && i.S6 === 12 * 812);
await preset('cyc29'); i = await info(); G = agl(29, 3);
const p4 = countsInd(G, w29[0], i.sigma), p6 = countsInd(G, w29[1], i.sigma), pk29 = pickInd(p4, p6, w29[0], w29[1]);
check('expansion preset: the page expands the first translate with at least 10 u-visits (four-t family first), counted independently', i.mode === 'cycle' && i.p === 29 && i.a === 3 && !!i.pick && i.pick.k === pk29.k && i.pick.word === pk29.word && i.pick.count === pk29.count && pk29.count >= 10);
const cy29 = cycleInd(G, i.tau, i.cycle);
check('…the cycle has exactly 64 = 2⁶ distinct vertices, and every step is an edge of the replacement graph built from the Lean edge list', cy29.len === 64 && cy29.distinct && cy29.edges);
const pk0 = i.pick || pk29, x29 = G.elem(pk0.k), copies = walk(G, pk0.word).pref.map((f) => G.idOf(G.compose(x29, f))), runs = [];
for (const [v] of i.cycle || []) if (!runs.length || runs[runs.length - 1] !== v) runs.push(v);
check('…it runs through the 14 gadgets of the translate x·W in order, each one once', same(runs, copies));
const vis29 = i.visits || [], portsOK = vis29.length === 14 && vis29.every((q, n) => q.from === i.tau[copies[n]][INVL[pk0.word[(n + 13) % 14]]] && q.to === i.tau[copies[n]][pk0.word[n]]);
check('…each visit enters and leaves through the ports τ assigns; ten u-visits take 3 edges and the other four take 5: 14 + 30 + 20 = 64', portsOK && vis29.filter((q) => q.len === 3).length === 10 && vis29.filter((q) => q.len === 5).length === 4 && vis29.every((q) => q.len === 5 || q.from === 'u' || q.to === 'u'));
check('…the page’s own check agrees, and the readouts state 14 + 10·3 + 4·5 = 64 with both ticks and the frozen theorem', !!i.check && i.check.distinct && i.check.edges && i.check.length === 64 && /14 \+ 10·3 \+ 4·5 = 64/.test(await text('ro3')) && /✓.*✓/.test(await text('ro4')) && /冻结定理/.test(await text('ro5')));
await setFrac(0.5); i = await info();
check('the time axis walks the cycle: at 0.5 the page is at edge 32 of 64', i.step === 32 && (await text('clock')) === '32/64');
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps one edge along the cycle', (await info()).step === 33);
await preset('cyc31'); i = await info(); G = agl(31, 17);
const cy31 = cycleInd(G, i.tau, i.cycle);
check('p = 31 preset: AGL(1, 31), a = 17, N = 930, and the 64-cycle passes the independent check', i.mode === 'cycle' && i.p === 31 && i.a === 17 && i.N === 930 && cy31.len === 64 && cy31.distinct && cy31.edges);
await click('[data-preset="gadget"]'); const stG = await state(); i = await info();
const uv = gadgetPaths(14, 7), uw = gadgetPaths(14, 0), vw = gadgetPaths(7, 0);
check('gadget preset (paused): depth-first search in H₁₅ finds 3-edge and 5-edge paths u–v and u–w, and no v–w path shorter than 5', i.mode === 'cycle' && i.p === 29 && i.a === 11 && stG.playing === false && uv.includes(3) && uv.includes(5) && uw.includes(3) && uw.includes(5) && vw[0] === 5 && /H₁₅/.test(await text('c2Title')), `u–v ${uv} · u–w ${uw} · v–w ${vw}`);
check('…every visit on the page uses a path length that exists between its two ports', !!i.visits && i.visits.every((q) => gadgetPaths(PORTN[q.from], PORTN[q.to]).includes(q.len)));
await preset('reroll'); i = await info(); const sig0 = i.sigma.join('');
check('re-roll preset: AGL(1, 31), a = 22, seed 11', i.mode === 'base' && i.p === 31 && i.a === 22 && i.seed === 11);
await click('#reroll'); i = await info(); G = agl(31, 22);
const r4 = countsInd(G, wordOf(LEAN[31][22][0]), i.sigma), r6 = countsInd(G, wordOf(LEAN[31][22][1]), i.sigma);
check('Re-roll draws a new orientation (seed 12); the counts still match and 2S₄ + S₆ = 28N', i.seed === 12 && i.sigma.join('') !== sig0 && tauOK(i) && same(r4, i.c4) && same(r6, i.c6) && 2 * sum(r4) + sum(r6) === 28 * 930 && (await state()).preset === null);
await click('#sigmaChips [data-sigma="allT"]'); await click('#reroll'); i = await info();
check('re-rolling from “σ always t” returns to a random orientation', i.sigmaMode === 'random' && i.seed === 13 && i.sigma.some((s) => s !== 't'));

/* ---------- timeline and views ---------- */
await preset('avg'); await setFrac(0.97); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing the sweep to the end raises the swept toast', await waitToast(/扫完/));
await pause(); await preset('cyc29'); await setFrac(0.97); await click('#play');
check('playing the cycle to the end raises the closed-cycle toast', await waitToast(/回到起点/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');

/* ---------- language ---------- */
await click('#modeChips [data-mode="base"]');
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }).catch(() => {}); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
for (const p of ['avg', 'six', 'cyc29', 'gadget']) {
  await preset(p); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('POWER//CYCLES · A 64-cycle in every orientation'));
check('English readouts name the frozen theorem', /frozen theorem/.test(await text('ro5')));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the two dossiers, the three Lean files and the four sources', (await D(() => { const h = [...document.querySelectorAll('#drawer .en a')].map((a) => a.href).join(' '); return ['garcia-2026-erdos64-agl29-orientation.md', 'garcia-2026-erdos64-agl31-orientation.md', 'ErdosGyarfasGarciaOrientation.lean', 'ErdosGyarfasGarciaOrientationThirtyOne.lean', 'ErdosGyarfasGarciaOrientationBase.lean', 'arxiv.org/abs/2609.04686', 'erdosproblems.com/64', '10.1090/jams/1018', '10.37236/3252'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="power-cycles"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.PC_DEBUG && PC_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'power-cycles');

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
