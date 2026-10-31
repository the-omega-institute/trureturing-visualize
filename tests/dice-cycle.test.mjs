#!/usr/bin/env node
// Browser regression suite for viz/dice-cycle (Playwright + Chromium with software WebGL).
//   node tests/dice-cycle.test.mjs
// Reads page state through the read-only window.DC_DEBUG probe and checks it against an independent implementation: the dice
// enumerated by stars and bars, the dominance graph from direct win counts, strongly connected components by Kosaraju's
// algorithm (the page uses Tarjan's), longest cycles by brute force over orderings, and the cycle lengths stated in Lean.
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
  const start = await page.evaluate(() => DC_DEBUG.frames());
  await page.waitForFunction((f0) => !DC_DEBUG.pending() && DC_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => DC_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D((t) => DC_DEBUG.setT(t), t); await settle(); };
const setN = async (n) => { await click(`#nChips [data-n="${n}"]`); };
const info = () => D(() => DC_DEBUG.info());
const state = () => D(() => DC_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => DC_DEBUG.frames()); await page.waitForFunction((t) => DC_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- independent implementation ---------- */
const th = (n) => Math.floor(n * n / 2) + 1;
/* dice by stars and bars: counts c_1 … c_n ≥ 0 summing to n, read off as a sorted face list */
function dice(n) {
  const out = [];
  (function rec(v, left, acc) { if (v === n) { out.push([...acc, ...Array(left).fill(n)]); return; } for (let c = left; c >= 0; c--) rec(v + 1, left - c, [...acc, ...Array(c).fill(v)]); })(1, n, []);
  return out;
}
const nm = (d) => d.map((x) => x.toString(36)).join('');
const dec = (s) => [...s].map((c) => parseInt(c, 36));
const wins = (d, e) => { let w = 0; for (const x of d) for (const y of e) if (x > y) w++; return w; };
const isDie = (n, d) => d.length === n && d.every((x, i) => x >= 1 && x <= n && (i === 0 || d[i - 1] <= x));
const binom = (a, b) => { let r = 1n; for (let i = 1n; i <= BigInt(b); i++) r = r * (BigInt(a) - BigInt(b) + i) / i; return Number(r); };
function graphRef(n) {
  const V = dice(n), t = th(n), out = V.map(() => []), inn = V.map(() => []);
  for (let a = 0; a < V.length; a++) for (let b = 0; b < V.length; b++) if (wins(V[a], V[b]) === t) { out[a].push(b); inn[b].push(a); }
  /* Kosaraju: finishing order on G, then components on the reverse graph */
  const seen = new Uint8Array(V.length), order = [];
  for (let s = 0; s < V.length; s++) { if (seen[s]) continue; const st = [[s, 0]]; seen[s] = 1; while (st.length) { const top = st[st.length - 1]; if (top[1] < out[top[0]].length) { const w = out[top[0]][top[1]++]; if (!seen[w]) { seen[w] = 1; st.push([w, 0]); } } else { order.push(top[0]); st.pop(); } } }
  const comp = new Int32Array(V.length).fill(-1), comps = [];
  for (let i = order.length - 1; i >= 0; i--) { const s = order[i]; if (comp[s] >= 0) continue; const c = [], st = [s]; comp[s] = comps.length; while (st.length) { const v = st.pop(); c.push(v); for (const w of inn[v]) if (comp[w] < 0) { comp[w] = comps.length; st.push(w); } } comps.push(c); }
  return { V, out, comps: comps.filter((c) => c.length > 1) };
}
const perms = (a) => (a.length <= 1 ? [a] : a.flatMap((x, i) => perms([...a.slice(0, i), ...a.slice(i + 1)]).map((p) => [x, ...p])));
function longestBrute(G, comp) {
  const E = new Set(); comp.forEach((a) => G.out[a].forEach((b) => E.add(a + ',' + b)));
  let best = 0;
  for (let size = comp.length; size >= 2 && !best; size--) {
    const subsets = []; (function rec(i, acc) { if (acc.length === size) { subsets.push(acc.slice()); return; } if (i >= comp.length) return; acc.push(comp[i]); rec(i + 1, acc); acc.pop(); rec(i + 1, acc); })(0, []);
    for (const sub of subsets) { const [h, ...rest] = sub; if (perms(rest).some((p) => { const c = [h, ...p]; return c.every((v, i) => E.has(v + ',' + c[(i + 1) % c.length])); })) { best = size; break; } }
  }
  return best;
}
/* the seed cycle for n = 6 and the cycle lengths for n ≥ 7, as stated in EaslickCycleSeeds and EaslickPaddedCycles.longer_cycle */
const LEAN_SIX = ['112555', '134444', '222366', '112556', '133444', '223336'];
const LEAN_LEN = { 7: 14, 8: 29, 9: 10, 10: 110, 11: 14 };
const leanLen = (n) => LEAN_LEN[n] || (n % 2 === 0 ? 6 * ((n - 6) / 2 + 1) : 14 * ((n - 7) / 2 + 1));
/* the rank fibers with seven dice and their cuts, as stated in EaslickSixBound (blockA, blockB, cuts6) */
const BLOCK_A = ['112555', '112556', '122366', '133444', '134444', '222366', '223336'], BLOCK_B = ['114555', '114556', '122566', '144455', '222566', '333346', '333446'];
const CUT_A = { a: '122366', b: '223336', to: '112555' }, CUT_B = { a: '114556', b: '114555', to: '333346' };
/* the attaining pairs of threshold_attained */
const rep = (m, v) => Array(Math.max(0, m)).fill(v);
const leanPair = (n) => { const k = Math.floor(n / 2); return n % 2 === 0 ? [[...rep(k - 1, 1), 2, ...rep(k, 3)], [1, ...rep(2 * k - 1, 2)]] : [[...rep(k, 1), 2, ...rep(k, 3)], [...rep(k + 1, 1), ...rep(k, 2)]]; };

await page.goto(`${origin}${BASE}viz/dice-cycle/`);
await page.waitForFunction(() => window.DC_DEBUG && DC_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();

/* ---------- the minimum and the graph ---------- */
check('opens on Lean’s six-cycle at n = 6, paused, at its first step', st.preset === 'lean' && st.playing === false && i.n === 6 && i.step === 0 && i.cycle.join() === LEAN_SIX.join());
const G = {}; for (let n = 3; n <= 7; n++) G[n] = graphRef(n);
let minOK = true; const minBad = [];
for (let n = 3; n <= 7; n++) { let m = Infinity; for (const d of G[n].V) for (const e of G[n].V) { const w = wins(d, e); if (2 * w > n * n && w < m) m = w; } if (m !== th(n)) { minOK = false; minBad.push(n); } }
check('for n = 3 … 7 the smallest win count above n²/2 over all ordered pairs is ⌊n²/2⌋ + 1', minOK, minBad.join(' '));
let pairOK = true;
for (let n = 3; n <= 16; n++) { const [x, y] = leanPair(n); if (!isDie(n, x) || !isDie(n, y) || wins(x, y) !== th(n)) pairOK = false; }
check('Lean’s attaining pairs (evenX/evenY, oddX/oddY) are valid dice winning exactly ⌊n²/2⌋ + 1 for n = 3 … 16', pairOK);
let cntOK = true;
for (let n = 3; n <= 11; n++) { await setN(n); const x = await info(); if (x.count !== binom(2 * n - 1, n) || x.threshold !== th(n) || (n <= 7 && x.count !== G[n].V.length)) cntOK = false; }
check('the page’s dice count C(2n − 1, n) and threshold match for n = 3 … 11, and enumeration for n ≤ 7', cntOK);
let edOK = true; const edBad = [];
for (let n = 3; n <= 7; n++) {
  const mine = new Set(); G[n].V.forEach((d, a) => G[n].out[a].forEach((b) => mine.add(nm(d) + '>' + nm(G[n].V[b]))));
  const pg = await D((n) => DC_DEBUG.edges(n), n);
  if (pg.length !== mine.size || !pg.every((e) => mine.has(e))) { edOK = false; edBad.push(`${n}: ${pg.length} vs ${mine.size}`); }
}
check('the page’s minimal-advantage edges equal an independent count for n = 3 … 7 (3, 67, 620, 5491, 89153)', edOK && G[6].out.flat().length === 5491 && G[7].out.flat().length === 89153, edBad.join(' | '));
const sizes = (n) => G[n].comps.map((c) => c.length).sort((a, b) => b - a).join(',');
let sccOK = true;
for (let n = 3; n <= 7; n++) { await setN(n); const x = await info(); if (x.graph.knots.slice().sort((a, b) => b - a).join(',') !== sizes(n)) sccOK = false; }
check('strongly connected components (Kosaraju): none for n ≤ 5, two of 7 dice for n = 6, one of 1081 for n = 7; the page agrees', sccOK && sizes(3) === '' && sizes(4) === '' && sizes(5) === '' && sizes(6) === '7,7' && sizes(7) === '1081');
const knotNames = G[6].comps.map((c) => c.map((v) => nm(G[6].V[v])).sort().join());
check('the two knots for n = 6 are exactly Lean’s seven-dice fibers blockA and blockB', knotNames.includes(BLOCK_A.join()) && knotNames.includes(BLOCK_B.join()));
const lb = G[6].comps.map((c) => longestBrute(G[6], c));
await setN(6); i = await info();
check('the longest cycle in each knot is 6 by brute force over all orderings (no 7-cycle); the page finds 6 and 6', lb.join() === '6,6' && i.graph.longest.join() === '6,6');
const cutOf = (c) => { const S6 = new Set(c), single = c.map((v) => [v, G[6].out[v].filter((w) => S6.has(w))]).filter(([, l]) => l.length === 1); const res = []; for (let p = 0; p < single.length; p++) for (let q = p + 1; q < single.length; q++) if (single[p][1][0] === single[q][1][0]) res.push([nm(G[6].V[single[p][0]]), nm(G[6].V[single[q][0]]), nm(G[6].V[single[p][1][0]])]); return res; };
const cuts = G[6].comps.map(cutOf).flat().map((r) => `${[r[0], r[1]].sort().join('+')}>${r[2]}`).sort();
check('in each knot exactly two dice have the same unique successor inside the knot, as in Lean’s cuts6', cuts.join(' ') === [`${[CUT_A.a, CUT_A.b].sort().join('+')}>${CUT_A.to}`, `${[CUT_B.a, CUT_B.b].sort().join('+')}>${CUT_B.to}`].sort().join(' '), cuts.join(' '));
const phi = (d) => d.map((x) => 7 - x).reverse();
const key6 = new Set(); G[6].V.forEach((d, a) => G[6].out[a].forEach((b) => key6.add(nm(d) + '>' + nm(G[6].V[b]))));
check('the mirror φ(d) = 7 − d reverses every edge for n = 6 and maps blockA onto blockB', [...key6].every((e) => { const [x, y] = e.split('>'); return key6.has(nm(phi(dec(y))) + '>' + nm(phi(dec(x)))); }) && BLOCK_A.map((s) => nm(phi(dec(s)))).sort().join() === BLOCK_B.join());
check('about 95% of the n = 6 edges point to a smaller face sum (5195 of 5491), as the drawer says', i.graph.down === 5195 && G[6].V.reduce((s, d, a) => s + G[6].out[a].filter((b) => d.reduce((u, x) => u + x, 0) > G[6].V[b].reduce((u, x) => u + x, 0)).length, 0) === 5195);

/* ---------- the cycles ---------- */
let cyOK = true; const cyBad = [];
for (let n = 6; n <= 11; n++) {
  await setN(n); const x = await info(), c = x.cycle.map(dec);
  const ok = c.length === (n === 6 ? 6 : LEAN_LEN[n]) && new Set(x.cycle).size === c.length && c.every((d) => isDie(n, d)) && c.every((d, j) => wins(d, c[(j + 1) % c.length]) === th(n));
  if (!ok) { cyOK = false; cyBad.push(n); }
}
check('the page’s cycles for n = 6 … 11 are simple cycles of valid dice, every edge (with the closing one) winning ⌊n²/2⌋ + 1, of lengths 6, 14, 29, 10, 110, 14', cyOK, cyBad.join(' '));
const kn = await D(() => [12, 13, 14, 15, 16].map((n) => DC_DEBUG.known(n)));
check('for n = 12 … 16 the chart uses Lean’s padded lengths 3n − 12 and 7(n − 5): 24, 56, 30, 70, 36', kn.join() === [12, 13, 14, 15, 16].map(leanLen).join() && kn.join() === '24,56,30,70,36');
await preset('lean');
let duelOK = true;
for (let s = 0; s < 6; s++) {
  await setT(s / 6 + 0.01); const x = await info(), d = dec(x.cur), e = dec(x.next); let w = 0, t = 0;
  for (const a of d) for (const b of e) { if (a > b) w++; else if (a === b) t++; }
  if (x.step !== s || x.cur !== LEAN_SIX[s] || x.next !== LEAN_SIX[(s + 1) % 6] || x.duel.win !== w || x.duel.tie !== t || x.duel.lose !== 36 - w - t || w !== 19) duelOK = false;
}
check('walking the six steps: each duel’s win, tie and lose counts match direct comparison, every win count 19', duelOK);

/* ---------- presets ---------- */
await preset('cut'); i = await info();
check('cut preset: the current step is 223336 → 112555 and the page names the collision 122366, 223336 → 112555', i.step === 5 && i.cur === '223336' && i.next === '112555' && i.cut && [i.cut.a, i.cut.b].sort().join() === [CUT_A.a, CUT_A.b].sort().join() && i.cut.to === CUT_A.to && /122366, 223336 → 112555/.test(await text('ro5')));
await preset('mirror'); i = await info();
const cB = i.cycle.map(dec);
check('mirror preset: a six-cycle inside blockB, with the collision 114555, 114556 → 333346', i.k === 6 && i.cycle.every((s) => BLOCK_B.includes(s)) && cB.every((d, j) => wins(d, cB[(j + 1) % 6]) === 19) && i.knot.join() === BLOCK_B.join() && i.cut && i.cut.to === CUT_B.to);
await preset('five'); i = await info();
check('five preset: n = 5 with no cycle; the duel shows Lean’s attaining pair 11233 → 11122, 13 of 25', i.n === 5 && i.k === 0 && i.cur === nm(leanPair(5)[0]) && i.next === nm(leanPair(5)[1]) && i.duel.win === 13 && /没有循环/.test(await text('ro3')));
await preset('seven'); i = await info();
check('seven preset: n = 7, Easlick’s 14-cycle, every die in the 1081-dice component', i.n === 7 && i.k === 14 && i.cycle.every((s) => G[7].comps[0].some((v) => nm(G[7].V[v]) === s)));
await preset('ten'); i = await info();
check('ten preset: n = 10 and the 110-cycle, with no graph drawn', i.n === 10 && i.k === 110 && i.graph === null);
for (const p of ['lean', 'cut', 'mirror', 'five', 'seven', 'ten']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }

/* ---------- controls ---------- */
await preset('lean');
check('the rail marks d₁, d₄ at the midpoint and the return to d₁', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => `${m.textContent}@${parseFloat(m.style.left)}`).join(' | '))) === 'd₁@0 | d₄@50 | 回到 d₁@100');
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ moves one step along the cycle and marks the settings custom', (await info()).step === 1 && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await page.keyboard.press('e'); await settle();
check('E goes round to the end and pauses', (await state()).t === 1 && (await state()).playing === false);
await D(() => { const e = document.getElementById('now'); e.value = 0.55; e.dispatchEvent(new Event('input')); }); await settle();
check('the slider moves along the cycle', (await info()).step === 3);
await setN(8); i = await info();
check('the face chips switch to n = 8 and its 29-cycle', i.n === 8 && i.k === 29 && (await D(() => document.querySelector('#nChips [aria-pressed="true"]').dataset.n)) === '8');
await preset('lean'); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('walking the whole six-cycle reports the round trip', await waitToast(/走完一圈.*6 颗骰子.*19\/36/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await preset('lean');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'seven']) {
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
check('English title', (await D(() => document.title)).startsWith('DICE//CYCLE · Minimal-advantage dice cycles are longest exactly at six faces'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean files, the Blueprint, the literature note, the DOI, arXiv and the licence', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['easlick-2026-minimal-advantage-cycle-conjecture-one.md', 'D5/S3/Combinatorics/Dice/EaslickSixBound.lean', 'D5/S3/Combinatorics/Dice/EaslickCycleSeeds.lean', 'Blueprint/D5/S3/Combinatorics/Dice/EaslickSixBound.md', 'Library/Certificates/easlick2026minimaldice.md', 'doi.org/10.48550/arXiv.2610.40321', 'arxiv.org/abs/2610.40321', 'creativecommons.org/licenses/by/4.0'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="dice-cycle"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.DC_DEBUG && DC_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'dice-cycle');

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
