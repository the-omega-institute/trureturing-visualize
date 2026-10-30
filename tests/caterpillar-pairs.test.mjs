#!/usr/bin/env node
// Browser regression suite for viz/caterpillar-pairs (Playwright + Chromium with software WebGL).
//   node tests/caterpillar-pairs.test.mjs
// Reads page state through the read-only window.CP_DEBUG probe and checks it against an independent implementation: the
// caterpillar built as a graph from Lean's edge relation, ps(G, k) by a generic rooted-tree recursion (not the page's spine
// transfer), brute-force colourings for the base pair, its own exhaustive search, and AHU canonical forms for tree isomorphism.
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
  const start = await page.evaluate(() => CP_DEBUG.frames());
  await page.waitForFunction((f0) => !CP_DEBUG.pending() && CP_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => CP_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const info = () => D(() => CP_DEBUG.info());
const state = () => D(() => CP_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => CP_DEBUG.frames()); await page.waitForFunction((t) => CP_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- the caterpillar as a graph, from Lean's edge relation ---------- */
/* vertex (i, r): r = 0 is the spine vertex, r ≥ 1 a leaf; edges (i,0)–(i,r) and (i,0)–(i+1,0) */
function graph(a) {
  const id = []; let n = 0; a.forEach((m, i) => { id.push([]); for (let r = 0; r < m; r++) id[i].push(n++); });
  const adj = Array.from({ length: n }, () => []);
  const edge = (u, v) => { adj[u].push(v); adj[v].push(u); };
  a.forEach((m, i) => { for (let r = 1; r < m; r++) edge(id[i][0], id[i][r]); if (i + 1 < a.length) edge(id[i][0], id[i + 1][0]); });
  return adj;
}
const padd = (p, q) => { const r = new Array(Math.max(p.length, q.length)).fill(0); p.forEach((v, i) => { r[i] += v; }); q.forEach((v, i) => { r[i] += v; }); return r; };
const pmul = (p, q) => { const r = new Array(p.length + q.length - 1).fill(0); p.forEach((x, i) => { if (x) q.forEach((y, j) => { r[i + j] += x * y; }); }); return r; };
const trim = (p) => { const r = p.slice(); while (r.length > 1 && r[r.length - 1] === 0) r.pop(); return r; };
const eq = (p, q) => { const x = trim(p), y = trim(q); return x.length === y.length && x.every((v, i) => v === y[i]); };
/* ps(G, k) for a tree: f_v(c) = X^c·Π_children Σ_{c' ≠ c} f_u(c'), rooted at vertex 0 */
function psTree(adj, k) {
  const f = (v, par) => {
    const kids = adj[v].filter((u) => u !== par).map((u) => f(u, v));
    return Array.from({ length: k }, (_, c) => { let p = new Array(c + 1).fill(0); p[c] = 1; for (const g of kids) { let s = [0]; g.forEach((q, d) => { if (d !== c) s = padd(s, q); }); p = pmul(p, s); } return p; });
  };
  return trim(f(0, -1).reduce(padd, [0]));
}
const ps = (a, k) => psTree(graph(a), k);
/* brute force over all k^n colourings */
function psBrute(a, k) {
  const adj = graph(a), n = adj.length, col = new Array(n).fill(0), out = [];
  const rec = (v, s) => { if (v === n) { out[s] = (out[s] || 0) + 1; return; } for (let c = 0; c < k; c++) { if (adj[v].some((u) => u < v && col[u] === c)) continue; col[v] = c; rec(v + 1, s + c); } };
  rec(0, 0); return trim(Array.from({ length: out.length }, (_, d) => out[d] || 0));
}
/* AHU canonical form of an unrooted tree (root at the centre or centres) */
function ahu(adj) {
  const n = adj.length; let deg = adj.map((x) => x.length), leaves = [], left = n; const removed = new Array(n).fill(false);
  deg.forEach((d, v) => { if (d <= 1) leaves.push(v); });
  while (left > 2) { const nx = []; for (const v of leaves) { removed[v] = true; left--; for (const u of adj[v]) if (!removed[u] && --deg[u] === 1) nx.push(u); } leaves = nx; }
  const centres = [...Array(n).keys()].filter((v) => !removed[v]);
  const enc = (v, p) => '(' + adj[v].filter((u) => u !== p).map((u) => enc(u, v)).sort().join('') + ')';
  return centres.map((c) => enc(c, -1)).sort()[0];
}
const alpha = (j) => [5, j, j, 4, 3], beta = (j) => [4, j, j, 5, 3];
const BASEP = [[5, 4, 3], [4, 5, 3]], WIT = [[2, 2, 2, 2, 2, 1, 4, 3], [2, 2, 3, 2, 3, 4, 2]];
const X = (d) => { const p = new Array(d + 1).fill(0); p[d] = 1; return p; };
const isoSet = (p) => new Set(p.map((a) => ahu(graph(a))));
const samePairIso = (p, q) => { const a = p.map((x) => ahu(graph(x))).sort().join('|'), b = q.map((x) => ahu(graph(x))).sort().join('|'); return a === b; };
const listedIndep = (p) => { const n = p[0].reduce((s, v) => s + v, 0); if (samePairIso(p, BASEP)) return true; for (let j = 1; 2 * j + 12 <= n; j++) if (samePairIso(p, [alpha(j), beta(j)])) return true; return false; };

/* ---------- open ---------- */
await page.goto(origin + BASE + 'viz/caterpillar-pairs/');
await page.waitForFunction(() => window.CP_DEBUG && CP_DEBUG.frames() > 3, null, { timeout: 120000 });
const searchOK = await page.waitForFunction(() => CP_DEBUG.searchDone(), null, { timeout: 120000 }).then(() => true, () => false);
await settle();
let [s0, i] = await D(() => [CP_DEBUG.state(), CP_DEBUG.info()]);
check('opens on the listed family and plays through j (the pair shown is α_j/β_j for the current j), and the search finishes', searchOK && s0.preset === 'family' && s0.mode === 'family' && i.pair && i.pair[0].join() === alpha(s0.j).join() && i.pair[1].join() === beta(s0.j).join() && s0.playing, `j = ${s0.j}`);
await pause();

/* ---------- the first question: the family ---------- */
let famOK = true, famBad = [];
for (let j = 1; j <= 12; j++) {
  await D((j) => CP_DEBUG.setRail(j), j); await settle(); const x = await info();
  const a = alpha(j), b = beta(j), p2a = ps(a, 2), p2b = ps(b, 2), p3a = ps(a, 3), p3b = ps(b, 3);
  const ok = x.pair[0].join() === a.join() && x.pair[1].join() === b.join() && eq(p2a, padd(X(j + 5), X(j + 7))) && eq(p2b, pmul([2], X(j + 6))) && eq(p3a, p3b) && eq(x.p3a, p3a) && eq(x.p3b, p3b) && eq(x.p2a, p2a) && eq(x.p2b, p2b) && x.eq3 && !x.eq2 && x.listed === `j = ${j}`;
  if (!ok) { famOK = false; famBad.push(j); }
}
check('for j = 1 … 12 the tree recursion gives ps(α_j, 2) = X^{j+5} + X^{j+7}, ps(β_j, 2) = 2X^{j+6}, equal ps(·, 3), and the page agrees', famOK, famBad.join(' '));
await preset('base'); i = await info();
const bA2 = psBrute([5, 4, 3], 2), bB2 = psBrute([4, 5, 3], 2), bA3 = psBrute([5, 4, 3], 3), bB3 = psBrute([4, 5, 3], 3);
check('base pair by brute force over all 3¹² colourings: ps(·, 3) equal with coefficients 1, 7, 31, 94, 224, 444, 729, 991, 1102, …; ps(·, 2) = X⁵ + X⁷ against 2X⁶', eq(bA3, bB3) && bA3.slice(4).join() === '1,7,31,94,224,444,729,991,1102,991,729,444,224,94,31,7,1' && eq(bA2, padd(X(5), X(7))) && eq(bB2, pmul([2], X(6))));
check('…and the page reports exactly those polynomials and calls the pair listed', eq(i.p3a, bA3) && eq(i.p3b, bB3) && eq(i.p2a, bA2) && eq(i.p2b, bB2) && i.listed === 'base' && /X⁵ \+ X⁷ · 2X⁶/.test(await text('ro2')));

/* ---------- the second question: Lean's witness ---------- */
await preset('witness'); i = await info();
const wA3 = ps(WIT[0], 3), wB3 = ps(WIT[1], 3);
check('witness: 18 vertices each, ps(·, 2) = X⁸ + X¹⁰ against 2X⁹ and equal ps(·, 3) by the tree recursion; the page agrees', i.n === 18 && eq(ps(WIT[0], 2), padd(X(8), X(10))) && eq(ps(WIT[1], 2), pmul([2], X(9))) && eq(wA3, wB3) && eq(i.p3a, wA3) && eq(i.p2a, ps(WIT[0], 2)) && eq(i.p2b, ps(WIT[1], 2)) && i.eq3 && !i.eq2);
check('…its three-colour coefficients are 3, 42, 268, 1116, 3490, …, 61900, … from degree 8 and sum to 3·2¹⁷', wA3.slice(8).join() === '3,42,268,1116,3490,8718,17950,31050,45643,57378,61900,57378,45643,31050,17950,8718,3490,1116,268,42,3' && wA3.reduce((s, v) => s + v, 0) === 3 * 2 ** 17);
const lenSpine = (a) => { const adj = graph(a); return adj.filter((nb) => nb.length >= 2).length; };
check('…and it is not listed: A has 8 non-leaf vertices, the listed 18-vertex pair α₃/β₃ only 5, and AHU forms differ', lenSpine(WIT[0]) === 8 && lenSpine(alpha(3)) === 5 && lenSpine(beta(3)) === 5 && !listedIndep(WIT) && i.listed === null && /不在名单里/.test(await text('ro4')));

/* ---------- the exhaustive search ---------- */
const comps = (n) => { const out = []; const rec = (r, pre) => { if (!r) { out.push(pre.slice()); return; } for (let f = 1; f <= r; f++) { pre.push(f); rec(r - f, pre); pre.pop(); } }; rec(n, []); return out; };
const adm = (a) => (a.length === 1 && a[0] === 1) || (a[0] >= 2 && a[a.length - 1] >= 2);
const key = (a) => { const r = a.slice().reverse(); return a.join(',') <= r.join(',') ? a.join(',') : r.join(','); };
const pageSearch = await D(() => CP_DEBUG.search());
let srOK = true, srBad = [];
for (let n = 1; n <= 18; n++) {
  const reps = new Map(); for (const a of comps(n)) if (adm(a)) reps.set(key(a), a);
  const groups = new Map(); for (const a of reps.values()) { const k3 = ps(a, 3).join(','); if (!groups.has(k3)) groups.set(k3, []); groups.get(k3).push(a); }
  const mine = []; for (const g of groups.values()) for (let x = 0; x < g.length; x++) for (let y = x + 1; y < g.length; y++) if (!eq(ps(g[x], 2), ps(g[y], 2))) mine.push([g[x], g[y]]);
  const pg = pageSearch.find((r) => r.n === n);
  const sig = (p) => [key(p[0]), key(p[1])].sort().join(' / ');
  const a = mine.map(sig).sort().join('; '), b = pg ? pg.pairs.map((p) => sig([p.a, p.b])).sort().join('; ') : '?';
  const listedOK = pg && pg.pairs.every((p) => (p.listed !== null) === listedIndep([p.a, p.b]));
  if (!pg || pg.classes !== reps.size || a !== b || !listedOK) { srOK = false; srBad.push(n); }
}
check('for every n ≤ 18 the page’s classes, pairs and listed flags equal an independent search with the tree recursion', srOK, srBad.join(' '));
const at = (n) => pageSearch.find((r) => r.n === n);
check('only listed pairs up to n = 17 (one each at 12, 14, 16); at n = 18 six pairs, five unlisted, Lean’s witness among them', [...Array(17).keys()].every((m) => { const r = at(m + 1); return r.pairs.every((p) => p.listed); }) && [12, 14, 16].every((m) => at(m).pairs.length === 1) && at(18).pairs.length === 6 && at(18).pairs.filter((p) => !p.listed).length === 5 && at(18).pairs.some((p) => samePairIso([p.a, p.b], WIT)));
let isoOK = true;
for (let n = 4; n <= 15; n++) { const reps = new Map(); for (const a of comps(n)) if (adm(a)) reps.set(key(a), a); const codes = new Set([...reps.values()].map((a) => ahu(graph(a)))); if (codes.size !== reps.size) isoOK = false; }
check('for n ≤ 15, different compositions up to reversal give non-isomorphic caterpillars (AHU), so the search covers isomorphism classes', isoOK);
check('every ps(·, 3) in the search sums to 3·2ⁿ⁻¹ (checked on the six n = 18 pairs)', at(18).pairs.every((p) => [p.a, p.b].every((a) => ps(a, 3).reduce((s, v) => s + v, 0) === 3 * 2 ** 17)));

/* ---------- other presets ---------- */
await preset('other'); i = await info();
check('other preset: (3, 3, 3, 4, 5)/(3, 3, 3, 5, 4), unlisted, equal ps(·, 3) by the tree recursion', !!i.pair && i.pair[0].join() === '3,3,3,4,5' && i.pair[1].join() === '3,3,3,5,4' && i.listed === null && eq(ps([3, 3, 3, 4, 5], 3), ps([3, 3, 3, 5, 4], 3)) && ((await D(() => { const b = document.querySelector('#pairChips [aria-pressed="true"]'); return b ? b.textContent : ''; })).startsWith('33345/33354')));
await preset('big'); i = await info();
const g5 = ps(alpha(5), 3);
check('big preset: j = 5, n = 22, 31 nonzero coefficients from degree 7 to 37, largest 819624, as the note says', i.n === 22 && g5.filter((c) => c > 0).length === 31 && g5.findIndex((c) => c > 0) === 7 && g5.length - 1 === 37 && Math.max(...g5) === 819624 && /819624/.test(await text('presetNote')) && (await text('ro3')).startsWith('7–37'));

/* ---------- controls ---------- */
await click('[data-mode="search"]'); await D(() => CP_DEBUG.setRail(18)); await settle();
const chips = await D(() => [...document.querySelectorAll('#pairChips [data-pick]')].length);
if (chips > 3) await click('#pairChips [data-pick="3"]'); i = await info();
const p18 = at(18).pairs[3];
check('search mode lists the six n = 18 pairs as chips and a chip selects its pair', chips === 6 && !!p18 && !!i.pair && i.pair[0].join() === p18.a.join() && i.pair[1].join() === p18.b.join() && (await state()).preset === null);
await D(() => CP_DEBUG.setRail(13)); await settle(); i = await info();
check('n = 13 has no pair: the page says so instead of drawing one', i.pair === null && /没有/.test(await text('roNote')));
await D(() => { const e = document.getElementById('jIn'); e.value = 4; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the j slider switches to the family and marks the settings custom', (await state()).mode === 'family' && i.pair[0].join() === '5,4,4,4,3' && /自定义|Custom/.test(await text('presetNote')));
for (const p of ['family', 'base', 'witness', 'search', 'other', 'big']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
await preset('family');
check('family rail marks j = 1, j = 7 (checked in the source) and j = 12', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 'j = 1 | j = 7（原文检查到此） | j = 12');
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps j by one and marks the settings custom', (await state()).j === 2 && (await state()).preset === null);
await page.keyboard.press('e'); await settle();
check('E jumps to j = 12 and pauses', (await state()).j === 12 && (await state()).playing === false);
await preset('search'); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing the search to the end reports five unlisted pairs at n = 18', await waitToast(/n = 18，一共 5 对/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
check('search rail marks n = 6, 16 (searched in the source) and n = 18', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 'n = 6 | 16（原文搜到此） | n = 18');
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await preset('witness');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['witness', 'family']) {
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
check('English title', (await D(() => document.title)).startsWith('CATER//PAIRS · Caterpillars that only the third specialization cannot tell apart'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links both dossiers, both Lean files, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['bingham-2026-caterpillar-principal-specialization-family.md', 'bingham-2026-caterpillar-principal-specialization-uniqueness.md', 'PrincipalSpecialization/BinghamCaterpillarPs3Family.lean', 'PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.lean', 'Blueprint/D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.md', 'Library/Combinatorics/bingham2026principalspecializations.md', 'doi.org/10.48550/arXiv.2610.31785', 'arxiv.org/abs/2610.31785'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="caterpillar-pairs"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.CP_DEBUG && CP_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'caterpillar-pairs');

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
