#!/usr/bin/env node
// Browser regression suite for viz/fourth-basis (Playwright + Chromium with software WebGL).
//   node tests/fourth-basis.test.mjs
// Reads page state through the read-only window.MUB_DEBUG probe and checks it against an independent implementation:
// the known bases rebuilt from their definitions (Pauli bases, Fourier and quadratic-phase bases as nested complex arrays,
// qubit ⊗ qutrit products), overlap probabilities recomputed from the page's own candidates, unitarity of the candidates,
// the commutator identity Σ‖[P, Q]‖² = 2(cols − Σp²) checked on explicit projectors, and the honesty of the status labels.
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
  const start = await page.evaluate(() => MUB_DEBUG.frames());
  await page.waitForFunction((f0) => !MUB_DEBUG.pending() && MUB_DEBUG.frames() >= f0 + 2, start, { timeout: 60000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => MUB_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => MUB_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => MUB_DEBUG.info());
const state = () => D(() => MUB_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => MUB_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => MUB_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 60000 }); return true; } catch { return false; }
};

// --- independent implementation: vectors as arrays of [re, im]; a basis is an array of column vectors
const cexp = (t) => [Math.cos(t), Math.sin(t)];
const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const inner = (u, v) => u.reduce((s, x, k) => { const p = cmul([x[0], -x[1]], v[k]); return [s[0] + p[0], s[1] + p[1]]; }, [0, 0]);
const abs2 = (z) => z[0] * z[0] + z[1] * z[1];
const std = (d) => Array.from({ length: d }, (_, k) => Array.from({ length: d }, (_, j) => [j === k ? 1 : 0, 0]));
const four = (d, q) => Array.from({ length: d }, (_, k) => Array.from({ length: d }, (_, j) => cexp(2 * Math.PI * (j * k + q * j * j) / d).map((x) => x / Math.sqrt(d))));
const r2 = Math.SQRT1_2;
const qubit = [std(2), [[[r2, 0], [r2, 0]], [[r2, 0], [-r2, 0]]], [[[r2, 0], [0, r2]], [[r2, 0], [0, -r2]]]];
const tensor = (A, B) => A.flatMap((a) => B.map((b) => a.flatMap((x) => b.map((y) => cmul(x, y)))));     // columns a ⊗ b
const known = (d) => d === 2 ? qubit : d === 6 ? [0, 1, 2].map((r) => tensor(qubit[r], [std(3), four(3, 0), four(3, 1)][r])) : [std(d), four(d, 0), four(d, 1)];
const pageCols = (M) => { const n = Math.round(Math.sqrt(M.re.length)); return Array.from({ length: n }, (_, k) => Array.from({ length: n }, (_, j) => [M.re[j * n + k], M.im[j * n + k]])); };
const candCols = (U, d, cols) => Array.from({ length: cols }, (_, k) => Array.from({ length: d }, (_, j) => [U.re[j * cols + k], U.im[j * cols + k]]));
const maxUnbiasDev = (A, B, d) => { let m = 0; for (const a of A) for (const b of B) m = Math.max(m, Math.abs(abs2(inner(a, b)) - 1 / d)); return m; };
const defect = (Bs, V, d) => { let s = 0; for (const B of Bs) for (const b of B) for (const v of V) s += (abs2(inner(b, v)) - 1 / d) ** 2; return s; };
const orthoDev = (V) => { let m = 0; V.forEach((a, i) => V.forEach((b, j) => { const z = inner(a, b); m = Math.max(m, Math.hypot(z[0] - (i === j ? 1 : 0), z[1])); })); return m; };
// ‖[P, Q]‖² for rank-one projectors P = |a⟩⟨a|, Q = |b⟩⟨b| built as explicit matrices
const proj = (a) => a.map((x) => a.map((y) => cmul(x, [y[0], -y[1]])));
const mm = (A, B) => A.map((r) => B[0].map((_, j) => r.reduce((s, x, k) => { const p = cmul(x, B[k][j]); return [s[0] + p[0], s[1] + p[1]]; }, [0, 0])));
const commSq = (a, b) => { const P = proj(a), Q = proj(b), X = mm(P, Q), Y = mm(Q, P); let s = 0; X.forEach((r, i) => r.forEach((x, j) => { s += (x[0] - Y[i][j][0]) ** 2 + (x[1] - Y[i][j][1]) ** 2; })); return s; };

await page.goto(origin + BASE + 'viz/fourth-basis/');
await page.waitForFunction(() => window.MUB_DEBUG && MUB_DEBUG.frames() > 2, null, { timeout: 60000 });
await settle();

// --- the known bases
check('opens on the six-dimensional search and plays', (await state()).preset === 'six' && (await state()).d === 6 && (await state()).playing === true);
await pause();
for (const d of [2, 3, 5, 6, 7]) {
  await click(`#dimChips [data-dim="${d}"]`); const i = await info(), Bs = known(d);
  let same = true; i.bases.forEach((M, r) => { const C = pageCols(M); C.forEach((col, k) => col.forEach((z, j) => { if (Math.hypot(z[0] - Bs[r][k][j][0], z[1] - Bs[r][k][j][1]) > 1e-12) same = false; })); });
  const dev = Math.max(maxUnbiasDev(Bs[0], Bs[1], d), maxUnbiasDev(Bs[0], Bs[2], d), maxUnbiasDev(Bs[1], Bs[2], d));
  check(`d = ${d}: the page’s three bases match their definitions and are pairwise unbiased`, same && dev < 1e-12 && i.pairDev < 1e-12 && Bs.every((B) => orthoDev(B) < 1e-12), dev.toExponential(1));
}

// --- six dimensions: the search stalls
await preset('six'); await setFrac(1); let i = await info();
let Bs = known(6), worstD = 0, worstO = 0;
i.Ufinal.forEach((U, k) => { const V = candCols(U, 6, 6); worstD = Math.max(worstD, Math.abs(defect(Bs, V, 6) - i.finals[k])); worstO = Math.max(worstO, orthoDev(V)); });
check('d = 6: every final candidate is unitary and its defect matches an independent recomputation', worstO < 1e-10 && worstD < 1e-10, `${worstO.toExponential(1)} · ${worstD.toExponential(1)}`);
check('d = 6: no start brings the defect below 10⁻²⁰; all stall above 0.1', i.finals.every((x) => x > 0.1) && i.stats.hits === 0 && i.stats.n === 8, i.finals.map((x) => x.toFixed(3)).join(' '));
check('d = 6: the defect never increases along a run (descent)', i.hist.every((x, t) => t === 0 || x <= i.hist[t - 1] + 1e-15));
check('d = 6: the status reads OPEN and the note calls it a numerical lead, not a proof', /OPEN/.test(await text('pillOpen')) && /不是证明|数值线索/.test(await text('roNote')) && /≥ 3 \/ 7/.test(await text('roKnown')));
await setFrac(0.06); i = await info();               // mid-run, where the snapshot shown differs from the final candidate
const P0 = i.P, Vnow = candCols(i.U, 6, 6);
check('the bar heights are the overlap probabilities |⟨b|u⟩|² of the candidate shown now (mid-run)', i.pos.t > 0 && i.pos.t < 400 && P0.every((P, r) => P.every((p, q) => Math.abs(p - abs2(inner(Bs[r][Math.floor(q / 6)], Vnow[q % 6]))) < 1e-12)), `start ${i.pos.s + 1} step ${i.pos.t}`);
let cs = 0; for (const b of Bs[1]) for (const v of Vnow) cs += commSq(b, v);
const cs2 = 2 * (6 - P0[1].reduce((s, p) => s + p * p, 0));
check('commutator readout: Σ‖[P_j, Q_r]‖² from explicit projectors equals 2(d − Σp²), at most 2(d − 1) = 10', Math.abs(cs - cs2) < 1e-10 && cs2 <= 10 + 1e-12 && (await text('roComm')).split(' · ')[1] === cs2.toFixed(4), `${cs.toFixed(6)}`);

// --- prime dimensions: the same search finds a fourth basis
// with the page's default seed; other batches of starts can find none in d = 7
for (const [name, d, minHits] of [['five', 5, 1], ['three', 3, 6], ['seven', 7, 1]]) {
  await preset(name); await setFrac(1); i = await info(); Bs = known(d);
  const k = i.finals.findIndex((x) => x < 1e-20), V = k >= 0 ? candCols(i.Ufinal[k], d, d) : null;
  const ok = V && orthoDev(V) < 1e-10 && Bs.every((B) => maxUnbiasDev(B, V, d) < 1e-12);
  check(`d = ${d}: at least ${minHits} start(s) find a basis unbiased to all three, verified independently`, i.stats.hits >= minHits && ok && /EXISTS/.test(await text('pillOpen')), `hits ${i.stats.hits}/8`);
}
await preset('five'); await setFrac(1); i = await info();
const kFound = i.finals.findIndex((x) => x < 1e-20); Bs = known(5);
const Vf = candCols(i.Ufinal[kFound], 5, 5); let csF = 0; for (const b of Bs[2]) for (const v of Vf) csF += commSq(b, v);
check('d = 5: for a basis found, the commutator sum reaches its maximum 2(d − 1) = 8', Math.abs(csF - 8) < 1e-9, csF.toFixed(9));

// --- dimension two: proved impossible
await preset('two'); await setFrac(1); i = await info();
check('d = 2: the defect stalls (no fourth basis exists) and the status says proved', i.finals.every((x) => x > 0.5) && /PROVED/.test(await text('pillOpen')) && /已证/.test(await text('roNote')));

// --- single vectors
await preset('sixvec'); await setFrac(1); i = await info(); Bs = known(6);
let vOK = true; i.Ufinal.forEach((U, k) => { const v = candCols(U, 6, 1); if (Math.abs(defect(Bs, v, 6) - i.finals[k]) > 1e-10 || orthoDev(v) > 1e-10) vOK = false; });
check('d = 6, one vector: all starts stall above 0.03; the defects match an independent recomputation', vOK && i.finals.every((x) => x > 0.03) && i.stats.hits === 0 && i.cols === 1, i.finals.map((x) => x.toFixed(4)).join(' '));
check('…and the commutator readout is not shown for a single vector', (await text('roComm')) === '—');
await preset('fivevec'); await setFrac(1); i = await info(); Bs = known(5);
const v5 = candCols(i.Ufinal[i.finals.findIndex((x) => x < 1e-20)], 5, 1);
check('d = 5, one vector: found, and unbiased to all three bases by direct check', i.stats.hits >= 6 && Bs.every((B) => maxUnbiasDev(B, v5, 5) < 1e-12));

// --- the known three, pairwise
await preset('known'); i = await info();
check('known three in d = 6: every pairwise overlap is 1/6, no search is run', i.view === 'known' && i.P.every((P) => P.every((p) => Math.abs(p - 1 / 6) < 1e-12)) && !(await visible('targetChips')) && (await text('roHits')) === '—');

// --- rail, keys, controls
await preset('six');
check('the rail marks the 8 starts', (await D(() => [...document.querySelectorAll('#marks i')].map(m => m.textContent).join(' '))) === '0 1 2 3 4 5 6 7 8');
await setFrac(0);
await page.keyboard.press('ArrowRight'); await settle();
check('→ jumps to the next start', (await info()).pos.s === 1 && (await info()).pos.t === 0);
await page.keyboard.press('ArrowLeft'); await settle();
check('← jumps back', (await info()).pos.s === 0);
const f0 = (await info()).finals.join(',');
await page.keyboard.press('r'); await settle();
check('R draws new random starts', (await info()).finals.join(',') !== f0);
await click('#targetChips [data-target="vector"]');
check('changing the target marks the settings custom and resets the search', (await state()).preset === null && (await state()).nowFrac === 0 && (await info()).cols === 1 && /自定义/.test(await text('presetNote')));
await click('#viewChips [data-view="known"]');
check('the known-three view hides the target chips and blanks the rail', !(await visible('targetChips')) && (await D(() => document.getElementById('marks').children.length)) === 0);
await click('#viewChips [data-view="search"]');
const PRE = ['six', 'five', 'three', 'seven', 'two', 'sixvec', 'fivevec', 'known'];
for (const name of PRE) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }

// --- play and toasts
await preset('six'); await setFrac(0.995); await click('#play');
check('the toast in six dimensions says nothing was found and that this is not a proof', await waitToast(/不是证明/));
await pause();
await preset('three'); await setFrac(0.995); await click('#play');
check('the toast in three dimensions reports the starts that found it', await waitToast(/找到了/));
await pause();
await preset('five'); await setFrac(0.3); await click('#play'); await waitFrames(12); const g1 = (await state()).nowFrac; await pause();
check('play advances the search', g1 > 0.3);
await click('#rev'); await waitFrames(12); const g2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', g2 < g1);
await page.click('#rev'); await pause();
await page.focus('#now'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with the slider focused', playing === true);
await pause();

// --- language
await click('#dimChips [data-dim="7"]');
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /vs Fourier/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('FOURTH//BASIS · A fourth mutually unbiased basis'));
await page.click('#infoBtn'); await page.waitForTimeout(200);
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
await page.keyboard.press('Escape'); await page.waitForTimeout(150);
check('Esc closes the drawer', (await D(() => document.getElementById('drawer').hidden)) === true);
check('focus returns to the drawer button', (await D(() => document.activeElement?.id)) === 'infoBtn');

// --- index round trip
const live = readRegistry().visualizations.filter(v => v.status === 'live').length;
await page.click('.crumb'); await page.waitForLoadState('load'); await page.waitForTimeout(800);
check('language choice carries to the index', (await D(() => document.documentElement.dataset.lang)) === 'en');
check('index lists every live visualization', (await D(() => document.querySelectorAll('.card').length)) === live, `live ${live}`);
await page.click('.card:has(a[href*="fourth-basis"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'fourth-basis');

// --- narrow layouts in both languages
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await page.waitForTimeout(300);
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await page.waitForTimeout(700);
    check(`no horizontal scroll at ${w}px (${lang})`, (await D(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 }); await page.waitForTimeout(300);
}
check('no script errors during the whole session', errors.length === 0, errors.join(' | '));

const failed = results.filter(r => !r.ok);
console.log(`\n${results.length - failed.length}/${results.length} passed`);
await browser.close(); server.close();
if (failed.length) process.exit(1);
