#!/usr/bin/env node
// Browser regression suite for viz/pauli-volumes (Playwright + Chromium with software WebGL).
//   node tests/pauli-volumes.test.mjs
// Reads page state through the read-only window.PV_DEBUG probe and checks it against an independent implementation: the three
// ratios as exact BigInt fractions, the d = 2 volumes as determinants of the expected vertex sets, region membership rewritten with
// the minimum coordinate, an independent random-number generator for the d = 2 box ratio, the section of a 4-simplex classified by
// how many vertices lie above λ₄ = t, and the closed form (1 − t)³/6 of the section of the standard simplex. Fixed reference data:
// Siudzińska (2020) printed the ratios for d = 2 … 5.
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
  const start = await page.evaluate(() => PV_DEBUG.frames());
  await page.waitForFunction((f0) => !PV_DEBUG.pending() && PV_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => PV_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => PV_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => PV_DEBUG.info());
const state = () => D(() => PV_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => PV_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => PV_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
const bf = (n) => { let r = 1n; for (let i = 2n; i <= BigInt(n); i++) r *= i; return r; };
const gcd = (a, b) => { while (b) [a, b] = [b, a % b]; return a; };
const frac = (p, q) => { const g = gcd(p, q); return [p / g, q / g]; };
function exactFr(d) {   // r1 = d/(d+1)!, r2 = (d² − 1)(d − 1)^d / d^(d+2), r3 = 1/(d + 1)
  const D = BigInt(d);
  return [frac(D, bf(d + 1)), frac((D * D - 1n) * (D - 1n) ** D, D ** (D + 2n)), frac(1n, D + 1n)];
}
const val = ([p, q]) => Number(p) / Number(q);
const fstr = ([p, q]) => `${p}/${q}`;
const PAPER = { 2: ['1/3', '3/16', '1/3'], 3: ['1/8', '64/243', '1/4'], 4: ['1/30', '1215/4096', '1/5'], 5: ['1/144', '24576/78125', '1/6'] };
const lowB = (d) => -1 / (d - 1);
function region(x, d) {   // 0 = outside C, 1 = C only, 2 = G only, 3 = E; complete positivity as s ≤ 1 + d·min x
  const s = x.reduce((a, b) => a + b, 0); let mn = Infinity; for (const v of x) mn = Math.min(mn, v);
  if (!(s >= lowB(d) - 1e-12 && s <= 1 + d * mn + 1e-12)) return 0;
  if (mn < -1e-12) return 1;
  return s <= 1 + 1e-12 ? 3 : 2;
}
const det3 = (a, b, c) => a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0]) + a[2] * (b[0] * c[1] - b[1] * c[0]);
const tetVol = (v) => Math.abs(det3(...[1, 2, 3].map((i) => v[i].map((x, k) => x - v[0][k])))) / 6;
const sameSet = (A, B) => A.length === B.length && A.every((a) => B.some((b) => b.every((x, k) => Math.abs(x - a[k]) < 1e-12)));
let lcg = 12345; const rnd = () => { lcg = (Math.imul(lcg, 1103515245) + 12345) >>> 0; return lcg / 4294967296; };
let inC2 = 0; const NB = 200000; for (let i = 0; i < NB; i++) if (region([-1 + 2 * rnd(), -1 + 2 * rnd(), -1 + 2 * rnd()], 2) > 0) inC2++;
const within = (est, p, n, k = 4) => Math.abs(est - p) <= k * Math.sqrt(p * (1 - p) / n);

/* ---------- load ---------- */
await page.goto(origin + BASE + 'viz/pauli-volumes/');
await page.waitForFunction(() => window.PV_DEBUG && PV_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let st = await state(), i = await info();
check('opens on the tetrahedron preset (d = 2, focus C) and plays', st.mode === 'solid' && st.preset === 'tetra' && st.playing === true && i.d === 2 && i.focus === 'C');
await pause();

/* ---------- the frozen formulas ---------- */
let fOK = true, fDet = '';
// the page reports exact values for the current d; walk d through the sample mode
await click('#modeChips [data-mode="sample"]');
for (const d of [2, 3, 4, 5, 6]) {
  await click(`#dChips [data-d="${d}"]`); i = await info();
  const [a, b, c] = exactFr(d);
  if (i.d !== d || Math.abs(i.exact.r1 - val(a)) > 1e-14 * val(a) || Math.abs(i.exact.r2 - val(b)) > 1e-14 || Math.abs(i.exact.r3 - val(c)) > 1e-15) { fOK = false; fDet += `d=${d} `; }
}
check('d = 2 … 6: the page’s three ratios equal the exact fractions d/(d+1)!, (d²−1)(d−1)^d/d^(d+2), 1/(d+1)', fOK, fDet);
check('the exact fractions reproduce the twelve ratios Siudzińska printed for d = 2 … 5', [2, 3, 4, 5].every((d) => exactFr(d).map(fstr).join() === PAPER[d].join()));
await click('#dChips [data-d="4"]');
check('the readouts show the d = 4 fractions 1/30, 1215/4096, 1/5', (await text('ro2')).startsWith('1/30') && (await text('ro3')).startsWith('1215/4096') && (await text('ro4')).startsWith('1/5'));
await click('#dChips [data-d="6"]');
check('…and for d = 6 the reduced fraction 546875/1679616', (await text('ro3')).startsWith(fstr(exactFr(6)[1])) && fstr(exactFr(6)[1]) === '546875/1679616');
i = await info();
const m6 = 7, L6 = 6 / 5;
check('d = 6 volumes: Leb(P) = Lᵐ, Leb(C) = dLᵐ/m!, Leb(G) = (d+1)/m!, Leb(E) = 1/m!', Math.abs(i.exact.P - L6 ** m6) < 1e-12 && Math.abs(i.exact.C - 6 * L6 ** m6 / 5040) < 1e-12 && Math.abs(i.exact.G - 7 / 5040) < 1e-15 && Math.abs(i.exact.E - 1 / 5040) < 1e-15);
check('the second ratio increases with d and stays below 1/e (d = 2 … 16, exact fractions)', Array.from({ length: 15 }, (_, k) => val(exactFr(k + 2)[1])).every((r, k, arr) => r < 1 / Math.E && (k === 0 || r > arr[k - 1])));

/* ---------- d = 2 solids ---------- */
await preset('tetra'); i = await info();
const CV = [[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], SV = [[0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 0, 1]], TV = [[1, 1, 1], [1, 0, 0], [0, 1, 0], [0, 0, 1]];
check('C is the tetrahedron with vertices (1,1,1), (1,−1,−1), (−1,1,−1), (−1,−1,1)', sameSet(i.verts.C, CV));
check('…its determinant volume is 8/3, one third of the box [−1, 1]³', Math.abs(tetVol(CV) - 8 / 3) < 1e-12 && Math.abs(tetVol(CV) / 8 - val(exactFr(2)[0])) < 1e-12);
check('G is S ∪ T₁(S): the page’s two simplices are the expected vertex sets, volume 1/6 + 1/3 = 1/2 = 3/16 of C', sameSet(i.verts.S, SV) && sameSet(i.verts.T1, TV) && Math.abs(tetVol(SV) + tetVol(TV) - 0.5) < 1e-12 && Math.abs((tetVol(SV) + tetVol(TV)) / tetVol(CV) - 3 / 16) < 1e-12);
check('E = S has volume 1/6, one third of G', Math.abs(tetVol(SV) / (tetVol(SV) + tetVol(TV)) - 1 / 3) < 1e-12);
check('an independent generator puts the share of the box in C within 4σ of 1/3 (2·10⁵ points)', within(inC2 / NB, 1 / 3, NB), (inC2 / NB).toFixed(5));
await setFrac(1); i = await info();
check('every shown point is coloured by the region the independent membership test assigns', i.shown.length === 400 && i.shown.every(([x, c]) => region(x, 2) === c));
check('the page’s three estimates at n = 30000 lie within 4σ of 1/3, 3/16, 1/3', i.n === 30000 && within(i.eA, 1 / 3, 30000) && within(i.eB, 3 / 16, 30000) && within(i.eC, 1 / 3, i.hitsG), `${i.eA} ${i.eB} ${i.eC}`);
check('the C-points are uniform in C: every shown one is in C, classified correctly', i.shownB.every(([x, c]) => region(x, 2) === c && c > 0));
await click('#focusChips [data-focus="G"]');
check('focus chips mark the settings custom', (await state()).focus === 'G' && (await state()).preset === null);

/* ---------- d = 3 slices ---------- */
await preset('slice'); i = await info();
check('the slice preset is d = 3 with exact 4D volumes 0.6328125, 1/6, 1/24', i.mode === 'slice' && i.d === 3 && Math.abs(i.exact.C - 0.6328125) < 1e-12 && Math.abs(i.exact.G - 1 / 6) < 1e-15 && Math.abs(i.exact.E - 1 / 24) < 1e-15);
check('integrating the exact section volumes over λ₄ returns the 4D volumes (to 10⁻⁵)', Math.abs(i.iC - i.exact.C) < 1e-5 && Math.abs(i.iG - i.exact.G) < 1e-5 && Math.abs(i.iE - i.exact.E) < 1e-5, `${i.iC} ${i.iG} ${i.iE}`);
let segOK = true, volOK = true, onOK = true, det = '';   // the page cuts its sections at t + 10⁻⁹, hence the tolerances below
for (const t of [-0.3, 0.07, 0.42, 0.77]) {
  await setFrac((t + 0.5) / 1.5); i = await info();
  for (const [key, V] of [['segC', i.verts.C], ['segS', i.verts.S], ['segT', i.verts.T1]]) {
    const above = V.filter((v) => v[3] > i.t + 1e-9).length, want = above === 0 || above === 5 ? 0 : above === 1 || above === 4 ? 6 : 9;
    if (i[key].length !== want) { segOK = false; det += `${key}@${i.t.toFixed(2)}:${i[key].length}≠${want} `; }
    for (const seg of i[key]) for (const p of seg) { const x = [...p, i.t]; const s = x.reduce((a, b) => a + b, 0), mn = Math.min(...x); const e = 1e-7, inside = key === 'segC' ? s >= -0.5 - e && s <= 1 + 3 * mn + e : key === 'segS' ? mn >= -e && s <= 1 + e : mn >= -e && s >= 1 - e && s <= 1 + 3 * mn + e; if (!inside) onOK = false; }
  }
  if (i.t > 0 && Math.abs(i.vE - (1 - i.t) ** 3 / 6) > 1e-8) volOK = false;
}
check('section segment counts match the vertex split (tetrahedron 6, prism 9, empty 0)', segOK, det);
check('every section vertex lies in its region’s closure on λ₄ = t', onOK);
check('the section of E = S has volume (1 − t)³/6', volOK);
await click('#focusChips [data-focus="E"]');
check('slice mode keeps the d chips hidden', !(await visible('dChips')) && (await state()).focus === 'E');

/* ---------- higher d by random points ---------- */
await preset('sample5'); await setFrac(1); i = await info();
const [a5, b5, c5] = exactFr(5).map(val);
check('d = 5: the estimates at n = 30000 lie within 4σ of 1/144, 24576/78125, 1/6', i.d === 5 && within(i.eA, a5, 30000) && within(i.eB, b5, 30000) && within(i.eC, c5, i.hitsG), `${i.eA} ${i.eB} ${i.eC}`);
check('d = 5: every shown C-point has six coordinates and is classified correctly', i.shownB.every(([x, c]) => x.length === 6 && region(x, 5) === c && c > 0));
check('the d chips are visible in this mode', await visible('dChips'));

/* ---------- presets, modes, timeline ---------- */
for (const p of ['tetra', 'bipyramid', 'simplex', 'slice', 'sample5', 'limit']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await click('#modeChips [data-mode="solid"]');
check('the solid mode chip returns to d = 2', (await info()).d === 2 && (await state()).mode === 'solid');
await preset('tetra'); await setFrac(0.97); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing the random points to the end reports the estimates and the formulas', await waitToast(/估计.*公式/));
await pause();
await preset('slice'); await setFrac(0.97); await click('#play');
check('playing the slices to the end reports the integrals and the 4D volumes', await waitToast(/∫ 截面 dt/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
await setFrac(0.5); const k0 = (await info()).k;
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps the slice by one sample', (await info()).k === k0 + 1);
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await info()).k === 150 && (await state()).playing === false);
check('the slice rail marks −1/2, 0, 1', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' '))) === 'λ₄ = −1/2 0 1');
for (const cam of ['front', 'diag', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['bipyramid', 'slice', 'sample5']) {
  await preset(p); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#focusChips [data-focus="C"]');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('PAULI//VOLUMES · Volume ratios of generalized Pauli channels'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['siudzinska-2020-generalized-pauli-volume-ratios.md', 'GeneralizedPauliVolumeRatios.lean', 'Blueprint/D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.md', 'siudzinska2020pauligeometry.md', '10.1103/PhysRevA.101.062323', 'arxiv.org/abs/2002.04657'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="pauli-volumes"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.PV_DEBUG && PV_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'pauli-volumes');

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
