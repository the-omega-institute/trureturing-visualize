#!/usr/bin/env node
// Browser regression suite for viz/lemniscate-area (Playwright + Chromium with software WebGL).
//   node tests/lemniscate-area.test.mjs
// Reads page state through the read-only window.LE_DEBUG probe and checks it against independent computations: log|p| as a
// sum over the roots, areas of {|p| < 1} by counting grid cells (the page integrates along vertical slices or in polar
// coordinates), the disc formula π Σ 1/|p′(a)|² (second order for the petals; |q(a)|^(−2/m) for a root of multiplicity m), exact rational
// arithmetic for the certificate radii, and |p| sampled on the certificate circles. Fixed reference data come from the Lean
// modules and the dossiers: the radii 97/1250000, 217/1250000, 53/625000, 849/5000000, the bounds 7.231744e-8π and
// 7.204616e-8π, the bound 20π·2⁻ᵏ with N = k² + 1, and the containment in 1 ± 2⁻ᵏ and |z − 4| < 2⁻⁽ᵏ⁻²⁾.
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
  const start = await page.evaluate(() => LE_DEBUG.frames());
  await page.waitForFunction((f0) => !LE_DEBUG.pending() && LE_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => LE_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => LE_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => LE_DEBUG.info());
const state = () => D(() => LE_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const slide = async (id, v) => { await D(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input')); }, [id, v]); await settle(); };
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => LE_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => LE_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
// log|p(z)| as a sum over the roots, with roots given as [re, im]; areas by counting grid cells, and the disc formula
// π Σ 1 / |p′(a)|² over the simple roots (plus π |q(a)|^(−2/m) for a root a of multiplicity m, q = p / (z − a)^m)
const lg = (roots, x, y) => roots.reduce((t, [a, b]) => t + Math.log(Math.hypot(x - a, y - b)), 0);
const real = (rs) => rs.map((a) => [a, 0]);
function gridArea(f, x0, x1, y0, y1, nx, ny) {   // returns the area and whether the box edge was hit
  const dx = (x1 - x0) / nx, dy = (y1 - y0) / ny; let c = 0, edge = false;
  for (let i = 0; i < nx; i++) for (let j = 0; j < ny; j++) if (f(x0 + (i + 0.5) * dx, y0 + (j + 0.5) * dy) < 0) { c++; if (i === 0 || j === ny - 1 || i === nx - 1) edge = true; }
  return { area: c * dx * dy, edge };
}
function discArea(roots) {   // simple roots only
  return roots.reduce((t, [a, b], i) => { let d = 0; roots.forEach(([c, e], j) => { if (j !== i) d += Math.log(Math.hypot(a - c, b - e)); }); return t + Math.PI * Math.exp(-2 * d); }, 0);
}
function gridAreaSimple(roots, n = 500) {   // a box of half-width 3/|p′(a)| about every simple root, upper half by symmetry when real
  let A = 0, edge = false;
  roots.forEach(([a, b], i) => { let d = 0; roots.forEach(([c, e], j) => { if (j !== i) d += Math.log(Math.hypot(a - c, b - e)); }); const r = 3 * Math.exp(-d), g = gridArea((x, y) => lg(roots, x, y), a - r, a + r, b - r, b + r, n, n); A += g.area; edge = edge || g.edge; });
  return { area: A, edge };
}
const decayRoots = (N, k) => { const r = []; for (let j = 0; j < N; j++) r.push([Math.cos(2 * Math.PI * j / N), Math.sin(2 * Math.PI * j / N)]); return r; };
function decayDisc(N, k) {   // petals at the roots of unity ω with a = p′(ω), b = p″(ω): area π/|a|² · (1 + |b|²/(2|a|⁴)), from
  // inverting w = p(ω + z) to second order and integrating |dz/dw|² over |w| < 1; the k-fold root 4 gives π |4^N − 1|^(−2/k)
  const mul = ([a, b], [c, d]) => [a * c - b * d, a * d + b * c], pw = (z, n) => { let r = [1, 0]; for (let t = 0; t < n; t++) r = mul(r, z); return r; };
  let A = 0;
  for (const w of decayRoots(N, k)) {
    const u = [w[0] - 4, w[1]], p1 = mul(pw(w, N - 1), pw(u, k)).map((x) => N * x), p2a = mul(pw(w, N - 2), pw(u, k)).map((x) => N * (N - 1) * x), p2b = mul(pw(w, N - 1), pw(u, k - 1)).map((x) => 2 * N * k * x);
    const a = Math.hypot(...p1), b = Math.hypot(p2a[0] + p2b[0], p2a[1] + p2b[1]); A += Math.PI / (a * a) * (1 + b * b / (2 * a ** 4));
  }
  return A + Math.PI * Math.pow(4 ** N - 1, -2 / k);
}
const fracC = (R, c) => (c - 0.02 * R) / (0.98 * R);
const rel = (a, b) => Math.abs(a - b) / Math.abs(b);
const CERT = { Fo: [97n, 1250000n], Fi: [217n, 1250000n], Go: [53n, 625000n], Gi: [849n, 5000000n] };

await page.goto(origin + BASE + 'viz/lemniscate-area/');
await page.waitForFunction(() => window.LE_DEBUG && LE_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle(); await pause();
let i = await info();

/* ---------- the Fekete counterexample ---------- */
check('the page opens on the frozen counterexample: K = [−20, 20], F = ±20, ±√80, G = ±20, ±10', i.mode === 'fekete' && Math.abs(i.R - 20) < 1e-12 && Math.abs(i.u - Math.sqrt(80)) < 1e-12 && Math.abs(i.c - 10) < 1e-9 && i.cert === true && (await D(() => document.querySelector('.preset[aria-pressed="true"]').dataset.preset)) === 'witness');
check('…√80 = R/√5 are the Fekete points of [−R, R] for n = 4: the roots of (1 − x²)P₃′(x) with P₃ the Legendre polynomial', [-1, 1, -1 / Math.sqrt(5), 1 / Math.sqrt(5)].every((x) => Math.abs((1 - x * x) * (15 * x * x - 3) / 2) < 1e-12) && Math.abs(20 / Math.sqrt(5) - Math.sqrt(80)) < 1e-12);
const fd = discArea(real([-20, -Math.sqrt(80), Math.sqrt(80), 20])), gd = discArea(real([-20, -10, 10, 20]));
const fg = gridAreaSimple(real([-20, -Math.sqrt(80), Math.sqrt(80), 20])), gg = gridAreaSimple(real([-20, -10, 10, 20]));
check('…the page’s areas equal the disc formula π Σ 1/|p′(a)|² (relative 1e-5) and an independent grid count (relative 2e-3)', rel(i.areaF, fd) < 1e-5 && rel(i.areaG, gd) < 1e-5 && rel(i.areaF, fg.area) < 2e-3 && rel(i.areaG, gg.area) < 2e-3 && !fg.edge && !gg.edge, `F ${i.areaF / Math.PI} vs ${fd / Math.PI}, G ${i.areaG / Math.PI} vs ${gd / Math.PI}`);
check('…the page’s areas lie beyond the Lean bounds: F ≥ 7.231744e-8π, G ≤ 7.204616e-8π, so G < F', i.areaF / Math.PI >= 7.231744e-8 && i.areaG / Math.PI <= 7.204616e-8 && i.areaG < i.areaF);
const sq = ([p, q]) => [p * p, q * q], add2 = ([a, b], [c, d]) => [a * d + c * b, b * d];
const fSum = [CERT.Fo, CERT.Fo, CERT.Fi, CERT.Fi].map(sq).reduce(add2), gSum = [CERT.Go, CERT.Go, CERT.Gi, CERT.Gi].map(sq).reduce(add2);
check('…the certificate radii give exactly the Lean bounds: 2(97/1250000)² + 2(217/1250000)² = 7.231744e-8 and 2(53/625000)² + 2(849/5000000)² = 7.204616e-8', fSum[0] * 10n ** 14n === 7231744n * fSum[1] && gSum[0] * 10n ** 14n === 7204616n * gSum[1]);
const circ = (roots, a, r, sign) => { let ok = true; for (let t = 0; t < 2000; t++) { const th = 2 * Math.PI * t / 2000, v = lg(roots, a + r * Math.cos(th), r * Math.sin(th)); if (sign * v <= 0) ok = false; } return ok; };
const Fr = real([-20, -Math.sqrt(80), Math.sqrt(80), 20]), Gr = real([-20, -10, 10, 20]);
check('…on the certificate circles |F| < 1 (discs inside Λ_F) and |G| > 1 (discs cover Λ_G), sampled at 2000 points each', circ(Fr, 20, 97 / 1250000, -1) && circ(Fr, Math.sqrt(80), 217 / 1250000, -1) && circ(Gr, 20, 53 / 625000, 1) && circ(Gr, 10, 849 / 5000000, 1));
check('…the readouts show both Lean bounds and call the result a frozen theorem', /7\.231744e-8π/.test(await text('ro4')) && /7\.204616e-8π/.test(await text('ro4')) && /冻结定理/.test(await text('ro5')));
check('…four pieces for each polynomial, each about 2/|p′(a)| wide', i.partsF.length === 4 && i.partsG.length === 4 && i.partsF.every((p) => p.x1 - p.x0 < 4e-4));
check('the zoom panel draws the certificate circles at R = 20', /Lean/.test(await text('c2Meta')));

/* ---------- the competitor curve ---------- */
const curveOK = i.curve.slice(0, 80).every(([c, a]) => rel(a, discArea(real([-20, -c, c, 20]))) < 1e-3);
check('the area curve over c = 0.4 … 19.755 equals the disc formula point by point (relative 1e-3; c = R is a double root)', curveOK);
const belowInd = i.curve.slice(0, 80).filter(([c]) => discArea(real([-20, -c, c, 20])) < fd).map(([c]) => c), belowPage = i.curve.slice(0, 80).filter(([, a]) => a < i.areaF).map(([c]) => c);
check('…the competitors that beat Fekete are the same on the page and in the formula: every curve point from just above √80 to about 12.2', JSON.stringify(belowInd) === JSON.stringify(belowPage) && belowInd[0] > Math.sqrt(80) && belowInd[0] < Math.sqrt(80) + 19.6 / 80 && belowInd[belowInd.length - 1] > 12 && belowInd[belowInd.length - 1] < 12.3 && belowInd.length === Math.round((belowInd[belowInd.length - 1] - belowInd[0]) / (19.6 / 80)) + 1, belowInd.map((c) => c.toFixed(2)).join(' '));
check('…the best c on the curve is about 10.6, about 0.94 of Fekete', i.best[0] > 10.3 && i.best[0] < 10.9 && rel(i.best[1] / i.areaF, 0.94) < 0.01);
await preset('scan'); i = await info();
check('the scan preset starts the sweep of c near 0, and its note names √80, 12.2 and the best c ≈ 10.6', i.mode === 'fekete' && i.frac < 0.2 && /10\.6/.test(await text('presetNote')) && /√80/.test(await text('presetNote')) && /12\.2/.test(await text('presetNote')));
await setFrac(0.97); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('…playing to the end raises the sweep toast with the best c', await waitToast(/扫完/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
await setFrac(fracC(20, 11)); i = await info();
check('…at c = 11 the readouts show a smaller competitor (page numerics)', Math.abs(i.c - 11) < 1e-9 && i.areaG < i.areaF && /页面数值/.test(await text('ro5')) && /更小/.test(await text('ro5')));
await setFrac(fracC(20, 5)); i = await info();
check('…at c = 5 the competitor is larger', i.areaG > i.areaF && /更大/.test(await text('ro5')));

/* ---------- smaller intervals ---------- */
await preset('small'); i = await info();
const g2F = gridArea((x, y) => lg(real(i.F), x, y), -2.6, 2.6, 0, 0.6, 2600, 300), g2G = gridArea((x, y) => lg(real(i.G), x, y), -2.6, 2.6, 0, 0.6, 2600, 300);
check('R = 2: four visible pieces; the page’s area of F equals twice an upper-half grid count (relative 3e-3)', Math.abs(i.R - 2) < 1e-9 && i.partsF.length === 4 && rel(i.areaF, 2 * g2F.area) < 3e-3 && !g2F.edge, `${i.areaF} vs ${2 * g2F.area}`);
check('…and so does the competitor at the current c (relative 3e-3)', rel(i.areaG, 2 * g2G.area) < 3e-3 && !g2G.edge);
const beat2 = i.curve.filter(([, a]) => a < i.areaF).map(([c]) => c);
check('…competitors with c from just above R/√5 to about 1.19 beat Fekete, as the preset says', beat2.length > 0 && beat2[0] > 2 / Math.sqrt(5) && beat2[0] < 2 / Math.sqrt(5) + 1.96 / 80 && beat2[beat2.length - 1] > 1.16 && beat2[beat2.length - 1] < 1.2 && /0\.89/.test(await text('presetNote')));
await preset('one'); i = await info();
const g1F = gridArea((x, y) => lg(real(i.F), x, y), -2.2, 2.2, 0, 2.2, 1400, 700), cR = i.curve[i.curve.length - 1], g1R = gridArea((x, y) => lg(real([-i.R, -cR[0], cR[0], i.R]), x, y), -2.2, 2.2, 0, 2.2, 1400, 700);
check('R = 1.2: one piece; the area of F equals the grid count (relative 3e-3)', i.partsF.length === 1 && rel(i.areaF, 2 * g1F.area) < 3e-3 && !g1F.edge, `${i.areaF} vs ${2 * g1F.area}`);
check('…the curve ends at c = R (two double roots) with about 0.46 of Fekete’s area, confirmed by the grid count', Math.abs(cR[0] - i.R) < 1e-12 && rel(cR[1], 2 * g1R.area) < 3e-3 && Math.abs(cR[1] / i.areaF - 0.46) < 0.01 && i.curve.every(([c, a], k) => k === 0 || a <= i.curve[k - 1][1] + 1e-9 || c < i.u));
check('…the readout note says the pieces have merged', /连在一起/.test(await D(() => document.getElementById('roNote').textContent)));
await slide('rr', 0.5); i = await info();
check('moving the R slider leaves the presets and recomputes F, the curve and the Fekete roots R/√5', (await state()).preset === null && Math.abs(i.R - 0.8 * Math.sqrt(25)) < 1e-9 && Math.abs(i.u - i.R / Math.sqrt(5)) < 1e-12 && /自定义/.test(await text('presetNote')));

/* ---------- capacity one ---------- */
await preset('decay'); i = await info();
check('the decay preset: K = disc ∪ {4}, k from 2 to 8 with N = k² + 1 and n = N + k', i.mode === 'decay' && i.k === 2 && i.ks.length === 7 && i.ks.every((d, j) => d.k === j + 2 && d.N === d.k * d.k + 1 && d.n === d.N + d.k));
check('…every bound is 20π·2⁻ᵏ (Lean), and n·bound decreases', i.ks.every((d) => rel(d.bound, 20 * Math.PI * 2 ** -d.k) < 1e-12) && i.ks.every((d, j) => j === 0 || d.n * d.bound < i.ks[j - 1].n * i.ks[j - 1].bound));
check('…the page’s areas equal the disc formula with its second-order term (relative 1e-3), lie far below the bound and make n·area decrease', i.ks.every((d) => rel(d.area, decayDisc(d.N, d.k)) < 1e-3 && d.area < d.bound / 1000) && i.ks.every((d, j) => j === 0 || d.n * d.area < i.ks[j - 1].n * i.ks[j - 1].area), i.ks.map((d) => (d.area / decayDisc(d.N, d.k)).toFixed(5)).join(' '));
const k2roots = decayRoots(5, 2).concat([[4, 0], [4, 0]]), k2f = (x, y) => lg(k2roots, x, y); let k2grid = 0, k2edge = false;
for (const [x, y] of decayRoots(5, 2)) { const r = 3 / (5 * ((x - 4) ** 2 + y * y)), g = gridArea(k2f, x - r, x + r, y - r, y + r, 500, 500); k2grid += g.area; k2edge = k2edge || g.edge; }
const g4 = gridArea(k2f, 3.9, 4.1, -0.1, 0.1, 500, 500);
check('…k = 2, N = 5: the page’s area equals a grid count over the five petals and the disc at 4 (relative 3e-3)', rel(i.ks[0].area, k2grid + g4.area) < 3e-3 && !k2edge && !g4.edge, `${i.ks[0].area} vs ${k2grid + g4.area}`);
check('…the readouts state the Lean bound and the frozen verdict', /冻结定理/.test(await text('ro5')) && (await text('ro3')).length > 0);
await preset('petals'); i = await info();
const band = 2 ** -3, petal = i.parts.slice(0, i.N), worst = Math.max(...petal.map((p) => Math.max(...p.radii.map((r, j) => { const t = 2 * Math.PI * (j + 0.5) / p.radii.length; return Math.abs(Math.hypot(p.cx + r * Math.cos(t), p.cy + r * Math.sin(t)) - 1); })))), disc4 = i.parts[i.N] ? Math.max(...i.parts[i.N].radii) : Infinity;
check('N = 10, k = 3 (N ≥ k(k − 2) + 1): every petal stays in the annulus 1 ± 2⁻³ and the piece at 4 in the disc of radius 2⁻⁽ᵏ⁻²⁾ (the Lean containment)', i.k === 3 && i.N === 10 && petal.length === 10 && worst < band && disc4 < 2 ** -(3 - 2), `max | |z| − 1 | = ${worst}`);
const pa = petal.map((p) => p.area);
check('…the petal at z = 1 (nearest 4) is the largest and the one at z = −1 the smallest, each about π/(N|ω − 4|ᵏ)²', pa.indexOf(Math.max(...pa)) === 0 && pa.indexOf(Math.min(...pa)) === 5 && petal.every((p) => rel(p.area, Math.PI / (i.N * i.N * Math.pow((p.cx - 4) ** 2 + p.cy ** 2, 3))) < 2e-3));
await preset('far'); i = await info();
check('k = 8, N = 65: the piece at 4 has radius about 4^(−65/8) ≈ 1.3e-5', i.k === 8 && i.N === 65 && !!i.parts[i.N] && rel(Math.max(...i.parts[i.N].radii), Math.pow(4 ** 65 - 1, -1 / 8)) < 1e-3 && /1\.3 × 10⁻⁵/.test(await text('presetNote')));
await preset('rate');
check('the rate preset plots n·Aₙ on log–log axes', /n·Aₙ/.test(await text('c1Title')) && /1\/n/.test(await text('c1Meta')));
await slide('nn', 30); i = await info();
check('moving the N slider fixes N = 30 for every k and marks the result as page numerics only', i.ks.every((d) => d.N === 30 && d.n === 30 + d.k && rel(d.area, decayDisc(30, d.k)) < 1e-3) && /只有页面数值/.test(await text('ro5')) && (await state()).Nauto === false);

/* ---------- timeline and keys ---------- */
await preset('decay'); await setFrac(0.95); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing the decay mode to the end raises the k = 8 toast', await waitToast(/k = 8/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
check('the rail marks k = 2 … 8', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' '))) === 'k=2 k=3 k=4 k=5 k=6 k=7 k=8');
await setFrac(0); await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps k by one', (await info()).k === 3);
await page.keyboard.press('e'); await settle();
check('E jumps to k = 8 and pauses', (await info()).k === 8 && (await state()).playing === false);
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Capacity|Disc/i.test(document.getElementById('hudBig').textContent) || /disc/.test(document.getElementById('hudBig').textContent), null, { timeout: 30000 }).catch(() => {}); await waitFrames(3);
for (const p of ['witness', 'one', 'decay', 'petals']) {
  await preset(p); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
check('English title', (await D(() => document.title)).startsWith('LEMNISCATE//AREA · Erdős’s minimal area problem'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links both dossiers, both Lean files and the four sources', (await D(() => { const h = [...document.querySelectorAll('#drawer .en a')].map((a) => a.href).join(' '); return ['ghosh-ramachandran-2026-fekete-lemniscate-area.md', 'ghosh-ramachandran-2026-capacity-one-decay-rate.md', 'FeketeLemniscateAreaRefutation.lean', 'CapacityOneAreaDecayRate.lean', '10.1090/proc/17897', 'arxiv.org/abs/2604.03036', '10.1007/BF02790232', 'arxiv.org/abs/2606.17097'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="lemniscate-area"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.LE_DEBUG && LE_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'lemniscate-area');

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
