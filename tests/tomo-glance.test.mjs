#!/usr/bin/env node
// Browser regression suite for viz/tomo-glance (Playwright + Chromium with software WebGL).
//   node tests/tomo-glance.test.mjs
// Reads page state through the read-only window.TOMO_DEBUG probe and checks it against an independent implementation:
// 2×2 complex density matrices and Pauli projectors, Born probabilities, the Hilbert–Schmidt residual outside the visible span,
// least-squares estimates rebuilt from the page's own samples, trace distances from eigenvalues, and a Monte Carlo check of the
// expected error curve.
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
  const start = await page.evaluate(() => TOMO_DEBUG.frames());
  await page.waitForFunction((f0) => !TOMO_DEBUG.pending() && TOMO_DEBUG.frames() >= f0 + 2, start, { timeout: 20000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => TOMO_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => TOMO_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => TOMO_DEBUG.info());
const state = () => D(() => TOMO_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => TOMO_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => TOMO_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 30000 }); return true; } catch { return false; }
};
const toastOn = async () => (await D(() => document.getElementById('toast').style.opacity)) === '1';

// --- independent implementation: 2×2 complex matrices as [[a, b], [c, d]] of [re, im]
const c = (re, im = 0) => [re, im];
const cadd = (a, b) => [a[0] + b[0], a[1] + b[1]];
const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const mm = (A, B) => [0, 1].map((i) => [0, 1].map((j) => cadd(cmul(A[i][0], B[0][j]), cmul(A[i][1], B[1][j]))));
const madd = (A, B, s = 1) => A.map((row, i) => row.map((x, j) => [x[0] + s * B[i][j][0], x[1] + s * B[i][j][1]]));
const msc = (A, s) => A.map((row) => row.map((x) => [x[0] * s, x[1] * s]));
const tr = (A) => cadd(A[0][0], A[1][1]);
const I2 = [[c(1), c(0)], [c(0), c(1)]], SX = [[c(0), c(1)], [c(1), c(0)]], SY = [[c(0), c(0, -1)], [c(0, 1), c(0)]], SZ = [[c(1), c(0)], [c(0), c(-1)]];
const ndotsigma = (n) => madd(madd(msc(SX, n[0]), msc(SY, n[1])), msc(SZ, n[2]));
const rhoOf = (r) => msc(madd(I2, ndotsigma(r)), 0.5);
const born = (rho, n, sgn) => tr(mm(rho, msc(madd(I2, ndotsigma(n), sgn), 0.5)))[0];
const hs = (A, B) => tr(mm(A.map((row, i) => row.map((_, j) => [A[j][i][0], -A[j][i][1]])), B))[0];   // Tr(A†B), real part
const eig2 = (A) => { const a = A[0][0][0], d = A[1][1][0], b = A[0][1], m = (a + d) / 2, q = Math.sqrt(((a - d) / 2) ** 2 + b[0] ** 2 + b[1] ** 2); return [m + q, m - q]; };
const traceDist = (A, B) => eig2(madd(A, B, -1)).reduce((s, l) => s + Math.abs(l), 0) / 2;
const DEG = Math.PI / 180;
const blochFrom = (th, ph, R) => [R * Math.sin(th * DEG) * Math.cos(ph * DEG), R * Math.sin(th * DEG) * Math.sin(ph * DEG), R * Math.cos(th * DEG)];
const axis = (k, tilt) => ({ Z: [0, 0, 1], X: [1, 0, 0], Y: [0, 1, 0], T: [Math.sin(tilt * DEG), 0, Math.cos(tilt * DEG)] })[k];
// the residual: Hilbert–Schmidt mass of ρ − I/2 outside span{n·σ} (Gram–Schmidt in operator space)
function residualHS(rho, normals) {
  const X = madd(rho, msc(I2, 0.5), -1), basis = [];
  for (const n of normals) { let O = ndotsigma(n); for (const E of basis) O = madd(O, msc(E, hs(E, O)), -1); const l = Math.sqrt(hs(O, O)); if (l > 1e-9) basis.push(msc(O, 1 / l)); }
  let V = X; for (const E of basis) V = madd(V, msc(E, hs(E, X)), -1);
  return hs(V, V);
}
const entropy = (rho) => eig2(rho).reduce((s, l) => s - (l > 1e-15 ? l * Math.log(l) : 0), 0);
const h2 = (p) => (p <= 0 || p >= 1 ? 0 : -p * Math.log(p) - (1 - p) * Math.log(1 - p));
// least squares over the measured directions: normal equations in 3D with a pseudo-inverse restricted to their span
function lsEstimate(normals, m) {
  const G = [0, 1, 2].map((i) => [0, 1, 2].map((j) => normals.reduce((s, n) => s + n[i] * n[j], 0)));
  const b = [0, 1, 2].map((i) => normals.reduce((s, n, l) => s + n[i] * m[l], 0));
  // eigen-decomposition of the symmetric 3×3 G by Jacobi rotations
  const A = G.map((r) => r.slice()), V = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
  for (let sweep = 0; sweep < 50; sweep++) for (let p = 0; p < 3; p++) for (let q = p + 1; q < 3; q++) {
    if (Math.abs(A[p][q]) < 1e-15) continue;
    const th = (A[q][q] - A[p][p]) / (2 * A[p][q]), t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), cs = 1 / Math.sqrt(t * t + 1), sn = t * cs;
    for (let k = 0; k < 3; k++) { const a1 = A[k][p], a2 = A[k][q]; A[k][p] = cs * a1 - sn * a2; A[k][q] = sn * a1 + cs * a2; }
    for (let k = 0; k < 3; k++) { const a1 = A[p][k], a2 = A[q][k]; A[p][k] = cs * a1 - sn * a2; A[q][k] = sn * a1 + cs * a2; }
    for (let k = 0; k < 3; k++) { const v1 = V[k][p], v2 = V[k][q]; V[k][p] = cs * v1 - sn * v2; V[k][q] = sn * v1 + cs * v2; }
  }
  const x = [0, 0, 0];
  for (let e = 0; e < 3; e++) { if (A[e][e] < 1e-9) continue; const coef = [0, 1, 2].reduce((s, i) => s + V[i][e] * b[i], 0) / A[e][e]; for (let i = 0; i < 3; i++) x[i] += coef * V[i][e]; }
  return x;
}
function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }

const P = {
  onlyZ: { ctx: ['Z'], th: 90, ph: 0, R: 1 }, phase: { ctx: ['Z'], th: 90, ph: 0, R: 1 }, two: { ctx: ['Z', 'X'], th: 60, ph: 50, R: 1 },
  full: { ctx: ['Z', 'X', 'Y'], th: 60, ph: 50, R: 1 }, tilted: { ctx: ['Z', 'T'], th: 60, ph: 50, R: 1, tilt: 45 }, mixed: { ctx: ['Z', 'X', 'Y'], th: 60, ph: 50, R: 0.5 },
  single: { ctx: ['Z', 'X', 'Y'], th: 60, ph: 50, R: 1 }, clone: { ctx: ['Z', 'X', 'Y'], th: 60, ph: 50, R: 1 }
};

await page.goto(origin + BASE + 'viz/tomo-glance/');
await page.waitForTimeout(700);
check('no toast pops up at load', !(await toastOn()));
check('page loads without script errors', errors.length === 0, errors.join(' | '));
await pause();

// --- the physics against the independent implementation, preset by preset
for (const [name, q] of Object.entries(P)) {
  await preset(name);
  if (name !== 'single') await setFrac(1);
  const i = await info(), r = blochFrom(q.th, q.ph, q.R), rho = rhoOf(r), normals = q.ctx.map((k) => axis(k, q.tilt || 45));
  const purity = tr(mm(rho, rho))[0];
  const squares = normals.reduce((s, n) => s + [1, -1].reduce((t, sg) => t + (born(rho, n, sg) - 0.5) ** 2, 0), 0);
  const res = residualHS(rho, normals);
  const ortho = normals.every((a, x) => normals.every((b, y) => x === y || Math.abs(a[0] * b[0] + a[1] * b[1] + a[2] * b[2]) < 1e-9));
  check(`${name}: purity, the squared deviations and the Hilbert–Schmidt residual match`, Math.abs(i.purity - purity) < 1e-12 && Math.abs(i.visSum - squares) < 1e-12 && Math.abs(i.residual - res) < 1e-12 && i.orthogonal === ortho,
    `Tr ρ² ${purity.toFixed(4)}, Σ ${squares.toFixed(4)}, R ${res.toFixed(4)}`);
  if (ortho) check(`${name}: Pythagoras holds for the page’s own readings — Tr ρ² − ½ = Σ(p − ½)² + R`, Math.abs(i.purity - 0.5 - i.visSum - i.residual) < 1e-12 && Math.abs(purity - 0.5 - squares - res) < 1e-12);
  else check(`${name}: without complementarity the squares overcount the visible part`, squares > (purity - 0.5 - res) + 0.05 && Math.abs(i.visProj - (purity - 0.5 - res)) < 1e-12, `squares ${squares.toFixed(3)} vs visible ${(purity - 0.5 - res).toFixed(3)}`);
  // samples: round robin over the directions, outcome +1 when u < (1 + r·n)/2; the estimate and its error rebuilt from them
  let samplesOK = true;
  for (let k = 0; k < i.ctxOf.length; k++) { const l = i.ctxOf[k], n = normals[l]; if (l !== k % normals.length || i.out[k] !== (i.u[k] < born(rho, n, 1) ? 1 : -1)) { samplesOK = false; break; } }
  const N = i.N, plus = new Array(normals.length).fill(0), cnt = new Array(normals.length).fill(0);
  for (let k = 0; k < N; k++) { cnt[i.ctxOf[k]]++; if (i.out[k] > 0) plus[i.ctxOf[k]]++; }
  const have = normals.filter((_, l) => cnt[l] > 0), mvals = normals.map((_, l) => (cnt[l] ? (2 * plus[l] - cnt[l]) / cnt[l] : null)).filter((x) => x !== null);
  const est = lsEstimate(have, mvals), estErr = Math.hypot(...est.map((v, x) => v - i.est[x]));
  const dist = traceDist(rhoOf(i.est), rho);
  check(`${name}: samples follow the Born rule; the least-squares estimate and its trace distance agree`, samplesOK && estErr < 1e-9 && Math.abs(dist - i.err) < 1e-9, `N ${N}, |Δr̂| ${estErr.toExponential(1)}, D ${dist.toFixed(4)}`);
  check(`${name}: collision sum over X, Y, Z equals 1 + Tr ρ²`, Math.abs(i.collisionTrue - (1 + purity)) < 1e-12 && Math.abs(['X', 'Y', 'Z'].reduce((s, k) => s + [1, -1].reduce((t, sg) => t + born(rho, axis(k), sg) ** 2, 0), 0) - (1 + purity)) < 1e-12);
  const S = entropy(rho), HZ = h2(born(rho, [0, 0, 1], 1)), HX = h2(born(rho, [1, 0, 0], 1));
  check(`${name}: H(Z) + H(X) ≥ ln 2 + S(ρ), with the page’s entropies`, Math.abs(i.H.Z - HZ) < 1e-12 && Math.abs(i.H.X - HX) < 1e-12 && Math.abs(i.H.S - S) < 1e-12 && HZ + HX >= Math.LN2 + S - 1e-12, `${(HZ + HX).toFixed(3)} ≥ ${(Math.LN2 + S).toFixed(3)}`);
}

// --- Theorem 83.1: states differing by a residual direction give identical statistics; the page’s consistent set is that set
await preset('two');
{
  const i = await info(), r = i.r, perp = i.rPerp, v = [0, 1, 0];      // the missing direction for Z and X
  const s1 = [r[0], r[1] - 0.6 * Math.sign(r[1]), r[2]];
  const same = ['Z', 'X'].every((k) => Math.abs(born(rhoOf(r), axis(k), 1) - born(rhoOf(s1), axis(k), 1)) < 1e-12);
  check('Theorem 83.1: moving along the invisible direction leaves every measured probability unchanged', same && Math.abs(perp[0]) < 1e-12 && Math.abs(perp[2]) < 1e-12 && Math.abs(perp[1] - r[1]) < 1e-12 && v[1] === 1);
  check('the estimated Bloch vector shows ? for the direction never measured', /\?/.test(await text('roEst')) && (await text('roEst')).split(',').length === 3);
}

// --- the expected error curve against an independent Monte Carlo
await preset('full');
{
  const i = await info(), r = i.r, normals = ['Z', 'X', 'Y'].map((k) => axis(k)), rng = mulberry32(12345);
  let sum = 0; const runs = 3000, Nt = 300;
  for (let t = 0; t < runs; t++) {
    const plus = [0, 0, 0], cnt = [0, 0, 0];
    for (let k = 0; k < Nt; k++) { const l = k % 3, pp = (1 + r[0] * normals[l][0] + r[1] * normals[l][1] + r[2] * normals[l][2]) / 2; cnt[l]++; if (rng() < pp) plus[l]++; }
    const est = [0, 1, 2].map((l) => (2 * plus[l] - cnt[l]) / cnt[l]);   // x, y, z order is Z, X, Y here
    const e = [est[1], est[2], est[0]]; sum += ((e[0] - r[0]) ** 2 + (e[1] - r[1]) ** 2 + (e[2] - r[2]) ** 2) / 4;
  }
  const rms = Math.sqrt(sum / runs);
  check('expected rms error at N = 300 matches a 3000-run Monte Carlo', Math.abs(i.expct[Nt] - rms) / rms < 0.05, `page ${i.expct[Nt].toFixed(4)}, MC ${rms.toFixed(4)}`);
}
await preset('two');
{
  const i = await info(), floor = Math.hypot(...i.rPerp) / 2;
  check('with a direction missing the expected error tends to the blind floor, not to zero', i.expct[600] > floor && i.expct[600] - floor < 0.01 && i.errAll[600] > floor * 0.9, `floor ${floor.toFixed(3)}, expected ${i.expct[600].toFixed(3)}`);
}

// --- phase blindness and the twin
await preset('phase');
let i = await info();
check('phase preset: |+⟩ and Z|+⟩Z = |−⟩ have identical Z statistics', i.twinDiff < 1e-12 && Math.abs(born(rhoOf(i.r), [0, 0, 1], 1) - born(rhoOf(i.zr), [0, 0, 1], 1)) < 1e-12 && (await text('ro6')) === '0.000');
await click('[data-ctx="X"]');
i = await info();
check('adding X tells them apart completely (|Δp| = 1)', Math.abs(i.twinDiff - 1) < 1e-12 && (await state()).preset === null);

// --- presets and their notes
await preset('mixed'); i = await info();
check('mixed preset: Tr ρ² = 0.625, squares 0.125, collision 1.625', Math.abs(i.purity - 0.625) < 1e-12 && Math.abs(i.visSum - 0.125) < 1e-12 && Math.abs(i.collisionTrue - 1.625) < 1e-12 && /1\.625/.test(await text('presetNote')));
await preset('tilted'); i = await info();
check('tilted preset: the meta line flags the double counting', /≠/.test(await text('pyMeta')) && /0\.404/.test(await text('pyMeta')));
await preset('full'); i = await info();
check('full preset: no blind residual, three visible dimensions', i.residual < 1e-12 && /3\/3/.test(await text('pillVis')));
await preset('single'); i = await info();
check('one-shot preset: one sample, paused, and → adds one more', i.N === 1 && (await state()).playing === false && /100\.1/.test(await text('presetNote')));
await page.keyboard.press('ArrowRight'); await settle();
check('→ steps exactly one sample', (await info()).N === 2);
await page.keyboard.press('ArrowLeft'); await settle();
check('← steps back one sample', (await info()).N === 1);

// --- the copying machine
await preset('clone');
let note = await text('cloneNote');
check('clone preset: at Θ = 60° the overlap 0.866 ≠ c² = 0.750, so no machine copies both', /0\.866/.test(note) && /0\.750/.test(note) && Math.abs(Math.cos(30 * DEG) - 0.866) < 1e-3);
await setRange('cloneAngle', 0); note = await text('cloneNote');
const at0 = /c = 1\.000 = c²/.test(note) || /c = 1\.000 = c²/.test(note);
await setRange('cloneAngle', 180); note = await text('cloneNote');
check('only identical (Θ = 0) or orthogonal (Θ = 180°) pairs pass c = c²', at0 && /c = 0\.000 = c²/.test(note));
let gapOK = true; for (let a = 1; a < 180; a++) { const cc = Math.cos(a * DEG / 2); if (Math.abs(cc - cc * cc) < 1e-9) gapOK = false; }
check('independently: c ≠ c² for every angle strictly between', gapOK);

// --- controls
await preset('onlyZ');
await click('[data-ctx="Z"]');
check('the last measured direction cannot be switched off', (await state()).ctx.Z === true && (await toastOn()));
await click('[data-ctx="T"]');
check('the tilt slider appears with the tilted direction', (await D(() => document.getElementById('tiltField').hidden)) === false);
await setRange('tilt', 0); i = await info();
check('a tilt of 0° coincides with Z and adds no new visible dimension', i.basis.length === 1);
await click('[data-ctx="T"]');
check('changing a control marks the settings as custom', (await state()).preset === null && /自定义/.test(await text('presetNote')));
await preset('full');
const showBefore = (await state()).showTrue; await page.keyboard.press('h'); await settle();
check('H hides and shows the true state', showBefore === true && (await state()).showTrue === false);
await page.keyboard.press('h'); await settle();
const h0 = (await info()).hash, o0 = (await info()).out.join(''); await page.keyboard.press('r'); await settle();
check('R draws a new batch of samples', (await info()).hash !== h0 && (await info()).out.join('') !== o0);
for (const name of Object.keys(P)) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }

// --- rail, play, toasts
await preset('full'); await setFrac(0.97); await click('#play');
check('the toast reports a complete reconstruction when the samples run out', await waitToast(/看全了/));
await pause();
await preset('two'); await setFrac(0.97); await click('#play');
check('…and the blind floor when a direction is missing', await waitToast(/再测也没用/));
await pause();
await setFrac(0.3); await click('#play'); await waitFrames(12); const f1 = (await state()).nowFrac; await pause();
check('play advances the samples', f1 > 0.3);
await click('#rev'); await waitFrames(12); const f2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', f2 < f1);
await page.click('#rev'); await pause();
await page.focus('#theta'); await page.keyboard.press('Space'); await page.waitForTimeout(150);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await setRange('theta', 75);
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /TRUE ρ/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('TOMO//GLANCE · Complementarity and tomography'));
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
await page.click('.card:has(a[href*="tomo-glance"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'tomo-glance');

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
