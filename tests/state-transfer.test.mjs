#!/usr/bin/env node
// Browser regression suite for viz/state-transfer (Playwright + Chromium with software WebGL).
//   node tests/state-transfer.test.mjs
// Reads page state through the read-only window.ST_DEBUG probe and checks it against an independent implementation: Hamiltonians
// rebuilt from their definitions, the propagator by a scaling-and-squaring Taylor series (no diagonalization), closed-form
// eigenvectors of the uniform chain, sin⁴(t/√2) for the 3-site chain, exact BigInt powers for zero transfer, and Kay's sums R_k
// recomputed exactly from the spectrum.
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
  const start = await page.evaluate(() => ST_DEBUG.frames());
  await page.waitForFunction((f0) => !ST_DEBUG.pending() && ST_DEBUG.frames() >= f0 + 2, start, { timeout: 60000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => ST_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => ST_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => ST_DEBUG.info());
const state = () => D(() => ST_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => ST_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => ST_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 60000 }); return true; } catch { return false; }
};

// --- independent implementation: complex matrices as {n, re, im}; exp(−iHt) by scaling and squaring of a Taylor series
const zeros = (n) => ({ n, re: new Float64Array(n * n), im: new Float64Array(n * n) });
function mul(A, B) { const n = A.n, R = zeros(n); for (let i = 0; i < n; i++) for (let k = 0; k < n; k++) { const ar = A.re[i * n + k], ai = A.im[i * n + k]; if (!ar && !ai) continue; for (let j = 0; j < n; j++) { R.re[i * n + j] += ar * B.re[k * n + j] - ai * B.im[k * n + j]; R.im[i * n + j] += ar * B.im[k * n + j] + ai * B.re[k * n + j]; } } return R; }
function expmI(H, t) {                          // exp(−i t H)
  const n = H.n; let nrm = 0; for (let i = 0; i < n; i++) { let s = 0; for (let j = 0; j < n; j++) s += Math.hypot(H.re[i * n + j], H.im[i * n + j]); nrm = Math.max(nrm, s); }
  let sq = 0; while (nrm * Math.abs(t) / 2 ** sq > 0.25) sq++;
  const h = t / 2 ** sq, A = zeros(n); for (let k = 0; k < n * n; k++) { A.re[k] = h * H.im[k]; A.im[k] = -h * H.re[k]; }      // A = −i h H
  let R = zeros(n), term = zeros(n); for (let i = 0; i < n; i++) { R.re[i * n + i] = 1; term.re[i * n + i] = 1; }
  for (let k = 1; k <= 24; k++) { term = mul(term, A); for (let q = 0; q < n * n; q++) { term.re[q] /= k; term.im[q] /= k; R.re[q] += term.re[q]; R.im[q] += term.im[q]; } }
  for (let s = 0; s < sq; s++) R = mul(R, R);
  return R;
}
const prob = (U, v, a) => U.re[v * U.n + a] ** 2 + U.im[v * U.n + a] ** 2;
function chainH(w, pot) { const n = w.length + 1, H = zeros(n); w.forEach((x, i) => { H.re[i * n + i + 1] = x; H.re[(i + 1) * n + i] = x; }); if (pot) pot.forEach((x, i) => { H.re[i * n + i] = x; }); return H; }
const krawW = (N) => Array.from({ length: N - 1 }, (_, i) => 0.5 * Math.sqrt((i + 1) * (N - 1 - i)));
const sameH = (pageH, H, tol = 1e-12) => pageH.re.every((x, k) => Math.abs(x - H.re[k]) < tol) && pageH.im.every((x, k) => Math.abs(x - H.im[k]) < tol);
const KAY = [0, 31, 46, 65, 88, 107, 122, 153];

await page.goto(origin + BASE + 'viz/state-transfer/');
await page.waitForFunction(() => window.ST_DEBUG && ST_DEBUG.frames() > 2, null, { timeout: 60000 });
await settle();

// --- the Krawtchouk chain
check('opens on the Krawtchouk preset and plays', (await state()).preset === 'kraw9' && (await state()).playing === true);
await pause(); await setFrac(0.37);
let i = await info(), H = chainH(krawW(9));
check('Krawtchouk N = 9: the page Hamiltonian has couplings ½√(n(N − n))', i.n === 9 && sameH(i.H, H));
let U = expmI(H, Math.PI);
check('Krawtchouk N = 9: the independent propagator gives F(π) = 1, and so does the page', Math.abs(prob(U, 8, 0) - 1) < 1e-10 && Math.abs(i.fPi - 1) < 1e-10 && Math.abs(i.maxF - 1) < 1e-9 && Math.abs(i.tMax - Math.PI) < 1e-4, `${prob(U, 8, 0)}`);
U = expmI(H, i.t);
check('the amplitudes now match the independent propagator on every vertex', i.psi.re.every((x, v) => Math.hypot(x - U.re[v * 9], i.psi.im[v] - U.im[v * 9]) < 1e-9));
check('total probability stays 1 (unitarity)', Math.abs(i.psi.re.reduce((s, x, v) => s + x * x + i.psi.im[v] ** 2, 0) - 1) < 1e-12);
let curveOK = true; for (const k of [0, 111, 350, 512, 700]) if (Math.abs(i.curve[k] - prob(expmI(H, i.ts[k]), 8, 0)) > 1e-9) curveOK = false;
check('the F(t) curve matches the independent propagator at sampled times', curveOK);
check('the spectrum is evenly spaced −4, …, 4', i.lam.every((x, k) => Math.abs(x - (k - 4)) < 1e-9));

// --- uniform chains
await preset('uniform3'); i = await info();
check('uniform P3: F(t) = sin⁴(t/√2), so F(π) = sin⁴(π/√2) and the first maximum is at t = π/√2', Math.abs(i.fPi - Math.sin(Math.PI / Math.SQRT2) ** 4) < 1e-12 && Math.abs(i.tMax - Math.PI / Math.SQRT2) < 1e-5 && i.maxF > 1 - 1e-9, `t ${i.tMax.toFixed(6)}`);
await preset('uniform6'); i = await info();
const N6 = 6, closed = (t) => { let r = 0, m = 0; for (let k = 1; k <= N6; k++) { const lam = 2 * Math.cos(k * Math.PI / (N6 + 1)), w = (2 / (N6 + 1)) * Math.sin(k * Math.PI / (N6 + 1)) * Math.sin(N6 * k * Math.PI / (N6 + 1)); r += w * Math.cos(lam * t); m -= w * Math.sin(lam * t); } return r * r + m * m; };
let mx = 0; for (let t = 0; t <= 200; t += 0.01) mx = Math.max(mx, closed(t));
check('uniform P6: the largest F for t < 200 from closed-form eigenvectors matches the page and stays below 0.99', Math.abs(mx - i.longMax) < 1e-9 && i.longMax < 0.99 && i.maxF < 0.99, mx.toFixed(9));

// --- rational weights at t = π
await preset('rational5'); i = await info();
check('rational chain q = 8: the weights are Krawtchouk rounded to eighths, 1, 5/4, 5/4, 1', i.weights.join(',') === '1,5/4,5/4,1' && sameH(i.H, chainH([1, 1.25, 1.25, 1])));
const fq8 = prob(expmI(chainH([1, 1.25, 1.25, 1]), Math.PI), 4, 0);
check('rational chain q = 8: F(π) from the independent propagator equals the page value and is below 1', Math.abs(fq8 - i.fPi) < 1e-10 && fq8 < 1 - 1e-4, fq8.toFixed(10));
let qOK = true, minGap = 1;
for (let q = 1; q <= 48; q++) { const w = krawW(5).map((x) => Math.max(1, Math.round(x * q)) / q), g = 1 - prob(expmI(chainH(w), Math.PI), 4, 0); minGap = Math.min(minGap, g); if (Math.abs(g - i.qCurve[q - 1]) > 1e-9) qOK = false; }
check('for every q ≤ 48 the gap 1 − F(π) matches the independent value and stays positive (frozen theorem: no rational PST at π)', qOK && minGap > 1e-11 && i.qCurve.every((g) => g > 1e-11), `smallest gap ${minGap.toExponential(2)}`);
await setRange('qq', 40); i = await info();
check('q = 40: F(π) is 1.2 × 10⁻⁷ short and the readout shows the gap instead of rounding to 1', Math.abs(1 - i.fPi - 1.204e-7) < 2e-10 && /1 − 1\.20e-7/.test(await text('roPi')), await text('roPi'));
await setRange('qq', 48); i = await info();
check('q = 48 brings F(π) closer to 1 than q = 8, but not to 1', i.fPi > fq8 && i.fPi < 1 - 1e-6 && /48/.test(await text('oQ')));
await setRange('nN', 6); i = await info();
check('the size slider keeps the rational chain odd (6 becomes 7)', i.n === 7 && (await state()).N === 7);

// --- Kay's counterexample
await preset('kay8'); i = await info();
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const Rk = [0, 1, 2, 3].map(() => [0n, 1n]);
KAY.forEach((x, n) => { let B = 1n; KAY.forEach((y, j) => { if (j !== n) B *= BigInt(x - y); }); const k = (x - KAY[0]) % 4, sg = (n + 1) % 2 === 0 ? 1n : -1n, [p, q] = Rk[k]; let num = p * B + sg * q, den = q * B; const g = gcd(num, den); num /= g; den /= g; if (den < 0n) { num = -num; den = -den; } Rk[k] = [num, den]; });
const Rs = Rk.map(([a, b]) => `${a}/${b}`);
check('Kay: the four sums R_k recomputed exactly all equal 194/38984495395755, as on the page', Rs.every((r) => r === '194/38984495395755') && i.kayR.join() === Rs.join() && /194\/38984495395755/.test(await text('ro6')));
const kayH = { n: 8, re: Float64Array.from(i.H.re), im: Float64Array.from(i.H.im) };
let mirror = true; for (let k = 0; k < 7; k++) if (Math.abs(kayH.re[k * 8 + k + 1] - kayH.re[(6 - k) * 8 + 7 - k]) > 1e-9) mirror = false;
check('Kay chain: the rebuilt chain is mirror-symmetric with spectrum λ − 76.5', mirror && i.lam.every((x, k) => Math.abs(x - (KAY[k] - 76.5)) < 1e-7));
check('Kay chain: the independent propagator confirms perfect transfer at t = π', Math.abs(prob(expmI(kayH, Math.PI), 7, 0) - 1) < 1e-8);

// --- the cube
await preset('cube'); i = await info();
const Q3 = zeros(8); for (let a = 0; a < 8; a++) for (let b = 0; b < 3; b++) Q3.re[a * 8 + (a ^ (1 << b))] = 1;
check('cube: H is the adjacency matrix of Q₃ and F(π/2) = 1 to the opposite corner', sameH(i.H, Q3) && Math.abs(prob(expmI(Q3, Math.PI / 2), 7, 0) - 1) < 1e-10 && Math.abs(i.tMax - Math.PI / 2) < 1e-5);

// --- zero transfer on G(Z₃₀, {5, 6, 9, 20})
await preset('zero30'); i = await info();
const Z = zeros(30), Sint = Array.from({ length: 30 }, () => new Array(30).fill(0n));
for (let a = 0; a < 30; a++) for (const c of [5, 6, 9, 20]) { const b = (a + c) % 30; Z.im[a * 30 + b] = 1; Z.im[b * 30 + a] = -1; Sint[a][b] = 1n; Sint[b][a] = -1n; }
check('Z₃₀: H has i on every arc a → a + c, c ∈ {5, 6, 9, 20}, and −i in reverse', sameH(i.H, Z));
let row = new Array(30).fill(0n); row[0] = 1n; const reached = new Array(30).fill(false); reached[0] = true;
for (let k = 1; k < 30; k++) { const nx = new Array(30).fill(0n); for (let a = 0; a < 30; a++) if (row[a]) for (let b = 0; b < 30; b++) if (Sint[a][b]) nx[b] += row[a] * Sint[a][b]; row = nx; row.forEach((x, b) => { if (x) reached[b] = true; }); }
const zeroSet = reached.map((x, b) => (x ? -1 : b)).filter((b) => b >= 0);
check('Z₃₀: the exact zero-transfer set (BigInt powers of S, Cayley–Hamilton) equals the page’s and contains the even vertex 2', i.zeroSet.join() === zeroSet.join() && zeroSet.includes(2), zeroSet.join(','));
check('Z₃₀: it contains even vertices besides 2 as well', zeroSet.filter((v) => v % 2 === 0 && v !== 2).length >= 1, zeroSet.filter((v) => v % 2 === 0).join(','));
let zmax = 0; for (const t of [0.7, 3.3, 7.9, 11.2]) { const Ut = expmI(Z, t); zmax = Math.max(zmax, prob(Ut, 2, 0), prob(Ut, 0, 2)); }
check('Z₃₀: the independent propagator gives |U(t)₂,₀|² = |U(t)₀,₂|² = 0 at sampled times', zmax < 1e-24 && i.maxF < 1e-24 && i.reach[2] < 1e-24, zmax.toExponential(1));
check('Z₃₀: the readouts call it exact zero transfer and a counterexample (2 is even)', /零传输/.test(await text('roNote')) && /Song–Lin/.test(await text('roNote')) && /全程为零/.test(await text('roMax')));
await setRange('target', 3); i = await info();
check('Z₃₀: vertex 3 (not in the set) does receive amplitude', i.maxF > 0.01 && !i.zeroSet.includes(3));

// --- the unit-phase triangle
await preset('universal3'); i = await info();
const al = [-4 * Math.sqrt(3) / 7, 1 / 7], TT = zeros(3); for (let j = 0; j < 3; j++) { TT.re[j * 3 + (j + 1) % 3] = al[0]; TT.im[j * 3 + (j + 1) % 3] = al[1]; TT.re[j * 3 + (j + 2) % 3] = al[0]; TT.im[j * 3 + (j + 2) % 3] = -al[1]; }
check('triangle: H = Circ(0, α, ᾱ) with α = (−4√3 + i)/7 of modulus 1 (property 𝕋)', sameH(i.H, TT) && Math.abs(Math.hypot(...al) - 1) < 1e-15);
const [t1, t2] = i.firstPST;
check('triangle: at the page’s first transfer times the independent propagator gives F = 1 for 0 → 1 and 0 → 2', prob(expmI(TT, t1), 1, 0) > 1 - 1e-10 && prob(expmI(TT, t2), 2, 0) > 1 - 1e-10 && Math.abs(t2 - 8.4637) < 2e-3 && Math.abs(t1 - 16.928) < 2e-3, `${t1.toFixed(4)} · ${t2.toFixed(4)}`);
await click('#graphChips [data-graph="triI"]'); i = await info();
const TI = zeros(3); for (let j = 0; j < 3; j++) { TI.im[j * 3 + (j + 1) % 3] = -1; TI.im[j * 3 + (j + 2) % 3] = 1; }
check('oriented triangle Circ(0, −i, i): transfer to 2 at its first time, confirmed independently', sameH(i.H, TI) && prob(expmI(TI, i.firstPST[1]), 2, 0) > 1 - 1e-10 && i.zeroSet.length === 0);

// --- controls, keys, presets
for (const name of ['uniform3', 'uniform6', 'kraw9', 'rational5', 'kay8', 'cube', 'zero30', 'universal3']) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await preset('kraw9');
await page.keyboard.press('p'); await settle();
check('P jumps to t = π', Math.abs((await info()).t - Math.PI) < 1e-9 && (await state()).playing === false);
await setFrac(0.1); await page.keyboard.press('m'); await settle();
check('M jumps to the maximum', Math.abs((await info()).t - (await info()).tMax) < 1e-9);
await page.keyboard.press('ArrowRight'); await settle(); i = await info();
check('→ nudges time forward by a 200th of the window', Math.abs(i.t - (i.tMax + i.span / 200)) < 1e-9);
check('the size slider is shown for chains and hidden for the cube', await visible('nField'));
await click('#graphChips [data-graph="cube"]');
check('…and hidden for the cube; changing the graph marks the settings custom', !(await visible('nField')) && (await state()).preset === null && /自定义/.test(await text('presetNote')) && (await info()).b === 7);
check('the rail marks the window in multiples of π', /π/.test(await D(() => document.getElementById('marks').textContent)));

// --- play and toasts
await preset('kraw9'); await setFrac(0.47); await click('#play');
check('the toast reports perfect transfer at t = π', await waitToast(/完美传输/));
await pause();
await preset('rational5'); await setFrac(0.47); await click('#play');
check('the rational chain toasts the shortfall at t = π', await waitToast(/到不了 1/));
await pause();
await preset('zero30'); await setFrac(0.99); await click('#play');
check('the zero-transfer toast appears at the end of the window', await waitToast(/零传输/));
await pause();
await setFrac(0.3); await click('#play'); await waitFrames(12); const g1 = (await state()).nowFrac; await pause();
check('play advances time', g1 > 0.3);
await click('#rev'); await waitFrames(12); const g2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', g2 < g1);
await page.click('#rev'); await pause();
await page.focus('#target'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await preset('rational5'); await setRange('qq', 12);
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /TARGET/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('STATE//TRANSFER · Perfect state transfer'));
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
await page.click('.card:has(a[href*="state-transfer"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'state-transfer');

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
