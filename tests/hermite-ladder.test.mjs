#!/usr/bin/env node
// Browser regression suite for viz/hermite-ladder (Playwright + Chromium with software WebGL).
//   node tests/hermite-ladder.test.mjs
// Reads page state through the read-only window.OSC_DEBUG probe and checks it against an independent implementation:
// Hermite functions from the physicists' polynomial recurrence H_{n+1} = 2xH_n − 2nH_{n−1} with the normalization √(2^n n! √π),
// closed-form coherent and cat wave functions ψ_a(x) = π^{-1/4}exp(−x²/2 + √2ax − a²/2 − |a|²/2), Gauss–Legendre coefficients of
// the target shapes, Poisson moments, and the closed-form 2D densities of the Lissajous and vortex states.
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
  const start = await page.evaluate(() => OSC_DEBUG.frames());
  await page.waitForFunction((f0) => !OSC_DEBUG.pending() && OSC_DEBUG.frames() >= f0 + 2, start, { timeout: 20000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => OSC_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => OSC_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => OSC_DEBUG.info());
const state = () => D(() => OSC_DEBUG.state());
const psiAt = (t) => D((t) => OSC_DEBUG.psi(t), t);
const dens2At = (t) => D((t) => OSC_DEBUG.density2(t), t);
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => OSC_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => OSC_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 30000 }); return true; } catch { return false; }
};

// --- independent implementation
const lnFact = (n) => { let s = 0; for (let k = 2; k <= n; k++) s += Math.log(k); return s; };
function phi(n, x) {                                   // physicists' Hermite polynomial, normalized
  let h0 = 1, h1 = 2 * x;
  if (n === 0) return Math.exp(-x * x / 2) / Math.PI ** 0.25;
  for (let k = 1; k < n; k++) { const h2 = 2 * x * h1 - 2 * k * h0; h0 = h1; h1 = h2; }
  return h1 * Math.exp(-x * x / 2 - 0.5 * (n * Math.LN2 + lnFact(n) + 0.5 * Math.log(Math.PI)));
}
const cx = { add: (a, b) => [a[0] + b[0], a[1] + b[1]], mul: (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]], exp: (a) => [Math.exp(a[0]) * Math.cos(a[1]), Math.exp(a[0]) * Math.sin(a[1])], sc: (a, s) => [a[0] * s, a[1] * s] };
// ψ_a(x) = π^{-1/4} exp(−x²/2 + √2·a·x − a²/2 − |a|²/2) for a complex a; under H the state |α⟩ becomes e^{−it/2}|αe^{−it}⟩
function coherentPsi(alpha, t, x) {
  const a = [alpha * Math.cos(t), -alpha * Math.sin(t)], a2 = cx.mul(a, a);
  const e = [-x * x / 2 + Math.SQRT2 * a[0] * x - a2[0] / 2 - alpha * alpha / 2, Math.SQRT2 * a[1] * x - a2[1] / 2 - t / 2];
  return cx.sc(cx.exp(e), Math.PI ** -0.25);
}
const catPsi = (alpha, t, x) => cx.sc(cx.add(coherentPsi(alpha, t, x), coherentPsi(-alpha, t, x)), 1 / Math.sqrt(2 * (1 + Math.exp(-2 * alpha * alpha))));
const maxDiffPsi = (P, f, xs) => { let m = 0; for (let i = 0; i < xs.length; i++) { const z = f(xs[i]); m = Math.max(m, Math.hypot(P.re[i] - z[0], P.im[i] - z[1])); } return m; };
const GX = [-0.906179845938664, -0.5384693101056831, 0, 0.5384693101056831, 0.906179845938664], GW = [0.2369268850561891, 0.4786286704993665, 0.5688888888888889, 0.4786286704993665, 0.2369268850561891];
const gl = (f, a, b, m = 600) => { let s = 0; const h = (b - a) / m; for (let k = 0; k < m; k++) { const c = a + (k + 0.5) * h; for (let j = 0; j < 5; j++) s += GW[j] * f(c + GX[j] * h / 2) * h / 2; } return s; };
const SHAPES = {
  box: { pieces: [[-1, 2, () => 1]], norm: Math.sqrt(3) },
  tri: { pieces: [[-2, 0, (x) => 1 + x / 2], [0, 2, (x) => 1 - x / 2]], norm: Math.sqrt(4 / 3) },
  hump: { pieces: [[-12, 12, (x) => Math.exp(-((x - 2) ** 2)) + Math.exp(-((x + 2) ** 2))]], norm: Math.sqrt(2 * Math.sqrt(Math.PI / 2) * (1 + Math.exp(-8))) }
};
const shapeCoef = (k, n) => SHAPES[k].pieces.reduce((s, [a, b, g]) => s + gl((x) => g(x) * phi(n, x), a, b, k === 'hump' ? 2400 : 600), 0) / SHAPES[k].norm;
const G2 = 72, X2 = 5.5, grid2 = (i) => -X2 + 2 * X2 * i / (G2 - 1);

await page.goto(origin + BASE + 'viz/hermite-ladder/');
await page.waitForFunction(() => window.OSC_DEBUG && OSC_DEBUG.frames() > 2, null, { timeout: 30000 });
await settle();

// --- the energy ladder and Hermite functions
check('opens on the coherent preset and plays', (await state()).preset === 'coherent' && (await state()).playing === true);
let i = await info();
check('numerical orthonormality defect of the first 40 Hermite functions is below 1e-12', i.orth < 1e-12, i.orth.toExponential(2));
await preset('ground'); i = await info();
let P = await psiAt(0.9);
check('ground state: E = ½ and ψ(x, t) = Φ₀(x)e^{−it/2}', Math.abs(i.meanE - 0.5) < 1e-12 && maxDiffPsi(P, (x) => cx.sc([Math.cos(-0.45), Math.sin(-0.45)], phi(0, x)), i.xd) < 1e-12);
await preset('excited'); i = await info();
P = await psiAt(1.7);
const ex = maxDiffPsi(P, (x) => cx.sc([Math.cos(-4.5 * 1.7), Math.sin(-4.5 * 1.7)], phi(4, x)), i.xd);
check('fourth excited state: E = 4.5 and ψ = Φ₄e^{−i4.5t} against the physicists’ recurrence', Math.abs(i.meanE - 4.5) < 1e-12 && ex < 1e-12, ex.toExponential(2));
let nodes = 0; const P0 = await psiAt(0); for (let k = 1; k < P0.re.length; k++) if (P0.re[k - 1] * P0.re[k] < 0) nodes++;
check('Φ₄ has exactly 4 nodes', nodes === 4, String(nodes));
const d0 = await psiAt(0), d1 = await psiAt(2.3); let still = 0; for (let k = 0; k < d0.re.length; k++) still = Math.max(still, Math.abs(d0.re[k] ** 2 + d0.im[k] ** 2 - d1.re[k] ** 2 - d1.im[k] ** 2));
check('an eigenstate’s density does not move', still < 1e-12);
await setRange('nq', 9); i = await info();
P = await psiAt(0.4);
check('the n slider selects Φ₉ with E = 9.5', Math.abs(i.meanE - 9.5) < 1e-12 && maxDiffPsi(P, (x) => cx.sc([Math.cos(-9.5 * 0.4), Math.sin(-9.5 * 0.4)], phi(9, x)), i.xd) < 1e-11 && /9\.5/.test(await text('srcNote')));

// --- coherent and cat states against closed forms
await preset('coherent'); i = await info();
let coefOK = true; for (let n = 0; n < 60; n++) { const c = Math.exp(-2 - lnFact(n) / 2 + n * Math.log(2)); if (Math.abs(i.full[n] - c) > 1e-14) coefOK = false; }
check('coherent |α| = 2: c_n = e^{−|α|²/2}α^n/√n!', coefOK);
check('coherent: ⟨E⟩ = |α|² + ½ = 4.5 and Σ E_n²|c_n|² = λ² + 2λ + ¼ = 24.25', Math.abs(i.meanE - 4.5) < 1e-12 && Math.abs(i.ESum[i.ESum.length - 1] - 24.25) < 1e-9);
let worst = 0, worstX = 0;
for (const t of [0, 0.7, 2.2, Math.PI, 5.1]) {
  P = await psiAt(t); worst = Math.max(worst, maxDiffPsi(P, (x) => coherentPsi(2, t, x), i.xd));
  await setFrac(t / i.span); worstX = Math.max(worstX, Math.abs((await info()).meanX - 2 * Math.SQRT2 * Math.cos(t)));
}
check('coherent: ψ(x, t) matches the closed form e^{−it/2}ψ_{αe^{−it}}(x)', worst < 1e-12, worst.toExponential(2));
check('coherent: ⟨x⟩ follows the classical path √2|α|cos t', worstX < 1e-10, worstX.toExponential(2));
await setFrac(0.25); i = await info();
check('the readout shows ⟨x⟩ at the current time', /-2\.828/.test(await text('ro6')) && Math.abs(i.t - Math.PI) < 1e-12);
P = await psiAt(2 * Math.PI); const Q = await psiAt(0);
let rev = 0; for (let k = 0; k < P.re.length; k++) rev = Math.max(rev, Math.hypot(P.re[k] + Q.re[k], P.im[k] + Q.im[k]));
check('after one period every coefficient gains the same phase e^{−iπ}: ψ(T) = −ψ(0)', rev < 1e-12 && i.revivalErr < 1e-12 && Math.abs(i.period - 2 * Math.PI) < 1e-15);
check('the revival period readout is 2π/ω₁', /6\.283/.test(await text('roT')));
await preset('cat'); i = await info();
check('cat |α| = 2.5: only even levels, ⟨E⟩ = α²tanh(α²) + ½', i.full.every((v, n) => n % 2 === 0 || v === 0) && Math.abs(i.meanE - (6.25 * Math.tanh(6.25) + 0.5)) < 1e-9);
worst = 0; for (const t of [0, Math.PI / 2, 1.1]) { P = await psiAt(t); worst = Math.max(worst, maxDiffPsi(P, (x) => catPsi(2.5, t, x), i.xd)); }
check('cat: ψ(x, t) matches (ψ_α + ψ_{−α})/√(2(1 + e^{−2|α|²}))', worst < 1e-10, worst.toExponential(2));
P = await psiAt(Math.PI / 2); let minima = 0; const dc = P.re.map((r, k) => r * r + P.im[k] ** 2);
for (let k = 1; k + 1 < dc.length; k++) if (dc[k] < dc[k - 1] && dc[k] <= dc[k + 1] && Math.abs(i.xd[k]) < 2) minima++;
check('cat: when the packets meet at t = π/2 the density shows fringes', minima >= 3, `${minima} minima in |x| < 2`);

// --- buildable shapes and the domain of H
await preset('box'); i = await info();
let cmax = 0; const cInd = []; for (let n = 0; n < 80; n++) { cInd.push(shapeCoef('box', n)); cmax = Math.max(cmax, Math.abs(i.full[n] - cInd[n])); }
check('box: page coefficients match Gauss–Legendre integrals to 1e-4', cmax < 1e-4, cmax.toExponential(2));
const tail20 = 1 - cInd.slice(0, 20).reduce((s, v) => s + v * v, 0);
check('box: the error of the first 20 terms equals Σ_{n≥20}|c_n|² (Parseval)', Math.abs(i.errN - tail20) < 2e-4 && Math.abs(i.tail[20] - i.errN) < 1e-15, `${i.errN.toFixed(5)} vs ${tail20.toFixed(5)}`);
const ES = (c, N) => c.slice(0, N).reduce((s, v, n) => s + ((n + 0.5) * v) ** 2, 0);
const relE = [40, 80].map((N) => Math.abs(i.ESum[N] - ES(cInd, N)) / ES(cInd, N));
check('box: the energy-weighted sums at N = 40 and 80 agree with the independent coefficients to 0.3%', relE.every((r) => r < 3e-3), relE.map((r) => r.toExponential(2)).join(' · '));
const rBox = i.ESum[80] / i.ESum[40];
check('box: Σ E²|c|² keeps growing like N^{3/2} (ratio 80 vs 40 near 2^{3/2})', rBox > 2.5 && rBox < 3.3 && i.inDomain === false, rBox.toFixed(3));
check('box: the readout and pill say H cannot act', /发散/.test(await text('roDom')) && /OUT/.test(await text('pillDom')));
await setRange('terms', 60); i = await info();
check('more terms leave a smaller error (completeness)', i.errN < tail20 && Math.abs(i.errN - (1 - cInd.slice(0, 60).reduce((s, v) => s + v * v, 0))) < 2e-4);
await click('[data-tgt="tri"]'); i = await info();
cmax = 0; const tInd = []; for (let n = 0; n < 80; n++) { tInd.push(shapeCoef('tri', n)); cmax = Math.max(cmax, Math.abs(i.full[n] - tInd[n])); }
const rTri = i.ESum[80] / i.ESum[40];
check('triangle: coefficients match to 1e-4, and Σ E²|c|² grows like N^{1/2}', cmax < 1e-4 && rTri > 1.2 && rTri < 1.6 && i.inDomain === false, `${cmax.toExponential(2)} · ratio ${rTri.toFixed(3)}`);
await preset('smooth'); i = await info();
cmax = 0; for (let n = 0; n < 40; n++) cmax = Math.max(cmax, Math.abs(i.full[n] - shapeCoef('hump', n)));
check('double hump: coefficients match, the error of 20 terms is below 1e-9, and the weighted sum converges', cmax < 1e-6 && i.errN < 1e-9 && i.inDomain === true && Math.abs(i.ESum[80] - i.ESum[40]) / i.ESum[80] < 1e-9, `${cmax.toExponential(2)} · err ${i.errN.toExponential(2)}`);
check('double hump: the readout and pill say H acts', /收敛/.test(await text('roDom')) && /IN/.test(await text('pillDom')));
await click('[data-tgt="gauss"]'); i = await info();
const a15 = 1.5 / Math.SQRT2; let gOK = true;                // a shifted ground-state Gaussian is a coherent state with α = 1.5/√2
for (let n = 0; n < 30; n++) if (Math.abs(i.full[n] - Math.exp(-a15 * a15 / 2 - lnFact(n) / 2 + n * Math.log(a15))) > 1e-6) gOK = false;
check('shifted Gaussian = coherent state with α = 1.5/√2: its coefficients are Poisson amplitudes', gOK && i.inDomain === true);

// --- two dimensions
await preset('lissajous'); i = await info();
check('Lissajous preset: ratio 3/2, ⟨E⟩ = (|α|² + ½)(1 + ω₂) = 11.25, period 4π', i.dim === 2 && i.rat[0] === 3 && i.rat[1] === 2 && Math.abs(i.meanE - 11.25) < 1e-9 && Math.abs(i.period - 4 * Math.PI) < 1e-12);
check('the period readout is 2π·2/ω₁ and the ratio controls are shown', /2π·2\/ω₁ = 12\.566/.test(await text('roT')) && (await visible('ratioField')) && !(await visible('srcChips1')));
const lissDens = (t, x, y) => { const w = 1.5, xc = 2 * Math.SQRT2 * Math.cos(t), yc = 2 * Math.SQRT2 * Math.sin(w * t) / Math.sqrt(w); return Math.exp(-((x - xc) ** 2)) / Math.sqrt(Math.PI) * Math.sqrt(w) * Math.exp(-w * (y - yc) ** 2) / Math.sqrt(Math.PI); };
worst = 0; let wc = 0;
for (const t of [0, 1.3, 2 * Math.PI + 0.4]) {
  const dd = await dens2At(t); for (let j = 0; j < G2; j++) for (let k = 0; k < G2; k++) worst = Math.max(worst, Math.abs(dd[j * G2 + k] - lissDens(t, grid2(k), grid2(j))));
  await setFrac(t / i.span); const c = (await info()).centre; wc = Math.max(wc, Math.hypot(c[0] - 2 * Math.SQRT2 * Math.cos(t), c[1] - 2 * Math.SQRT2 * Math.sin(1.5 * t) / Math.sqrt(1.5)));
}
check('Lissajous: the 2D density matches the product of two displaced Gaussians', worst < 1e-10, worst.toExponential(2));
check('Lissajous: the centre (a sum over the 72×72 grid, tails beyond ±5.5 cut) follows (√2α cos t, √2α sin(ω₂t)/√ω₂)', wc < 2e-3, wc.toExponential(2));
const r0 = await dens2At(0), rT = await dens2At(4 * Math.PI), rh = await dens2At(Math.PI);
let dT = 0, dh = 0; for (let k = 0; k < r0.length; k++) { dT = Math.max(dT, Math.abs(r0[k] - rT[k])); dh = Math.max(dh, Math.abs(r0[k] - rh[k])); }
check('Lissajous: the density returns exactly after 4π and not at π', dT < 1e-12 && dh > 0.05 && i.revivalErr < 1e-12);
await click('#ratioChips [data-ratio="1.4142135623730951"]'); i = await info();
check('ratio √2: no fraction with q ≤ 8 matches, so no exact revival', i.rat === null && i.period === Infinity && i.revivalErr === null && /∞/.test(await text('roT')) && /无理数/.test(await text('roNote')));
await setRange('ratio', 2.5); i = await info();
check('a slider ratio of 2.5 is recognized as 5/2 with period 4π', i.rat && i.rat[0] === 5 && i.rat[1] === 2 && Math.abs(i.period - 4 * Math.PI) < 1e-12);
await preset('vortex'); i = await info();
const vort = (x, y) => (x * x + y * y) * Math.exp(-(x * x + y * y)) / Math.PI;
const v0 = await dens2At(0), v1 = await dens2At(2.7); worst = 0; let vs = 0;
for (let j = 0; j < G2; j++) for (let k = 0; k < G2; k++) { worst = Math.max(worst, Math.abs(v0[j * G2 + k] - vort(grid2(k), grid2(j)))); vs = Math.max(vs, Math.abs(v0[j * G2 + k] - v1[j * G2 + k])); }
check('vortex: density (x² + y²)e^{−(x² + y²)}/π, still in time, ⟨E⟩ = 2', worst < 1e-12 && vs < 1e-12 && Math.abs(i.meanE - 2) < 1e-12, `${worst.toExponential(2)} · ${vs.toExponential(2)}`);
check('vortex: the centre sits at the origin', Math.hypot(...i.centre) < 1e-9);
await click('[data-src="eig2"]'); await setRange('nq', 4); await setRange('nq2', 1); i = await info();
check('2D eigenstate (4, 1) at ω₂ = 1: E = 4.5 + 1.5 and the density is still', Math.abs(i.meanE - 6) < 1e-12 && (await visible('n2Field')) && i.revivalErr < 1e-12);

// --- the dimension switch and the displacement limit in 2D
await preset('coherent'); await setRange('alpha', 3.5);
await click('[data-dim="2"]'); await click('[data-src="coh2"]');
check('switching to 2D caps |α| at 2.5 so the shells n₁ + n₂ < 40 hold the state', (await state()).alpha === 2.5 && (await D(() => document.getElementById('alpha').max)) === '2.5' && Math.abs((await info()).norm - 1) < 1e-8);
await click('[data-dim="1"]');
check('back in 1D the slider allows 3.5 again', (await D(() => document.getElementById('alpha').max)) === '3.5' && (await visible('srcChips1')) && !(await visible('ratioField')));

// --- presets and notes
const PRE = ['ground', 'excited', 'coherent', 'cat', 'box', 'smooth', 'lissajous', 'vortex'];
for (const name of PRE) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await setRange('ratio', 1.25);
check('changing a control marks the settings as custom', (await state()).preset === null && /自定义/.test(await text('presetNote')));

// --- keys, rail, play, toast
await preset('box');
await page.keyboard.press('+'); await settle();
check('+ adds one term', (await state()).terms === 21);
await page.keyboard.press('-'); await page.keyboard.press('-'); await settle();
check('− removes terms', (await state()).terms === 19);
await preset('coherent'); await setFrac(0);
await page.keyboard.press('ArrowRight'); await settle();
check('→ steps an eighth of a period', Math.abs((await info()).t - Math.PI / 4) < 1e-12);
await page.keyboard.press('ArrowLeft'); await settle();
check('← steps back', Math.abs((await info()).t) < 1e-12);
check('the rail marks 0, 1T and 2T', (await D(() => [...document.querySelectorAll('#marks i')].map(m => m.textContent).join(' '))) === '0 1T 2T');
await setFrac(0.47); await click('#play');
check('the toast reports the exact revival after one period', await waitToast(/精确回归/));
await pause();
await setFrac(0.3); await click('#play'); await waitFrames(12); const f1 = (await state()).nowFrac; await pause();
check('play advances time', f1 > 0.3);
await click('#rev'); await waitFrames(12); const f2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', f2 < f1);
await page.click('#rev'); await pause();
await page.focus('#alpha'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await preset('box'); await setRange('terms', 25);
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
check('the domain verdict reads in English', /diverges/.test(await text('roDom')) && /model calculation/.test(await text('domNote')));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /TARGET/i.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('HERMITE//LADDER · The quantum oscillator'));
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
await page.click('.card:has(a[href*="hermite-ladder"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'hermite-ladder');

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
