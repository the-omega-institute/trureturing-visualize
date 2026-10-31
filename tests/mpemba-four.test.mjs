#!/usr/bin/env node
// Browser regression suite for viz/mpemba-four (Playwright + Chromium with software WebGL).
//   node tests/error-disturbance.test.mjs
// Reads page state through the read-only window.MF_DEBUG probe and checks it against an independent implementation: exact
// rational arithmetic (BigInt fractions) for the Lean instance — orthogonality, the 36 certificates by principal minors and the
// witness states — and, along the paths, quaternion rotations with eigenvalues from the closed-form cubic.
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
  const start = await page.evaluate(() => MF_DEBUG.frames());
  await page.waitForFunction((f0) => !MF_DEBUG.pending() && MF_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => MF_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D((t) => MF_DEBUG.setT(t), t); await settle(); };
const info = () => D(() => MF_DEBUG.info());
const state = () => D(() => MF_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => MF_DEBUG.frames()); await page.waitForFunction((t) => MF_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const Q = (n, d = 1n) => { n = BigInt(n); d = BigInt(d); if (d < 0n) { n = -n; d = -d; } const g = gcd(n, d) || 1n; return { n: n / g, d: d / g }; };
const add = (a, b) => Q(a.n * b.d + b.n * a.d, a.d * b.d), sub = (a, b) => Q(a.n * b.d - b.n * a.d, a.d * b.d), mul = (a, b) => Q(a.n * b.n, a.d * b.d), div = (a, b) => Q(a.n * b.d, a.d * b.n);
const sgn = (a) => (a.n > 0n ? 1 : a.n < 0n ? -1 : 0), bits = (x) => (x < 0n ? -x : x).toString(2).length;
/* a fraction to the nearest double, keeping relative precision for tiny values such as 16⁻⁶⁴ */
const num = (a) => { if (a.n === 0n) return 0; const k = bits(a.d) - bits(a.n) + 64; const v = k >= 0 ? (a.n << BigInt(k)) / a.d : a.n / (a.d << BigInt(-k)); return Number(v) * 2 ** -k; };
const Z = Q(0), ONE = Q(1);
/* the Lean witness: r = 16^−64, mean, rates, weights, g and f */
const R64 = Q(1n, 16n ** 64n);
const leanRates = (r) => {
  const mu = div(mul(Q(2), add(Q(125), mul(Q(1024), r))), mul(Q(15), add(Q(273), mul(Q(256), r))));
  const A = sub(sub(Q(47, 48), mu), div(mul(Q(112), r), Q(25))), B = sub(sub(Q(3, 2), mul(Q(3, 2), mu)), div(mul(Q(128), r), Q(25))), C = sub(Q(31, 20), mul(Q(15, 8), mu));
  return { mu, a: [[Z, A, B, C], [div(A, Q(16)), Z, ONE, Q(3, 5)], [div(B, Q(256)), Q(1, 16), Z, Q(1, 10)], [mul(C, r), mul(Q(48, 5), r), mul(Q(128, 5), r), Z]] };
};
const { mu: MU, a: AQ } = leanRates(R64);
const WQ = [ONE, Q(1, 16), Q(1, 256), R64], GQ = [Z, ONE, Q(2, 3), Q(8, 15)], FQ = GQ.map((g) => sub(g, MU));
const MQ = AQ.map((row, i) => row.map((v, j) => (i === j ? AQ.reduce((s, rr, k) => (k === j ? s : sub(s, rr[j])), Z) : v)));
/* the 2 × 2 block of the dossier (MarkovMpembaTripletRefutation.block), in floating point */
const blockEigs = (r) => { const den = 256 * r + 273, a = (-201261056 * r * r - 231756288 * r - 25704025) / (38400 * den), b = (458752 * r * r + 3703296 * r + 3359825) / (38400 * den), c = r * (146048 * r + 153329) / (150 * den), d = (-206464 * r * r - 285097 * r - 87450) / (150 * den), tr = a + d, det = a * d - b * c, disc = Math.sqrt(tr * tr - 4 * det); return [(tr + disc) / 2, (tr - disc) / 2]; };
/* floating point model for any n, written independently of the page */
const LN16 = Math.log(16);
function fmodel(n) {
  const r = 16 ** -n, mu = 2 * (125 + 1024 * r) / (15 * (273 + 256 * r)), A = 47 / 48 - mu - 112 * r / 25, B = 1.5 - 1.5 * mu - 128 * r / 25, C = 31 / 20 - 15 * mu / 8;
  const a = [[0, A, B, C], [A / 16, 0, 1, 0.6], [B / 256, 1 / 16, 0, 0.1], [C * r, 9.6 * r, 25.6 * r, 0]];
  const M = a.map((row, i) => row.map((v, j) => (i === j ? -(a[0][j] + a[1][j] + a[2][j] + a[3][j]) : v)));
  const lv = [0, 1, 2, n], f = [0, 1, 2 / 3, 8 / 15].map((g) => g - mu);
  const gibbs = (beta) => { const w = lv.map((l) => Math.exp(-beta * l * LN16)), s = w[0] + w[1] + w[2] + w[3]; return w.map((v) => v / s); };
  const b2 = (beta) => gibbs(beta).reduce((s, p, i) => s + f[i] * p, 0);
  return { r, mu, a, M, gibbs, b2 };
}
/* RK4 for dp/dt = M p, sampled every 0.05 */
function rk4(M, p0, T = 12, h = 0.002) {
  const f = (p) => M.map((row) => row.reduce((s, v, j) => s + v * p[j], 0)), out = [[0, p0.slice()]]; let p = p0.slice(), t = 0;
  const steps = Math.round(T / h);
  for (let s = 1; s <= steps; s++) { const k1 = f(p), k2 = f(p.map((v, i) => v + h / 2 * k1[i])), k3 = f(p.map((v, i) => v + h / 2 * k2[i])), k4 = f(p.map((v, i) => v + h * k3[i])); p = p.map((v, i) => v + h / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i])); t = s * h; if (s % 25 === 0) out.push([t, p.slice()]); }
  return out;
}
const near = (a, b, tol) => Math.abs(a - b) <= tol;
const B1 = Math.log(1024 / 1023) / LN16, B2 = Math.log(128 / 127) / LN16;

await page.goto(`${origin}${BASE}viz/mpemba-four/`);
await page.waitForFunction(() => window.MF_DEBUG && MF_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();

/* ---------- the Lean witness in exact arithmetic ---------- */
check('opens on Lean’s counterexample: n = 64, x = 1023/1024 and 127/128, t = 0, paused', st.preset === 'lean' && st.playing === false && i.n === 64 && near(i.beta1, B1, 1e-15) && near(i.beta2, B2, 1e-15) && i.t === 0);
check('the page’s rates for n = 64 match the exact Lean rates to 1e-12 relative, all positive', AQ.every((row, a) => row.every((v, b) => (a === b ? true : sgn(v) > 0 && near(i.a[a][b], num(v), 1e-12 * num(v))))));
check('exact detailed balance: a_ij w_j = a_ji w_i for all pairs, with weights (1, 1/16, 1/256, 16⁻⁶⁴)', [0, 1, 2, 3].every((a) => [0, 1, 2, 3].every((b) => sgn(sub(mul(AQ[a][b], WQ[b]), mul(AQ[b][a], WQ[a]))) === 0)));
const fM = [0, 1, 2, 3].map((j) => FQ.reduce((s, f, k) => add(s, mul(f, MQ[k][j])), Z)), Mw = [0, 1, 2, 3].map((k) => MQ[k].reduce((s, v, j) => add(s, mul(v, WQ[j])), Z)), colsum = [0, 1, 2, 3].map((j) => MQ.reduce((s, row) => add(s, row[j]), Z));
check('exact slow mode: fᵀM = −fᵀ, Mw = 0 and every column of M sums to 0; the page’s residual is below 1e-14', fM.every((v, j) => sgn(add(v, FQ[j])) === 0) && Mw.every((v) => sgn(v) === 0) && colsum.every((v) => sgn(v) === 0) && i.resid < 1e-14 && near(i.mu, num(MU), 1e-15));
const be = blockEigs(16 ** -64);
check('the eigenvalues are 0, −1 and the two eigenvalues of the dossier’s 2 × 2 block (≈ −2.1355, −2.4519), all below −2', near(i.eig[0], 0, 1e-12) && near(i.eig[1], -1, 1e-12) && near(i.eig[2], be[0], 1e-9) && near(i.eig[3], be[1], 1e-9) && be.every((x) => x < -2));
const xs = [0, 1, 2, 3], LV = [0, 1, 2, 64];
const exactMargins = [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]].map(([p, q, s]) => { const x = Q(1n, 16n ** BigInt(LV[q] - LV[p])), y = Q(1n, 16n ** BigInt(LV[s] - LV[q])); return { m1: sub(sub(mul(AQ[p][s], add(ONE, div(mul(x, y), Q(2)))), mul(AQ[q][s], add(ONE, div(y, Q(2))))), mul(AQ[p][q], sub(ONE, x))), m2: sub(mul(AQ[p][s], x), AQ[q][s]) }; });
check('exact triplet margins: in all four triplets both inequalities of (3) fail (both margins negative), and the page agrees', exactMargins.every((m) => sgn(m.m1) < 0 && sgn(m.m2) < 0) && i.margins.every((m, k) => near(m.m1, num(exactMargins[k].m1), 1e-12) && near(m.m2, num(exactMargins[k].m2), 1e-12)));
const overlap = (x) => { const w = LV.map((l) => { let v = ONE; for (let k = 0; k < l; k++) v = mul(v, x); return v; }), s = w.reduce(add, Z); return div(w.reduce((acc, v, k) => add(acc, mul(FQ[k], v)), Z), s); };
const oHot = overlap(Q(1023, 1024)), oWarm = overlap(Q(127, 128));
check('exact Gibbs overlaps: f·Π ≈ 0.4890371 at x = 1023/1024 and ≈ 0.4892979 at x = 127/128; the hotter one is strictly smaller', sgn(sub(oWarm, oHot)) > 0 && near(i.b2a, num(oHot), 1e-12) && near(i.b2b, num(oWarm), 1e-12) && near(num(oHot), 0.4890371, 5e-8) && near(num(oWarm), 0.4892979, 5e-8) && i.effect === true);

/* ---------- the relaxation, by RK4 ---------- */
const m64 = fmodel(64), pi64 = m64.gibbs(1), L1d = (p) => p.reduce((s, v, k) => s + Math.abs(v - pi64[k]), 0);
const run1 = rk4(m64.M, m64.gibbs(B1)), run2 = rk4(m64.M, m64.gibbs(B2));
let relOK = true; const relBad = [];
for (const t of [0, 1, 2.5, 4.3, 6, 9, 12]) {
  await setT(t / 12); const x = await info(), k = Math.round(t / 0.05), d1 = L1d(run1[k][1]), d2 = L1d(run2[k][1]);
  if (!near(x.D1, d1, 1e-9 * Math.max(1, d1)) || !near(x.D2, d2, 1e-9 * Math.max(1, d2)) || !x.q1.every((v, j) => near(v, run1[k][1][j], 1e-9))) { relOK = false; relBad.push(t); }
}
check('populations and L1 distances at t = 0, 1, 2.5, 4.3, 6, 9, 12 match RK4 integration', relOK, relBad.join(' '));
const Rk = run1.map((r, k) => L1d(r[1]) / L1d(run2[k][1]) - 1); let tc = null; for (let k = 0; k + 1 < Rk.length; k++) if (Rk[k] > 0 && Rk[k + 1] <= 0) { tc = run1[k][0] + 0.05 * Rk[k] / (Rk[k] - Rk[k + 1]); break; }
i = await info();
check('the distance curves cross once, at t ≈ 4.28 (RK4: same within 0.005); afterwards the hot start stays closer', tc !== null && near(i.cross, tc, 0.005) && near(tc, 4.28, 0.01) && Rk.slice(Math.ceil(tc / 0.05) + 1).every((v) => v < 0));
check('the ratio minus one starts near +3.8% and tends to b₂(β₁)/b₂(β₂) − 1 ≈ −0.053%', near(Rk[0], 0.0382, 0.0005) && near(Rk[Rk.length - 1], num(oHot) / num(oWarm) - 1, 2e-5) && near((await D(() => MF_DEBUG.ratio()))[0], Rk[0], 1e-9));

/* ---------- the hump against n ---------- */
let humpOK = true; const humpBad = [];
for (const n of [3, 20, 41, 42, 43, 64, 100, 120]) {
  const m = fmodel(n), Ls = []; for (let k = 0; k <= 4000; k++) Ls.push(-9 + 9 * k / 4000);
  const vals = Ls.map((L) => m.b2(10 ** L)); let km = 0; vals.forEach((v, k) => { if (v > vals[km]) km = k; });
  const interior = km > 0 && vals[km] > vals[0] + 1e-15, h = await D((n) => MF_DEBUG.hump(n), n);
  if (interior !== (h.betaStar !== null) || interior !== (n >= 42) || (interior && Math.abs(Math.log10(h.betaStar) - Ls[km]) > 0.01)) { humpOK = false; humpBad.push(n); }
}
check('an interior maximum of b₂ exists exactly for n ≥ 42 among n = 3, 20, 41, 42, 43, 64, 100, 120, at the page’s β*', humpOK, humpBad.join(' '));
let slopeOK = true;
for (const n of [10, 41, 42, 64, 100]) { const m = fmodel(n), h = 1e-7, sl = (m.b2(h) - m.b2(-h)) / (2 * h); if (!near(sl, LN16 * (n - 41) / 240, 2e-5)) slopeOK = false; }
check('the slope of b₂ at β = 0 equals ln 16·(n − 41)/240 by finite differences, for n = 10, 41, 42, 64, 100', slopeOK && near(i.slope0, LN16 * 23 / 240, 1e-12));
const h64 = await D(() => MF_DEBUG.hump(64));
check('for n = 64 the maximum is near β* ≈ 2.69·10⁻³ with b₂ ≈ 0.4892987', near(h64.betaStar, 2.69e-3, 0.02e-3) && near(h64.b2Star, 0.4892987, 5e-7));

/* ---------- presets ---------- */
await preset('hump'); i = await info();
check('hump preset: β₁ = 10⁻⁶ and β₂ = β*, a contrast of about 3.5·10⁻⁴ in b₂', i.n === 64 && near(i.beta1, 1e-6, 1e-12) && near(i.beta2, h64.betaStar, 1e-12) && near(i.b2b - i.b2a, 3.49e-4, 0.01e-4) && i.effect);
await preset('n41'); i = await info();
check('n41 preset: no hump and no effect between Lean’s two temperatures; the hot start stays farther all the way', i.n === 41 && i.betaStar === null && i.effect === false && i.cross === null && (await D(() => MF_DEBUG.ratio())).every((r) => r > 0));
await preset('n42'); i = await info();
check('n42 preset: β₂ = β* ≈ 2.1·10⁻⁴ with b₂(β*) − b₂(0) ≈ 1.2·10⁻⁶, and the effect', i.n === 42 && near(i.betaStar, 2.14e-4, 0.02e-4) && near(i.b2Star - i.b2Zero, 1.24e-6, 0.05e-6) && i.effect && /1\.2·10⁻⁶/.test(await text('presetNote')));
await preset('n100'); i = await info();
check('n100 preset: β* ≈ 3.5·10⁻³, a hump of about 1.1·10⁻³, and an earlier crossing', i.n === 100 && near(i.betaStar, 3.5e-3, 0.05e-3) && near(i.b2Star - i.b2Zero, 1.12e-3, 0.02e-3) && i.cross !== null && i.cross < 4.28);
for (const p of ['lean', 'race', 'hump', 'n41', 'n42', 'n100']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }

/* ---------- readouts, tags and controls ---------- */
await preset('lean'); i = await info();
check('the readouts give the eigenvalues, both b₂, the hump and the triplet margins, and say the effect is the Lean theorem', /-2\.1355/.test(await text('ro1')) && /0\.4890371 · 0\.4892979/.test(await text('ro2')) && /2\.69e-3/.test(await text('ro3')) && /\(123\) -0\.481\/-0\.912/.test(await text('ro5')) && /Lean 定理/.test(await text('roNote')));
const tagTxt = await D(() => [...document.querySelectorAll('#tags .tag')].filter((t) => t.style.display !== 'none').map((t) => t.textContent));
const pc = (x) => `${(100 * x).toFixed(1)}%`;
check('the 3D occupation labels show both columns’ populations (hot 23.9% on the top level at t = 0)', i.q1.every((v) => tagTxt.includes(pc(v))) && i.q2.every((v) => tagTxt.includes(pc(v))) && tagTxt.includes('23.9%'));
check('the rail marks t = 0, the crossing at 4.28 and t = 12', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 't = 0 | 交叉 4.28 | t = 12');
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ advances t by 0.5 and marks the settings custom', near((await info()).t, 0.5, 1e-9) && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await page.keyboard.press('e'); await settle();
check('E jumps to t = 12 and pauses', near((await info()).t, 12, 1e-9) && (await state()).playing === false);
await D(() => { const e = document.getElementById('nIn'); e.value = 80; e.dispatchEvent(new Event('input')); }); await settle();
check('the top-level slider sets n', (await info()).n === 80);
await D(() => { const e = document.getElementById('b1In'); e.value = -5; e.dispatchEvent(new Event('input')); const g = document.getElementById('b2In'); g.value = -2; g.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the two temperature sliders set β₁ = 10⁻⁵ and β₂ = 10⁻²', near(i.beta1, 1e-5, 1e-15) && near(i.beta2, 1e-2, 1e-14) && near(i.b2a, fmodel(80).b2(1e-5), 1e-12));
await preset('race'); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('running the race reports the crossing at t ≈ 4.28', await waitToast(/t ≈ 4\.28.*交叉/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await preset('lean');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'n100']) {
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
check('English title', (await D(() => document.title)).startsWith('MPEMBA//FOUR · Every triplet fails the test, yet four levels show the Mpemba effect'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and both arXiv papers', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['avitan-factor-gelbwaser-klimovsky-2026-mpemba-triplet-conjecture.md', 'D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.lean', 'Blueprint/D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.md', 'Library/StatisticalMechanics/avitanfactorgelbwaserklimovsky2026mpembatriplets.md', 'doi.org/10.48550/arXiv.2603.04567', 'arxiv.org/abs/2603.04567', 'arxiv.org/abs/2609.09988'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="mpemba-four"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.MF_DEBUG && MF_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'mpemba-four');

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
