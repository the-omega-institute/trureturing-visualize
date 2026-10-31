#!/usr/bin/env node
// Browser regression suite for viz/granular-two (Playwright + Chromium with software WebGL).
//   node tests/granular-two.test.mjs
// Reads page state through the read-only window.GR_DEBUG probe and checks it against independent sources: Lean's J, flux, rhs,
// p10, q10, X and Y transcribed and evaluated in the test's own exact rational arithmetic, the dossier's printed digits of Z,
// a finite-difference Jacobian, and the test's own classical RK4 integration (dt = 10⁻⁴) of every trajectory the page shows.
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
const D2 = (expr, arg) => page.evaluate(expr, arg);
const settle = async () => {
  const start = await page.evaluate(() => GR_DEBUG.frames());
  await page.waitForFunction((f0) => !GR_DEBUG.pending() && GR_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D2(() => GR_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D2((t) => GR_DEBUG.setT(t), t); await settle(); };
const info = () => D2(() => GR_DEBUG.info());
const state = () => D2(() => GR_DEBUG.state());
const text = (id) => D2((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D2(() => GR_DEBUG.frames()); await page.waitForFunction((t) => GR_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };


/* a seeded generator for sample states */
const mulberry = (a) => () => { a |= 0; a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };

/* ---------- Lean's definitions, transcribed, in the test's own exact arithmetic ---------- */
const C10 = 10, KS = [3, 4, 5, 6, 7, 8, 9, 10];
/* J C: the pairs of Icc 3 C ×ˢ Icc 3 C with i ≤ j and i + j − 2 ≤ C, in lexicographic order */
const J10 = []; for (let i = 3; i <= C10; i++) for (let j = 3; j <= C10; j++) if (i <= j && i + j - 2 <= C10) J10.push([i, j]);
const g = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const Q = (n, d = 1n) => { n = BigInt(n); d = BigInt(d); if (d < 0n) { n = -n; d = -d; } const c = g(n, d) || 1n; return [n / c, d / c]; };
const add = (a, b) => Q(a[0] * b[1] + b[0] * a[1], a[1] * b[1]), sub = (a, b) => Q(a[0] * b[1] - b[0] * a[1], a[1] * b[1]), mul = (a, b) => Q(a[0] * b[0], a[1] * b[1]);
const str = (a) => `${a[0] < 0n ? '−' : ''}${a[0] < 0n ? -a[0] : a[0]}${a[1] === 1n ? '' : '/' + a[1]}`;
const num = (a) => Number(a[0]) / Number(a[1]);
/* p10 and q10 as Lean writes them, keyed by (i, j) */
const P10 = { '3,3': [10, 3], '3,4': [2, 3], '3,5': [4, 15], '3,6': [4, 3], '3,7': [2, 3], '3,8': [2, 1], '3,9': [509018, 225], '4,4': [1, 1], '4,5': [35579, 175], '4,6': [2, 1], '4,7': [422, 5], '4,8': [2, 1], '5,5': [386, 225], '5,6': [30416, 25], '5,7': [255689, 25], '6,6': [4, 1] };
const Q10 = { '3,3': [1, 1], '3,4': [2, 5], '3,5': [2, 1], '3,6': [972, 5], '3,7': [2, 1], '3,8': [2, 1], '3,9': [2138, 75], '4,4': [141, 10], '4,5': [1, 1], '4,6': [2, 1], '4,7': [2, 1], '4,8': [3967, 35], '5,5': [35878, 315], '5,6': [2, 1], '5,7': [233557, 35], '6,6': [2, 1] };
const pE = (i, j) => Q(...P10[`${Math.min(i, j)},${Math.max(i, j)}`]), qE = (i, j) => Q(...Q10[`${Math.min(i, j)},${Math.max(i, j)}`]);
const XL = { 3: [3, 16], 4: [2, 16], 5: [5, 16], 6: [1, 16], 7: [2, 16], 8: [1, 16], 9: [1, 16], 10: [1, 16] };
const YL = { 3: [12, 34], 4: [6, 34], 5: [5, 34], 6: [4, 34], 7: [4, 34], 8: [1, 34], 9: [1, 34], 10: [1, 34] };
const asState = (o) => (k) => Q(...o[k]);
/* flux p q Q i j = p (min i j) (max i j) · Q i · Q j − q (min i j) (max i j) · Q (i + j − 2), and rhs C p q Q k */
const fluxL = (s, i, j) => sub(mul(mul(pE(i, j), s(i)), s(j)), mul(qE(i, j), s(i + j - 2)));
const dL = (i, j) => (i === j ? Q(1) : Q(0));
function rhsL(s, k) {
  let gain = Q(0), loss = Q(0), tot = Q(0);
  for (let i = 3; i <= k - 1; i++) gain = add(gain, mul(fluxL(s, i, k - i + 2), add(Q(1), dL(i, k - i + 2))));
  for (let i = k + 1; i <= C10; i++) loss = add(loss, mul(fluxL(s, k, i - k + 2), add(Q(1), dL(i, 2 * k - 2))));
  for (const [i, j] of J10) tot = add(tot, fluxL(s, i, j));
  gain = mul(Q(1, 2), gain); const norm = mul(s(k), tot);
  return { gain, loss, norm, rhs: add(sub(gain, loss), norm), tot };
}
/* the same right-hand side in floating point, literally; and the stoichiometric form used for fast integration */
const pF = (i, j) => num(pE(i, j)), qF = (i, j) => num(qE(i, j));
const PFL = J10.map(([i, j]) => pF(i, j)), QFL = J10.map(([i, j]) => qF(i, j));
function rhsF(x, k) { const s = (m) => x[m - 3], fl = (i, j) => pF(i, j) * s(i) * s(j) - qF(i, j) * s(i + j - 2); let gain = 0, loss = 0, tot = 0;
  for (let i = 3; i <= k - 1; i++) gain += fl(i, k - i + 2) * (1 + (i === k - i + 2 ? 1 : 0));
  for (let i = k + 1; i <= C10; i++) loss += fl(k, i - k + 2) * (1 + (i === 2 * k - 2 ? 1 : 0));
  for (const [i, j] of J10) tot += fl(i, j);
  return gain / 2 - loss + s(k) * tot; }
const rhsVec = (x) => KS.map((k) => rhsF(x, k));
function fast(x) { const out = new Array(8).fill(0); let tot = 0; for (let e = 0; e < 16; e++) { const [i, j] = J10[e], h = PFL[e] * x[i - 3] * x[j - 3] - QFL[e] * x[i + j - 5]; tot += h; out[i + j - 5] += h; out[i - 3] -= h; out[j - 3] -= h; } for (let a = 0; a < 8; a++) out[a] += x[a] * tot; return out; }
/* classical RK4 with dt = 10⁻⁴ up to t = 14 */
function rk4(x0, T = 14, dt = 1e-4) { let x = x0.slice(); const n = Math.round(T / dt); const ax = (u, k, c) => u.map((v, a) => v + c * k[a]);
  for (let s = 0; s < n; s++) { const k1 = fast(x), k2 = fast(ax(x, k1, dt / 2)), k3 = fast(ax(x, k2, dt / 2)), k4 = fast(ax(x, k3, dt)); x = x.map((v, a) => v + dt / 6 * (k1[a] + 2 * k2[a] + 2 * k3[a] + k4[a])); } return x; }
const dmax = (a, b) => Math.max(...a.map((v, q) => Math.abs(v - b[q])));
const XF = KS.map((k) => num(Q(...XL[k]))), YF = KS.map((k) => num(Q(...YL[k])));
/* the test's own Jacobian by central differences */
function fdJac(x, h = 1e-7) { const Jm = KS.map(() => new Array(8).fill(0)); for (let c = 0; c < 8; c++) { const a = x.slice(), b = x.slice(); a[c] += h; b[c] -= h; const fa = rhsVec(a), fb = rhsVec(b); for (let r = 0; r < 8; r++) Jm[r][c] = (fa[r] - fb[r]) / (2 * h); } return Jm; }
const ZDOS = [0.43995, 0.50554, 0.0050850, 0.044208, 0.0041825, 0.00048549, 0.00045463, 0.000099506];
const sig5 = (v) => Number(v.toPrecision(5));
const supT = (e) => String(e).replace(/-/g, '⁻').replace(/[0-9]/g, (d) => '⁰¹²³⁴⁵⁶⁷⁸⁹'[d]);
const sciT = (v) => { const e = Math.floor(Math.log10(Math.abs(v))), m = v / 10 ** e; return `${m.toFixed(1)}×10${supT(e)}`; };

await page.goto(`${origin}${BASE}viz/granular-two/`);
await page.waitForFunction(() => window.GR_DEBUG && GR_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();
check('starts on the first preset (Y − 10⁻³·v), playing from the start', st.preset === 'lean' && st.playing === true && st.mode === 'saddle' && st.side === -1 && st.lgEps === -3);
await pause();

/* ---------- the certificate against Lean ---------- */
const PROCp = await D2(() => GR_DEBUG.PROC), rates = await D2(() => GR_DEBUG.rates()), sts = await D2(() => GR_DEBUG.states());
check('the 16 processes are Lean’s J 10 (3 ≤ i ≤ j, i + j − 2 ≤ 10), in the dossier’s order', J10.length === 16 && JSON.stringify(PROCp) === JSON.stringify(J10.map(([a, b]) => [a, b, a + b - 2])));
check('the rates are Lean’s p10 and q10, all positive (PositiveRates)', JSON.stringify(rates.p) === JSON.stringify(J10.map(([a, b]) => str(pE(a, b)))) && JSON.stringify(rates.q) === JSON.stringify(J10.map(([a, b]) => str(qE(a, b)))) && J10.every(([a, b]) => pE(a, b)[0] > 0n && qE(a, b)[0] > 0n));
const sX = asState(XL), sY = asState(YL);
const phys = (s) => KS.every((k) => s(k)[0] > 0n) && str(KS.reduce((a, k) => add(a, s(k)), Q(0))) === '1';
check('the states are Lean’s X and Y, both physical (every Q_k > 0, Σ Q_k = 1)', JSON.stringify(sts.X) === JSON.stringify(KS.map((k) => str(sX(k)))) && JSON.stringify(sts.Y) === JSON.stringify(KS.map((k) => str(sY(k)))) && phys(sX) && phys(sY));
for (const [nm, s] of [['X', sX], ['Y', sY]]) {
  const pc = await D2((n) => GR_DEBUG.cert(n), nm), rows = KS.map((k) => rhsL(s, k));
  check(`Lean’s rhs at ${nm} vanishes in all 8 rows (the test’s exact arithmetic), and the page’s gain, loss, Q_k Σ η and fluxes agree`, rows.every((r) => str(r.rhs) === '0') && pc.rows.every((r, q) => r.gain === str(rows[q].gain) && r.loss === str(rows[q].loss) && r.norm === str(rows[q].norm) && r.rhs === '0') && JSON.stringify(pc.etas) === JSON.stringify(J10.map(([a, b]) => str(fluxL(s, a, b)))) && pc.sum === '1' && pc.positive);
}
const cX = await D2(() => GR_DEBUG.cert('X')), cY = await D2(() => GR_DEBUG.cert('Y'));
check('Σ η = 0 at both, with all 16 net fluxes nonzero (no detailed balance), and X₃ = 3/16 ≠ 6/17 = Y₃', str(rhsL(sX, 3).tot) === '0' && str(rhsL(sY, 3).tot) === '0' && cX.tot === '0' && cY.tot === '0' && J10.every(([a, b]) => fluxL(sX, a, b)[0] !== 0n && fluxL(sY, a, b)[0] !== 0n) && str(sX(3)) === '3/16' && str(sY(3)) === '6/17');
const th = (a, b) => Q(pE(a, b)[0] * qE(a, b)[1], pE(a, b)[1] * qE(a, b)[0]);
check('no detailed-balance state: θ₃₃θ₄₄ = 100/423 ≠ 2/9 = θ₃₄θ₃₅ (θ = p/q), as the page reports', str(mul(th(3, 3), th(4, 4))) === '100/423' && str(mul(th(3, 4), th(3, 5))) === '2/9' && JSON.stringify(await D2(() => GR_DEBUG.db())) === JSON.stringify({ left: '100/423', right: '2/9' }));

/* ---------- the dynamics ---------- */
const rnd = mulberry(7), samples = Array.from({ length: 20 }, () => { const v = KS.map(() => -Math.log(rnd())); const s = v.reduce((a, b) => a + b, 0); return v.map((c) => c / s); });
const pageF = await D2((xs) => xs.map((x) => GR_DEBUG.f(x)), samples);
check('the page’s Q̇ equals Lean’s rhs (literal sums, floating point) at 20 random states', samples.every((x, q) => { const r = rhsVec(x); return r.every((v, a) => Math.abs(v - pageF[q][a]) <= 1e-12 * (1 + Math.abs(v))); }));
check('the fast stoichiometric form used by the test’s integrator agrees with Lean’s rhs at the same states', samples.every((x) => { const r = rhsVec(x), s = fast(x); return r.every((v, a) => Math.abs(v - s[a]) <= 1e-12 * (1 + Math.abs(v))); }));
const Zp = sts.Z;
check('Z is a physical steady state (Lean’s rhs below 10⁻¹², Σ = 1, all positive) matching the dossier’s five digits', Math.max(...rhsVec(Zp).map(Math.abs)) < 1e-12 && Math.abs(Zp.reduce((a, b) => a + b, 0) - 1) < 1e-14 && Zp.every((v) => v > 0) && Zp.every((v, q) => sig5(v) === ZDOS[q]), Zp.map((v) => v.toPrecision(6)).join(' '));
const eig = await D2(() => GR_DEBUG.eig());
const eigOK = ['X', 'Y', 'Z'].every((nm) => { const x = nm === 'X' ? XF : nm === 'Y' ? YF : Zp, Jm = fdJac(x), { lam, v } = eig[nm], Jv = Jm.map((r) => r.reduce((s, c, b) => s + c * v[b], 0)); return Math.max(...Jv.map((c, a) => Math.abs(c - lam * v[a]))) < 1e-5 && Math.abs(v.reduce((a, b) => a + b, 0)) < 1e-12; });
check('the eigenpairs are eigenpairs of the test’s finite-difference Jacobian, tangent to the simplex: X −2.613, Y +2.350, Z −6.768', eigOK && eig.X.lam.toFixed(3) === '-2.613' && eig.Y.lam.toFixed(3) === '2.350' && eig.Z.lam.toFixed(3) === '-6.768', `${eig.X.lam} ${eig.Y.lam} ${eig.Z.lam}`);
const vY = eig.Y.v, push = (sg, e) => YF.map((y, a) => y + sg * e * vY[a]);
await setT(1); i = await info();
const endLean = rk4(i.start);
check('Y − 10⁻³·v: the page starts there and settles at X; the test’s RK4 from the same start ends within 10⁻⁸ of X', dmax(i.start, push(-1, 1e-3)) < 1e-15 && i.ends[0].name === 'X' && i.ends[0].d < 1e-12 && dmax(endLean, XF) < 1e-8, `${i.ends[0].d} ${dmax(endLean, XF)}`);
check('readouts: the rates, X₃ ≠ Y₃, the exact certificate at X, its largest flux, the trajectory and the eigenvalues', (await text('ro1')) === '16 · 4/15 … 255689/25 · 2/5 … 233557/35' && (await text('ro2')) === 'X₃ = 3/16 · Y₃ = 6/17 · ≠' && (await text('ro3')) === '全为 0 · 0 · 1 · 16 / 16' && (await text('ro4')) === 'η(3, 9) = 15827/640 ≈ 24.730' && (await text('ro5')) === `Y − 10⁻³·v · 14.00 · X · ${sciT(i.ends[0].d)}` && (await text('ro6')) === '−2.613 · +2.350 · −6.768');
check('the HUD, the pills and the detailed-balance note', (await text('hudBig')) === 'Y − 10⁻³·v → X' && (await text('pillC')) === '物理稳态 X ≠ Y' && (await text('pillD')) === 't 14.00' && (await text('roNote')).startsWith('θ = p/q：θ₃₃·θ₄₄ = 100/423，θ₃₄·θ₃₅ = 2/9'));
const mani = await D2(() => GR_DEBUG.manifold());
/* the branches start 10⁻⁷ from Y and need about ln(10⁷)/2.35 ≈ 6.9 time units to leave it, so by t = 14 the X branch is about 10⁻¹⁰ from X */
check('Y’s unstable manifold: the branch along −v ends at X and the one along +v at Z (within 10⁻⁸)', dmax(mani[0], XF) < 1e-8 && dmax(mani[1], Zp) < 1e-8, `${dmax(mani[0], XF)} ${dmax(mani[1], Zp)}`);

/* ---------- other presets ---------- */
await preset('toz'); await setT(1); i = await info();
const endZ = rk4(i.start);
check('Y + 10⁻³·v settles at Z on the page and in the test’s RK4', dmax(i.start, push(1, 1e-3)) < 1e-15 && i.ends[0].name === 'Z' && i.ends[0].d < 1e-12 && dmax(endZ, Zp) < 1e-8 && (await text('hudBig')) === 'Y + 10⁻³·v → Z');
check('the certificate chart switches to Y, whose largest flux is η(3, 6) = −32968/1445', (await text('c2Title')) === 'Y 处的 16 个净通量' && (await text('ro4')) === 'η(3, 6) = −32968/1445 ≈ −22.815' && (await text('ro3')) === '全为 0 · 0 · 1 · 16 / 16');
await preset('sweep'); await setT(1); i = await info();
const grid = []; for (let b = 0; b < 9; b++) for (let a = 0; a < 9; a++) { if (a + b > 8) continue; const qa = 0.05 + 0.1 * a, qb = 0.05 + 0.1 * b, r = (1 - qa - qb) / 6; grid.push([qa, qb, r, r, r, r, r, r]); }
const sweepEnds = grid.map((x0) => { const e = rk4(x0); return dmax(e, XF) < 1e-6 ? 'X' : dmax(e, Zp) < 1e-6 ? 'Z' : '?'; });
check('45 grid starts: the page sends 20 to X and 25 to Z, start by start as the test’s RK4 does', i.n === 45 && i.starts.every((x, q) => dmax(x, grid[q]) < 1e-15) && i.counts.X === 20 && i.counts.Z === 25 && i.ends.every((e, q) => e.name === sweepEnds[q] && e.d < 1e-6), sweepEnds.join(''));
check('the sweep readouts and HUD', (await text('ro5')) === '45 个网格起点 · 14.00 · X 20 / Z 25' && (await text('hudBig')) === 'X 20 · Z 25' && (await text('c1Title')) === '到达 X 与 Z 的起点数');
await preset('corner'); await setT(1); i = await info();
check('a start with Q₃ + Q₄ = 0.9 goes to Z (page and RK4); Z₃ + Z₄ = 94.5%', i.ends[0].name === 'Z' && dmax(rk4(i.start), Zp) < 1e-8 && (Zp[0] + Zp[1]).toFixed(3) === '0.945');
await preset('nearx'); await setT(1); i = await info();
check('X with Q₃ + 0.02 and Q₄ − 0.02 returns to X (page and RK4)', dmax(i.start, XF.map((v, a) => v + (a === 0 ? 0.02 : a === 1 ? -0.02 : 0))) < 1e-15 && i.ends[0].name === 'X' && dmax(rk4(i.start), XF) < 1e-8);
await preset('slow'); await setT(4 / 14); i = await info(); const slow4 = dmax(i.cur, YF);
await preset('lean'); await setT(4 / 14); const lean4 = dmax((await info()).cur, YF);
await preset('slow'); await setT(1); i = await info();
check('ε = 10⁻⁶ lingers: at t = 4 still within 0.05 of Y while the 10⁻³ push has left; it ends at X (RK4 too)', slow4 < 0.05 && lean4 > 0.05 && i.ends[0].name === 'X' && dmax(rk4(i.start), XF) < 1e-8, `${slow4} ${lean4}`);

/* ---------- controls ---------- */
await preset('lean');
await D2(() => { const e = document.getElementById('epsIn'); e.value = -2; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the ε slider sets 10⁻²: the start moves to Y − 10⁻²·v, custom settings', dmax(i.start, push(-1, 1e-2)) < 1e-15 && (await text('epsOut')) === '10⁻²' && (await state()).preset === null && /自定义/.test(await text('presetNote')));
await click('#sideChips [data-side="1"]'); await setT(1); i = await info();
check('the +v chip pushes towards Z', dmax(i.start, push(1, 1e-2)) < 1e-15 && i.ends[0].name === 'Z');
await click('#certChips [data-cert="Y"]');
check('the flux chips switch the certificate to Y', (await state()).cert === 'Y' && (await text('c2Title')) === 'Y 处的 16 个净通量');

/* ---------- labels, rail, keys, playback ---------- */
const boxes = await D2(() => [...document.querySelectorAll('.side .lean')].map((b) => [b.className, b.querySelector('.ok').textContent, b.textContent]));
check('label boxes: two LEAN ✓, NUM, dossier ARGUED, page ARGUED (dashed), OPEN, LIT', boxes.map((b) => b[1]).join(' ') === 'LEAN ✓ LEAN ✓ NUM ARGUED ARGUED OPEN LIT' && /theory/.test(boxes[3][0]) && /page/.test(boxes[4][0]));
check('the LEAN boxes name the frozen declarations', boxes[0][2].includes('GranularCellOrderSteadyStateRefutation.result') && ['p10', 'q10', 'rhs10', 'X_stationary', 'Y_stationary', 'X3_ne_Y3'].every((s) => boxes[1][2].includes(s)));
check('the NUM box states the page’s eigenvalues and sweep counts', ['−2.613', '+2.350', '−6.768', '20 个停在 X，25 个停在 Z'].every((s) => boxes[2][2].includes(s)));
check('the LIT box cites the paper with its DOI', boxes[6][2].includes('10.1088/1751-8121/ace56d') && boxes[6][2].includes('345001'));
await preset('lean');
check('the rail marks t = 0, 7 and 14', (await D2(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 't = 0 | t = 7 | t = 14');
await setT(0); await D2(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await page.keyboard.press('ArrowRight'); await settle();
check('→ → advances to t = 2', Math.abs((await info()).tau - 2) < 1e-9 && (await text('clock')) === 't = 2.00');
await page.keyboard.press('ArrowLeft'); await settle();
check('← goes back to t = 1', Math.abs((await info()).tau - 1) < 1e-9);
await page.keyboard.press('e'); await settle();
check('E jumps to t = 14 and pauses', (await info()).tau === 14 && (await state()).playing === false);
await page.keyboard.press(' '); await settle();
check('Space toggles playback', (await state()).playing === true);
await D2(() => document.querySelector('#speedChips [data-speed="2.5"]').click());
check('playing to the end reports where the trajectory settled', await waitToast(/停在 X：t = 14 时距离/));
await pause(); await D2(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['side', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D2(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await setT(0.5);
const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels mark X and Y as Lean’s and Z as numeric', ['X（Lean）', 'Y（Lean · 鞍点）', 'Z（数值）'].every((s) => tags.includes(s)), tags);
const lit = await D2(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
await D2(() => window.TRV_THUMB()); await settle();
check('the thumbnail state is the paused sweep at t = 8.4', (await state()).preset === 'sweep' && (await state()).playing === false && Math.abs((await info()).tau - 8.4) < 1e-9);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'sweep']) {
  await preset(p); await setT(0.6);
  const leftovers = await D2(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await D2(() => { const e = document.getElementById('epsIn'); e.value = -4; e.dispatchEvent(new Event('input')); }); await settle();
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D2(() => document.title)).startsWith('GRANULAR//TWO · One set of positive rates, two physical steady states of a granular packing'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D2(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D2(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['myhill-blumenfeld-2023-granular-steady-state-uniqueness-refutation.md', 'D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.lean', 'Blueprint/D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.md', 'Library/StatisticalMechanics/myhill2023granularsteadystates.md', 'doi.org/10.1088/1751-8121/ace56d', 'arxiv.org/abs/2306.10526v2'].every((s) => h.includes(s)); })));
await page.keyboard.press('Escape'); await page.waitForFunction(() => document.getElementById('drawer').hidden === true, null, { timeout: 10000 }).catch(() => {});
check('Esc closes the drawer', (await D2(() => document.getElementById('drawer').hidden)) === true);
await page.waitForFunction(() => document.activeElement?.id === 'infoBtn', null, { timeout: 10000 }).catch(() => {});
check('focus returns to the drawer button', (await D2(() => document.activeElement?.id)) === 'infoBtn');

/* ---------- index round trip ---------- */
const live = readRegistry().visualizations.filter(v => v.status === 'live').length;
await page.click('.crumb'); await page.waitForLoadState('load');
await page.waitForFunction((n) => document.querySelectorAll('.card').length >= n, live, { timeout: 30000 }).catch(() => {});
check('language choice carries to the index', (await D2(() => document.documentElement.dataset.lang)) === 'en');
check('index lists every live visualization', (await D2(() => document.querySelectorAll('.card').length)) === live, `live ${live}`);
await page.click('.card:has(a[href*="granular-two"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.GR_DEBUG && GR_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D2(() => document.body.dataset.vizId)) === 'granular-two');

/* ---------- narrow layouts in both languages ---------- */
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await waitFrames(3);
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await waitFrames(6);
    check(`no horizontal scroll at ${w}px (${lang})`, (await D2(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 });
}
check('no script errors during the whole session', errors.length === 0, errors.slice(0, 3).join(' | '));

await browser.close(); server.close();
const failed = results.filter(r => !r.ok).length;
console.log(`\n${results.length - failed}/${results.length} passed`);
process.exit(failed ? 1 : 0);
