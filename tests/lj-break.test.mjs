#!/usr/bin/env node
// Browser regression suite for viz/lj-break (Playwright + Chromium with software WebGL).
//   node tests/lj-break.test.mjs
// Reads page state through the read-only window.LJ_DEBUG probe and checks it against an independent implementation: bond lengths
// from the polynomial τr¹³ − 12r⁶ + 12 = 0, equilibria found by scanning the broken length instead of the tension, the Hessian
// written from the potential energy, eigenvalue counts and eigenvalues from Sturm sequences of the tridiagonal matrix, and the
// motion re-integrated by classical Runge–Kutta from the page's initial frame.
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
  const start = await page.evaluate(() => LJ_DEBUG.frames());
  await page.waitForFunction((f0) => !LJ_DEBUG.pending() && LJ_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => LJ_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => LJ_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => LJ_DEBUG.info());
const state = () => D(() => LJ_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const frameAt = (g) => D((g) => LJ_DEBUG.frameAt(g), g);
const slide = async (id, v) => { await D(([id, v]) => { const el = document.getElementById(id); el.value = String(v); el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]); await settle(); };
const setChain = async (m, k, d, pos = 'spread', branch = 0) => {
  const s = await state();
  if (s.m !== m) await click(`#mChips [data-m="${m}"]`);
  await slide('kk', k); await slide('dd', d);
  if ((await state()).pos !== pos) await click(`#posChips [data-pos="${pos}"]`);
  if (branch && await visible('branchChips')) await click(`#branchChips [data-branch="${branch}"]`);
};
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => LJ_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => LJ_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 120000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
const RI = Math.pow(13 / 7, 1 / 6);
const V = (r) => Math.pow(r, -12) - 2 * Math.pow(r, -6);
const Vp = (r) => (12 * Math.pow(r, 6) - 12) / Math.pow(r, 13);          // φ′ written as one fraction
const Vpp = (r) => 156 * Math.pow(r, -14) - 84 * Math.pow(r, -8);        // φ″ expanded
const TMAX = Vp(RI);
/* φ′(r) = τ  ⟺  τr¹³ − 12r⁶ + 12 = 0; Newton from the side of the wanted root, polished by bisection on the polynomial */
function lengthFor(tau, broken) {
  const p = (r) => tau * Math.pow(r, 13) - 12 * Math.pow(r, 6) + 12;
  let lo = broken ? RI : 1, hi = broken ? Math.max(2, 3 * Math.pow(12 / tau, 1 / 7)) : RI;
  const sLo = Math.sign(p(lo));
  for (let i = 0; i < 200; i++) { const mid = (lo + hi) / 2; if (Math.sign(p(mid)) === sLo) lo = mid; else hi = mid; }
  return (lo + hi) / 2;
}
/* equilibria by scanning the broken length r_b ∈ (rᵢ, 60): τ = φ′(r_b), r_u = r_u(τ) */
function myEquilibria(m, k, d) {
  const g = (rB) => { const tau = Vp(rB); return k * rB + (m + 1 - k) * lengthFor(tau, false) - (m + 1) * d; };
  const xs = []; for (let i = 0; i <= 6000; i++) xs.push(RI * Math.pow(60 / RI, Math.pow(i / 6000, 2.2)));
  const out = [];
  for (let i = 1; i < xs.length; i++) {
    let a = xs[i - 1], b = xs[i], ga = g(a), gb = g(b);
    if (ga * gb < 0) { for (let j = 0; j < 100; j++) { const mid = (a + b) / 2, gm = g(mid); if (ga * gm <= 0) { b = mid; gb = gm; } else { a = mid; ga = gm; } } out.push(Vp((a + b) / 2)); }
  }
  return out.sort((x, y) => x - y);
}
/* J = −Hessian of Σ φ(x_{j+1} − x_j): diagonal −(φ″(r_{i−1}) + φ″(r_i)), off-diagonal φ″(r_i) */
function myJ(rs) { const m = rs.length - 1, c = rs.map(Vpp); return { a: Array.from({ length: m }, (_, i) => -(c[i] + c[i + 1])), b: Array.from({ length: m - 1 }, (_, i) => c[i + 1]) }; }
function countBelow({ a, b }, x) { let q = 1, n = 0; for (let i = 0; i < a.length; i++) { q = a[i] - x - (i ? b[i - 1] * b[i - 1] / q : 0); if (q === 0) q = -1e-300; if (q < 0) n++; } return n; }
const positives = (J) => J.a.length - countBelow(J, 1e-13);
function sturmEigs(J) {
  const n = J.a.length; let lo = Infinity, hi = -Infinity;
  for (let i = 0; i < n; i++) { const r = (i ? Math.abs(J.b[i - 1]) : 0) + (i < n - 1 ? Math.abs(J.b[i]) : 0); lo = Math.min(lo, J.a[i] - r); hi = Math.max(hi, J.a[i] + r); }
  const out = [];
  for (let k = 1; k <= n; k++) { let x0 = lo, x1 = hi; for (let it = 0; it < 200; it++) { const mid = (x0 + x1) / 2; if (countBelow(J, mid) >= n - k + 1) x1 = mid; else x0 = mid; } out.push((x0 + x1) / 2); }
  return out;   // decreasing
}
function rk4(x0, m, T1, h) {
  const n = m + 2; let x = x0.slice(), v = new Array(n).fill(0);
  const acc = (x) => { const a = new Array(n).fill(0); for (let i = 1; i <= m; i++) a[i] = Vp(x[i + 1] - x[i]) - Vp(x[i] - x[i - 1]); return a; };
  const steps = Math.round(T1 / h);
  for (let s = 0; s < steps; s++) {
    const k1x = v, k1v = acc(x);
    const x2 = x.map((q, i) => q + h / 2 * k1x[i]), v2 = v.map((q, i) => q + h / 2 * k1v[i]), k2v = acc(x2);
    const x3 = x.map((q, i) => q + h / 2 * v2[i]), v3 = v.map((q, i) => q + h / 2 * k2v[i]), k3v = acc(x3);
    const x4 = x.map((q, i) => q + h * v3[i]), v4 = v.map((q, i) => q + h * k3v[i]), k4v = acc(x4);
    x = x.map((q, i) => q + h / 6 * (k1x[i] + 2 * v2[i] + 2 * v3[i] + v4[i]));
    v = v.map((q, i) => q + h / 6 * (k1v[i] + 2 * k2v[i] + 2 * k3v[i] + k4v[i]));
  }
  return x;
}
const rel = (a, b) => Math.abs(a - b) / Math.max(1e-300, Math.abs(b));

/* ---------- load ---------- */
await page.goto(origin + BASE + 'viz/lj-break/');
await page.waitForFunction(() => window.LJ_DEBUG && LJ_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let st = await state(), i = await info();
check('opens on the one-break preset (m = 10, k = 1, d = 1.3) and plays', st.preset === 'one' && i.m === 10 && i.k === 1 && i.d === 1.3 && st.playing === true);
check('the inflection point is (13/7)^(1/6) and φ′(rᵢ) is the largest tension', rel(i.ri, RI) < 1e-15 && rel(i.tauMax, TMAX) < 1e-12 && Math.abs(Vpp(RI)) < 1e-10, `${i.ri} ${i.tauMax} ${Vpp(RI)}`);
await pause();

/* ---------- equilibria and spectra on the presets ---------- */
const presetData = {};
for (const p of ['one', 'two', 'five', 'all', 'high', 'twin']) { await preset(p); presetData[p] = await info(); }
const eqOK = (x) => {
  const mine = myEquilibria(x.m, x.k, x.d);
  return mine.length === x.taus.length && mine.every((t, j) => rel(x.taus[j], t) < 1e-8);
};
check('every preset’s equilibria match the independent scan over the broken length (count and τ to 10⁻⁸)', Object.values(presetData).every(eqOK), Object.entries(presetData).map(([p, x]) => `${p}:${x.taus.map((t) => t.toFixed(5)).join('/')}`).join(' '));
const forceOK = (x) => {
  const X = x.u.map((u, n) => n * x.d + u), r = X.slice(1).map((q, j) => q - X[j]);
  const f = r.slice(1).map((rr, j) => Vp(rr) - Vp(r[j]));
  return Math.max(...f.map(Math.abs)) < 1e-9 && Math.abs(r.reduce((a, b) => a + b, 0) - (x.m + 1) * x.d) < 1e-9 && r.filter((q) => q > RI).length === x.k && r.every((q) => q > 0);
};
check('at every preset equilibrium the force on each particle vanishes, the walls are (m + 1)d apart and exactly k bonds exceed rᵢ', Object.values(presetData).every(forceOK));
check('the broken and unbroken lengths solve τr¹³ − 12r⁶ + 12 = 0 on either side of rᵢ', Object.values(presetData).every((x) => x.branches.every((b) => rel(b.rB, lengthFor(b.tau, true)) < 1e-9 && rel(b.rU, lengthFor(b.tau, false)) < 1e-9)));
const specOK = (x) => {
  const J = myJ(x.rs), ev = sturmEigs(J);
  return x.U === positives(J) && x.vals.every((v, j) => Math.abs(v - ev[j]) < 1e-8 * Math.max(1, Math.abs(ev[j])));
};
check('every preset’s spectrum equals the Sturm-sequence eigenvalues of the independent Hessian, and U equals the inertia count', Object.values(presetData).every(specOK), Object.entries(presetData).map(([p, x]) => `${p}:U=${x.U}`).join(' '));
check('the eigenvector drawn in amber satisfies J v = μ₁ v (residual < 10⁻⁹)', Object.values(presetData).every((x) => { const J = x.J, v = x.vec, mu = x.vals[0]; return J.every((row, a) => Math.abs(row.reduce((s, q, b) => s + q * v[b], 0) - mu * v[a]) < 1e-9 * Math.max(1, Math.abs(mu))); }));
const P = presetData;
check('one: k = 1, U = 0, all eigenvalues negative', P.one.k === 1 && P.one.U === 0 && P.one.vals[0] < 0);
check('two: k = 2, U = 1 with μ₁ ≈ 0.011', P.two.k === 2 && P.two.U === 1 && Math.abs(P.two.vals[0] - 0.011) < 0.001, `${P.two.vals[0]}`);
check('five: k = 5, U = 4', P.five.k === 5 && P.five.U === 4);
check('all: k = m + 1 = 11 gives U = m = 10 and J positive definite', P.all.k === 11 && P.all.U === 10 && P.all.vals[9] > 0);
check('high: d = 1.104, upper branch τ ≈ 2.68, r_b ≈ 1.120, U = k = 3', P.high.taus.length === 2 && P.high.branch === 1 && Math.abs(P.high.tau - 2.68) < 0.005 && Math.abs(P.high.rs[P.high.broken[0]] - 1.120) < 0.0005 && P.high.U === 3, `${P.high.tau} ${P.high.rs[P.high.broken[0]]}`);
check('twin: the same d and k, lower branch τ ≈ 1.45, r_b ≈ 1.311, U = k − 1 = 2', P.twin.branch === 0 && Math.abs(P.twin.tau - 1.45) < 0.005 && Math.abs(P.twin.rs[P.twin.broken[0]] - 1.311) < 0.0005 && P.twin.U === 2 && P.twin.branches.map((b) => b.U).join() === '2,3');
check('on every preset branch the sign of Σ 1/cⱼ matches U (negative ↔ k − 1, positive ↔ k)', Object.values(presetData).every((x) => x.branches.every((b) => { const rs = Array.from({ length: x.m + 1 }, (_, j) => (x.broken.includes(j) ? lengthFor(b.tau, true) : lengthFor(b.tau, false))), sum = rs.reduce((a, r) => a + 1 / Vpp(r), 0); return Math.sign(sum) === Math.sign(b.dLdt) && (sum < 0 ? b.U === x.k - 1 : b.U === x.k); })));

/* ---------- the theorem across chains ---------- */
const sweep = [];
for (const [m, ks] of [[6, [1, 2, 3, 4, 7]], [10, [1, 2, 3, 4, 6, 11]], [14, [1, 2, 5, 8, 15]]]) for (const k of ks) for (const d of [1.09, 1.104, 1.2, 1.45]) for (const pos of k > 1 && k < m + 1 ? ['spread', 'block', 'ends'] : ['spread']) sweep.push([m, k, d, pos]);
let sweepOK = true, sweepEq = 0, sweepNone = 0, both = 0, sweepBad = [];
const seenEnds = new Set();
for (const [m, k, d, pos] of sweep.filter((_, j) => j % 3 === 0)) {
  await setChain(m, k, d, pos);
  const x = await info(), mine = myEquilibria(m, k, x.d);
  if (x.none !== (mine.length === 0) || x.taus.length !== mine.length) { sweepOK = false; sweepBad.push(`${m}/${k}/${x.d}/${pos} count`); continue; }
  if (x.none) { sweepNone++; continue; }
  for (const b of x.branches) {
    const rs = Array.from({ length: m + 1 }, (_, j) => (x.broken.includes(j) ? lengthFor(b.tau, true) : lengthFor(b.tau, false))), U = positives(myJ(rs));
    sweepEq++;
    if (b.U !== U || U < k - 1 || U > k) { sweepOK = false; sweepBad.push(`${m}/${k}/${d}/${pos} U=${b.U}/${U}`); }
    seenEnds.add(U === k ? 'k' : 'k-1');
  }
  if (x.taus.length === 2) both++;
}
check('sweep over m, k, d and break positions: equilibria agree, and every computed U equals the independent count and lies in [k − 1, k]', sweepOK && sweepEq > 15, `${sweepEq} equilibria, ${sweepNone} empty, ${both} with two branches ${sweepBad.slice(0, 4).join(' ')}`);
check('both ends of the theorem’s range occur in the sweep', seenEnds.has('k') && seenEnds.has('k-1'));

/* ---------- motion ---------- */
for (const p of ['five', 'two']) {
  await preset(p); const x = await info(), f0 = await frameAt(0), eqX = x.u.map((u, n) => n * x.d + u);
  const big = x.vec.reduce((a, b) => (Math.abs(b) > Math.abs(a) ? b : a), 0);
  check(`${p}: frame 0 is the equilibrium plus 10⁻³ times the eigenvector scaled to largest entry 1`, f0.every((q, n) => Math.abs(q - (eqX[n] + (n > 0 && n <= x.m ? 1e-3 * x.vec[n - 1] / big : 0))) < 1e-12));
  const mu = x.vals[0], gLin = x.dev.findIndex((dv) => dv >= 0.01), t = gLin * x.sample, pred = 1e-3 * Math.cosh(Math.sqrt(mu) * t);
  check(`${p}: in the linear regime the largest displacement follows 10⁻³ cosh(√μ₁ t) (within 3 %)`, gLin > 0 && rel(x.dev[gLin], pred) < 0.03, `t=${t.toFixed(2)} ${x.dev[gLin]} vs ${pred}`);
  const gCmp = Math.max(1, x.dev.findIndex((dv) => dv >= 0.05)), ref = rk4(f0, x.m, gCmp * x.sample, 0.0005), got = await frameAt(gCmp);
  const err = Math.max(...ref.map((q, n) => Math.abs(q - got[n])));
  check(`${p}: an independent Runge–Kutta run reproduces the page’s positions up to displacement 0.05 (to 10⁻⁴ of it)`, err < 5e-6, `t=${(gCmp * x.sample).toFixed(2)} err ${err.toExponential(2)}`);
}
{
  const x = P.all; let ok = true;
  await preset('all');
  for (const g of [0, 40, 200, x.NF - 1]) { const fr = await frameAt(g); if (Math.abs(fr[0]) > 1e-12 || Math.abs(fr[x.m + 1] - (x.m + 1) * x.d) > 1e-12) ok = false; const nb = fr.slice(1).filter((q, j) => q - fr[j] > RI).length; if (nb !== x.nBroken[g]) ok = false; }
  check('the walls stay fixed in every frame and the broken-bond counts match a recount of the frames', ok);
}
check('energy is conserved on every preset to 10⁻³ of |E|', Object.values(presetData).every((x) => x.drift < 1e-3 * Math.abs(x.E0)), Object.entries(presetData).map(([p, x]) => `${p}:${(x.drift / Math.abs(x.E0)).toExponential(1)}`).join(' '));
const after = (x) => x.nBroken.slice(x.fGrow);
check('one: the displacement never exceeds 1.5·10⁻³ and the single break stays', Math.max(...P.one.dev) < 1.5e-3 && P.one.nBroken.every((n) => n === 1));
check('two: the first change is one break healing near t ≈ 70, leaving a single broken bond at the end', P.two.fChange > 0 && Math.abs(P.two.fChange * 0.05 - 70) < 5 && P.two.nBroken[P.two.fChange] === 1 && P.two.nBroken[P.two.NF - 1] === 1, `t=${P.two.fChange * 0.05}`);
check('five: after the growth the number of broken bonds stays between 2 and 8', P.five.fGrow > 0 && Math.min(...after(P.five)) === 2 && Math.max(...after(P.five)) === 8, `${Math.min(...after(P.five))}–${Math.max(...after(P.five))}`);
check('all: the displacement reaches 0.1 by t ≈ 1 and the count then swings between 2 and 11', Math.abs(P.all.fGrow * 0.05 - 1) < 0.5 && Math.min(...after(P.all).slice(1)) === 2 && Math.max(...after(P.all).slice(1)) === 11, `t=${P.all.fGrow * 0.05} ${Math.min(...after(P.all).slice(1))}–${Math.max(...after(P.all).slice(1))}`);

/* ---------- controls ---------- */
await preset('five'); await click('#mChips [data-m="6"]');
check('m chips change the chain and clamp k to m + 1', (await info()).m === 6 && (await info()).k === 5 && (await D(() => document.getElementById('kk').max)) === '7');
await slide('kk', 7); i = await info();
check('the k slider reaches k = m + 1 = 7, where U = 6 = k − 1', i.k === 7 && i.U === 6);
await setChain(10, 3, 1.3, 'block'); const blk = (await info()).broken;
await click('#posChips [data-pos="ends"]'); const ends = await info();
await click('#posChips [data-pos="spread"]'); const spr = await info();
check('break positions: block is contiguous, ends uses both end bonds, spread does neither; lengths unchanged, U still in range', blk.join() === '4,5,6' && ends.broken.includes(0) && ends.broken.includes(10) && spr.broken.join() === '1,5,9'
  && [ends, spr].every((x) => x.rs.slice().sort().join() === ends.rs.slice().sort().join() && x.U >= 2 && x.U <= 3));
check('the branch chips stay hidden when only one equilibrium exists', !(await visible('branchChips')));
await setChain(10, 3, 1.104);
check('…and appear when there are two', await visible('branchChips'));
await click('#branchChips [data-branch="1"]'); i = await info();
check('the branch chips switch to the high-tension branch', i.branch === 1 && i.U === 3 && /Custom|自定义/.test(await text('presetNote')));
await setChain(10, 6, 1.104); i = await info();
check('with no equilibrium (m = 10, k = 6, d = 1.104) the page says so instead of drawing one', i.none === true && myEquilibria(10, 6, 1.104).length === 0 && /无平衡|no equilibrium/i.test(await text('hudBig')) && /OPEN/.test(await text('roNote')));
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('…the right chart still draws the length curves', lit[1] > 2000, `${lit}`);

/* ---------- presets, timeline ---------- */
for (const p of ['one', 'two', 'five', 'all', 'high', 'twin']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
await preset('five'); await setFrac(0.95); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing to the end reports the growth time against the linear prediction', await waitToast(/位移在 t = .*线性预言/));
await pause();
await preset('one'); await setFrac(0.95); await click('#play');
check('…and for a stable equilibrium reports that it stayed put', await waitToast(/稳定/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
await setFrac(0.5); const f1 = (await info()).f;
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
const f2 = (await info()).f;
check('→ steps the time forward by 1/200 of the run', f2 > f1 && Math.abs((f2 - f1) - (await info()).NF / 200) <= 1.5, `${f1}→${f2}`);
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await info()).f === (await info()).NF - 1 && (await state()).playing === false);
await preset('five');
check('the rail marks t = 0, the displacement 0.1 and the end', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' '))) === 't = 0 位移 0.1 t = 30');
check('the readouts state U against the theorem’s range', /U = 4 · \[4, 5\] ✓/.test(await text('ro3')));
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
const lit2 = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit2.every((n) => n > 2000), `${lit2}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['five', 'twin']) {
  await preset(p); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#posChips [data-pos="block"]');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('LJ//BREAK · Broken bonds and unstable directions in a Lennard-Jones chain'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['rodrigues-kevrekidis-dobson-2019-n-break-instability-count.md', 'LennardJonesChainBreakInstabilityCount.lean', 'Blueprint/D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.md', 'rodrigueskevrekidisdobson2019nbreak.md', '10.1103/PhysRevE.99.022201', 'arxiv.org/abs/1802.03477'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="lj-break"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.LJ_DEBUG && LJ_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'lj-break');

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
