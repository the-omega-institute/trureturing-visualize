#!/usr/bin/env node
// Browser regression suite for viz/oqw-ruin (Playwright + Chromium with software WebGL).
//   node tests/oqw-ruin.test.mjs
// Reads page state through the read-only window.OQ_DEBUG probe and checks it against an independent implementation: Lean's
// pair built from u = (1, i) and v = (1, −i), the mean time summed over first-absorbing step sequences exactly as the Lean
// definitions read, a separate density-matrix walk for every other pair, and the conditions of the conjectured form recovered
// from walk means of the six Bloch-axis states (no linear solve).
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
  const start = await page.evaluate(() => OQ_DEBUG.frames());
  await page.waitForFunction((f0) => !OQ_DEBUG.pending() && OQ_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => OQ_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setRange = async (id, v) => { await D(([id, v]) => { const e = document.getElementById(id); e.value = v; e.dispatchEvent(new Event('input')); }, [id, v]); await settle(); };
const info = () => D(() => OQ_DEBUG.info());
const state = () => D(() => OQ_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D(() => OQ_DEBUG.frames()); await page.waitForFunction((t) => OQ_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- independent complex 2 × 2 arithmetic: a matrix is [[{re, im}, …], …] ---------- */
const c = (re, im = 0) => ({ re, im });
const cm = (a, b) => c(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re), ca = (a, b) => c(a.re + b.re, a.im + b.im), cj = (a) => c(a.re, -a.im);
const mm = (A, B) => [0, 1].map((i) => [0, 1].map((j) => ca(cm(A[i][0], B[0][j]), cm(A[i][1], B[1][j]))));
const dag = (A) => [0, 1].map((i) => [0, 1].map((j) => cj(A[j][i])));
const madd = (A, B) => [0, 1].map((i) => [0, 1].map((j) => ca(A[i][j], B[i][j])));
const tr = (A) => A[0][0].re + A[1][1].re;
const fromFlat = (f) => [[c(f[0], f[1]), c(f[2], f[3])], [c(f[4], f[5]), c(f[6], f[7])]];
const outer = (x, y, s) => [0, 1].map((i) => [0, 1].map((j) => { const p = cm(x[i], cj(y[j])); return c(s * p.re, s * p.im); }));
const u = [c(1), c(0, 1)], v = [c(1), c(0, -1)];
const LEAN = { L: outer(v, u, 0.5), R: outer(v, v, 0.5) }, RHO = outer(u, u, 0.5), SIGMA = outer(v, v, 0.5);
const blochRho = ([x, y, z]) => [[c((1 + z) / 2), c(x / 2, -y / 2)], [c(x / 2, y / 2), c((1 - z) / 2)]];
const close = (a, b, e = 1e-9) => Math.abs(a - b) <= e * Math.max(1, Math.abs(b));
/* Lean's reading: words of Booleans (true = right), operator = reversed product, first absorption, Σ n·mass */
function wordMean(P, M, k, rho, maxLen) {
  let mean = 0, mass = 0;
  for (let n = 1; n <= maxLen; n++) for (let w = 0; w < 1 << n; w++) {
    let pos = k, ok = true;
    for (let t = 0; t < n; t++) { pos += (w >> t) & 1 ? 1 : -1; if (t < n - 1 && (pos <= 0 || pos >= M)) { ok = false; break; } }
    if (!ok || (pos !== 0 && pos !== M)) continue;
    let W = [[c(1), c(0)], [c(0), c(1)]];
    for (let t = 0; t < n; t++) W = mm((w >> t) & 1 ? P.R : P.L, W);
    const m = tr(mm(mm(W, rho), dag(W))); mean += n * m; mass += m;
  }
  return { mean, mass };
}
/* a separate density walk: per site, branch by L and R, absorb at 0 and M */
function walk(P, M, k, rho) {
  let st = new Map([[k, rho]]); let mean = 0, p0 = 0, pM = 0, t = 0; const series = [0];
  while (t < 30000) {
    t++; const nx = new Map(); let a = 0, b = 0;
    for (const [x, S] of st) for (const [y, X] of [[x - 1, P.L], [x + 1, P.R]]) {
      const T2 = mm(mm(X, S), dag(X));
      if (y === 0) a += tr(T2); else if (y === M) b += tr(T2); else nx.set(y, nx.has(y) ? madd(nx.get(y), T2) : T2);
    }
    mean += t * (a + b); p0 += a; pM += b; series.push([a, b]); st = nx;
    let rem = 0; for (const S of st.values()) rem += tr(S); if (rem < 1e-15) break;
  }
  return { mean, p0, pM, series };
}
/* the conditions of the conjectured form from walk means only: A₀₀ = E(+z), A₁₁ = E(−z), Re A₀₁ = (E(+x) − E(−x))/2, Im A₀₁ = −(E(+y) − E(−y))/2 */
function opFromMeans(P, M, k) {
  const E = (b) => walk(P, M, k, blochRho(b)).mean;
  return { a00: E([0, 0, 1]), a11: E([0, 0, -1]), re: (E([1, 0, 0]) - E([-1, 0, 0])) / 2, im: -(E([0, 1, 0]) - E([0, -1, 0])) / 2 };
}
const pairOfInfo = (i) => ({ L: fromFlat(i.L), R: fromFlat(i.R) });
const normErr = (P) => { const N = madd(mm(dag(P.L), P.L), mm(dag(P.R), P.R)); return Math.max(Math.abs(N[0][0].re - 1), Math.abs(N[0][0].im), Math.hypot(N[0][1].re, N[0][1].im), Math.hypot(N[1][0].re, N[1][0].im), Math.abs(N[1][1].re - 1), Math.abs(N[1][1].im)); };

/* ---------- open ---------- */
await page.goto(origin + BASE + 'viz/oqw-ruin/');
await page.waitForFunction(() => window.OQ_DEBUG && OQ_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let [s0, i] = await D(() => [OQ_DEBUG.state(), OQ_DEBUG.info()]);
check('opens on Lean’s counterexample (M = 3, k = 1, ρ along +y) and plays', s0.preset === 'lean' && i.M === 3 && i.k === 1 && s0.playing);
await pause();

/* ---------- Lean's counterexample ---------- */
const P0 = pairOfInfo(i);
check('the page’s pair is L = ½vu*, R = ½vv* with u = (1, i), v = (1, −i), normalized, and L·R = 0', [0, 1].every((a) => [0, 1].every((b) => close(P0.L[a][b].re, LEAN.L[a][b].re, 1e-15) && close(P0.L[a][b].im, LEAN.L[a][b].im, 1e-15) && close(P0.R[a][b].re, LEAN.R[a][b].re, 1e-15) && close(P0.R[a][b].im, LEAN.R[a][b].im, 1e-15))) && normErr(LEAN) < 1e-15 && mm(LEAN.L, LEAN.R).flat().every((z) => Math.hypot(z.re, z.im) < 1e-15));
const rhoPage = fromFlat(i.rho);
check('the page’s initial state is ρ = ½uu*, and σ = ½vv* has the same ρ₀₀, ρ₁₁ and Re ρ₀₁', [0, 1].every((a) => [0, 1].every((b) => close(rhoPage[a][b].re, RHO[a][b].re, 1e-15) && close(rhoPage[a][b].im, RHO[a][b].im, 1e-15))) && RHO[0][0].re === SIGMA[0][0].re && RHO[1][1].re === SIGMA[1][1].re && RHO[0][1].re === SIGMA[0][1].re && RHO[0][1].im === -SIGMA[0][1].im);
const wr = wordMean(LEAN, 3, 1, RHO, 14), ws = wordMean(LEAN, 3, 1, SIGMA, 14);
check('summing n·tr(WρW*) over first-absorbing words up to length 14 gives mean 1 for ρ and 2 for σ (total mass 1)', close(wr.mean, 1, 1e-12) && close(ws.mean, 2, 1e-12) && close(wr.mass, 1, 1e-12) && close(ws.mass, 1, 1e-12), `${wr.mean} ${ws.mean}`);
check('…and the page reports E(ρ) = 1 with the conjugate σ at 2, all mass absorbed at 0 for ρ', close(i.mean, 1, 1e-12) && close(i.meanConj, 2, 1e-12) && close(i.p0, 1, 1e-12) && Math.abs(i.rem) < 1e-14 && /1\.000 与 2\.000/.test(await text('roNote')));
await preset('conj'); i = await info();
check('conj preset: σ itself has mean 2, every bit absorbed at M = 3 at time 2', close(i.mean, 2, 1e-12) && close(i.pM, 1, 1e-12) && close(i.absM[2], 1, 1e-12) && close(i.meanConj, 1, 1e-12));

/* ---------- Lean's pair beyond the frozen instance ---------- */
let closedOK = true, closedBad = [];
for (const [M, k] of [[4, 1], [4, 2], [5, 3], [8, 4], [12, 7]]) {
  await setRange('mIn', M); await setRange('kIn', k); await setRange('phIn', 90); const x = await info();
  const want = k === 1 ? 1 : M - k + 2, wantC = M - k, ind = walk(LEAN, M, k, RHO).mean;
  if (!close(x.mean, want, 1e-12) || !close(x.meanConj, wantC, 1e-12) || !close(ind, want, 1e-12)) { closedOK = false; closedBad.push(`${M},${k}: ${x.mean}/${x.meanConj}`); }
}
check('for Lean’s pair ρ has mean M − k + 2 (1 at k = 1) and σ has M − k, for (M, k) = (4, 1), (4, 2), (5, 3), (8, 4), (12, 7)', closedOK, closedBad.join(' '));

/* ---------- every pair: the page's walk against an independent walk ---------- */
let walkOK = true, walkBad = [];
for (const p of ['long', 'fair', 'complex', 'real']) {
  await preset(p); const x = await info(), P = pairOfInfo(x), W = walk(P, x.M, x.k, fromFlat(x.rho));
  const ser = x.abs0.every((a, t) => { const w = W.series[t] || [0, 0]; return t === 0 || (close(a, w[0], 1e-10) && close(x.absM[t], w[1], 1e-10)); });
  if (!close(x.mean, W.mean, 1e-9) || !close(x.p0, W.p0, 1e-10) || !close(x.pM, W.pM, 1e-10) || !ser || normErr(P) > 1e-12) { walkOK = false; walkBad.push(p); }
}
check('long, fair, complex and real presets: mean, P(0), P(M) and the absorption series match an independent walk, and L*L + R*R = I', walkOK, walkBad.join(' '));
await preset('fair'); i = await info();
check('fair coin: mean k(M − k) = 8, P(0) = (M − k)/M, A_k = k(M − k)·I, all three gaps 0 and the form holds', close(i.mean, 8, 1e-9) && close(i.p0, 4 / 6, 1e-10) && i.A.every((A, q) => close(A[0], (q + 1) * (6 - q - 1), 1e-9) && close(A[6], (q + 1) * (6 - q - 1), 1e-9) && Math.abs(A[2]) < 1e-9 && Math.abs(A[3]) < 1e-9) && i.fits && /成立/.test(await text('ro5')));

/* ---------- the hitting-time operators and the three gaps ---------- */
let opOK = true, opBad = [];
for (const p of ['lean', 'long', 'complex', 'real']) {
  await preset(p); const x = await info(), P = pairOfInfo(x), M = x.M;
  for (let q = 1; q < M; q++) {
    const A = x.A[q - 1], o = opFromMeans(P, M, q);
    if (!close(A[0], o.a00, 1e-8) || !close(A[6], o.a11, 1e-8) || !close(A[2], o.re, 1e-8) || !close(A[3], o.im, 1e-8)) { opOK = false; opBad.push(`${p} k=${q}`); }
  }
  for (let q = 1; q < M; q++) {
    const A = x.A[q - 1], B = x.A[M - q - 1];
    if (!close(x.gaps.im[q - 1], A[3], 1e-12) || !close(x.gaps.refl[q - 1], A[0] - B[6], 1e-12) || !close(x.gaps.anti[q - 1], A[2] + B[2], 1e-12)) { opOK = false; opBad.push(`${p} gap ${q}`); }
  }
}
check('lean, long, complex, real: every A_k entry equals what walk means of the six Bloch-axis states give, and the gaps are Im A₀₁, A₀₀ − A′₁₁, Re A₀₁ + Re A′₀₁', opOK, opBad.join(' '));
await preset('lean'); i = await info();
check('Lean’s pair at M = 3: A₁ = [[3/2, i/2], [−i/2, 3/2]], A₂ = [[2, −i], [i, 2]], so Im A₀₁ ≠ 0 and the reflection gap is ∓1/2', close(i.A[0][0], 1.5, 1e-12) && close(i.A[0][3], 0.5, 1e-12) && close(i.A[1][0], 2, 1e-12) && close(i.A[1][3], -1, 1e-12) && close(i.gaps.refl[0], -0.5, 1e-12) && !i.fits);
await preset('complex'); i = await info();
let ind = walk(pairOfInfo(i), i.M, i.k, blochRho([i.bloch[0], -i.bloch[1], i.bloch[2]])).mean;
check('complex preset: the conjugate state’s mean differs (independent walk agrees), and Im A₀₁ is nonzero at every k', close(i.meanConj, ind, 1e-9) && Math.abs(i.mean - i.meanConj) > 0.1 && i.gaps.im.every((g) => Math.abs(g) > 1e-3), `${i.mean.toFixed(4)} vs ${i.meanConj.toFixed(4)}`);
await preset('real'); i = await info();
check('real preset: real L and R, Im A₀₁ = 0 and the conjugate has the same mean, yet a reflection gap is nonzero (page numbers)', i.L.filter((_, n) => n % 2).every((z) => z === 0) && i.R.filter((_, n) => n % 2).every((z) => z === 0) && i.gaps.im.every((g) => Math.abs(g) < 1e-9) && close(i.mean, i.meanConj, 1e-9) && i.gapMax[1] > 0.1 && !i.fits && /反射等式不成立/.test(await text('roNote')));

/* ---------- the initial state and the Bloch ball ---------- */
await setRange('thIn', 50); await setRange('phIn', 200); await setRange('rIn', 0.6); i = await info();
const th = 50 * Math.PI / 180, ph = 200 * Math.PI / 180, bx = [0.6 * Math.sin(th) * Math.cos(ph), 0.6 * Math.sin(th) * Math.sin(ph), 0.6 * Math.cos(th)], R0 = blochRho(bx), Rp = fromFlat(i.rho);
check('θ, φ and r set ρ = (I + r·n·σ)/2, and the page’s mean equals both the independent walk and tr(A_k ρ)', [0, 1].every((a) => [0, 1].every((b) => close(Rp[a][b].re, R0[a][b].re, 1e-12) && close(Rp[a][b].im, R0[a][b].im, 1e-12))) && close(i.mean, walk(pairOfInfo(i), i.M, i.k, R0).mean, 1e-9) && close(i.eOp, i.mean, 1e-8) && (await state()).preset === null);
check('the sphere colouring spans the mean over pure states: E(±y) lie within [eMin, eMax] and eMax − eMin ≥ |E(+y) − E(−y)|', (() => { const P = pairOfInfo(i), a = walk(P, i.M, i.k, blochRho([0, 1, 0])).mean, b = walk(P, i.M, i.k, blochRho([0, -1, 0])).mean; return a >= i.eMin - 1e-9 && a <= i.eMax + 1e-9 && b >= i.eMin - 1e-9 && b <= i.eMax + 1e-9 && i.eMax - i.eMin >= Math.abs(a - b) - 1e-9; })());

/* ---------- controls ---------- */
await preset('complex'); const seed0 = (await state()).seed, L0 = (await info()).L;
await click('#redraw'); i = await info();
check('redraw draws a new normalized random pair and marks the settings custom', (await state()).seed !== seed0 && i.L.some((z, n) => z !== L0[n]) && normErr(pairOfInfo(i)) < 1e-12 && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await click('[data-pair="fair"]');
check('pair chips switch the pair', (await info()).pair === 'fair' && (await D(() => document.querySelector('[data-pair="fair"]').getAttribute('aria-pressed'))) === 'true');
await setRange('mIn', 4); await setRange('kIn', 3); await setRange('mIn', 3);
check('lowering M clamps k to M − 1', (await info()).k === 2 && (await D(() => document.getElementById('kIn').max)) === '2');
for (const p of ['lean', 'conj', 'long', 'fair', 'complex', 'real']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }
await preset('long'); i = await info();
check('the rail marks t = 0 and the end; long preset ends at t = 6 with all mass at M', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 't = 0 | t = 6' && i.TV === 6 && close(i.pM, 1, 1e-12));
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ advances one time step and marks the settings custom', (await state()).t === 1 && (await state()).preset === null);
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await state()).t === i.TV && (await state()).playing === false);
await preset('lean'); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing to the end reports the absorption probabilities and both means', await waitToast(/落到 0 的概率 1\.000.*平均吸收时间 1\.000.*共轭态是 2\.000/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
const lit = await D(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'real']) {
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
check('English title', (await D(() => document.title)).startsWith('OQW//RUIN · The quantum gambler’s mean hitting time needs Im ρ₀₁'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['jacq-lardizabal-2017-oqw-gambler-mean-hitting-time-form.md', 'D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.lean', 'Blueprint/D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.md', 'Library/Observer/jacqlardizabal2017oqwhalfline.md', 'doi.org/10.1007/s10955-017-1876-x', 'arxiv.org/abs/1701.08400'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="oqw-ruin"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.OQ_DEBUG && OQ_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'oqw-ruin');

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
