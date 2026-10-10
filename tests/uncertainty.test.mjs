#!/usr/bin/env node
// Browser regression suite for viz/uncertainty (Playwright + Chromium with software WebGL).
//   node tests/uncertainty.test.mjs
// Reads page state through the read-only window.UN_DEBUG probe and checks it against an independent implementation: closed forms
// for Pauli observables on the Bloch ball, dense spin matrices built from J₊ = √((j − m)(j + m + 1)), a direct eigenvector check of
// the coherent state, the defining overlaps of mutually unbiased bases, and entropies recomputed from the page's states.
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
  const start = await page.evaluate(() => UN_DEBUG.frames());
  await page.waitForFunction((f0) => !UN_DEBUG.pending() && UN_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => UN_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => UN_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => UN_DEBUG.info());
const state = () => D(() => UN_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => UN_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => UN_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

// --- independent implementation
const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const crs = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
// Pauli observables A = a·σ, B = b·σ in ρ = (I + r·σ)/2: tr ρ(a·σ)(b·σ) = a·b + i (a×b)·r
const qubitClosed = (a, b, r) => {
  const ar = dot(a, r), br = dot(b, r), ab = crs(a, b), r2 = dot(r, r);
  return { varA: 1 - ar * ar, varB: 1 - br * br, cov: dot(a, b) - ar * br, comm: dot(ab, r), G: dot(ab, ab) * (1 - r2) };
};
// complex numbers as [re, im]; dense matrices as arrays of rows
const cm = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const conj = (a) => [a[0], -a[1]];
function spinMatrices(j) {   // basis m = j, j − 1, …, −j; ⟨m + 1|J₊|m⟩ = √((j − m)(j + m + 1))
  const d = Math.round(2 * j + 1), ms = Array.from({ length: d }, (_, k) => j - k), zero = () => Array.from({ length: d }, () => Array.from({ length: d }, () => [0, 0]));
  const Jp = zero(); for (let k = 1; k < d; k++) Jp[k - 1][k] = [Math.sqrt((j - ms[k]) * (j + ms[k] + 1)), 0];
  const Jm = zero(); for (let a = 0; a < d; a++) for (let b = 0; b < d; b++) Jm[a][b] = conj(Jp[b][a]);
  const Jx = zero(), Jy = zero(), Jz = zero();
  for (let a = 0; a < d; a++) for (let b = 0; b < d; b++) {
    Jx[a][b] = [(Jp[a][b][0] + Jm[a][b][0]) / 2, (Jp[a][b][1] + Jm[a][b][1]) / 2];
    const diff = [Jp[a][b][0] - Jm[a][b][0], Jp[a][b][1] - Jm[a][b][1]]; Jy[a][b] = [diff[1] / 2, -diff[0] / 2];   // (J₊ − J₋)/2i
  }
  for (let k = 0; k < d; k++) Jz[k][k] = [ms[k], 0];
  return { d, ms, Jx, Jy, Jz };
}
const apply = (M, v) => M.map((row) => row.reduce((s, x, k) => { const p = cm(x, v[k]); return [s[0] + p[0], s[1] + p[1]]; }, [0, 0]));
const ip = (a, b) => a.reduce((s, x, k) => { const p = cm(conj(x), b[k]); return [s[0] + p[0], s[1] + p[1]]; }, [0, 0]);   // ⟨a|b⟩
const vecOf = (o) => o.re.map((x, k) => [x, o.im[k]]);
function ledgerDense(psi, A, B) {
  const Ap = apply(A, psi), Bp = apply(B, psi), ea = ip(psi, Ap)[0], eb = ip(psi, Bp)[0];
  const u = Ap.map((x, k) => [x[0] - ea * psi[k][0], x[1] - ea * psi[k][1]]), v = Bp.map((x, k) => [x[0] - eb * psi[k][0], x[1] - eb * psi[k][1]]);
  const uu = ip(u, u)[0], vv = ip(v, v)[0], uv = ip(u, v);
  return { varA: uu, varB: vv, cov: uv[0], comm: uv[1], G: uu * vv - uv[0] ** 2 - uv[1] ** 2 };
}
const log2 = (x) => Math.log(x) / Math.LN2;
const Hbits = (p) => p.reduce((s, x) => s - (x > 1e-300 ? x * log2(x) : 0), 0);
const over = (e, f) => { const z = ip(vecOf(e), vecOf(f)); return z[0] * z[0] + z[1] * z[1]; };
function basesError(B, d) {   // max deviation from |⟨e|f⟩|² = δ within a basis and 1/d across bases
  let worst = 0;
  for (let a = 0; a < B.length; a++) for (let b = 0; b < B.length; b++) for (let i = 0; i < d; i++) for (let k = 0; k < d; k++) {
    const want = a === b ? (i === k ? 1 : 0) : 1 / d; worst = Math.max(worst, Math.abs(over(B[a][i], B[b][k]) - want));
  }
  return worst;
}
const probsPure = (B, psi) => B.map((basis) => basis.map((e) => { const z = ip(vecOf(e), vecOf(psi)); return z[0] * z[0] + z[1] * z[1]; }));
const maxAbs = (xs) => xs.reduce((m, x) => Math.max(m, Math.abs(x)), 0);

await page.goto(origin + BASE + 'viz/uncertainty/');
await page.waitForFunction(() => window.UN_DEBUG && UN_DEBUG.frames() > 3, null, { timeout: 120000 });
let i = await info();
check('opens on one-axis twisting of spin 5 and plays', i.mode === 'spin' && i.j === 5 && (await state()).playing === true);
await pause();

// --- qubit
await preset('pure'); i = await info();
const dirOf = (th, ph) => [Math.sin(th * Math.PI / 180) * Math.cos(ph * Math.PI / 180), Math.sin(th * Math.PI / 180) * Math.sin(ph * Math.PI / 180), Math.cos(th * Math.PI / 180)];
const qubitOK = (j) => { const c = qubitClosed(j.a, j.b, j.r), b0 = [Math.cos(j.alpha * Math.PI / 180), Math.sin(j.alpha * Math.PI / 180), 0], r0 = dirOf(j.theta, j.phi).map((x) => x * (1 - j.frac));
  return maxAbs([j.varA - c.varA, j.varB - c.varB, j.cov - c.cov, j.comm - c.comm, j.G - c.G, j.Gformula - c.G, ...j.b.map((x, k) => x - b0[k]), ...j.r.map((x, k) => x - r0[k]), j.a[0] - 1, j.a[1], j.a[2]]) < 1e-12; };
check('pure qubit: variances, covariance, commutator term and G match the Pauli closed forms', qubitOK(i), `G ${i.G.toExponential(1)}`);
check('…the pure-state ledger closes with G = 0: ΔA²ΔB² = cov² + c² (Robertson–Schrödinger is an equality)', Math.abs(i.G) < 1e-12 && Math.abs(i.varA * i.varB - i.cov ** 2 - i.comm ** 2) < 1e-12);
let allPure = true, tried = 0;
for (const [al, th, ph] of [[30, 100, 200], [150, 20, 75], [5, 170, 330], [90, 90, 0], [120, 45, 260]]) { await setRange('alpha', al); await setRange('theta', th); await setRange('phi', ph); const j = await info(); tried++; if (!(qubitOK(j) && Math.abs(j.G) < 1e-12 && j.s === 1)) allPure = false; }
check(`…${tried} more pure states and angles: G = 0 every time, closed forms hold`, allPure && (await state()).preset === null);
await preset('mixed'); await setFrac(0.5); i = await info();
check('mixed qubit at |r| = 1/2 with 60° between a and b: G = |a×b|²(1 − |r|²) = 3/4 · 3/4 = 0.5625', qubitOK(i) && Math.abs(i.s - 0.5) < 1e-12 && Math.abs(i.G - 0.5625) < 1e-12, i.G.toFixed(12));
check('…ΔA²ΔB² = cov² + c² + G to 10⁻¹²', Math.abs(i.varA * i.varB - i.cov ** 2 - i.comm ** 2 - i.G) < 1e-12);
check('…mixed-state Robertson ‖u‖·‖v‖ ≥ ½|tr ρ[A, B]| holds and the readout shows both sides', Math.sqrt(i.varA * i.varB) >= Math.abs(i.comm) && /≥/.test(await text('ro5')) && (await text('ro5')).includes(Math.abs(i.comm).toFixed(6)));
let sweepOK = true; for (const f of [0, 0.25, 0.75, 1]) { await setFrac(f); const j = await info(); if (!qubitOK(j)) sweepOK = false; }
await setFrac(1); i = await info();
check('…along the whole rail the closed forms hold; at |r| = 0 the commutator term is 0 and G = |a×b|² = 3/4', sweepOK && Math.abs(i.comm) < 1e-15 && Math.abs(i.G - 0.75) < 1e-12 && Math.abs(i.varA * i.varB - 1) < 1e-12);

// --- spin j
await preset('coherent'); i = await info();
const S5 = spinMatrices(5), psi0 = vecOf(i.psi), Jxpsi = apply(S5.Jx, psi0);
check('spin 5, μ = 0: the page state is the +5 eigenvector of Jx built independently, normalized', Math.abs(ip(psi0, psi0)[0] - 1) < 1e-12 && maxAbs(Jxpsi.flatMap((x, k) => [x[0] - 5 * psi0[k][0], x[1] - 5 * psi0[k][1]])) < 1e-10);
check('…ΔJy² = ΔJz² = j/2, c = ⟨Jx⟩/2 = 5/2, cov = G = 0: Robertson is an equality', Math.abs(i.varA - 2.5) < 1e-10 && Math.abs(i.varB - 2.5) < 1e-10 && Math.abs(i.comm - 2.5) < 1e-10 && Math.abs(i.cov) < 1e-10 && Math.abs(i.G) < 1e-9);
check('…the Husimi maximum on the grid is close to 1 (a coherent state)', i.qmax > 0.99 && i.qmax <= 1 + 1e-12, i.qmax.toFixed(4));
let spinOK = true; const spinDetail = [];
for (const f of [0.1, 0.3, 0.5, 0.8]) {
  await setFrac(f); const j = await info(), mu = Math.PI * f;
  const tw = psi0.map((x, k) => cm(x, [Math.cos(-mu * S5.ms[k] ** 2 / 2), Math.sin(-mu * S5.ms[k] ** 2 / 2)])), pv = vecOf(j.psi);
  const L = ledgerDense(tw, S5.Jy, S5.Jz);
  const e = maxAbs([...pv.flatMap((x, k) => [x[0] - tw[k][0], x[1] - tw[k][1]]), j.varA - L.varA, j.varB - L.varB, j.cov - L.cov, j.comm - L.comm, j.G - L.G]);
  spinDetail.push(e.toExponential(0)); if (!(e < 1e-9 && L.G > -1e-9 && Math.abs(L.varA * L.varB - L.cov ** 2 - L.comm ** 2 - L.G) < 1e-9)) spinOK = false;
}
check('…twisted states at μ = 0.1π … 0.8π equal e^(−iμm²/2)ψ₀ and their ledgers match dense matrices', spinOK, spinDetail.join(' '));
await setFrac(0.1); const early = await info(); await setFrac(0.5); const late = await info();
check('…small twist moves the balance into the covariance; larger twist moves it into G', early.cov ** 2 > early.G && late.G > late.cov ** 2 && late.G > late.comm ** 2, `μ = 0.1π: cov² ${(early.cov ** 2).toFixed(2)} G ${early.G.toFixed(2)} · μ = 0.5π: G ${late.G.toFixed(2)}`);
await preset('cat'); i = await info();
check('cat state j = 5, μ = π: c = cov = 0 and G = ΔJy²ΔJz² = 6.25', Math.abs(i.comm) < 1e-9 && Math.abs(i.cov) < 1e-9 && Math.abs(i.G - 6.25) < 1e-9 && Math.abs(i.mu - Math.PI) < 1e-12);
check('…Q(+x) = |⟨+x|ψ⟩|² = ½ for the cat, so the grid maximum is just below ½', i.qmax > 0.45 && i.qmax <= 0.5 + 1e-12, i.qmax.toFixed(4));
check('…the readout says the bulk is booked in the Gram remainder', /Gram/.test(await text('roNote')));
await setRange('jj', 1); i = await info();
check('spin ½: G = 0 at every twist (two dimensions again)', i.j === 0.5 && i.curveMaxG < 1e-12 && i.curveMinG > -1e-12 && (await state()).preset === null);

// --- mutually unbiased bases
await preset('mub5'); await setFrac(0.3); i = await info();
for (const d of [2, 3, 5, 7]) {
  await click(`#dChips [data-d="${d}"]`); await setFrac(0.3); const j = await info(), B = await D(() => UN_DEBUG.bases());
  check(`d = ${d}: ${d + 1} bases, orthonormal and pairwise unbiased (|⟨e|f⟩|² = 1/${d})`, j.d === d && B.length === d + 1 && B.every((b) => b.length === d) && basesError(B, d) < 1e-12, basesError(B, d).toExponential(1));
  const w = j.w, pp = probsPure(B, j.psi).map((p) => p.map((x) => (1 - w) * x + w / d)), P = (1 - w) ** 2 + (2 * w - w * w) / d;
  const coll = pp.reduce((s, p) => s + p.reduce((a, x) => a + x * x, 0), 0), Hs = pp.reduce((s, p) => s + Hbits(p), 0), bound = (d + 1) * log2((d + 1) / (1 + P));
  check(`…probabilities of ρ = 0.7|ψ⟩⟨ψ| + 0.3·I/${d} match, Σp² = 1 + tr ρ² (collision conservation)`, maxAbs(pp.flat().map((x, k) => x - j.probs.flat()[k])) < 1e-12 && Math.abs(coll - 1 - P) < 1e-12 && Math.abs(j.purity - P) < 1e-12 && Math.abs(j.collision - coll) < 1e-12, `${coll.toFixed(9)} = 1 + ${P.toFixed(9)}`);
  check(`…entropy sum ≥ collision-entropy sum ≥ (d + 1)log₂((d + 1)/(1 + tr ρ²)), recomputed`, Math.abs(j.Hsum - Hs) < 1e-10 && Math.abs(j.bound - bound) < 1e-12 && j.Hsum >= j.cSum - 1e-12 && j.cSum >= j.bound - 1e-12, `${bound.toFixed(4)} ≤ ${j.cSum.toFixed(4)} ≤ ${Hs.toFixed(4)}`);
}
await setFrac(1); i = await info();
check('…fully mixed (w = 1): all three equal (d + 1)log₂ d, the bound is attained', Math.abs(i.Hsum - 8 * log2(7)) < 1e-9 && Math.abs(i.bound - 8 * log2(7)) < 1e-9 && Math.abs(i.cSum - 8 * log2(7)) < 1e-9);
const psiA = (await info()).psi; await page.keyboard.press('r'); await settle(); const psiB = (await info()).psi;
check('R draws another random state', psiA.re.some((x, k) => Math.abs(x - psiB.re[k]) > 1e-6) && (await state()).preset === null);

// --- the least entropy sum
const huntCheck = async (d) => {
  await setFrac(1); const j = await info(), B = await D(() => UN_DEBUG.bases()), pv = probsPure(B, j.bestState), H = pv.reduce((s, p) => s + Hbits(p), 0), pb = (d + 1) * log2((d + 1) / 2);
  return { j, H, pb, ok: basesError(B, d) < 1e-12 && Math.abs(H - j.best) < 1e-9 && Math.abs(j.pureBound - pb) < 1e-12 && j.best >= pb - 1e-12 && j.best <= d * log2(d) + 1e-9 };
};
await preset('tight3'); let h = await huntCheck(3);
check('d = 3: the best state found has entropy sum 4 bits (recomputed), equal to the frozen bound 4·log₂2', h.ok && Math.abs(h.H - 4) < 1e-6 && Math.abs(h.pb - 4) < 1e-12, h.H.toFixed(10));
const wpr = probsPure(await D(() => UN_DEBUG.bases()), h.j.witness.psi);
check('…(|0⟩ − |1⟩)/√2 gives (½, ½, 0) in all four bases, 4 bits exactly', wpr.every((p) => p.filter((x) => Math.abs(x - 0.5) < 1e-12).length === 2 && p.filter((x) => Math.abs(x) < 1e-12).length === 1) && Math.abs(h.j.witness.H - 4) < 1e-12);
await setFrac(0.5); const mid = await info();
check('…half way the best so far is no better than the final best, and the snapshots are monotone', mid.best >= h.j.best - 1e-15 && mid.rep < h.j.R && mid.it < h.j.it);
for (const d of [2, 5, 7]) {
  await click(`#dChips [data-d="${d}"]`); h = await huntCheck(d);
  const extra = d === 2 ? Math.abs(h.H - 2) < 1e-6 : h.H > h.pb + 0.5;
  check(`d = ${d}: the best state’s entropy sum (recomputed) lies between the bound ${h.pb.toFixed(4)} and d·log₂d${d === 2 ? ', and equals 2 bits' : ', with a gap above the bound'}`, h.ok && extra, h.H.toFixed(6));
}
await preset('hunt5'); await setFrac(1);
check('…the d = 5 readout calls the result a numerical search, not a proof', /数值搜索/.test(await text('roNote')));

// --- controls, keys, presets
for (const name of ['pure', 'mixed', 'coherent', 'twist', 'cat', 'mub5', 'tight3', 'hunt5']) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await click('#modeChips [data-mode="qubit"]');
check('the model chips switch to the qubit, show its three sliders and mark the settings custom', (await info()).mode === 'qubit' && (await visible('alphaField')) && (await visible('thetaField')) && (await visible('phiField')) && !(await visible('jField')) && !(await visible('dField')) && (await state()).preset === null);
await click('#modeChips [data-mode="mub"]');
check('…and the entropy mode shows only the dimension chips', (await visible('dField')) && !(await visible('alphaField')) && !(await visible('jField')));
await setFrac(0); await page.keyboard.press('ArrowRight'); await settle();
check('→ moves one step along the rail', Math.abs((await info()).frac - 0.01) < 1e-12);
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await info()).frac === 1 && (await state()).playing === false);

// --- play and toasts
await preset('mixed'); await setFrac(0.97); await click('#play');
check('the qubit toast fires at |r| = 0', await waitToast(/\|r\| = 0/));
await pause();
await preset('cat'); await setFrac(0.97); await click('#play');
check('the spin toast fires at μ = π', await waitToast(/μ = π/));
await pause();
await preset('mub5'); await setFrac(0.97); await click('#play');
check('the entropy toast reports the bound attained at w = 1', await waitToast(/w = 1/));
await pause();
await preset('tight3'); await setFrac(0.97); await click('#play');
check('the d = 3 search toast reports the bound attained', await waitToast(/等于冻结下界/));
await pause();
await preset('twist'); await setFrac(0.2); await click('#play'); await waitFrames(12); const p1 = (await state()).nowFrac; await pause();
check('play advances along the rail', p1 > 0.2);
await click('#rev'); await waitFrames(12); const p2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', p2 < p1);
await page.click('#rev'); await pause();
await page.focus('#jj'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await click('#modeChips [data-mode="qubit"]');
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags) && /a × b/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('UNCERTAINTY//LEDGER · Where the price of non-commuting is booked'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
await page.keyboard.press('Escape'); await page.waitForFunction(() => document.getElementById('drawer').hidden === true, null, { timeout: 10000 }).catch(() => {});
check('Esc closes the drawer', (await D(() => document.getElementById('drawer').hidden)) === true);
await page.waitForFunction(() => document.activeElement?.id === 'infoBtn', null, { timeout: 10000 }).catch(() => {});
check('focus returns to the drawer button', (await D(() => document.activeElement?.id)) === 'infoBtn');

// --- index round trip
const live = readRegistry().visualizations.filter(v => v.status === 'live').length;
await page.click('.crumb'); await page.waitForLoadState('load');
await page.waitForFunction((n) => document.querySelectorAll('.card').length >= n, live, { timeout: 30000 }).catch(() => {});
check('language choice carries to the index', (await D(() => document.documentElement.dataset.lang)) === 'en');
check('index lists every live visualization', (await D(() => document.querySelectorAll('.card').length)) === live, `live ${live}`);
await page.click('.card:has(a[href*="uncertainty"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.UN_DEBUG && UN_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'uncertainty');

// --- narrow layouts in both languages
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
