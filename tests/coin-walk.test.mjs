#!/usr/bin/env node
// Browser regression suite for viz/coin-walk (Playwright + Chromium with software WebGL).
//   node tests/coin-walk.test.mjs
// Reads page state through the read-only window.CW_DEBUG probe and checks it against independent implementations: Lean's
// hadamardStep run in complex arithmetic, the reflection identities of walk_reflection, and the largest product overlap of the
// single-photon vector found by coordinate ascent over product states (a different method from the page's stationary equations).
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
  const start = await page.evaluate(() => CW_DEBUG.frames());
  await page.waitForFunction((f0) => !CW_DEBUG.pending() && CW_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D2(() => CW_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D2((t) => CW_DEBUG.setT(t), t); await settle(); };
const info = () => D2(() => CW_DEBUG.info());
const state = () => D2(() => CW_DEBUG.state());
const text = (id) => D2((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D2(() => CW_DEBUG.frames()); await page.waitForFunction((t) => CW_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */

/* complex numbers as [re, im] */
const cadd = (a, b) => [a[0] + b[0], a[1] + b[1]], csub = (a, b) => [a[0] - b[0], a[1] - b[1]], cscale = (a, k) => [a[0] * k, a[1] * k], n2 = (a) => a[0] * a[0] + a[1] * a[1];
/* Lean's hadamardStep: (0, x) ← (ψ(0, x+1) + ψ(1, x+1))/√2, (1, x) ← (ψ(0, x−1) − ψ(1, x−1))/√2; walkState starts c at site 0 */
function walkC(P, n, c) {
  let s0 = Array.from({ length: P }, () => [0, 0]), s1 = Array.from({ length: P }, () => [0, 0]); s0[0] = c[0]; s1[0] = c[1];
  for (let k = 0; k < n; k++) {
    const t0 = [], t1 = [];
    for (let x = 0; x < P; x++) { const r = (x + 1) % P, l = (x - 1 + P) % P; t0.push(cscale(cadd(s0[r], s1[r]), Math.SQRT1_2)); t1.push(cscale(csub(s0[l], s1[l]), Math.SQRT1_2)); }
    s0 = t0; s1 = t1;
  }
  return [...s0, ...s1];
}
const coin = (th, ph) => [[Math.cos(th / 2), 0], [Math.sin(th / 2) * Math.cos(ph), Math.sin(th / 2) * Math.sin(ph)]];
/* max over unit product states of (Σ_k c_k y_k Π_{j≠k} x_j)², c_k = |λ_k| ≥ 0, by coordinate ascent from several starts */
function gAscent(p) {
  const c = p.map((v) => Math.sqrt(Math.max(0, v))).filter((v) => v > 1e-14), N = c.length; if (!N) return 0;
  let best = Math.max(...c) ** 2;
  const starts = [c.map(() => 0.3), c.map(() => 0.05), ...c.map((_, k) => c.map((_, j) => (j === k ? 1.5 : 0.05)))];
  for (const th0 of starts) {
    const th = th0.slice();
    for (let sweep = 0; sweep < 4000; sweep++) {
      let ch = 0;
      for (let k = 0; k < N; k++) {
        let A = 0, prodOthers = 1;
        for (let j = 0; j < N; j++) if (j !== k) prodOthers *= Math.cos(th[j]);
        for (let m = 0; m < N; m++) { if (m === k) continue; let pr = c[m] * Math.sin(th[m]); for (let j = 0; j < N; j++) if (j !== k && j !== m) pr *= Math.cos(th[j]); A += pr; }
        const nt = Math.atan2(c[k] * prodOthers, A); ch = Math.max(ch, Math.abs(nt - th[k])); th[k] = nt;
      }
      if (ch < 1e-14) break;
    }
    let F = 0; for (let k = 0; k < N; k++) { let pr = c[k] * Math.sin(th[k]); for (let j = 0; j < N; j++) if (j !== k) pr *= Math.cos(th[j]); F += pr; }
    best = Math.max(best, F * F);
  }
  return best;
}
const STAR = [Math.PI / 2, Math.PI / 2];

await page.goto(`${origin}${BASE}viz/coin-walk/`);
await page.waitForFunction(() => window.CW_DEBUG && CW_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();
check('starts on the first preset (P = 8, coin |0⟩), playing from n = 0', st.preset === 'lean' && st.playing === true && i.P === 8 && i.th === 0 && i.ph === 0);
await pause(); await setT(0.5); i = await info();

/* ---------- the walk ---------- */
let maxErr = 0;
for (const [P, n] of [[1, 3], [2, 5], [3, 4], [8, 6], [11, 9], [16, 20]]) for (const [th, ph] of [[0, 0], STAR, [1.1, 2.3], [2.7, -0.4]]) {
  const ref = walkC(P, n, coin(th, ph)).map(n2), pg = await D2(([P, n, th, ph]) => CW_DEBUG.probs(P, n, th, ph), [P, n, th, ph]);
  maxErr = Math.max(maxErr, ...ref.map((v, k) => Math.abs(v - pg[k])));
}
check('the page’s mode probabilities equal |Lean’s hadamardStep run in complex arithmetic|² (6 circles × 4 coins)', maxErr < 1e-13, `max err ${maxErr}`);
let reflOK = true;
for (const [P, n] of [[1, 2], [5, 7], [8, 6], [9, 10], [16, 13]]) {
  const { u, w } = await D2(([P, n]) => CW_DEBUG.basis(P, n), [P, n]), sg = n % 2 ? -1 : 1;
  for (let x = 0; x < P; x++) { const mx = (P - x) % P; if (Math.abs(u[P + mx] + sg * w[x]) > 1e-12 || Math.abs(w[P + mx] - sg * u[x]) > 1e-12) reflOK = false; }
}
check('walk_reflection on the page’s basis walks: u(1, −x) = −(−1)ⁿ w(0, x) and w(1, −x) = (−1)ⁿ u(0, x)', reflOK);
check('total probability is 1 and c* splits every reflection pair evenly; pair sums agree with the coin’s', Math.abs(i.norm - 1) < 1e-12 && i.imbS < 1e-12 && i.sumDiff < 1e-12);

/* ---------- the overlap ---------- */
const rnd = ((a) => () => { a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; })(5);
const vecs = Array.from({ length: 40 }, () => { const N = 2 + Math.floor(rnd() * 7), v = Array.from({ length: N }, () => rnd() ** (rnd() < 0.5 ? 1 : 3)), s = v.reduce((a, b) => a + b, 0); return v.map((x) => x / s); });
const pageG = await D2((vs) => vs.map((v) => CW_DEBUG.gW(v)), vecs);
const gErr = Math.max(...vecs.map((v, k) => Math.abs(gAscent(v) - pageG[k])));
check('the page’s maximal overlap g agrees with coordinate ascent on 40 random single-photon vectors (to 10⁻⁹)', gErr < 1e-9, `max err ${gErr.toExponential(2)}`);
const two = await D2(() => [[0.3, 0.7], [0.5, 0.5], [0.91, 0.09]].map((v) => CW_DEBUG.gW(v)));
check('two modes: g = the larger probability (two_factor_max with no spectators)', Math.abs(two[0] - 0.7) < 1e-12 && Math.abs(two[1] - 0.5) < 1e-12 && Math.abs(two[2] - 0.91) < 1e-12);
const pw = walkC(8, 6, coin(...STAR)).map(n2), p0 = walkC(8, 6, coin(0, 0)).map(n2);
check('E_g at P = 8, n = 6: 0.5788 for c* and 0.4375 for |0⟩, by coordinate ascent on the test’s own walk', Math.abs(1 - gAscent(pw) - i.Es) < 1e-9 && Math.abs(1 - gAscent(p0) - i.Ec) < 1e-9 && i.Es.toFixed(4) === '0.5788' && i.Ec.toFixed(4) === '0.4375');

/* ---------- the theorem, sampled ---------- */
const sweep = await D2(() => { let worst = Infinity, count = 0; const coins = []; for (let a = 0; a <= 12; a++) for (let b = -12; b < 12; b++) coins.push([Math.PI * a / 12, Math.PI * b / 12]);
  for (let P = 1; P <= 10; P++) for (let n = 0; n <= 12; n++) { const es = 1 - CW_DEBUG.gW(CW_DEBUG.probs(P, n, Math.PI / 2, Math.PI / 2)); for (const [th, ph] of coins) { worst = Math.min(worst, es - (1 - CW_DEBUG.gW(CW_DEBUG.probs(P, n, th, ph)))); count++; } }
  return { worst, count }; });
check('E_g(coin) ≤ E_g(c*) for 312 coins at every P ≤ 10 and n ≤ 12 (page’s functions)', sweep.worst > -1e-12 && sweep.count === 40560, `min gap ${sweep.worst.toExponential(2)} over ${sweep.count}`);
let spot = Infinity;
for (const [P, n, th, ph] of [[3, 3, 0.4, 1.0], [5, 5, 1.2, -2.0], [6, 7, 2.2, 0.3], [7, 4, 0.9, 3.0], [4, 9, 1.7, 1.2]]) { const es = 1 - gAscent(walkC(P, n, coin(...STAR)).map(n2)), ec = 1 - gAscent(walkC(P, n, coin(th, ph)).map(n2)); spot = Math.min(spot, es - ec); }
check('…and for 5 coins with the test’s own walk and overlap', spot > -1e-9, `min gap ${spot.toExponential(2)}`);
check('the E_g-in-time curves keep the chosen coin and |0⟩ at or below c* for n ≤ 12', i.curveS.every((v, k) => v >= i.curveC[k] - 1e-12 && v >= i.curve0[k] - 1e-12) && i.curveS.length === 13);
check('the sphere grid’s largest E_g does not exceed c*', i.sphMax <= i.Es + 1e-12 && Math.abs(i.sphArg[0] - Math.PI / 2) < 0.2);
const sym = await D2(() => { let d = 0; for (const [th, ph] of [[0.3, 0.7], [1.2, 2.2], [2.4, 1.1], [1.57, 0.4]]) d = Math.max(d, Math.abs(CW_DEBUG.gW(CW_DEBUG.probs(8, 6, th, ph)) - CW_DEBUG.gW(CW_DEBUG.probs(8, 6, th, -ph)))); return d; });
check('E_g(θ, φ) = E_g(θ, −φ) (the page’s mirror argument)', sym < 1e-12);
check('readouts: P, modes, n, coin; E_g and the difference; pair imbalances', (await text('ro1')) === '8 · 16 · 6 · (0, 0)' && (await text('ro2')) === '0.4375 · 0.5788 · +0.1413' && (await text('ro3')) === '0.5000 · < 10⁻¹² · < 10⁻¹²');
check('the HUD states E_g = 0.4375 ≤ E_g(c*) = 0.5788', (await text('hudBig')) === 'P = 8 · n = 6 · E_g = 0.4375 ≤ E_g(c*) = 0.5788');

/* ---------- the other presets ---------- */
await preset('one'); await setT(0.5); i = await info();
check('P = 1: E_g(c*) = 1/2 at every step, and |0⟩ alternates between 0 and 1/2', i.curveS.every((v) => Math.abs(v - 0.5) < 1e-12) && i.curveC.every((v, k) => Math.abs(v - (k % 2 ? 0.5 : 0)) < 1e-12));
await preset('conj'); await setT(0.5); i = await info();
check('the conjugate coin has the same probabilities and the same E_g as c*', i.pc.every((v, k) => Math.abs(v - i.ps[k]) < 1e-12) && Math.abs(i.Ec - i.Es) < 1e-12);
await preset('interp'); await setT(0.5); i = await info();
const mono = i.merStar.slice(0, 61).every((v, k) => k === 0 || v >= i.merStar[k - 1] - 1e-12);
check('along c_θ = (cos θ/2, i sin θ/2), E_g does not decrease from θ = 0 to π/2 (121-point meridian)', mono && Math.abs(i.merStar[60] - i.Es) < 1e-12);
await preset('plus'); await setT(0.5); i = await info();
check('|+⟩ leaves pairs unbalanced (0.375) and falls below c*', Math.abs(i.imbC - 0.375) < 1e-12 && i.Ec < i.Es - 0.05);
await preset('big'); await setT(1); i = await info();
check('P = 16, 32 steps, generic coin: E_g stays at or below c* at every step', i.P === 16 && i.nmax === 32 && i.curveS.every((v, k) => v >= i.curveC[k] - 1e-12) && i.n === 32);

/* ---------- controls ---------- */
await preset('lean');
await D2(() => { const e = document.getElementById('pIn'); e.value = 5; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the P slider sets five sites and marks the settings custom', i.P === 5 && i.pc.length === 10 && (await state()).preset === null && /自定义/.test(await text('presetNote')));
await D2(() => { const e = document.getElementById('thIn'); e.value = 1.3; e.dispatchEvent(new Event('input')); }); await settle();
await D2(() => { const e = document.getElementById('phIn'); e.value = -0.7; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the θ and φ sliders set the coin', i.th === 1.3 && i.ph === -0.7 && (await text('thOut')) === '1.30' && (await text('phOut')) === '-0.70');
await click('#coinChips [data-coin="star"]'); i = await info();
check('the c* chip sets the coin to c*', Math.abs(i.th - Math.PI / 2) < 1e-12 && Math.abs(i.ph - Math.PI / 2) < 1e-12 && Math.abs(i.Ec - i.Es) < 1e-12 && (await D2(() => document.querySelector('#coinChips [aria-pressed="true"]').dataset.coin)) === 'star');
await setT(7 / 12); i = await info();
const w57 = walkC(5, 7, coin(...STAR)).map(n2), wrongPair = Math.max(...[0, 1, 2, 3, 4].map((x) => Math.abs(w57[x] - w57[5 + x])));
check('at P = 5, n = 7 the readout pairs (0, x) with (1, −x): c* is balanced there, though not on the pairs (0, x), (1, x)', i.P === 5 && i.n === 7 && i.imbS < 1e-12 && (await text('ro3')).split(' · ')[1] === '< 10⁻¹²' && wrongPair > 0.02, `(0, x), (1, x) imbalance ${wrongPair.toFixed(4)}`);

/* ---------- labels, rail, keys, playback ---------- */
const boxes = await D2(() => [...document.querySelectorAll('.side .lean')].map((b) => [b.className, b.querySelector('.ok').textContent, b.textContent]));
check('label boxes: two LEAN ✓, NUM, dossier ARGUED, page ARGUED (dashed), OPEN, LIT', boxes.map((b) => b[1]).join(' ') === 'LEAN ✓ LEAN ✓ NUM ARGUED ARGUED OPEN LIT' && /theory/.test(boxes[3][0]) && /page/.test(boxes[4][0]));
check('the LEAN boxes name the frozen declarations', boxes[0][2].includes('SymmetricCoinMaximalWalkEntanglement.result') && boxes[1][2].includes('pair_balancing') && boxes[1][2].includes('walk_reflection'));
check('the LIT box cites the arXiv DOI', boxes[6][2].includes('10.48550/arXiv.2603.24679'));
await preset('lean');
check('the rail marks n = 0 and n = 12', (await D2(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 'n = 0 | n = 12');
await setT(0); await D2(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await page.keyboard.press('ArrowRight'); await settle();
check('→ → advances two steps', (await info()).n === 2 && (await text('clock')) === 'n = 2');
await page.keyboard.press('ArrowLeft'); await settle();
check('← goes back one step', (await info()).n === 1);
await page.keyboard.press('e'); await settle();
check('E jumps to the last step and pauses', (await info()).n === 12 && (await state()).playing === false);
await page.keyboard.press(' '); await settle();
check('Space toggles playback', (await state()).playing === true);
await D2(() => document.querySelector('#speedChips [data-speed="2.5"]').click());
check('playing to the end reports that every time satisfies the inequality', await waitToast(/13 个时刻全部满足 E_g\(硬币\) ≤ E_g\(c\*\)/));
await pause(); await D2(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['side', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D2(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await setT(0.5);
const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels give E_g for c* and the coin, the basis poles and the circle', tags.includes('c* · E_g = 0.5788') && tags.includes('硬币 · E_g = 0.4375') && tags.includes('|0⟩') && tags.includes('8 个格点 · 第 6 步'), tags);
const lit = await D2(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
await D2(() => window.TRV_THUMB()); await settle();
check('the thumbnail state is the paused first preset at n = 6', (await state()).preset === 'lean' && (await state()).playing === false && (await info()).n === 6);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'big']) {
  await preset(p); await setT(0.5);
  const leftovers = await D2(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#coinChips [data-coin="plus"]');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D2(() => document.title)).startsWith('COIN//WALK · The symmetric coin maximizes the entanglement of the Hadamard walk on every circle'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D2(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D2(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['donkersloot-sondenheimer-sperling-2026-symmetric-coin-entanglement.md', 'D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.lean', 'Blueprint/D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.md', 'Library/Entropy/donkerslootsondenheimersperling2026walks.md', 'doi.org/10.48550/arXiv.2603.24679', 'arxiv.org/abs/2603.24679'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="coin-walk"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.CW_DEBUG && CW_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D2(() => document.body.dataset.vizId)) === 'coin-walk');

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
