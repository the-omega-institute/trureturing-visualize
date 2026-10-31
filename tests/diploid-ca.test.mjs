#!/usr/bin/env node
// Browser regression suite for viz/diploid-ca (Playwright + Chromium with software WebGL).
//   node tests/diploid-ca.test.mjs
// Reads page state through the read-only window.DP_DEBUG probe and checks it against independent implementations: the
// cylinder probabilities of the process on ℤ summed over every parent block in exact BigInt arithmetic, an exact Markov chain
// on a ring of five cells, the rules re-applied to the page's recorded coins, and the dossier's formulas.
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
  const start = await page.evaluate(() => DP_DEBUG.frames());
  await page.waitForFunction((f0) => !DP_DEBUG.pending() && DP_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D2(() => DP_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D2((t) => DP_DEBUG.setT(t), t); await settle(); };
const info = () => D2(() => DP_DEBUG.info());
const state = () => D2(() => DP_DEBUG.state());
const text = (id) => D2((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D2(() => DP_DEBUG.frames()); await page.waitForFunction((t) => DP_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */

const rbit = (r, x, y, z) => (r >> (4 * x + 2 * y + z)) & 1;
const fval = ([n, d]) => Number(n * 10n ** 15n / d) / 1e15;
/* the process on ℤ: the law of a block of length n at time t + 1 is the sum over all parent blocks of length n + 2 of the
   product of the cell-wise update probabilities; λ = a/b, start Bernoulli(c/e); numerators over one shared denominator */
function exactCyl(f, g, a, b, c, e, Tn) {
  let N = 2 * Tn + 3, den = BigInt(e) ** BigInt(N), dist = new Map();
  for (let s = 0; s < 1 << N; s++) { let num = 1n; for (let k = 0; k < N; k++) num *= (s >> k) & 1 ? BigInt(c) : BigInt(e - c); dist.set(s, num); }
  const res = { d: [], q: [] };
  const meas = () => { let dn = 0n, qn = 0n; for (const [s, v] of dist) { if (s & 1) dn += v; else if ((s >> 2) & 1) qn += v; } res.d.push([dn, den]); res.q.push([qn, den]); };
  meas();
  for (let t = 1; t <= Tn; t++) {
    const n = N - 2, nd = new Map();
    for (let bb = 0; bb < 1 << n; bb++) {
      let tot = 0n;
      for (const [s, v] of dist) { let w = 1n; for (let j = 0; j < n && w; j++) { const x = (s >> j) & 1, y = (s >> (j + 1)) & 1, z = (s >> (j + 2)) & 1, p1 = BigInt((b - a) * rbit(f, x, y, z) + a * rbit(g, x, y, z)); w *= (bb >> j) & 1 ? p1 : BigInt(b) - p1; } tot += w * v; }
      nd.set(bb, tot);
    }
    den *= BigInt(b) ** BigInt(n); dist = nd; N = n; meas();
  }
  return res;
}
/* the automaton on a ring of Lr cells as an exact Markov chain from the fair start; expected density at each step */
function ringExact(f, g, a, b, Lr, Tn) {
  const SZ = 1 << Lr; let dist = new Array(SZ).fill(1n), den = BigInt(SZ); const out = [];
  const pop = (s) => { let c = 0; for (let k = 0; k < Lr; k++) c += (s >> k) & 1; return c; };
  for (let t = 0; t <= Tn; t++) {
    if (t) {
      const nd = new Array(SZ).fill(0n);
      for (let s = 0; s < SZ; s++) for (let s2 = 0; s2 < SZ; s2++) { let w = 1n; for (let i = 0; i < Lr && w; i++) { const x = (s >> ((i - 1 + Lr) % Lr)) & 1, y = (s >> i) & 1, z = (s >> ((i + 1) % Lr)) & 1, p1 = BigInt((b - a) * rbit(f, x, y, z) + a * rbit(g, x, y, z)); w *= (s2 >> i) & 1 ? p1 : BigInt(b) - p1; } nd[s2] += dist[s] * w; }
      dist = nd; den *= BigInt(b) ** BigInt(Lr);
    }
    out.push([dist.reduce((acc, v, s) => acc + v * BigInt(pop(s)), 0n), den * BigInt(Lr)]);
  }
  return out;
}
const ratEq = ([n, d], p, q) => n * BigInt(q) === BigInt(p) * d;

await page.goto(`${origin}${BASE}viz/diploid-ca/`);
await page.waitForFunction(() => window.DP_DEBUG && DP_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();
check('starts on the Lean preset (10-245, λ = 0.3, fair start), playing from t = 0', st.preset === 'lean' && st.playing === true && i.rule === '10-245' && i.lam === 0.3 && i.p === 0.5);
await pause(); await setT(0.025); i = await info();

/* ---------- the theorem on ℤ, exactly ---------- */
const lams = [[0, 1], [3, 10], [1, 7], [1, 2], [9, 10], [1, 1]];
let allExact = true, allQ = true;
for (const [a, b] of lams) { const r = exactCyl(10, 245, a, b, 1, 2, 3); for (let t = 1; t <= 3; t++) { if (!ratEq(r.d[t], b + 2 * a, 4 * b)) allExact = false; } for (let t = 0; t <= 3; t++) if (!ratEq(r.q[t], 1, 4)) allQ = false; }
check('summing over all parent blocks in BigInt: d_t = 1/4 + λ/2 exactly for t = 1, 2, 3 at λ = 0, 3/10, 1/7, 1/2, 9/10, 1', allExact);
check('…and q_t = P(0 at i − 1, 1 at i + 1) = 1/4 exactly for t = 0 … 3', allQ);
const ex03 = exactCyl(10, 245, 3, 10, 1, 2, 3);
check('the page’s exact values on ℤ at λ = 0.3 agree with the BigInt ones to 10⁻¹² (d and q, t ≤ 3)', [0, 1, 2, 3].every((t) => Math.abs(i.exD[t] - fval(ex03.d[t])) < 1e-12 && Math.abs(i.exQ[t] - fval(ex03.q[t])) < 1e-12));
check('the page’s exact d_t stays 0.4 and q_t 1/4 through t = 8 (to 10⁻¹²), and d_0 = 1/2', i.exD.length === 9 && i.exD[0] === 0.5 && i.exD.slice(1).every((v) => Math.abs(v - 0.4) < 1e-12) && i.exQ.every((v) => Math.abs(v - 0.25) < 1e-12) && i.dev < 1e-12);
const pageCyl = await D2(() => [[0, 0.5], [0.13, 0.5], [0.77, 0.5], [1, 0.5]].map(([l, p]) => DP_DEBUG.cylinder('10-245', l, p, 6).d));
check('the page’s cylinder recursion gives 1/4 + λ/2 at λ = 0, 0.13, 0.77, 1 for t = 1 … 6', pageCyl.every((d, k) => d.slice(1).every((v) => Math.abs(v - (0.25 + [0, 0.13, 0.77, 1][k] / 2)) < 1e-12)));
check('readouts: λ · α · p; 1/4 + λ/2 and a deviation below 10⁻¹²; the Lean note', (await text('ro1')) === '0.3 · 0.4 · p = 0.5' && (await text('ro3')) === '0.4000 · < 10⁻¹²' && /1\/4 \+ λ\/2，这里是 0\.4000/.test(await text('roNote')));
check('the HUD and pills state d_t = 1/4 + λ/2 = 0.4000', (await text('hudBig')) === '10-245 · λ = 0.3 · d_t = 1/4 + λ/2 = 0.4000' && /10-245/.test(await text('pillA')) && /0\.4000/.test(await text('pillC')));

/* ---------- a ring of five cells (the page's own argument) ---------- */
const r5 = ringExact(10, 245, 3, 10, 5, 4), r6 = ringExact(10, 245, 1, 7, 6, 3);
check('an exact Markov chain on rings of 5 and 6 cells gives expected density exactly 1/4 + λ/2 for t ≥ 1 (λ = 3/10, 1/7)', r5.slice(1).every((x) => ratEq(x, 16, 40)) && r6.slice(1).every((x) => ratEq(x, 9, 28)) && ratEq(r5[0], 1, 2));

/* ---------- the page's ring ---------- */
const hist = await D2(() => ({ rows: Array.from({ length: DP_DEBUG.TMAX + 1 }, (_, t) => DP_DEBUG.row(t)), coins: Array.from({ length: DP_DEBUG.TMAX + 1 }, (_, t) => DP_DEBUG.coins(t)) }));
const L = hist.rows[0].length;
const follows = (rows, coins, f, g) => rows.every((r, t) => t === 0 || r.every((v, k) => v === rbit(coins[t][k] ? g : f, rows[t - 1][(k - 1 + L) % L], rows[t - 1][k], rows[t - 1][(k + 1) % L])));
check('every cell of the ring at every step is rule 10 or rule 245 of its parents, as its recorded coin says', L === 240 && hist.rows.length === 161 && follows(hist.rows, hist.coins, 10, 245));
const coinFrac = hist.coins.slice(1).flat().reduce((a, b) => a + b, 0) / (160 * L);
check('the coins choose rule 245 with frequency λ = 0.3 (within 4 standard deviations)', Math.abs(coinFrac - 0.3) < 4 * Math.sqrt(0.21 / (160 * L)), coinFrac.toFixed(4));
check('the ring densities and q fractions are those of the recorded rows', hist.rows.every((r, t) => Math.abs(i.ringD[t] - r.reduce((a, b) => a + b, 0) / L) < 1e-15 && Math.abs(i.ringQ[t] - r.filter((_, k) => !r[(k - 1 + L) % L] && r[(k + 1) % L]).length / L) < 1e-15));
check('the ring’s time average over t ≥ 20 is within 0.015 of 0.4', Math.abs(i.avg - 0.4) < 0.015, i.avg.toFixed(4));
check('the λ sweep: all 21 ring averages lie within 0.03 of 1/4 + λ/2', i.sweep.length === 21 && i.sweep.every(([l, v], k) => Math.abs(l - k / 20) < 1e-12 && Math.abs(v - (0.25 + l / 2)) < 0.03));
check('the readout at t = 4 shows the ring density and the exact 0.400000', i.t === 4 && (await text('ro2')) === `${i.dRing.toFixed(4)} · 0.400000`);

/* ---------- mean field ---------- */
check('mean field iterates d_{t+1} = λ + α d_t(1 − d_t) from d_0 = p', i.mf.length === 161 && i.mf[0] === 0.5 && i.mf.every((v, t) => t === 0 || Math.abs(v - (0.3 + 0.4 * i.mf[t - 1] * (1 - i.mf[t - 1]))) < 1e-15));
const fps = await D2(() => Array.from({ length: 101 }, (_, k) => [k / 100, DP_DEBUG.mfFixed(k / 100)]));
check('the mean-field fixed point solves d = λ + α d(1 − d) in [0, 1] for 101 values of λ; 0.3956 at λ = 0.3', fps.every(([l, d]) => d >= -1e-12 && d <= 1 + 1e-12 && Math.abs(d - (l + (1 - 2 * l) * d * (1 - d))) < 1e-12) && i.dstar.toFixed(4) === '0.3956');

/* ---------- the other presets ---------- */
await preset('half'); i = await info();
check('λ = 1/2: exact density 1/2 and mean-field fixed point 1/2', i.exD.slice(1).every((v) => Math.abs(v - 0.5) < 1e-12) && i.dstar === 0.5);
await preset('zero'); i = await info();
let h0 = await D2(() => ({ rows: Array.from({ length: 161 }, (_, t) => DP_DEBUG.row(t)), coins: Array.from({ length: 161 }, (_, t) => DP_DEBUG.coins(t)) }));
check('λ = 0: no coin ever picks rule 245, every row is rule 10 of the previous one, the exact density is 1/4', h0.coins.flat().every((c) => c === 0) && follows(h0.rows, h0.coins, 10, 245) && i.exD.slice(1).every((v) => Math.abs(v - 0.25) < 1e-12) && i.dstar === 0);
await preset('one'); i = await info();
h0 = await D2(() => ({ coins: Array.from({ length: 160 }, (_, t) => DP_DEBUG.coins(t + 1)) }));
check('λ = 1: every coin picks rule 245, the exact density is 3/4, mean field goes to 1', h0.coins.flat().every((c) => c === 1) && i.exD.slice(1).every((v) => Math.abs(v - 0.75) < 1e-12) && Math.abs(i.dstar - 1) < 1e-12);
await preset('start'); i = await info();
const rS = exactCyl(10, 245, 1, 5, 1, 10, 3);
/* 7/20 + (3/5)^k (9/100 − 25/100) = (35·5^k − 16·3^k) / (100·5^k), k = 2t − 1 */
const formula = (t) => { const k = BigInt(2 * t - 1); return [35n * 5n ** k - 16n * 3n ** k, 100n * 5n ** k]; };
check('another start (p = 1/10, λ = 1/5): the dossier’s d_t = 1/4 + λ/2 + α^{2t−1}(q₀ − 1/4) holds exactly for t = 1, 2, 3 (BigInt)', [1, 2, 3].every((t) => rS.d[t][0] * formula(t)[1] === formula(t)[0] * rS.d[t][1]));
check('…and the page’s exact values follow it to 10⁻¹² for t = 1 … 8, converging to 0.35', i.exD.slice(1).every((v, k) => Math.abs(v - (0.35 + 0.6 ** (2 * k + 1) * (0.09 - 0.25))) < 1e-12) && !i.leanApplies);
check('the note says Lean covers only the fair start', /只管公平的 Bernoulli 初态/.test(await text('roNote')));
await preset('r36'); i = await info();
const r36 = exactCyl(36, 219, 1, 7, 1, 2, 3);
check('rule 36-219 at λ = 1/7: d₁ = 9/28 but d₂ = 1389/5488 exactly (BigInt), and the page agrees', ratEq(r36.d[1], 9, 28) && ratEq(r36.d[2], 1389, 5488) && Math.abs(i.exD[2] - 1389 / 5488) < 1e-12 && Math.abs(i.exD[3] - fval(r36.d[3])) < 1e-12);
h0 = await D2(() => ({ rows: Array.from({ length: 161 }, (_, t) => DP_DEBUG.row(t)), coins: Array.from({ length: 161 }, (_, t) => DP_DEBUG.coins(t)) }));
check('its ring follows rules 36 and 219 as the coins say', follows(h0.rows, h0.coins, 36, 219));
check('outside Lean’s theorem: no Lean line, the note says so, the deviation readout is 0.068331', !i.leanApplies && /36-219 不在 Lean 定理里/.test(await text('roNote')) && (await text('ro3')) === '0.3214 · 0.068331');

/* ---------- controls ---------- */
await preset('lean');
await D2(() => { const e = document.getElementById('lamIn'); e.value = 0.62; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the λ slider sets λ = 0.62: exact density 0.56 and custom settings', i.lam === 0.62 && i.exD.slice(1).every((v) => Math.abs(v - 0.56) < 1e-12) && (await state()).preset === null && /自定义/.test(await text('presetNote')));
await D2(() => { const e = document.getElementById('pIn'); e.value = 0.3; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the p slider changes the start: q₀ = 0.21 and Lean no longer applies', i.p === 0.3 && Math.abs(i.exQ[0] - 0.21) < 1e-12 && !i.leanApplies);
await click('#ruleChips [data-rule="36-219"]'); i = await info();
check('the rule chips switch to 36-219', i.rule === '36-219' && (await D2(() => document.querySelector('#ruleChips [aria-pressed="true"]').dataset.rule)) === '36-219');
await preset('lean'); await setT(0.05);
const row5 = await D2(() => DP_DEBUG.row(5)), exBefore = (await info()).exD;
await click('#seedBtn');
check('a new seed changes the ring’s history but not the exact values', JSON.stringify(await D2(() => DP_DEBUG.row(5))) !== JSON.stringify(row5) && JSON.stringify((await info()).exD) === JSON.stringify(exBefore) && (await state()).seed === 2 && await waitToast(/种子 2/));

/* ---------- labels, rail, keys, playback ---------- */
const boxes = await D2(() => [...document.querySelectorAll('.side .lean')].map((b) => [b.className, b.querySelector('.ok').textContent, b.textContent]));
check('label boxes: two LEAN ✓, NUM, dossier ARGUED, page ARGUED (dashed), OPEN, LIT', boxes.map((b) => b[1]).join(' ') === 'LEAN ✓ LEAN ✓ NUM ARGUED ARGUED OPEN LIT' && /theory/.test(boxes[3][0]) && /page/.test(boxes[4][0]));
check('the LEAN boxes name the frozen declarations', boxes[0][2].includes('Diploid10245Density.result') && boxes[1][2].includes('q_succ') && boxes[1][2].includes('A_overlap_zero'));
check('the LIT box cites the DOI and arXiv number', boxes[6][2].includes('10.1140/epjs/s11734-026-02447-z') && boxes[6][2].includes('2607.01917'));
check('the rail marks t = 0, 80 and 160', (await D2(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === 't = 0 | t = 80 | t = 160');
await preset('lean'); await setT(0); await D2(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ advances one step', (await info()).t === 1 && (await text('clock')) === 't = 1');
await page.keyboard.press('ArrowRight'); await page.keyboard.press('ArrowLeft'); await settle();
check('← goes back one step', (await info()).t === 1);
await page.keyboard.press('e'); await settle();
check('E jumps to the last step and pauses', (await info()).t === 160 && (await state()).playing === false);
await page.keyboard.press(' '); await settle();
check('Space toggles playback', (await state()).playing === true);
await D2(() => document.querySelector('#speedChips [data-speed="2.5"]').click());
check('playing to the end reports the ring average against 1/4 + λ/2 and mean field', await waitToast(/环上平均 0\.\d{4}.*1\/4 \+ λ\/2 = 0\.4000.*平均场 0\.3956/));
await pause(); await D2(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['side', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D2(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await setT(0.5);
const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels give the current step with the ring density and the start', tags.includes(`t = 80 · 环上密度 ${(await info()).dRing.toFixed(4)}`) && tags.includes('t = 0 · Bernoulli(0.5)'), tags);
const lit = await D2(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
await D2(() => window.TRV_THUMB()); await settle();
check('the thumbnail state is the paused Lean preset at the last step', (await state()).preset === 'lean' && (await state()).playing === false && (await info()).t === 160);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'r36']) {
  await preset(p); await setT(0.5);
  const leftovers = await D2(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#seedBtn');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D2(() => document.title)).startsWith('CA//DIPLOID · The diploid cellular automaton 10-245 has density exactly 1/4 + λ/2 from the first step'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D2(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D2(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['fuks-fates-2026-diploid-10-245-density.md', 'D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.lean', 'Blueprint/D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.md', 'Library/StatisticalMechanics/fuksfates2026diploid.md', 'doi.org/10.1140/epjs/s11734-026-02447-z', 'arxiv.org/abs/2607.01917'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="diploid-ca"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.DP_DEBUG && DP_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D2(() => document.body.dataset.vizId)) === 'diploid-ca');

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
