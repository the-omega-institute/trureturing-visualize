#!/usr/bin/env node
// Browser regression suite for viz/hard-squares (Playwright + Chromium with software WebGL).
//   node tests/hard-squares.test.mjs
// Reads page state through the read-only window.HS_DEBUG probe and checks it against an independent implementation: the
// partition function of the 8 × 8 torus by a numeric column transfer (trace of (TD)⁸), OEIS A027683, inclusion–exclusion counts
// of small independent sets, the necklace map T rewritten from the Lean definitions, and exact rationals for the star K₁,₂.
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
  const start = await page.evaluate(() => HS_DEBUG.frames());
  await page.waitForFunction((f0) => !HS_DEBUG.pending() && HS_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => HS_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => HS_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => HS_DEBUG.info());
const state = () => D(() => HS_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => HS_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => HS_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

// --- independent implementation
// Z(λ) of the 8 × 8 torus as the trace of (T D)⁸ over the 47 independent sets of the 8-cycle, with numeric λ
function torusZ(lam) {
  const w = 8, cols = []; for (let m = 0; m < 256; m++) { const r = ((m >> 1) | ((m & 1) << 7)); if ((m & r) === 0) cols.push(m); }
  const pc = (m) => m.toString(2).split('').filter((c) => c === '1').length, R = cols.length;
  const M = cols.map((a) => cols.map((b) => ((a & b) === 0 ? lam ** pc(b) : 0)));
  const mul = (A, B) => A.map((row) => B[0].map((_, j) => row.reduce((s, x, k) => s + x * B[k][j], 0)));
  let P = M; for (let s = 1; s < w; s++) P = mul(P, M);
  return { Z: P.reduce((s, row, i) => s + row[i], 0), states: R };
}
const binom = (n, k) => { let r = 1; for (let i = 1; i <= k; i++) r = r * (n - k + i) / i; return r; };
const mod = (a, n) => ((a % n) + n) % n;
// the necklace map from the Lean definitions: jumpTurn, then fix (shorten a length-2 vector that faces a stone at distance 3)
const turn = (v) => ({ '-2': 1, '-1': 2, '1': -2, '2': -1 })[v];
function stepT(N, n) {
  const J = new Map(N.map(([p, v]) => [mod(p + v, n), turn(v)]));
  return [...J].map(([p, v]) => { if (v > 0) { const w = J.get(mod(p + 3, n)); return [p, w !== undefined && w < 0 && v === 2 ? 1 : v]; } const w = J.get(mod(p - 3, n)); return [p, w !== undefined && w > 0 && v === -2 ? -1 : v]; }).sort((a, b) => a[0] - b[0]);
}
function pairAdmissible(d, v, w) { const pv = v > 0, pw = w > 0; if (!(d > 0) || pv === pw) return false; if (!pv && pw && d % 2 === 0) return false; if (pv && !pw) { if ((d + Math.abs(v) + Math.abs(w)) % 2 === 0 || d < 3) return false; if (d === 3 && (Math.abs(v) !== 1 || Math.abs(w) !== 1)) return false; } return true; }
const isNecklace = (N, n, k) => N.length === 2 * k && N.every(([p, v], i) => { const [q, w] = N[(i + 1) % N.length]; return pairAdmissible(i + 1 < N.length ? q - p : q - p + n, v, w); });
const key = (N, n) => { const a = new Array(n).fill(0); for (const [p, v] of N) a[p] = v; return a.join(','); };
const isIsometric = (A, B, n) => { const kb = key(B, n); for (let c = 0; c < n; c++) { if (key(A.map(([p, v]) => [mod(p + c, n), v]), n) === kb) return true; if (key(A.map(([p, v]) => [mod(c - p, n), -v]), n) === kb) return true; } return false; };
const gcd = (a, b) => (b ? gcd(b, a % b) : Math.abs(a));
const ratio = (p, q) => { const g = gcd(p, q); return `${p / g}/${q / g}`; };

await page.goto(origin + BASE + 'viz/hard-squares/');
await page.waitForFunction(() => window.HS_DEBUG && HS_DEBUG.frames() > 3, null, { timeout: 120000 });
let i = await info();
check('opens on the λ sweep of the 48 × 48 gas and plays', i.mode === 'gas' && i.L === 48 && (await state()).playing === true);
await pause();

// --- the exact 8 × 8 torus
check('the exact counts add up to OEIS A027683(8) = 213 256 442 503 independent sets', i.total === 213256442503 && i.counts.reduce((a, b) => a + b, 0) === 213256442503);
check('…c₀ = 1, c₁ = 64, c₂ = C(64, 2) − 128 = 1888, c₃ = 34 112 (inclusion–exclusion), c₃₂ = 2 (the two checkerboards)', i.counts[0] === 1 && i.counts[1] === 64 && i.counts[2] === binom(64, 2) - 128 && i.counts[3] === binom(64, 3) - 128 * 62 + 64 * 6 && i.counts[32] === 2 && i.counts.length === 33);
const zs = [0.3, 1, 3.8, 12].map((lam) => [torusZ(lam).Z, i.counts.reduce((s, c, m) => s + c * lam ** m, 0)]);
check('…Σ cₘ λᵐ equals the trace of (TD)⁸ from an independent numeric column transfer at λ = 0.3, 1, 3.8, 12', zs.every(([a, b]) => Math.abs(a / b - 1) < 1e-12) && torusZ(1).states === 47, zs.map(([a, b]) => (a / b - 1).toExponential(1)).join(' '));
await preset('exact'); await setFrac(Math.log(1 / 0.1) / Math.log(30 / 0.1)); i = await info();   // the preset plays, so pin λ = 1
const moments = (lam) => { let Z = 0, M1 = 0, M2 = 0; i.counts.forEach((c, m) => { const w = c * lam ** m; Z += w; M1 += m * w; M2 += m * m * w; }); const mean = M1 / Z; return { mean, varN: M2 / Z - mean * mean }; };
const resp = (lam) => { const h = 1e-6; return (moments(lam * Math.exp(h)).mean - moments(lam * Math.exp(-h)).mean) / (2 * h); };   // d⟨N⟩/d log λ
check('exact mode at λ = 1: ⟨N⟩ and Var(N) match the independent moments', Math.abs(i.lam - 1) < 1e-9 && Math.abs(i.mean - moments(1).mean) < 1e-9 && Math.abs(i.varN - moments(1).varN) < 1e-8, `${i.mean.toFixed(6)} · ${i.varN.toFixed(6)}`);
const pts = [0.2, 1, 3.8, 20].map((lam) => [moments(lam).varN, resp(lam)]);
check('…the frozen identity λ·d⟨N⟩/dλ = Var(N) holds at λ = 0.2, 1, 3.8, 20 (independent derivative in log λ)', pts.every(([v, r]) => Math.abs(v - r) < 1e-6 * Math.max(1, v)), pts.map(([v, r]) => (r - v).toExponential(1)).join(' '));
check('…and the page’s own derivative agrees with its variance to 10⁻⁶', Math.abs(i.response - i.varN) < 1e-6, (i.response - i.varN).toExponential(2));
check('…the distribution of N sums to 1 and its mean is ⟨N⟩', Math.abs(i.pmf.reduce((a, b) => a + b, 0) - 1) < 1e-12 && Math.abs(i.pmf.reduce((s, p, m) => s + m * p, 0) - i.mean) < 1e-9);
await setFrac(Math.log(10 / 0.1) / Math.log(300)); i = await info();
check('…at λ = 10 the exact density matches the independent one', Math.abs(i.lam - 10) < 1e-9 && Math.abs(i.mean - moments(10).mean) < 1e-9, (i.mean / 64).toFixed(6));

// --- Monte Carlo on the 48 × 48 torus
await preset('dilute'); await waitFrames(60); i = await info();
check('λ = 0.5: the Monte Carlo grid never has two neighbouring particles', i.lam > 0.499 && i.lam < 0.501 && i.legalGrid && i.sweeps > 100);
const ex05 = moments(0.5).mean / 64;
check('…and the running density is within 0.01 of the exact 8 × 8 density', Math.abs(i.rhoAvg - ex05) < 0.01 && i.accN >= 40, `${i.rhoAvg.toFixed(4)} vs ${ex05.toFixed(4)} over ${i.accN} sweeps`);
await preset('ordered'); await waitFrames(80); i = await info();
check('λ = 20: the grid stays legal and the density is high', i.legalGrid && i.rhoAvg > 0.35, `${i.rhoAvg.toFixed(3)} (exact 8 × 8: ${(moments(20).mean / 64).toFixed(3)})`);
await preset('critical'); i = await info();
check('the critical preset sits at λ ≈ 3.796', Math.abs(i.lam - 3.7962) < 1e-3);

// --- necklaces
await preset('neck12'); i = await info();
check('necklace n = 12, k = 2: the page’s start configuration satisfies Adamaszek’s necklace conditions (checked independently)', i.n === 12 && i.k === 2 && i.Lp === 6 && isNecklace(i.start, 12, 2));
let F = i.start, sameFrames = true, legalAll = true; for (let t = 1; t <= 2 * i.Lp; t++) { F = stepT(F, 12); if (key(F, 12) !== key(i.frames[t], 12)) sameFrames = false; if (!isNecklace(F, 12, 2)) legalAll = false; }
check('…every frame up to 2L equals the independent map T and stays a necklace', sameFrames && legalAll);
check('…T⁶N is a rotation or reflection of N (the frozen theorem, checked independently)', isIsometric(i.start, i.frames[6], 12) && i.iso[6] !== null && i.iso[0] === 'r0');
await setFrac(0.5); i = await info();
check('…half way along the rail is t = L = 6, and the readout names the isometry', i.t === 6 && /旋转|反射/.test(await text('ro3')));
let allOK = true, tried = 0; const sizes = [[12, 3], [16, 3], [20, 4], [24, 5], [30, 6], [36, 7], [40, 9]];
for (const [n, k] of sizes) { await setRange('nn', n); await setRange('kk', k); for (let r = 0; r < 2; r++) { await page.keyboard.press('r'); await settle(); const j = await info(); tried++; let G = j.start; for (let t = 0; t < j.Lp; t++) G = stepT(G, n); if (!(j.n === n && j.k === k && isNecklace(j.start, n, k) && isIsometric(j.start, G, n) && j.iso[j.Lp] !== null)) allOK = false; } }
check(`…${tried} random necklaces with n from 12 to 40: T^(n−3k) N is always an isometric copy of N`, allOK && tried === 14);
await preset('neck36'); i = await info();
check('necklace n = 36 with 10 stones: L = 21, legal throughout, return up to isometry at t = 21', i.n === 36 && i.k === 5 && i.Lp === 21 && i.legal.every(Boolean) && i.iso[21] !== null && isIsometric(i.start, i.frames[21], 36));

// --- the star K₁,₂
await preset('star'); i = await info();
check('star at (15, 2, 2): 𝔼|I| = 9/8, the bound is 259/230, the difference is −1/920 (exact fractions)', i.exact && i.exact.E === '9/8' && i.exact.B === '259/230' && i.exact.D === '-1/920' && Math.abs(i.l0 - 15) < 1e-9);
check('…matching independent rationals: weights 1, 15, 2, 2, 4 give 27/24, and 15/46 + 2/5 + 2/5 = 259/230', ratio(15 + 2 + 2 + 2 * 4, 24) === '9/8' && ratio(15 * 5 * 5 + 2 * 46 * 5 + 2 * 46 * 5, 46 * 25) === '259/230' && Math.abs(i.E - 9 / 8) < 1e-12 && Math.abs(i.B - 259 / 230) < 1e-12);
check('…and the readouts say the bound fails here', /9\/8/.test(await text('ro2')) && /259\/230/.test(await text('ro3')) && /失败/.test(await text('roNote')));
const s1 = await D(() => HS_DEBUG.starAt(1, 1));
check('…at (1, 1, 1) the bound holds: 𝔼|I| = (0 + 1 + 1 + 1 + 2)/5 = 1 > 1/4 + 1/3 + 1/3', s1.exact.E === '1' && s1.E > s1.B && Math.abs(s1.B - (0.25 + 2 / 3)) < 1e-12);
await setRange('leaf', 5); i = await info();
check('the leaf slider moves the point and marks the settings custom', i.leaf === 5 && (await state()).preset === null && Math.abs(i.E - (15 + 10 + 50) / (1 + 15 + 10 + 25)) < 1e-12);

// --- controls, keys, presets
for (const name of ['dilute', 'critical', 'ordered', 'sweep', 'exact', 'neck12', 'neck36', 'star']) { await preset(name); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), name); check(`preset ${name} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await click('#modeChips [data-mode="necklace"]');
check('the model chips switch to necklaces, show the n and k sliders and mark the settings custom', (await info()).mode === 'necklace' && (await visible('nField')) && (await visible('kField')) && !(await visible('leafField')) && (await state()).preset === null);
await setFrac(0); await page.keyboard.press('ArrowRight'); await settle();
check('→ moves one necklace step', (await info()).t === 1);
await page.keyboard.press('e'); await settle();
check('E jumps to t = 2L', (await info()).t === 2 * (await info()).Lp && (await state()).playing === false);

// --- play and toasts
await preset('neck12'); await setFrac(0.3); await click('#play');
check('the necklace toast fires at t = L', await waitToast(/t = L = 6/));
await pause();
await preset('exact'); await setFrac(0.98); await click('#play');
check('the exact toast reports the identity along the whole curve', await waitToast(/Var\(N\)/));
await pause();
await click('#modeChips [data-mode="star"]'); await setRange('leaf', 2); await setFrac(0.5); await click('#play');
check('the star toast fires when 𝔼|I| drops below the bound', await waitToast(/下界失败/));
await pause();
await preset('neck36'); await setFrac(0.2); await click('#play'); await waitFrames(12); const p1 = (await state()).nowFrac; await pause();
check('play advances along the rail', p1 > 0.2);
await click('#rev'); await waitFrames(12); const p2 = (await state()).nowFrac; await pause();
check('reverse runs backwards', p2 < p1);
await page.click('#rev'); await pause();
await page.focus('#nn'); await page.keyboard.press('Space'); await waitFrames(2);
const playing = (await state()).playing;
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await click('#modeChips [data-mode="gas"]');
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
check('3D labels are English', !/[一-鿿]/.test(tags) && /SUBLATTICE/.test(tags), tags);
check('English title', (await D(() => document.title)).startsWith('HARD//SQUARES · Particles that refuse to touch'));
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
await page.click('.card:has(a[href*="hard-squares"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.HS_DEBUG && HS_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'hard-squares');

// --- narrow layouts in both languages
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await waitFrames(3);
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await waitFrames(6);
    check(`no horizontal scroll at ${w}px (${lang})`, (await D(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 }); await waitFrames(3);
}
check('no script errors during the whole session', errors.length === 0, errors.join(' | '));

const failed = results.filter(r => !r.ok);
console.log(`\n${results.length - failed.length}/${results.length} passed`);
await browser.close(); server.close();
if (failed.length) process.exit(1);
