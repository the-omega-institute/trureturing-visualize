#!/usr/bin/env node
// Browser regression suite for viz/gronwall-edge (Playwright + Chromium with software WebGL).
//   node tests/gronwall-edge.test.mjs
// Reads page state through the read-only window.GE_DEBUG probe and checks it against an independent implementation: σ(n) from a
// smallest-prime-factor sieve and the multiplicative formula (the page sums divisors), primorial powers through exact BigInt
// divisor sums for small cases and a separately generated prime list for large ones, 1/ζ(2), 1/ζ(4), 1/ζ(6) from their closed
// forms, and the weighted tail of a hypothetical zero pair by Gauss–Legendre quadrature (the page integrates by Simpson’s rule
// backwards). Fixed reference data: Robin’s inequality fails exactly 26 times for 3 ≤ n ≤ 5040, the last at 5040; π(1.5·10⁶).
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
  const start = await page.evaluate(() => GE_DEBUG.frames());
  await page.waitForFunction((f0) => !GE_DEBUG.pending() && GE_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => GE_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => GE_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => GE_DEBUG.info());
const state = () => D(() => GE_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const slide = async (id, v) => { await D(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input')); }, [id, v]); await settle(); };
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => GE_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => GE_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};

/* ---------- independent implementation ---------- */
const N = 1000000, EG = Math.exp(0.57721566490153286);
const spf = new Int32Array(N + 1);
for (let i = 2; i <= N; i++) if (!spf[i]) for (let j = i; j <= N; j += i) if (!spf[j]) spf[j] = i;
function sigma(n) { let s = 1, m = n; while (m > 1) { const p = spf[m]; let pk = 1, t = 1; while (m % p === 0) { m /= p; pk *= p; t += pk; } s *= t; } return s; }
const R = (n) => sigma(n) / (EG * n * Math.log(Math.log(n)));
const vpOf = (n, p) => { let k = 0; while (n % p === 0) { n /= p; k++; } return k; };
const VIOL = []; for (let n = 3; n <= 5040; n++) if (R(n) >= 1) VIOL.push(n);
let MAXR = 0, ARGMAX = 0; for (let n = 5041; n <= N; n++) { const r = R(n); if (r > MAXR) { MAXR = r; ARGMAX = n; } }
const layerMax = (p, lo, hi) => { const out = Array(7).fill(-1); for (let n = lo; n <= hi; n++) { const L = Math.min(6, vpOf(n, p)), r = R(n); if (r > out[L]) out[L] = r; } return out; };
// primes for the primorial powers: a separate odd-only sieve up to 1.5·10⁶
const PM = 1500000, odd = new Uint8Array((PM >> 1) + 1), PR = [2];
for (let i = 3; i <= PM; i += 2) if (!odd[i >> 1]) { PR.push(i); for (let j = i * i; j <= PM; j += 2 * i) odd[j >> 1] = 1; }
const sigmaBig = (fac) => fac.reduce((s, [p, e]) => { const P = BigInt(p); return s * ((P ** BigInt(e + 1) - 1n) / (P - 1n)); }, 1n);
function primorialPowerR(k, a) {   // exact σ for small cases, then the ratio in double precision
  const fac = PR.slice(0, k).map((p) => [p, a]); let n = 1n; for (const [p] of fac) n *= BigInt(p) ** BigInt(a);
  const s = sigmaBig(fac), lnN = fac.reduce((t, [p]) => t + a * Math.log(p), 0);
  return Number(s * 10n ** 12n / n) / 1e12 / (EG * Math.log(lnN));
}
function primorialPowerRLarge(k, a) { let lr = 0, lnN = 0; for (let i = 0; i < k; i++) { const p = PR[i]; lr += Math.log((1 - Math.pow(p, -(a + 1))) / (1 - 1 / p)); lnN += a * Math.log(p); } return Math.exp(lr) / (EG * Math.log(lnN)); }
// the weighted tail by 5-point Gauss–Legendre on segments of 0.05 (the page integrates by Simpson’s rule)
const GL = [[-0.9061798459386640, 0.2369268850561891], [-0.5384693101056831, 0.4786286704993665], [0, 0.5688888888888889], [0.5384693101056831, 0.4786286704993665], [0.9061798459386640, 0.2369268850561891]];
function tail(u, beta, gamma, m) {
  const g = (v) => { const e = Math.exp((beta - 1) * v); return 2 * m * e * (beta * Math.cos(gamma * v) + gamma * Math.sin(gamma * v)) / (beta * beta + gamma * gamma) * (v + 1) / (v * v); };
  let s = 0; const L = u + 45 / (1 - beta);
  for (let a = u; a < L; a += 0.05) { const c = a + 0.025; for (const [x, w] of GL) s += w * 0.025 * g(c + 0.025 * x); }
  return s;
}
const ampOf = (u, beta, gamma, m) => 2 * m / (Math.hypot(beta, gamma) * Math.hypot(beta - 1, gamma)) * Math.exp((beta - 1) * u) / u;
const G1 = 14.134725141734693;

/* ---------- load ---------- */
await page.goto(origin + BASE + 'viz/gronwall-edge/');
await page.waitForFunction(() => window.GE_DEBUG && GE_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let st = await state(), i = await info();
check('opens on the layers preset with p = 2 and plays', st.mode === 'layers' && st.preset === 'edge' && st.playing === true && i.p === 2);
await pause();

/* ---------- the Robin ratio ---------- */
await setFrac(1); i = await info();
check('the scan reaches n = 10⁶', i.nCut === N);
check('n ≤ 5040: exactly the 26 independently computed violations, the last 5040', JSON.stringify(i.viol) === JSON.stringify(VIOL) && VIOL.length === 26 && VIOL[25] === 5040, VIOL.join(','));
check('the largest R(n) on (5040, 10⁶] matches the independent sieve, and it is below 1', i.best[0] === ARGMAX && Math.abs(i.best[1] - MAXR) < 1e-12 && MAXR < 1, `${ARGMAX} ${MAXR}`);
let spotOK = true; for (const n of [3, 12, 360, 5040, 10080, 55440, 720720, 997, 999983]) { const r = await D((n) => GE_DEBUG.robinAt(n), n); if (Math.abs(r - R(n)) > 1e-12) spotOK = false; }
check('R(n) at nine spot values agrees with σ from the multiplicative formula', spotOK);
let partOK = true; for (let b = 0; b < i.lo.length; b++) { if (!i.lo[b]) continue; if (b > 0 && i.lo[b] !== (i.hi.slice(0, b).filter(Boolean).pop() || 2) + 1) partOK = false; }
check('the log n bins partition 3 … 10⁶ into consecutive integer ranges', partOK && i.lo.find(Boolean) === 3 && i.hi[i.hi.length - 1] === N);
let envOK = true; for (const b of [20, 60, 90, 110, 119]) { if (!i.lo[b]) continue; let mx = -1; for (let n = i.lo[b]; n <= i.hi[b]; n++) mx = Math.max(mx, R(n)); if (Math.abs(mx - i.env[b]) > 1e-12) envOK = false; }
check('the envelope in five bins is the largest R(n) over the bin’s integers', envOK);
check('the layer caps for p = 2 are 1 − 2^(−v−1)', i.caps.every((c, v) => Math.abs(c - (1 - Math.pow(2, -(v + 1)))) < 1e-15));
const lm2 = layerMax(2, i.nLo, i.nCut);
check('the last-decade maximum of every 2-layer matches the independent scan of [nLo, 10⁶]', i.nLo > N / 10 && i.nLo < N / 9 && lm2.every((x, L) => Math.abs(x - i.decade[L]) < 1e-12), lm2.map((x) => x.toFixed(4)).join(' '));
check('slow convergence is shown honestly: odd numbers still reach above 1/2 on the last decade', lm2[0] > 0.5 && i.decade[0] > 0.5);
check('the readouts name the largest value after 5040 and the 26 violations', (await text('ro2')).includes(MAXR.toFixed(6)) && (await text('ro3')).includes('26') && (await text('ro3')).includes('5,040'));
await click('#pChips [data-p="3"]'); i = await info();
const lm3 = layerMax(3, i.nLo, i.nCut);
check('p = 3: caps 2/3, 8/9, 26/27 and decade maxima match', Math.abs(i.caps[0] - 2 / 3) < 1e-15 && Math.abs(i.caps[1] - 8 / 9) < 1e-15 && Math.abs(i.caps[2] - 26 / 27) < 1e-15 && lm3.every((x, L) => Math.abs(x - i.decade[L]) < 1e-12) && (await state()).preset === null);
await click('#pChips [data-p="5"]'); i = await info();
check('p = 5: the first cap is 4/5', i.p === 5 && Math.abs(i.caps[0] - 0.8) < 1e-15);
await preset('violations'); i = await info();
check('the violations preset stops just past 5040 and lists all 26', i.nCut >= 5040 && i.nCut < 5600 && i.viol.length === 26 && /26/.test(await text('presetNote')));
check('…and the verdict is still “no R ≥ 1 after 5040” up to the cut', /5040/.test(await text('ro5')) && i.best && i.best[1] < 1);

/* ---------- primorial powers ---------- */
await preset('primorial'); i = await info();
check('the witness mode sieves primes to 1.5·10⁶: K = π(1.5·10⁶) = 114155, matching the independent sieve', i.mode === 'witness' && i.K === 114155 && PR.length === 114155);
let exOK = true, exDet = '';
for (const [k, a] of [[2, 2], [3, 2], [4, 2], [3, 5], [5, 3], [8, 4]]) { const pg = await D(([a, k]) => GE_DEBUG.witnessAt(a, k), [a, k]), want = primorialPowerR(k, a); if (Math.abs(pg - want) > 1e-9) { exOK = false; exDet += `k=${k},a=${a}: ${pg} vs ${want} `; } }
check('R((p_k#)^a) for six small cases equals the exact BigInt divisor sum', exOK, exDet);
check('(2·3)² = 36 is one of the 26 violations and (2·3·5)² = 900 is not', primorialPowerR(2, 2) >= 1 && primorialPowerR(3, 2) < 1 && VIOL.includes(36) && !VIOL.includes(900));
let lgOK = true; for (const [k, a] of [[1000, 3], [50000, 5], [114155, 8]]) { const pg = await D(([a, k]) => GE_DEBUG.witnessAt(a, k), [a, k]); if (Math.abs(pg - primorialPowerRLarge(k, a)) > 1e-9) lgOK = false; }
check('three large cases agree with an independent product over the separately sieved primes', lgOK);
check('1/ζ(2) = 6/π², 1/ζ(4) = 90/π⁴, 1/ζ(6) = 945/π⁶', Math.abs(i.zinv[0] - 6 / Math.PI ** 2) < 1e-10 && Math.abs(i.zinv[2] - 90 / Math.PI ** 4) < 1e-10 && Math.abs(i.zinv[4] - 945 / Math.PI ** 6) < 1e-10);
await setFrac(1); i = await info();
check('at k = K every a has R < 1, below its limit 1/ζ(a + 1) for a ≥ 2, and the limits increase towards 1', i.k === 114155 && i.R.every((r) => r < 1) && i.R.slice(1).every((r, j) => r < i.zinv[j + 1]) && i.zinv.every((z, j) => j === 0 || z > i.zinv[j - 1]) && i.zinv[9] > 0.999);
await preset('zeta'); i = await info();
check('the zeta preset: a = 1 at k = K gives R within 10⁻⁴ of 6/π²', i.a === 1 && Math.abs(i.R[0] - 6 / Math.PI ** 2) < 1e-4, i.R[0].toFixed(6));
await click('#aChips [data-a="8"]'); i = await info();
check('a = 8 chip selects the exponent and marks the settings custom', i.a === 8 && (await state()).preset === null && /a = 8|\(p_k#\)\^8/.test(await text('ro2L')));

/* ---------- the off-line zero ---------- */
await preset('echo75'); i = await info();
const c75 = 1 / (Math.hypot(0.75, G1) * Math.hypot(-0.25, G1));
check('echo: ρ = 0.75 + 14.13i, m = 1, threshold c* = m/(|ρ||ρ − 1|)', i.mode === 'echo' && i.beta === 0.75 && Math.abs(i.gamma - G1) < 1e-12 && i.m === 1 && Math.abs(i.cstar - c75) < 1e-15);
let fOK = true, fDet = '';
for (const [u, f] of i.samples) { const want = tail(u, 0.75, G1, 1), A = ampOf(u, 0.75, G1, 1); if (Math.abs(f - want) > 1e-5 * A) { fOK = false; fDet += `u=${u}: ${f} vs ${want} `; } }
check('the tail f(u) at u = 5, 10, 20, 40, 80, 120 matches Gauss–Legendre quadrature', fOK, fDet);
let late = -Infinity; for (let u = 140; u <= 150; u += 0.01) late = Math.max(late, u * Math.exp(0.25 * u) * tail(u, 0.75, G1, 1));
check('arbitrarily late peaks: independently, the normalized tail exceeds c* on [140, 150], with amplitude near 2c*', late > c75 && late > 1.8 * c75 && late < 2.2 * c75, `${(late / c75).toFixed(3)} c*`);
await setFrac((145 - 2) / 158); i = await info();
check('…and the page counts peaks above c* in the window around u = 145', i.u > 144 && i.u < 146 && i.peaks.some((x) => x > 140 && x < 150) && /[1-9]/.test((await text('roNote')).match(/c\* (\d+)/)?.[1] || ''));
let crossWant = null; for (let u = 3; u <= 160; u += 0.01) { if (Math.abs(tail(u, 0.75, G1, 1)) > 7 * Math.exp(-u / 2)) { crossWant = u; break; } }
check('the first crossing of 7e^(−u/2) agrees with the independent scan (≈ 41)', crossWant !== null && Math.abs(i.cross - crossWant) < 0.05, `${i.cross} vs ${crossWant && crossWant.toFixed(2)}`);
const lc = i.layerCross;
let r55 = 0; for (let u = 150; u <= 160; u += 0.01) r55 = Math.max(r55, Math.abs(tail(u, 0.55, G1, 1)) / (7 * Math.exp(-u / 2)));
check('β = 1/2 never crosses; β = 0.55 not before 160 (independently |f| < 0.03·7e^(−u/2) on [150, 160]); β ≥ 0.6 cross, earlier for larger β', lc[0][0] === 0.5 && lc[0][1] === null && lc[1][0] === 0.55 && lc[1][1] === null && r55 < 0.03 && lc.slice(2).every(([, c]) => c !== null) && lc.slice(3).every(([, c], j) => c < lc[j + 2][1]), lc.map(([b, c]) => `${b}:${c}`).join(' '));
await preset('echo60'); i = await info();
check('β = 0.6 crosses much later (≈ 113)', i.beta === 0.6 && i.cross > 105 && i.cross < 120 && /11[0-9]/.test(await text('ro5')), String(i.cross));
await slide('beta', 0.9); i = await info();
check('the β slider recomputes: 0.9 crosses near 24 and marks the settings custom', i.beta === 0.9 && i.cross > 20 && i.cross < 30 && (await state()).preset === null);
await click('#mChips [data-m="2"]'); i = await info();
check('multiplicity 2 doubles the threshold and the tail', i.m === 2 && Math.abs(i.cstar - 2 / (Math.hypot(0.9, G1) * Math.hypot(-0.1, G1))) < 1e-15 && Math.abs(i.samples[1][1] - 2 * tail(10, 0.9, G1, 1)) < 1e-5 * ampOf(10, 0.9, G1, 2));
await click('#gChips [data-g="2"]'); i = await info();
check('γ = 25.01 lowers the threshold c*', Math.abs(i.gamma - 25.010857580145688) < 1e-12 && i.cstar < 2 / (Math.hypot(0.9, G1) * Math.hypot(-0.1, G1)));
check('echo controls are visible only in this mode', (await visible('echoBox')) && !(await visible('pChips')) && !(await visible('aChips')));

/* ---------- presets and modes ---------- */
for (const p of ['edge', 'violations', 'odd', 'three', 'primorial', 'zeta', 'echo75', 'echo60']) { await preset(p); const pressed = await D((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 40); }
await click('#modeChips [data-mode="layers"]');
check('mode chips switch to layers and show the p chips', (await state()).mode === 'layers' && (await visible('pChips')) && !(await visible('echoBox')));
await click('#modeChips [data-mode="witness"]');
check('…and to primorial powers with the a chips', (await state()).mode === 'witness' && (await visible('aChips')));

/* ---------- timeline and keys ---------- */
await preset('edge'); await setFrac(0.97); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing the layers to the end raises the toast: no R ≥ 1 after 5040', await waitToast(/没有 R ≥ 1/));
await pause();
await preset('primorial'); await setFrac(0.97); await click('#play');
check('playing the primorial powers to the end reports the limit', await waitToast(/极限/));
await pause();
await preset('echo75'); await setFrac(0.98); await click('#play');
check('playing the echo to the end reports the crossing', await waitToast(/越过 7e/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
await preset('odd'); await setFrac(0.5); const b0 = (await info()).b;
await D(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ steps the cut by one bin', (await info()).b === b0 + 1);
await page.keyboard.press('e'); await settle();
check('E jumps to the end and pauses', (await info()).nCut === N && (await state()).playing === false);
check('the rail marks n = 3, 5040, 10⁶', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' '))) === 'n=3 5040 n=10⁶');
for (const cam of ['front', 'side', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');

/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['edge', 'primorial', 'echo75']) {
  await preset(p); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await preset('odd'); await click('#pChips [data-p="3"]');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D(() => document.title)).startsWith('GRONWALL//EDGE · How close σ(n) comes to e^γ n log log n'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the four Lean files and the Gronwall, Choie et al. and Platt–Trudgian DOIs', (await D(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['GronwallLowerEnvelope.lean', 'PrimeValuationGap.lean', 'CriticalThetaTailPeak.lean', 'ActualThetaTailLaplace.lean', '10.1090/s0002-9947-1913-1500940-6', '10.5802/jtnb.591', '10.1112/blms.12460'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="gronwall-edge"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.GE_DEBUG && GE_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'gronwall-edge');

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
