#!/usr/bin/env node
// Browser regression suite for viz/delay-eraser (Playwright + Chromium with software WebGL).
//   node tests/delay-eraser.test.mjs
// Reads page state through the read-only window.ERASER_DEBUG probe and checks it against an independent
// implementation of the model below. Exit code 1 lists the failed checks.
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
  const start = await page.evaluate(() => ERASER_DEBUG.frames());
  await page.waitForFunction((f0) => !ERASER_DEBUG.pending() && ERASER_DEBUG.frames() >= f0 + 2, start, { timeout: 20000 });
};
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => ERASER_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => ERASER_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => ERASER_DEBUG.state().playing)) await click('#play'); };
const setTime = async (ns) => { await D((ns) => ERASER_DEBUG.setTime(ns), ns); await settle(); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const info = () => D(() => ERASER_DEBUG.info());
const archive = () => D(() => ERASER_DEBUG.archive());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const toastOn = async () => (await D(() => document.getElementById('toast').style.opacity)) === '1';

// independent implementation of the model: detector amplitudes on the two path records, joint law by direct modulus
const sinc = (u) => (Math.abs(u) < 1e-12 ? 1 : Math.sin(u) / u);
const env = (x, W) => sinc(Math.PI * x / W) ** 2;
function detectorAmps(w, r, phi) {
  const f = phi * Math.PI / 180, g = Math.sqrt(1 - w);
  const cis = (m, a) => ({ re: m * Math.cos(a), im: m * Math.sin(a) });
  return [
    [cis(g * Math.sqrt(r), 0), cis(g * Math.sqrt(1 - r), f)],
    [cis(g * Math.sqrt(1 - r), 0), cis(-g * Math.sqrt(r), f)],
    [cis(Math.sqrt(w), 0), cis(0, 0)],
    [cis(0, 0), cis(Math.sqrt(w), 0)]
  ];
}
function condRef(x, w, r, phi, W, db) {             // p(k | x) = ½ |a_k e^{iπx/Λ} + b_k e^{−iπx/Λ}|²
  const lam = W / db, h = Math.PI * x / lam;
  return detectorAmps(w, r, phi).map(([a, b]) => {
    const re = a.re * Math.cos(h) - a.im * Math.sin(h) + b.re * Math.cos(-h) - b.im * Math.sin(-h);
    const im = a.re * Math.sin(h) + a.im * Math.cos(h) + b.re * Math.sin(-h) + b.im * Math.cos(-h);
    return 0.5 * (re * re + im * im);
  });
}
function envelopeCDF(W) {                           // Simpson-integrated CDF of sinc² on [−1, 1]
  const n = 8000, xs = [], c = [0];
  for (let i = 0; i <= n; i++) xs.push(-1 + 2 * i / n);
  for (let i = 1; i <= n; i++) { const a = xs[i - 1], b = xs[i], m = (a + b) / 2; c.push(c[i - 1] + (b - a) / 6 * (env(a, W) + 4 * env(m, W) + env(b, W))); }
  const Z = c[n];
  return (x) => { const j = Math.min(n, Math.max(0, Math.round((x + 1) / 2 * n))); return c[j] / Z; };
}

await page.goto(origin + BASE + 'viz/delay-eraser/');
await page.waitForTimeout(700);
check('no toast pops up at load', !(await toastOn()));
check('page loads without script errors', errors.length === 0, errors.join(' | '));
await pause();

// --- the law
let maxErr = 0, maxSum = 0;
for (const [w, r, phi, x] of [[0.5, 0.5, 0, 0.13], [0, 0.85, 90, -0.4], [1, 0.3, 200, 0.77], [0.2, 0.1, 33, -0.91], [0.73, 0.62, 300, 0.05]]) {
  for (let j = 0; j < 40; j++) {
    const xx = Math.max(-1, Math.min(1, x + (j - 20) * 0.047));
    const got = (await D(([xx, w, r, phi]) => ERASER_DEBUG.model(xx, w, r, phi), [xx, w, r, phi])).cond;
    const ref = condRef(xx, w, r, phi, 0.8, 3);
    maxErr = Math.max(maxErr, ...got.map((g, k) => Math.abs(g - ref[k])));
    maxSum = Math.max(maxSum, Math.abs(got.reduce((a, b) => a + b) - 1));
  }
}
check('p(k | x) matches the direct amplitude modulus for every detector', maxErr < 1e-12, `max error ${maxErr.toExponential(1)}`);
check('Σ_k p(k | x) = 1 for every choice, so the D0 law is always the bare envelope', maxSum < 1e-12, `max |Σ−1| ${maxSum.toExponential(1)}`);
let kap = 0;
for (const [w, r, phi] of [[0.5, 0.5, 0], [0, 0.85, 90], [0.3, 0.2, 137]]) {
  const A = await D(([w, r, phi]) => ERASER_DEBUG.amplitudes(w, r, phi), [w, r, phi]);
  let re = 0, im = 0; for (const { a, b } of A) { re += a[0] * b[0] + a[1] * b[1]; im += a[1] * b[0] - a[0] * b[1]; }
  kap = Math.max(kap, Math.hypot(re, im));
}
check('the detector set sees orthogonal path records: Σ_k a_k b̄_k = 0', kap < 1e-15, kap.toExponential(1));
let i = await info();
check('unsorted D0: V = 0 and D = 1, read out on the page', i.kappa < 1e-15 && (await text('roV0')) === '0.000' && (await text('roD')) === '1.000');
check('no other choice changes the D0 law, and the choice–hit information is 0', i.diff === 0 && i.mi === 0 && /0/.test(await text('roDiff')) && /^0\.000/.test(await text('roMI')));
// fringes, anti-fringes and the eraser phase
{
  const lam = 0.8 / 3, peak = (await D(() => ERASER_DEBUG.model(0, 0, 0.5, 0))).cond, trough = (await D((x) => ERASER_DEBUG.model(x, 0, 0.5, 0), lam / 2)).cond;
  const q = (await D((x) => ERASER_DEBUG.model(x, 0, 0.5, 90), lam / 4)).cond;
  check('D1 fringe and D2 anti-fringe are half a period apart', Math.abs(peak[0] - 1) < 1e-12 && Math.abs(peak[1]) < 1e-12 && Math.abs(trough[0]) < 1e-12 && Math.abs(trough[1] - 1) < 1e-12);
  check('eraser phase 90° moves the D1 peak by a quarter period', Math.abs(q[0] - 1) < 1e-12);
}
for (const r of [0.5, 0.85, 0.2, 0]) {
  await setRange('refl', r); i = await info();
  check(`K² + V² = 1 behind the eraser at r = ${r}`, Math.abs(i.K ** 2 + i.V ** 2 - 1) < 1e-12 && Math.abs(i.V - 2 * Math.sqrt(r * (1 - r))) < 1e-12 && Math.abs(i.K - Math.abs(2 * r - 1)) < 1e-12);
}
await preset('partial'); i = await info();
check('partial erasure preset: K = 0.70 and V = 0.71', Math.abs(i.K - 0.7) < 1e-12 && Math.abs(i.V - 2 * Math.sqrt(0.85 * 0.15)) < 1e-12 && /0\.70/.test(await text('presetNote')));

// --- the archive: hits never move, only labels change
const hashes = {}, labelsOf = {};
for (const p of ['kim', 'erase', 'path', 'late', 'early', 'flip', 'phase', 'partial']) { await preset(p); const a = await archive(); hashes[p] = a.hD0; labelsOf[p] = a.hLab; }
check('every preset prints the same D0 hits (same D0 hash)', new Set(Object.values(hashes)).size === 1, JSON.stringify(hashes));
check('the labels do change between choices', labelsOf.erase !== labelsOf.path && labelsOf.kim !== labelsOf.erase);
await preset('kim');
let a = await archive();
const x0 = a.x.slice();
await setRange('refl', 0.3); await setRange('ephase', 140); await setRange('route', 0.8); await setRange('delay', -25); await setRange('sep', 6);
a = await archive();
check('changing r, φ, w, Δ and d/b moves no hit', a.x.every((x, k) => x === x0[k]) && a.hD0 === hashes.kim);
await setRange('slitw', 0.6);
a = await archive();
check('changing the slit envelope does move the hits', a.hD0 !== hashes.kim);
await preset('kim'); a = await archive();
{
  const F = envelopeCDF(0.8), xs = a.x.slice().sort((p, q) => p - q);
  let ks = 0; xs.forEach((x, k) => { ks = Math.max(ks, Math.abs(F(x) - (k + 1) / xs.length), Math.abs(F(x) - k / xs.length)); });
  check('D0 hits follow the single-slit envelope (Kolmogorov–Smirnov)', ks < 0.04, `D = ${ks.toFixed(4)}`);
  const lam = 0.8 / 3, meanCos = (k) => { const v = a.x.filter((_, j) => a.det[j] === k).map((x) => Math.cos(2 * Math.PI * x / lam)); return v.reduce((s, c) => s + c, 0) / v.length; };
  check('sorted by D1 the hits sit on fringes, by D2 on anti-fringes, by D3/D4 on neither', meanCos(0) > 0.3 && meanCos(1) < -0.3 && Math.abs(meanCos(2)) < 0.1 && Math.abs(meanCos(3)) < 0.1, [0, 1, 2, 3].map((k) => meanCos(k).toFixed(3)).join(' '));
  const fracP = a.route.reduce((s, v) => s + v, 0) / a.route.length;
  check('the random splitter sends about half the idlers to the path detectors', Math.abs(fracP - 0.5) < 0.05, fracP.toFixed(3));
  check('path-routed idlers click only D3/D4, erased ones only D1/D2', a.route.every((r, k) => (r ? a.det[k] >= 2 : a.det[k] <= 1)));
}
await preset('erase'); a = await archive();
check('erase-all: every label is D1 or D2', a.det.every((d) => d <= 1));
await preset('path'); a = await archive();
check('path-all: every label is D3 or D4', a.det.every((d) => d >= 2));

// --- timing and light cones
for (const d of [8, 300, -30, 0, 1, 9, -9]) {
  await preset('kim'); await setRange('delay', d);
  const A = await archive(), I = await info();
  const s = Math.max(0, 1 - d), id = Math.max(0, d - 1);
  const ok = A.t0.every((t, k) => Math.abs(t - (A.te[k] + 4 + s)) < 1e-9 && Math.abs(A.tc[k] - (A.te[k] + 5 + id)) < 1e-9 && Math.abs(A.tc[k] - t - d) < 1e-9 &&
    Math.abs(A.tcc[k] - Math.max(t + 4, A.tc[k] + 1 + 6)) < 1e-9);
  const rel = d > 9 ? 'future' : d === 9 ? 'light-after' : d === -9 ? 'light-before' : d < -9 ? 'past' : 'spacelike';
  check(`Δ = ${d} ns: event times and causal relation (${rel})`, ok && I.rel === rel && I.sepNs === 9 && I.sigDelay === s && I.idlDelay === id);
}
await preset('kim'); await setRange('delay', 8);
check('spacelike note gives the frame speed that reverses the order', /0\.89c/.test(await text('delayNote')));
await setTime(320); i = await info(); a = await archive();
check('lab-time tally: shown hits and labeled hits follow t0 and the coincidence time', i.shown === a.t0.filter((t) => t <= i.t).length && i.labeled === a.tcc.filter((t) => t <= i.t).length);
check('with an 8 ns delay only a thin band of labels is in flight', i.inFlight < 60, `in flight ${i.inFlight}`);
await setRange('delay', 300); await setTime(400); i = await info();
check('with a 300 ns delay hundreds of hits wait for their labels', i.inFlight > 500 && i.waiting > 400, `in flight ${i.inFlight}, waiting ${i.waiting}`);
check('the waiting hits show in the HUD', new RegExp(String(i.inFlight)).test(await text('hudSub')));

// --- the experimenter's switch
await preset('flip'); a = await archive();
check('mid-flight preset: choices before t = 300 ns erase, after it measure the path', a.tc.every((t, k) => (t < 300 ? a.route[k] === 0 && a.det[k] <= 1 : a.route[k] === 1 && a.det[k] >= 2)));
const printedBefore = a.t0.filter((t, k) => t < 300 && a.tc[k] >= 300).length;
check('hundreds of hits landed before the flip yet are sorted by the later setting', printedBefore > 600 && /50/.test(await text('presetNote')), `${printedBefore} hits`);
check('the mid-flight preset shows the same D0 hits', a.hD0 === hashes.kim);
check('switch mode shows the switch and the schedule, hides w', (await D(() => [document.getElementById('switchBox').hidden, document.getElementById('fieldW').hidden, document.getElementById('sched').hidden])).join() === 'false,true,false');
await setTime(150);
check('switch chips show the setting at the current lab time', (await D(() => document.querySelector('#switchChips [data-set="E"]').getAttribute('aria-pressed'))) === 'true');
const before = await archive();
await page.mouse.click(5, 450); await page.keyboard.press('s'); await settle();
const after = await archive(), st = await D(() => ERASER_DEBUG.state());
const last = st.sched[st.sched.length - 1];
check('key S flips the switch at the current lab time and drops the later plan', st.sched.length === 2 && last.set === 'P' && Math.abs(last.t - 150) < 1e-6 && st.preset === null);
check('after the flip, choices from t = 150 ns measure the path; earlier ones are untouched', after.tc.every((t, k) => (t < 150 ? after.det[k] === before.det[k] : after.route[k] === 1)));
check('the flip moves no hit but rewrites labels', after.hD0 === before.hD0 && after.hLab !== before.hLab);
check('the flip toast counts the hits already on the screen', /落点已经印在屏上/.test(await text('toast')) && (await toastOn()));
await click('#switchChips [data-set="E"]');
check('the ERASE chip flips back', (await D(() => ERASER_DEBUG.state().sched.at(-1).set)) === 'E');
await click('#modeChips [data-mode="bs"]');
check('back to the random splitter hides the switch', (await D(() => [document.getElementById('switchBox').hidden, document.getElementById('fieldW').hidden].join())) === 'true,false');

// --- presets
for (const p of ['kim', 'erase', 'path', 'late', 'early', 'flip', 'phase', 'partial']) {
  await page.click(`[data-preset="${p}"]`); await settle();
  check(`preset ${p} applies and explains itself`, (await D(() => ERASER_DEBUG.state().preset)) === p && (await text('presetNote')).length > 40);
}
await pause();

// --- selection, keyboard, transport
await preset('kim'); await setTime(560);
const sb = await page.locator('#stage').boundingBox();
const pd = await D(() => ERASER_DEBUG.projectDet(0));
await page.mouse.click(sb.x + pd.x, sb.y + pd.y); await settle();
check('clicking D1 in 3D shows only its coincidences', (await D(() => ERASER_DEBUG.state().selDet)) === 0 && (await D(() => document.querySelector('#detTable tr.det.sel')?.dataset.det)) === '0');
await page.keyboard.press('3'); await settle();
check('key 3 selects D3', (await D(() => ERASER_DEBUG.state().selDet)) === 2);
await page.click('#detTable tr.det[data-det="3"]'); await settle();
check('clicking a table row selects D4', (await D(() => ERASER_DEBUG.state().selDet)) === 3);
{
  const hb = await page.locator('#hist').boundingBox();
  await page.mouse.click(hb.x + hb.width * 0.5, hb.y + hb.height * 0.5); await settle();
  check('clicking the R02 histogram selects D2', (await D(() => ERASER_DEBUG.state().selDet)) === 1);
}
await page.keyboard.press('Escape'); await settle();
check('Esc clears the detector selection', (await D(() => ERASER_DEBUG.state().selDet)) === -1);
await click('[data-cam="screen"]'); await waitFrames(40);
{
  const target = 300, ph = await D((k) => ERASER_DEBUG.projectHit(k), target);
  await page.mouse.click(sb.x + ph.x, sb.y + ph.y); await settle();
  const sel = await D(() => ERASER_DEBUG.state().selPair);
  const ps = sel >= 0 ? await D((k) => ERASER_DEBUG.projectHit(k), sel) : null;
  check('clicking a hit selects that pair for the spacetime diagram', sel >= 0 && Math.hypot(ps.x - ph.x, ps.y - ph.y) < 10 && (await info()).pair === sel && /已选/.test(await text('stMeta')), `selected #${sel}`);
}
await page.keyboard.press('Escape'); await settle();
check('Esc clears the pair selection', (await D(() => ERASER_DEBUG.state().selPair)) === -1);
await click('[data-cam="iso"]');
const t1 = (await info()).t;
await page.keyboard.press('ArrowRight'); await settle();
check('→ steps 10 ns forward', Math.abs((await info()).t - t1 - 10) < 1e-6);
await page.keyboard.press('ArrowLeft'); await settle();
check('← steps 10 ns back', Math.abs((await info()).t - t1) < 1e-6);
await setTime(50);
await page.click('#play'); await waitFrames(4);
const f1 = (await info()).t; await waitFrames(12);
const f2 = (await info()).t;
check('play advances lab time', f2 > f1);
await page.click('#rev'); await waitFrames(4);
const f3 = (await info()).t; await waitFrames(12);
const f4 = (await info()).t;
check('reverse runs backwards', f4 < f3);
await page.click('#rev'); await pause();
await page.focus('#refl'); await page.keyboard.press('Space'); await page.waitForTimeout(150);
const playing = await D(() => ERASER_DEBUG.state().playing);
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await setRange('route', 0.3);
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags), tags.slice(0, 160));
check('table and notes are English', /Detector/.test(await text('detTable')) && /idler/.test(await text('routeNote')));
check('English title', (await D(() => document.title)).startsWith('DELAY//ERASER · Delayed-choice quantum eraser'));
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
await page.click('.card:has(a[href*="delay-eraser"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'delay-eraser');

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
