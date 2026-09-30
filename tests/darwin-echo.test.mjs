#!/usr/bin/env node
// Browser regression suite for viz/darwin-echo (Playwright + Chromium with software WebGL).
//   node tests/darwin-echo.test.mjs
// Reads page state through the read-only window.DARWIN_DEBUG probe and checks it against an independent
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
  const start = await page.evaluate(() => DARWIN_DEBUG.frames());
  await page.waitForFunction((f0) => !DARWIN_DEBUG.pending() && DARWIN_DEBUG.frames() >= f0 + 2, start, { timeout: 20000 });
};
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => DARWIN_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => DARWIN_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => DARWIN_DEBUG.state().playing)) await click('#play'); };
const setN = async (n) => { await D((n) => DARWIN_DEBUG.setNowRecords(n), n); await settle(); };
const info = () => D(() => DARWIN_DEBUG.info());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const toastOn = async () => (await D(() => document.getElementById('toast').style.opacity)) === '1';
const run = () => D(() => DARWIN_DEBUG.run());

// independent implementation of the model
const h2 = (r) => { const a = Math.min(1, Math.max(0, (1 + r) / 2)), b = 1 - a; let s = 0; if (a > 1e-15) s -= a * Math.log2(a); if (b > 1e-15) s -= b * Math.log2(b); return s; };
const qq = (p) => 4 * p * (1 - p);
const I_ref = (p, c, n, m) => h2(Math.sqrt((2 * p - 1) ** 2 + qq(p) * c ** (2 * n))) + h2(Math.sqrt(1 - qq(p) * (1 - c ** (2 * m)))) - h2(Math.sqrt(1 - qq(p) * (1 - c ** (2 * (n - m)))));
const H_ref = (p) => h2(Math.abs(2 * p - 1));
const pOf = (theta, phase, eta) => { const t = theta * Math.PI / 180, f = phase * Math.PI / 180, e = eta * Math.PI / 180; return 0.5 * (1 + Math.sin(t) * Math.cos(f) * Math.sin(e) + Math.cos(t) * Math.cos(e)); };

await page.goto(origin + BASE + 'viz/darwin-echo/');
await page.waitForTimeout(600);
check('no toast pops up at load', !(await toastOn()));
await page.waitForTimeout(1200);
check('page loads without script errors', errors.length === 0, errors.join(' | '));
await pause();
const r0 = await run();

// --- the plateau and the two frozen endpoints (c = 0)
let endOk = true, detail = '';
for (const theta of [30, 60, 90, 120]) {
  await setRange('theta', theta);
  for (const n of [2, 7, 30]) {
    await setN(n);
    const i = await info(), h = H_ref(pOf(theta, 0, 0));
    for (let m = 1; m < n; m++) if (Math.abs(i.I[m] - h) > 1e-12) { endOk = false; detail = `θ=${theta} n=${n} m=${m}: ${i.I[m]} vs ${h}`; }
    if (Math.abs(i.I[n] - 2 * h) > 1e-12 || Math.abs(i.I[0]) > 1e-12) { endOk = false; detail = `θ=${theta} n=${n} ends`; }
  }
}
check('perfect copies: every incomplete fragment gives exactly H(p) (SBS consensus), the whole gives 2H (correlation tax)', endOk, detail);
await setRange('theta', 60);

// --- exact closed form against an independent implementation, for partial records
let formOk = true, symOk = true, monoOk = true;
for (const [c, theta, phase, eta, n] of [[0.8, 60, 0, 0, 40], [0.5, 100, 45, 30, 12], [0.97, 20, 200, 70, 64], [0.3, 150, 90, 180, 5]]) {
  await setRange('overlap', c); await setRange('theta', theta); await setRange('phase', phase); await setRange('eta', eta);
  await setRange('envn', Math.max(n, 2)); await setN(n);
  const i = await info(), p = pOf(theta, phase, eta);
  if (Math.abs(i.p - p) > 1e-12) formOk = false;
  for (let m = 0; m <= n; m++) {
    if (Math.abs(i.I[m] - I_ref(p, c, n, m)) > 1e-12) formOk = false;
    if (Math.abs(i.I[m] + i.I[n - m] - 2 * i.SS) > 1e-9) symOk = false;
    if (m && i.I[m] < i.I[m - 1] - 1e-12) monoOk = false;
  }
}
check('I(S:F) matches the closed form for partial records and rotated pointer axes', formOk);
check('pure global state: I(m) + I(n − m) = 2 S(ρ_S)', symOk);
check('I(S:F) never decreases as the fragment grows', monoOk);

// --- coherence and the Bloch vector (record rule selects the pointer axis)
await setRange('overlap', 0.7); await setRange('theta', 70); await setRange('phase', 0); await setRange('eta', 0); await setRange('envn', 48); await setN(9);
let i = await info();
const p9 = pOf(70, 0, 0);
check('coherence left = √(p(1−p))·c^n', Math.abs(i.coherence - Math.sqrt(p9 * (1 - p9)) * 0.7 ** 9) < 1e-12, i.coherence.toExponential(4));
check('reduced Bloch vector keeps the pointer component and shrinks the rest by c^n', Math.abs(i.bloch[2] - Math.cos(70 * Math.PI / 180)) < 1e-12 && Math.abs(i.bloch[0] - Math.sin(70 * Math.PI / 180) * 0.7 ** 9) < 1e-12);
await click('#ruleChips [data-rule="90"]');
i = await info();
check('recording X instead of Z moves the pointer axis', (await D(() => DARWIN_DEBUG.state().eta)) === 90 && Math.abs(i.p - pOf(70, 0, 90)) < 1e-12 && Math.abs(i.bloch[0] - Math.sin(70 * Math.PI / 180)) < 1e-12, i.p.toFixed(4));
await click('#ruleChips [data-rule="0"]');

// --- redundancy
let redOk = true;
for (const [c, n] of [[0, 30], [0.6, 6], [0.8, 48], [0.97, 48]]) {
  await setRange('overlap', c); await setRange('theta', 60); await setN(n);
  const got = (await info()).red, p = pOf(60, 0, 0), h = H_ref(p);
  let mRef = null; for (let m = 1; m <= n; m++) if (I_ref(p, c, n, m) >= 0.9 * h - 1e-12) { mRef = m; break; }
  if (got.m !== mRef || Math.abs(got.R - n / mRef) > 1e-12) redOk = false;
}
check('redundancy R_δ = n / m_δ with δ = 0.1 matches an independent search', redOk);

// --- monogamy lock
await setRange('overlap', 0); await setRange('theta', 90); await setN(20);
i = await info();
check('perfect copies: a fragment predicts the pointer value with certainty', i.PZ.slice(1).every(x => Math.abs(x - 1) < 1e-12));
check('perfect copies: no incomplete fragment knows the phase; the whole environment does', i.PX.slice(0, 20).every(x => Math.abs(x - 0.5) < 1e-12) && Math.abs(i.PX[20] - 1) < 1e-12);
await setRange('overlap', 0.8); await setRange('theta', 60); await setN(24);
i = await info();
const pp = pOf(60, 0, 0);
check('phase correlation = 2√(p(1−p))·c^(n−m) at every fragment size', i.PX.every((x, m) => Math.abs(x - 0.5 * (1 + Math.sqrt(qq(pp)) * 0.8 ** (24 - m))) < 1e-12));

// --- this run is fixed by seeds; only writing controls change it
await click('[data-preset="ideal"]'); await pause(); await setN(40);
const rIdeal = await run();
check('ideal preset reproduces the load-time run', rIdeal.hash === r0.hash);
await click('#askChips [data-ask="1"]'); await click('#askChips [data-ask="0"]');
await setN(10); await setN(40);
await page.click('#camChips [data-cam="top"]'); await waitFrames(3); await page.click('#camChips [data-cam="iso"]');
check('question, time and view keep the run', (await run()).hash === rIdeal.hash);
await setRange('overlap', 0.5);
check('record overlap changes the run', (await run()).hash !== rIdeal.hash);
await setRange('overlap', 0);
check('returning restores the run', (await run()).hash === rIdeal.hash);

// --- observers
let obs = await D(() => DARWIN_DEBUG.observers());
const cs = await D(() => DARWIN_DEBUG.consensus());
check('ideal copies: every observer reads the fact and all agree', obs.every(o => o.ready && o.value === rIdeal.fact) && cs.all && cs.of === 5, JSON.stringify(cs));
check('ideal copies: probability that all agree is 1', Math.abs((await D(() => DARWIN_DEBUG.allAgree())) - 1) < 1e-12);
await setN(2);
obs = await D(() => DARWIN_DEBUG.observers());
check('observers wait until their fragment is complete', obs.every(o => !o.ready) && /尚未读完/.test(await text('roAgree')));
await click('[data-preset="weak"]'); await pause(); await setN(48);
const pAllWeak = await D(() => DARWIN_DEBUG.allAgree()), pw = 0.5 * (1 + Math.sqrt(1 - 0.97 ** 8));
check('weak records: all five agree with probability P⁵ + (1−P)⁵', Math.abs(pAllWeak - (pw ** 5 + (1 - pw) ** 5)) < 1e-12, pAllWeak.toFixed(4));
await click('[data-preset="askx"]'); await pause(); await setN(48);
check('asking the phase: each observer is guessing, all agree with probability 2·½⁵', Math.abs((await D(() => DARWIN_DEBUG.allAgree())) - 2 / 32) < 1e-12 && /相位/.test(await text('factTag')));
await page.keyboard.press('q'); await settle();
check('key Q switches the question', (await D(() => DARWIN_DEBUG.state().ask)) === 0);

// --- presets with specific claims
await click('[data-preset="few"]'); await pause(); await setN(6);
check('tiny environment: R_δ = 3', (await info()).red.R === 3);
await click('[data-preset="eigen"]'); await pause(); await setN(30);
i = await info();
check('pointer eigenstate: H = 0 and no information anywhere', i.H < 1e-12 && i.I.every(x => Math.abs(x) < 1e-12) && /无信息可记/.test(await text('roR')));
await click('[data-preset="fourier"]'); await pause();
check('Fourier rule preset records X', (await D(() => DARWIN_DEBUG.state().eta)) === 90);
for (const p of ['ideal', 'partial', 'weak', 'equal', 'fourier', 'askx', 'few', 'eigen']) {
  await page.click(`[data-preset="${p}"]`); await settle();
  check(`preset ${p} applies and explains itself`, (await D(() => DARWIN_DEBUG.state().preset)) === p && (await text('presetNote')).length > 20);
}

// --- plateau toast while recording
await click('[data-preset="ideal"]');
await page.waitForFunction(() => DARWIN_DEBUG.info().n >= 3, null, { timeout: 30000 });
check('the plateau toast announces the public fact', /平台形成/.test(await text('toast')));
await pause();

// --- selection, keyboard, transport
await setN(40);
const pos = await D(() => DARWIN_DEBUG.project(0));
const sb = await page.locator('#stage').boundingBox();
await page.mouse.click(sb.x + pos.x, sb.y + pos.y); await settle();
check('clicking an observer in 3D selects them', (await D(() => DARWIN_DEBUG.state().sel)) === 0);
await page.click('#obsList .o[data-obs="2"]'); await settle();
check('clicking an observer row selects them', (await D(() => DARWIN_DEBUG.state().sel)) === 2);
await page.keyboard.press('Escape'); await settle();
check('Esc clears the selection', (await D(() => DARWIN_DEBUG.state().sel)) === -1);
await page.mouse.click(5, 450);
await page.keyboard.press('ArrowLeft'); await settle();
check('← steps back one record', (await info()).n === 39);
await page.keyboard.press('ArrowRight'); await settle();
check('→ steps forward one record', (await info()).n === 40);
await setN(5);
await page.click('#play'); await waitFrames(4);
const f1 = await D(() => DARWIN_DEBUG.state().nowFrac); await waitFrames(12);
const f2 = await D(() => DARWIN_DEBUG.state().nowFrac);
check('play advances the records', f2 > f1);
await page.click('#rev'); await waitFrames(4);
const f3 = await D(() => DARWIN_DEBUG.state().nowFrac); await waitFrames(12);
const f4 = await D(() => DARWIN_DEBUG.state().nowFrac);
check('reverse runs backwards', f4 < f3);
await page.click('#rev'); await pause();
await page.focus('#theta'); await page.keyboard.press('Space'); await page.waitForTimeout(150);
const playing = await D(() => DARWIN_DEBUG.state().playing);
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playing === true);
await pause();

// --- language
await setRange('overlap', 0.3);
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(900);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags), tags.slice(0, 120));
check('English title', (await D(() => document.title)).startsWith('DARWIN//ECHO · Quantum Darwinism'));
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
await page.click('.card:has(a[href*="darwin-echo"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'darwin-echo');

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
