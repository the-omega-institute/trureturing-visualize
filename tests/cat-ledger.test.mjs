#!/usr/bin/env node
// Browser regression suite for viz/cat-ledger (Playwright + Chromium with software WebGL).
//   node tests/cat-ledger.test.mjs
// Reads page state through the read-only window.CAT_DEBUG probe. Exit code 1 lists the failed checks.
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
// Controls are applied on the next animation frame; wait until nothing is pending and two more frames have rendered,
// so the checks do not depend on how fast the machine renders.
const settle = async () => {
  const start = await page.evaluate(() => CAT_DEBUG.frames());
  await page.waitForFunction((f0) => !CAT_DEBUG.pending() && CAT_DEBUG.frames() >= f0 + 2, start, { timeout: 20000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => CAT_DEBUG.state().playing)) await click('#play'); };
const setNow = (t) => setRange('now', t / 60);
const dtV = (d) => Math.log10(d / 0.1) / 2;
const GAMMA = Math.LN2 / 20;
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const toastOn = async () => (await D(() => document.getElementById('toast').style.opacity)) === '1';
const tNow = () => D(() => CAT_DEBUG.state().nowFrac * 60);
const deathsUpTo = (arch, t) => arch.t.filter(x => x > 0 && x <= t + 1e-9).length;
const wait = (ms) => page.waitForTimeout(ms);
// playback checks wait for rendered frames, not wall-clock time, so a slow renderer cannot make them flaky
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => CAT_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => CAT_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};

await page.goto(origin + BASE + 'viz/cat-ledger/');
await wait(600);
check('no toast pops up at load', !(await toastOn()));
await wait(1200);
check('page loads without script errors', errors.length === 0, errors.join(' | '));
await pause();
const a0 = await D(() => CAT_DEBUG.archive());
check('archive has 400 cats with deaths inside the box', a0.t.length === 400 && a0.t.every(t => t === -1 || (t > 0 && t <= 60 + 1e-9)));
check('pill shows the archive fingerprint', (await text('pillHash')).includes(a0.hash));

// --- first-detection law (§11.2): first-click probabilities plus survival add up to one
for (const coupling of [0, 1]) {
  await click(`#couplingChips [data-coupling="${coupling}"]`);
  for (const d of [0.1, 1, 5]) {
    await setRange('dt', dtV(d));
    for (const w of [0, 0.35]) {
      await setRange('dark', w);
      const law = await D(() => { const n = CAT_DEBUG.law(1).nMax; return CAT_DEBUG.law(n); });
      check(`${coupling ? 'coherent' : 'Markov'} Δt≈${d} w=${w}: Σp(n) + s_N = 1`, Math.abs(law.total - 1) < 1e-9, `total ${law.total}`);
    }
  }
}
await setRange('dark', 0);

// --- Markov decay does not depend on the check interval; coherent coupling shows the Zeno effect
await click('#couplingChips [data-coupling="0"]');
let markovOk = true;
for (const v of [0, 0.35, 0.5, 0.85]) {
  await setRange('dt', v);
  const law = await D(() => { const n = CAT_DEBUG.law(1).nMax; return CAT_DEBUG.law(n); });
  const expect = Math.exp(-GAMMA * law.nMax * law.dt);
  if (Math.abs(law.survival - expect) > 1e-12) markovOk = false;
}
check('Markov: s = e^(−Γt) at every check time, whatever Δt', markovOk);
await setRange('dt', 0.5);
const aMarkov = await D(() => CAT_DEBUG.law(1).a);
await click('#couplingChips [data-coupling="1"]');
const aCoh = await D(() => CAT_DEBUG.law(1).a);
check('both couplings agree at Δt = 1 min', Math.abs(aMarkov - aCoh) < 1e-12, `${aMarkov} vs ${aCoh}`);
check('switching coupling at Δt = 1 keeps the archive', (await D(() => CAT_DEBUG.archive().hash)) === a0.hash);
const s60 = async () => D(() => CAT_DEBUG.survival(60));
const sMid = await s60();
await setRange('dt', 0); const sZeno = await s60();
await setRange('dt', dtV(5)); const sSparse = await s60();
check('coherent: frequent checks keep more cats alive (Zeno)', sZeno > 0.75 && sZeno > sMid && sMid > sSparse, `Δt 0.1: ${sZeno.toFixed(3)}, 1: ${sMid.toFixed(3)}, 5: ${sSparse.toExponential(2)}`);
const aSparse = await D(() => CAT_DEBUG.archive());
check('changing Δt changes the archive fingerprint', aSparse.hash !== a0.hash);
await setRange('dt', 0.5); await click('#couplingChips [data-coupling="0"]');
check('returning Δt and coupling restores the archive', (await D(() => CAT_DEBUG.archive().hash)) === a0.hash);

// --- dark state (§13, frozen finite_detection_survival_limit): long-run survival tends to w
await setRange('dark', 0.35);
const aDark = await D(() => CAT_DEBUG.archive());
check('dark weight changes the archive', aDark.hash !== a0.hash);
for (const coupling of [0, 1]) {
  await click(`#couplingChips [data-coupling="${coupling}"]`);
  const far = await D(() => CAT_DEBUG.survival(1e5));
  check(`${coupling ? 'coherent' : 'Markov'}: survival after a very long time equals w`, Math.abs(far - 0.35) < 1e-9, far.toFixed(12));
}
await click('#couplingChips [data-coupling="0"]');
await setNow(50);
const bars = await D(() => [...document.querySelectorAll('#condBars .row b')].map(b => +b.textContent));
const sAt50 = await D(() => CAT_DEBUG.survival(50));
check('conditional state: P(dark | alive at t) = w / s(t)', Math.abs(bars[1] - 0.35 / sAt50) < 1e-3 && Math.abs(bars[0] + bars[1] - 1) < 2e-3, bars.join(' / '));
let staleScrubs = 0;
for (let i = 0; i < 12; i++) {
  await setNow(5 + 4.3 * i);
  const r = await D(() => { const t = CAT_DEBUG.state().nowFrac * 60; return { b: +document.querySelectorAll('#condBars .row b')[1].textContent, want: 0.35 / CAT_DEBUG.survival(t), note: document.getElementById('condNote').textContent, t }; });
  if (Math.abs(r.b - r.want) > 1e-3 || !r.note.includes(r.t.toFixed(1))) staleScrubs++;
}
check('readouts follow every scrub of the clock (no stale notes)', staleScrubs === 0, `${staleScrubs}/12 stale`);
await setRange('dark', 0);
check('removing the dark state restores the archive', (await D(() => CAT_DEBUG.archive().hash)) === a0.hash);

// --- the archive agrees with the law
const aliveShare = a0.t.filter(t => t < 0).length / 400;
const sLaw = await s60();
check('share of cats alive at 60 min matches s(60) within 3σ', Math.abs(aliveShare - sLaw) < 3 * Math.sqrt(sLaw * (1 - sLaw) / 400), `${aliveShare} vs ${sLaw.toFixed(3)}`);

// --- observations that only read leave the archive untouched
const same = async () => JSON.stringify(await D(() => CAT_DEBUG.archive())) === JSON.stringify(a0);
await setRange('open', 15); const openHash = await same();
await setRange('open', 45); const openHash2 = await same();
check('moving the opening time keeps every death time', openHash && openHash2);
await click('#ledgerChips [data-ledger="1"]'); await click('#ledgerChips [data-ledger="0"]');
await click('#modes [data-mode="1"]'); await click('#modes [data-mode="0"]');
await click('#clockChips [data-clock="1"]'); await click('#clockChips [data-clock="0"]');
await setRange('split', 1); await setRange('split', 0);
await setRange('copies', 0); await setRange('overlap', 0.9); await setRange('fid', 0.9);
check('ledger, conditioning, clock, unfolding and record copies keep the archive', await same());
await setRange('copies', 15); await setRange('overlap', 0.5); await setRange('fid', 1 / 3);

// --- ledgers: the outside ledger holds nothing before opening, everything written by then at opening
await setRange('open', 30);
await click('#ledgerChips [data-ledger="1"]');
await setNow(20);
let lg = await D(() => CAT_DEBUG.ledger());
check('outside, before opening: no cat is in the ledger', lg.unknown === 400 && lg.outside === 0 && lg.inside > 0, JSON.stringify(lg));
check('branch table says the box is still closed', /尚未开箱/.test(await text('branchTable')));
await setNow(40);
lg = await D(() => CAT_DEBUG.ledger());
const deathsBy40 = deathsUpTo(a0, await tNow());
check('outside, after opening: the ledger holds every death so far', lg.unknown === 0 && lg.outside === deathsBy40 && lg.inside === deathsBy40 && lg.dead === deathsBy40, JSON.stringify(lg));
await click('#ledgerChips [data-ledger="0"]');
await setNow(20);
lg = await D(() => CAT_DEBUG.ledger());
check('inside: the ledger writes each death when it happens', lg.unknown === 0 && lg.dead === deathsUpTo(a0, await tNow()), JSON.stringify(lg));
await click('#modes [data-mode="1"]');
lg = await D(() => CAT_DEBUG.ledger());
check('BLOCK: conditioned on the whole box', lg.alive === a0.t.filter(t => t < 0).length && lg.dead + lg.alive === 400, JSON.stringify(lg));
const rows = await D(() => [...document.querySelectorAll('#branchTable tbody tr')].map(tr => [...tr.querySelectorAll('td')].map(td => td.textContent)));
check('branch table lists Σ, alive and dead with the law', rows.length === 3 && Math.abs(+rows[1][3] - sLaw) < 1e-3, JSON.stringify(rows));
await click('#modes [data-mode="0"]');

// --- opening toast when time crosses the opening in the outside ledger
await click('#ledgerChips [data-ledger="1"]');
await setNow(25); await wait(4600);
await click('#play'); await page.waitForFunction(() => CAT_DEBUG.state().nowFrac > 0.52, null, { timeout: 20000 }); await wait(150);
check('crossing the opening shows the opening toast', (await toastOn()) && /开箱/.test(await text('toast')), (await text('toast')).slice(0, 40));
await pause();
check('the archive is unchanged after the opening', await same());

// --- ledger clock: only records advance it; empty stretches collapse
await click('#clockChips [data-clock="1"]');
const yOut = await D(() => [CAT_DEBUG.y(0), CAT_DEBUG.y(29), CAT_DEBUG.y(31)]);
check('outside ledger clock: the time before opening collapses to one point', Math.abs(yOut[0] - yOut[1]) < 1e-9 && yOut[2] > yOut[1] + 0.5, yOut.map(v => v.toFixed(3)).join(' '));
check('ledger clock is reported as not injective', /非单射/.test(await text('clockNote')));
await click('#ledgerChips [data-ledger="0"]');
const deathTimes = [...new Set(a0.t.filter(t => t > 0))].sort((p, q) => p - q);
const steps = await D((ts) => ts.slice(0, 6).map(t => CAT_DEBUG.y(t) - CAT_DEBUG.y(t - 1e-6)), deathTimes);
const counts = deathTimes.slice(0, 6).map(t => a0.t.filter(x => Math.abs(x - t) < 1e-9).length);
const total = a0.t.filter(t => t > 0).length;
check('inside ledger clock: each death record advances the clock by the same step', steps.every((s, i) => Math.abs(s - 3 * counts[i] / total) < 1e-6), steps.map(s => s.toFixed(4)).join(' '));
await click('#clockChips [data-clock="0"]');
const yLab = await D(() => [CAT_DEBUG.y(0), CAT_DEBUG.y(30), CAT_DEBUG.y(60)]);
check('lab clock is linear', Math.abs(yLab[1] - (yLab[0] + yLab[2]) / 2) < 1e-9);

// --- record copies and complementarity (frozen repeated_record_exponential_decay, complementarity)
let compOk = true;
for (const [m, c] of [[0, 0.95], [2, 0.3], [5, 0.9], [9, 0.999], [15, 0.5], [0, 0]]) {
  await setRange('copies', m); await setRange('overlap', c);
  const co = await D(() => CAT_DEBUG.coherence());
  const M = [1, 2, 3, 5, 8, 13, 21, 50, 100, 1e3, 1e4, 1e6, 1e9, 1e12, 1e18, 1e23][m];
  const expectLog = c === 0 ? null : M * Math.log10(c);
  const logOk = c === 0 ? co.log10 === null || co.log10 === -Infinity : Math.abs(co.log10 - expectLog) <= Math.abs(expectLog) * 1e-12 + 1e-12;
  if (!logOk || Math.abs(co.D * co.D + co.V * co.V - 1) > 1e-12) { compOk = false; console.log('   ', m, c, JSON.stringify(co)); }
}
check('κ = c^M and D² + V² = 1 for every setting', compOk);
await setRange('copies', 0); await setRange('overlap', 0.95);
await setRange('open', 60); await setNow(30);
let co = await D(() => CAT_DEBUG.coherence());
const s30 = await D(() => CAT_DEBUG.survival(30));
check('weak record, box closed: the probe sees fringes 2√(s(1−s))·|κ|', Math.abs(co.Vt - 2 * Math.sqrt(s30 * (1 - s30)) * 0.95) < 1e-9 && co.Vt > 0.5, co.Vt.toFixed(4));
check('weak record: fact strength D < 1 in the inside ledger', co.fact < 0.5, co.fact.toFixed(3));
await setRange('open', 10);
co = await D(() => CAT_DEBUG.coherence());
check('after opening the probe sees no fringe', co.Vt === 0);
check('probe note explains the observer’s own record', /记忆/.test(await text('probeNote')));

// --- Wigner's undo
await setRange('copies', 2); await setRange('overlap', 0.3); await setRange('fid', (-Math.log10(1 - 0.98) - 1) / 6);
await setRange('open', 60); await setNow(30);
await click('#undoBtn');
co = await D(() => CAT_DEBUG.coherence());
const fNow = await D(() => { const v = CAT_DEBUG.state().fidV; return v >= 1 ? 1 : 1 - Math.pow(10, -1 - 6 * v); });
check('undo before opening: residual overlap f^M over M copies', Math.abs(co.log10 - 3 * Math.log10(fNow)) < 1e-9 && co.V > 0.9, co.log10.toFixed(5));
check('undo success toast', (await toastOn()) && /撤销成功/.test(await text('toast')));
check('undo pauses playback and holds the moment', (await D(() => CAT_DEBUG.state().undo)) === true && (await D(() => CAT_DEBUG.state().playing)) === false);
check('undo keeps the archive', await same());
await setRange('now', 0.6);
check('moving time releases the undo', (await D(() => CAT_DEBUG.state().undo)) === false && /撤销快照结束/.test(await text('toast')));
await setRange('open', 10); await setNow(30);
await click('#undoBtn');
co = await D(() => CAT_DEBUG.coherence());
check('undo after opening must also reverse the observer’s memory (M + 1 copies)', Math.abs(co.log10 - 4 * Math.log10(fNow)) < 1e-9, co.log10.toFixed(5));
await click('#undoBtn');
await setRange('copies', 15); await setRange('fid', 5 / 6); await setRange('open', 60);
await click('#undoBtn');
co = await D(() => CAT_DEBUG.coherence());
check('undoing a real-size cat fails', co.log10 < -1e15 && co.V === 0 && /撤销失败/.test(await text('toast')), co.log10.toExponential(2));
await click('#undoBtn');
await setRange('fid', 1); await click('#ledgerChips [data-ledger="0"]'); await click('#clockChips [data-clock="1"]');
await click('#undoBtn');
lg = await D(() => CAT_DEBUG.ledger());
check('an ideal undo empties the inside ledger, and its clock has no ticks', lg.empty === true && /账本为空/.test(await text('clockNote')), JSON.stringify(lg));
await click('#undoBtn'); await click('#clockChips [data-clock="0"]');
await setRange('fid', 1 / 3); await setRange('overlap', 0.5);

// --- branches, keyboard and selection
check('three branch buttons', (await D(() => document.querySelectorAll('#branches .branch').length)) === 3);
await click('#branches .branch[data-focus="1"]');
check('clicking “alive” focuses the alive spacetime', (await D(() => CAT_DEBUG.state().focus)) === 1);
await page.mouse.click(5, 450);
await page.keyboard.press('3'); await settle();
check('key 3 focuses the dead spacetime', (await D(() => CAT_DEBUG.state().focus)) === 2);
await page.keyboard.press('1'); await settle();
const ledgerBefore = await D(() => CAT_DEBUG.state().ledger);
await page.keyboard.press('l'); await settle();
check('key L switches the ledger', (await D(() => CAT_DEBUG.state().ledger)) === 1 - ledgerBefore);
await click('#ledgerChips [data-ledger="0"]');

await setNow(20);
const late = a0.t.findIndex(t => t > 40);
const hb = await page.locator('#hist').boundingBox();
const histX = (t) => hb.x + 34 + (hb.width - 34 - 10 - 10 - Math.max(10, (hb.width - 44) * 0.09)) * t / 60;
await page.mouse.click(histX(a0.t[late]), hb.y + hb.height * 0.8); await settle();
const selLate = await D(() => CAT_DEBUG.state().sel);
check('clicking the histogram selects a cat', selLate >= 0, `sel=${selLate}`);
const cardLate = await text('runcard');
const selT = a0.t[selLate];
check('LINEAR run card does not reveal a later death', selT <= 20 || /到此刻仍活着/.test(cardLate), `${selT} · ${cardLate.slice(0, 60)}`);
await click('#modes [data-mode="1"]');
check('BLOCK run card shows the death', selT < 0 || /死于/.test(await text('runcard')));
await click('#modes [data-mode="0"]');
await click('#ledgerChips [data-ledger="1"]');
check('outside run card before opening says the box is closed', /还没开箱/.test(await text('runcard')));
await page.keyboard.press('Escape'); await settle();
check('Esc clears the selection', (await D(() => CAT_DEBUG.state().sel)) === -1);
await click('#ledgerChips [data-ledger="0"]');
await setNow(50);
const target = await D(() => { for (let i = 0; i < 400; i++) { const p = CAT_DEBUG.project(i); if (p && p.visible > 0.5 && p.x > 40 && p.y > 40) return { i, ...p }; } return null; });
const sb = await page.locator('#stage').boundingBox();
if (target) {
  await page.mouse.click(sb.x + target.x, sb.y + target.y); await settle();
  check('clicking a worldline in 3D selects a cat', (await D(() => CAT_DEBUG.state().sel)) >= 0, `target ${target.i}`);
} else check('clicking a worldline in 3D selects a cat', false, 'no visible target');
const before = await D(() => CAT_DEBUG.state().sel);
await page.mouse.move(sb.x + 300, sb.y + 300); await page.mouse.down(); await page.mouse.move(sb.x + 420, sb.y + 330, { steps: 6 }); await page.mouse.up(); await settle();
check('dragging rotates without changing the selection', (await D(() => CAT_DEBUG.state().sel)) === before);
await page.click('#camChips [data-cam="top"]'); await wait(300);
check('camera preset chip highlights', (await D(() => document.querySelector('#camChips [aria-pressed="true"]')?.dataset.cam)) === 'top');
await page.click('#camChips [data-cam="iso"]');
await page.keyboard.press('Escape');

// --- transport
await setNow(10);
await page.click('#play'); await waitFrames(4);
const f1 = await D(() => CAT_DEBUG.state().nowFrac); await waitFrames(12);
const f2 = await D(() => CAT_DEBUG.state().nowFrac);
check('play advances the clock', f2 > f1, `${f1.toFixed(4)} → ${f2.toFixed(4)}`);
await page.click('#rev'); await waitFrames(4);
const f3 = await D(() => CAT_DEBUG.state().nowFrac); await waitFrames(12);
const f4 = await D(() => CAT_DEBUG.state().nowFrac);
check('reverse runs the clock backwards', f4 < f3, `${f3.toFixed(4)} → ${f4.toFixed(4)}`);
await page.click('#rev');
const nb = await page.locator('#now').boundingBox();
await page.mouse.move(nb.x + nb.width * 0.3, nb.y + nb.height / 2); await page.mouse.down(); await waitFrames(3);
const g1 = await D(() => CAT_DEBUG.state().nowFrac); await waitFrames(12);        // frames, not wall-clock time: rendering can stall under load
const g2 = await D(() => CAT_DEBUG.state().nowFrac);
await page.mouse.up(); await waitFrames(12);
const g3 = await D(() => CAT_DEBUG.state().nowFrac);
check('holding the clock slider stops playback from moving it', Math.abs(g2 - g1) < 1e-6);
check('playback resumes after releasing the slider', g3 > g2);
await pause();
await page.focus('#dt'); await page.keyboard.press('Space'); await wait(150);
const playingAfterSpace = await D(() => CAT_DEBUG.state().playing);
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playingAfterSpace === true);
await pause();

// --- presets
for (const p of ['classic', 'early', 'zeno', 'sparse', 'dark', 'qubit', 'wigner', 'macro']) {
  await page.click(`[data-preset="${p}"]`); await settle();
  const st = await D(() => CAT_DEBUG.state());
  const note = await text('presetNote');
  const undoExpected = p === 'wigner' || p === 'macro';
  check(`preset ${p} applies and explains itself`, st.preset === p && note.length > 20 && st.undo === undoExpected);
}
const early = await D(() => CAT_DEBUG.archive().hash);
await page.click('[data-preset="classic"]'); await settle();
check('early opening and classic share one archive', (await D(() => CAT_DEBUG.archive().hash)) === early && early === a0.hash);
await pause();
await setRange('split', 1); await click('#modes [data-mode="1"]'); await click('#clockChips [data-clock="1"]'); await wait(900);
check('unfolded ledger-clock view renders without errors', errors.length === 0, errors.join(' | '));
await setRange('split', 0); await click('#modes [data-mode="0"]'); await click('#clockChips [data-clock="0"]');

// --- language
await setRange('dark', 0.1);
await page.click('[data-lang-set="en"]'); await wait(900);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
await setRange('open', 20); await click('#ledgerChips [data-ledger="1"]'); await setNow(10);
await page.click('#hist'); await settle();
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags), tags.slice(0, 120));
check('English title', (await D(() => document.title)).startsWith('CAT//LEDGER · Schrödinger'));
await page.click('#infoBtn'); await wait(200);
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
await page.keyboard.press('Escape'); await wait(150);
check('Esc closes the drawer', (await D(() => document.getElementById('drawer').hidden)) === true);
check('focus returns to the drawer button', (await D(() => document.activeElement?.id)) === 'infoBtn');

// --- index round trip
const live = readRegistry().visualizations.filter(v => v.status === 'live').length;
await page.click('.crumb'); await page.waitForLoadState('load'); await wait(800);
check('language choice carries to the index', (await D(() => document.documentElement.dataset.lang)) === 'en');
check('index lists every live visualization', (await D(() => document.querySelectorAll('.card').length)) === live, `live ${live}`);
await page.click('.card:has(a[href*="cat-ledger"]) .enter'); await page.waitForLoadState('load'); await wait(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'cat-ledger');

// --- narrow layouts in both languages
for (const lang of ['en', 'zh']) {
  await page.click(`[data-lang-set="${lang}"]`); await wait(300);
  for (const w of [820, 390]) {
    await page.setViewportSize({ width: w, height: w === 390 ? 844 : 1000 }); await wait(700);
    check(`no horizontal scroll at ${w}px (${lang})`, (await D(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
  }
  await page.setViewportSize({ width: 1440, height: 900 }); await wait(300);
}
check('no script errors during the whole session', errors.length === 0, errors.join(' | '));

const failed = results.filter(r => !r.ok);
console.log(`\n${results.length - failed.length}/${results.length} passed`);
await browser.close(); server.close();
if (failed.length) process.exit(1);
