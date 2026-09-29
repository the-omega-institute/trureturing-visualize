#!/usr/bin/env node
// Browser regression suite for viz/friend-bell (Playwright + Chromium with software WebGL).
//   node tests/friend-bell.test.mjs
// Reads page state through the read-only window.FRIEND_DEBUG probe. Exit code 1 lists the failed checks.
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
// Controls apply on the next animation frame; wait until nothing is pending and two more frames have rendered.
const settle = async () => {
  const start = await page.evaluate(() => FRIEND_DEBUG.frames());
  await page.waitForFunction((f0) => !FRIEND_DEBUG.pending() && FRIEND_DEBUG.frames() >= f0 + 2, start, { timeout: 20000 });
};
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => FRIEND_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => FRIEND_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 30000 });
};
const setRange = async (id, v) => {
  await page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
  await settle();
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => FRIEND_DEBUG.state().playing)) await click('#play'); };
const setTau = async (tau) => { const [a, b] = (await D(() => FRIEND_DEBUG.tau())).range; await setRange('now', (tau - a) / (b - a)); };
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const toastOn = async () => (await D(() => document.getElementById('toast').style.opacity)) === '1';
const law = () => D(() => FRIEND_DEBUG.law());
const TS = 2 * Math.SQRT2;
const E_of = (phi, th, v) => { const r = Math.PI / 180; return [th.map(t => Math.cos(t * r)), th.map(t => Math.cos(phi * r) * Math.cos(t * r) + v * Math.sin(phi * r) * Math.sin(t * r))]; };
const chsh = (E) => E[0][0] + E[0][1] + E[1][0] - E[1][1];
const bruteMax = (phi, v) => { let m = -9; for (let a = -180; a <= 180; a += 1) for (let b = -180; b <= 180; b += 1) m = Math.max(m, chsh(E_of(phi, [a, b], v))); return m; };

await page.goto(origin + BASE + 'viz/friend-bell/');
await page.waitForTimeout(600);
check('no toast pops up at load', !(await toastOn()));
await page.waitForTimeout(1200);
check('page loads without script errors', errors.length === 0, errors.join(' | '));
await pause();
const a0 = await D(() => FRIEND_DEBUG.archive());
check('archive: 400 runs, every setting pair occurs', a0.x.length === 400 && [0, 1, 2, 3].every(k => a0.x.filter((x, i) => x * 2 + a0.y[i] === k).length > 60));

// --- the quantum law at the frozen observables
let lw = await law();
check('qubit friend: S = 2√2 at the default (frozen) observables', Math.abs(lw.S - TS) < 1e-12 && Math.abs(lw.E[0][0] - Math.SQRT1_2) < 1e-12 && Math.abs(lw.E[1][1] + Math.SQRT1_2) < 1e-12, lw.S);
check('qubit friend: v = 1 and S_max = 2√2', lw.v === 1 && Math.abs(lw.Smax - TS) < 1e-12);
const { tsOk, best } = await D((TS) => {
  let ok = true, m = -9;
  for (const v of [0, 0.5, 1]) for (let phi = 0; phi <= 180; phi += 15) for (let a = -180; a <= 180; a += 15) for (let b = -180; b <= 180; b += 15) {
    const s = FRIEND_DEBUG.lawFor(phi, a, b, v);
    if (Math.abs(s) > TS + 1e-12) ok = false; m = Math.max(m, s);
  }
  return { tsOk: ok, best: m };
}, TS);
check('no angle choice exceeds 2√2 (grid of φ, θ₀, θ₁, v)', tsOk && Math.abs(best - TS) < 1e-9, best.toFixed(6));
const emp0 = await D(() => FRIEND_DEBUG.empirical());
check('archive estimate agrees with the law within 3σ', Math.abs(emp0.S - TS) < 3 * emp0.sigma, `${emp0.S.toFixed(3)} ± ${emp0.sigma.toFixed(3)}`);

// --- S_max = 2√(1+v²) and the best-angle button
await setRange('phi', 60);
lw = await law();
check('S_max formula matches a brute-force search over Bob’s angles (φ = 60°)', Math.abs(lw.Smax - bruteMax(60, 1)) < 1e-3, `${lw.Smax.toFixed(5)} vs ${bruteMax(60, 1).toFixed(5)}`);
await click('#bestBtn');
lw = await law();
check('best-angle button reaches S_max', Math.abs(lw.S - lw.Smax) < 1e-3, `${lw.S.toFixed(5)} vs ${lw.Smax.toFixed(5)}`);
await setRange('phi', 90); await setRange('th0', 45); await setRange('th1', -45);
check('returning to the default angles restores the archive', (await D(() => FRIEND_DEBUG.archive().hash)) === a0.hash);

// --- undo visibility v = f^M
await click('[data-preset="partial"]'); await pause();
lw = await law();
check('partial undo: v = 0.95³', Math.abs(lw.v - 0.95 ** 3) < 1e-12, lw.v.toFixed(6));
check('partial undo at the best angles: S ≈ 2√(1+v²) > 2', Math.abs(lw.S - 2 * Math.sqrt(1 + lw.v ** 2)) < 1e-3 && lw.S > 2.6, lw.S.toFixed(4));
await click('[data-preset="human"]'); await pause();
lw = await law();
check('human friend: v is effectively 0 and S_max = 2', lw.vLog10 < -1e15 && Math.abs(lw.Smax - 2) < 1e-12 && Math.abs(lw.S - 2) < 1e-9, `${lw.vLog10.toExponential(2)} · ${lw.S}`);
check('S ≤ 2: the premises are reported compatible', /兼容/.test(await text('premises')));
await click('[data-preset="noundo"]'); await pause();
lw = await law();
check('no undo: the X part is uncorrelated and S = √2', Math.abs(lw.E[1][0]) < 1e-12 && Math.abs(lw.S - Math.SQRT2) < 1e-12, lw.S.toFixed(6));
await click('[data-preset="qubit"]'); await pause();
check('S > 2: absolute facts are the premise that fails', /不可兼得/.test(await text('premises')) && (await D(() => document.querySelector('#premises .p').classList.contains('drop'))));

// --- absolute answer tables: every table gives ±2, every mixture stays within [−2, 2]
await click('#modelChips [data-model="1"]');
const gray = [0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0];
const seenS = new Set(); let tablesOk = true, visited = new Set();
for (let i = 0; i <= gray.length; i++) {
  const l = await law(), e = await D(() => FRIEND_DEBUG.empirical());
  const tbl = (await D(() => FRIEND_DEBUG.state().table)).join(',');
  visited.add(tbl); seenS.add(l.S);
  if (Math.abs(Math.abs(l.S) - 2) > 1e-12 || Math.abs(e.S - l.S) > 1e-12) tablesOk = false;
  if (i < gray.length) await click(`#table4 .bit[data-bit="${gray[i]}"]`);
}
check('all 16 answer tables give S = ±2 exactly, in the law and in the archive', tablesOk && visited.size === 16 && seenS.size === 2, `${visited.size} tables, S ∈ {${[...seenS].join(', ')}}`);
check('answer-table mode: all three premises hold', /三条都成立/.test(await text('premises')));
let mixOk = true;
for (let k = 0; k < 6; k++) {
  await click('#mixBtn');
  const l = await law(), e = await D(() => FRIEND_DEBUG.empirical());
  if (Math.abs(l.S) > 2 + 1e-12 || Math.abs(e.S - l.S) > 4 * e.sigma + 1e-9) mixOk = false;
}
check('random mixtures of tables stay within |S| ≤ 2 (archive within 4σ)', mixOk);
await click('#pureBtn'); await click('#modelChips [data-model="0"]');
check('back to the quantum ledgers restores the archive', (await D(() => FRIEND_DEBUG.archive().hash)) === a0.hash);

// --- read-only controls keep the archive
const same = async () => { const a = await D(() => FRIEND_DEBUG.archive()); return JSON.stringify(a) === JSON.stringify(a0); };
await setRange('beta', -0.5); await setRange('beta', 0.4);
await click('#coordChips [data-coord="1"]'); await click('#coordChips [data-coord="0"]');
await click('#modes [data-mode="1"]'); await click('#modes [data-mode="0"]');
await setRange('split', 1); await setRange('split', 0);
await click('#branches .branch[data-focus="3"]'); await click('#branches .branch[data-focus="0"]');
await setTau(1.0); await setTau(3.0);
check('frame, coordinates, conditioning, focus, unfolding and the clock keep the archive', await same());
const settingsSame = JSON.stringify((await D(() => FRIEND_DEBUG.archive())).x) === JSON.stringify(a0.x);
check('settings are fixed seeds', settingsSame);
await setRange('beta', 0);

// --- frames: the order of the spacelike measurements depends on β, the meeting never does
const ord = async (b) => D((b) => FRIEND_DEBUG.order(b), b);
check('lab frame: Bob measures first', (await ord(0)).first === 'B');
check('β = −0.11: still Bob first; β = −0.13: Wigner first', (await ord(-0.11)).first === 'B' && (await ord(-0.13)).first === 'W');
let meetOk = true;
for (let b = -0.6; b <= 0.6 + 1e-9; b += 0.05) if ((await ord(b)).gapC <= 0) meetOk = false;
check('the meeting comes after both measurements in every frame', meetOk);
const E0 = JSON.stringify((await law()).E);
await click('[data-preset="wfirst"]');
check('boosting to β = −0.45 puts Wigner first and announces it', (await D(() => FRIEND_DEBUG.order().first)) === 'W' && /Wigner/.test(await text('toast')));
check('boosting does not change the correlations', JSON.stringify((await law()).E) === E0);
let o = await D(() => FRIEND_DEBUG.order());
await setTau((o.dW + o.dB) / 2);
let lg = await D(() => FRIEND_DEBUG.ledgers());
check('Wigner-first frame, slice between the two: Wigner’s ledger is written, Bob’s is not', lg.wigner === 400 && lg.bob === 0, JSON.stringify(lg));
await click('[data-preset="bfirst"]');
o = await D(() => FRIEND_DEBUG.order());
await setTau((o.dW + o.dB) / 2);
lg = await D(() => FRIEND_DEBUG.ledgers());
check('Bob-first frame, slice between the two: Bob’s ledger is written, Wigner’s is not', lg.wigner === 0 && lg.bob === 400, JSON.stringify(lg));
check('frame note names who measures first', /Bob 先测/.test(await text('frameNote')));

// --- LINEAR slices: the correlation becomes available only at the meeting
await click('[data-preset="qubit"]'); await pause();
o = await D(() => FRIEND_DEBUG.order());
await setTau(o.dC - 0.1);
check('before the meeting there is no archive estimate', (await D(() => FRIEND_DEBUG.empirical().shown)) === false && /尚无汇合/.test(await text('roSemp')));
await setTau(o.dC + 0.05);
check('after the meeting the archive estimate appears', (await D(() => FRIEND_DEBUG.empirical().shown)) === true && /±/.test(await text('roSemp')));
await setTau(0.2);
lg = await D(() => FRIEND_DEBUG.ledgers());
check('before the friend measures, the friend’s ledger is empty', lg.friendWritten === 0);
await setTau(2.4);
lg = await D(() => FRIEND_DEBUG.ledgers());
const nx1 = a0.x.filter(x => x === 1).length;
check('after the undo, the undone runs are struck from the friend’s ledger', lg.friendWritten === 400 && lg.erased === nx1, JSON.stringify(lg));
await click('[data-preset="human"]'); await pause(); await setTau(2.4);
check('a human friend cannot be undone: nothing is struck', (await D(() => FRIEND_DEBUG.ledgers())).erased === 0);
await click('#modes [data-mode="1"]');
check('BLOCK shows the whole block, estimate included', (await D(() => FRIEND_DEBUG.empirical().shown)) === true);
await click('#modes [data-mode="0"]');
await click('[data-preset="qubit"]'); await pause();

// --- focus, keyboard, grid
check('five spacetime buttons', (await D(() => document.querySelectorAll('#branches .branch').length)) === 5);
await page.mouse.click(5, 450);
await page.keyboard.press('3'); await settle();
check('key 3 focuses setting pair (0, 1)', (await D(() => FRIEND_DEBUG.state().focus)) === 2);
const gb = await page.locator('#grid').boundingBox();
const cell = (x, y) => ({ px: gb.x + 78 + (gb.width - 78 - 8) * (y + 0.5) / 2, py: gb.y + 16 + (gb.height - 22) * (x + 0.5) / 2 });
let c11 = cell(1, 1);
await page.mouse.click(c11.px, c11.py); await settle();
check('clicking grid cell (1, 1) focuses it', (await D(() => FRIEND_DEBUG.state().focus)) === 4);
await page.mouse.click(c11.px, c11.py); await settle();
check('clicking it again returns to Σ', (await D(() => FRIEND_DEBUG.state().focus)) === 0);

// --- selection
await setTau(3.0);
const target = await D(() => { for (let i = 0; i < 400; i++) { const p = FRIEND_DEBUG.project(i); if (p && p.visible > 0.5 && p.x > 40 && p.y > 40) return { i, ...p }; } return null; });
const sb = await page.locator('#stage').boundingBox();
if (target) {
  await page.mouse.click(sb.x + target.x, sb.y + target.y); await settle();
  const sel = await D(() => FRIEND_DEBUG.state().sel);
  check('clicking a Wigner event selects a run', sel >= 0, `target ${target.i}, sel ${sel}`);
  check('the run card shows Wigner’s result once he has measured', /Wigner（(问朋友|撤销后测)）：/.test(await text('runcard')));
  const oo = await D(() => FRIEND_DEBUG.order());
  await setTau(oo.dW - 0.2);
  const card = await text('runcard');
  check('scrubbing back before his measurement hides Wigner’s result again', /尚未测量/.test(card), card.slice(0, 80));
  await setTau(4.2);
  check('after the meeting the run card reports agreement or disagreement', /一致|相反/.test(await text('runcard')));
} else check('clicking a Wigner event selects a run', false, 'no target');
await page.keyboard.press('Escape'); await settle();
check('Esc clears the selection', (await D(() => FRIEND_DEBUG.state().sel)) === -1);
await page.mouse.move(sb.x + 300, sb.y + 300); await page.mouse.down(); await page.mouse.move(sb.x + 420, sb.y + 330, { steps: 6 }); await page.mouse.up(); await settle();
check('dragging clears the camera preset highlight', (await D(() => document.querySelectorAll('#camChips [aria-pressed="true"]').length)) === 0);
await page.click('#camChips [data-cam="front"]'); await waitFrames(3);
check('camera preset chip highlights', (await D(() => document.querySelector('#camChips [aria-pressed="true"]')?.dataset.cam)) === 'front');
await page.click('#camChips [data-cam="iso"]');

// --- transport
await setRange('now', 0.3);
await page.click('#play'); await waitFrames(4);
const f1 = await D(() => FRIEND_DEBUG.state().nowFrac); await waitFrames(12);
const f2 = await D(() => FRIEND_DEBUG.state().nowFrac);
check('play advances the clock', f2 > f1, `${f1.toFixed(4)} → ${f2.toFixed(4)}`);
await page.click('#rev'); await waitFrames(4);
const f3 = await D(() => FRIEND_DEBUG.state().nowFrac); await waitFrames(12);
const f4 = await D(() => FRIEND_DEBUG.state().nowFrac);
check('reverse runs the clock backwards', f4 < f3, `${f3.toFixed(4)} → ${f4.toFixed(4)}`);
await page.click('#rev'); await pause();
await page.focus('#phi'); await page.keyboard.press('Space'); await page.waitForTimeout(150);
const playingAfterSpace = await D(() => FRIEND_DEBUG.state().playing);
await page.keyboard.press('Space');
check('Space toggles play even with a slider focused', playingAfterSpace === true);
await pause();

// --- presets
for (const p of ['qubit', 'partial', 'human', 'noundo', 'table', 'mix', 'wfirst', 'bfirst']) {
  await page.click(`[data-preset="${p}"]`); await settle();
  const st = await D(() => FRIEND_DEBUG.state());
  check(`preset ${p} applies and explains itself`, st.preset === p && (await text('presetNote')).length > 20);
}
await pause();
await setRange('split', 1); await click('#modes [data-mode="1"]'); await click('#coordChips [data-coord="1"]'); await waitFrames(20);
check('unfolded, boosted frame-coordinate view renders without errors', errors.length === 0, errors.join(' | '));
await setRange('split', 0); await click('#modes [data-mode="0"]'); await click('#coordChips [data-coord="0"]');

// --- language
await click('[data-preset="qubit"]'); await pause(); await setRange('th0', 30);
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
check('English title', (await D(() => document.title)).startsWith('FRIEND//BELL · Wigner'));
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
await page.click('.card:has(a[href*="friend-bell"]) .enter'); await page.waitForLoadState('load'); await page.waitForTimeout(1200);
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'friend-bell');

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
