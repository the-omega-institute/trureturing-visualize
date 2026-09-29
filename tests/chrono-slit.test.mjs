#!/usr/bin/env node
// Browser regression suite for viz/chrono-slit (Playwright + Chromium with software WebGL).
//   node tests/chrono-slit.test.mjs
// Reads page state through the read-only window.CHRONO_DEBUG probe. Exit code 1 lists the failed checks.
import path from 'node:path';
import { createRequire } from 'node:module';
import { createServer, BASE } from '../scripts/serve.mjs';

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
const D = (expr) => page.evaluate(expr);
const setRange = (id, v) => page.evaluate(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); }, [id, v]);
const wait = (ms) => page.waitForTimeout(ms);

await page.goto(origin + BASE + 'viz/chrono-slit/');
await wait(600);
const toastAtLoad = await D(() => getComputedStyle(document.getElementById('toast')).opacity);
check('no toast pops up at load before anything happens', Number(toastAtLoad) < 0.1, `toast opacity ${toastAtLoad}`);
await wait(1500);
check('page loads without script errors', errors.length === 0, errors.join(' | '));
// pause for deterministic checks
await page.click('#play'); await wait(200);
const a0 = await D(() => CHRONO_DEBUG.archive());

// --- read order swap keeps the archive
const markBefore = await D(() => document.querySelector('#marks i.tr')?.style.left);
await setRange('tr', 0.7); await wait(300);
const a1 = await D(() => CHRONO_DEBUG.archive());
check('swapping read order keeps every hit and label', JSON.stringify(a0) === JSON.stringify(a1), `hash ${a0.hash} → ${a1.hash}`);
const markAfter = await D(() => document.querySelector('#marks i.tr')?.style.left);
check('timeline "read" mark follows T_R', markBefore !== markAfter, `${markBefore} → ${markAfter}`);
check('pill hash unchanged on T_R change', (await D(() => document.getElementById('pillHash').textContent)).includes(a0.hash));
await setRange('tr', 2.6); await wait(200);

// --- basis change re-sorts but does not move hits
await setRange('beta', 20); await wait(300);
const a2 = await D(() => CHRONO_DEBUG.archive());
check('changing β moves no hit', JSON.stringify(a0.x) === JSON.stringify(a2.x));
check('changing β re-sorts labels and changes the hash', a0.hash !== a2.hash && JSON.stringify(a0.k) !== JSON.stringify(a2.k));
await setRange('beta', 45); await wait(300);
const a2b = await D(() => CHRONO_DEBUG.archive());
check('returning β restores the archive', a2b.hash === a0.hash);

// --- N outcomes
for (const n of [3, 5, 8, 2]) {
  await setRange('nout', n); await wait(350);
  const st = await D(() => CHRONO_DEBUG.stats());
  const ar = await D(() => CHRONO_DEBUG.archive());
  const btns = await D(() => document.querySelectorAll('#branches .branch').length);
  const rows = await D(() => document.querySelectorAll('#branchTable tbody tr').length);
  const psum = st.P.reduce((a, b) => a + b, 0);
  const sums = await D(() => CHRONO_DEBUG.sums());
  check(`N=${n}: ${n + 1} branch buttons, ${n} table rows`, btns === n + 1 && rows === n, `buttons ${btns}, rows ${rows}`);
  check(`N=${n}: probabilities sum to 1, branch densities sum to the whole`, Math.abs(psum - 1) < 1e-4 && sums < 1e-6, `ΣP=${psum.toFixed(6)}, max|Σp_k−p|=${sums.toExponential(2)}`);
  check(`N=${n}: labels in range, hits unchanged`, ar.k.every(k => k >= 0 && k < n) && JSON.stringify(ar.x) === JSON.stringify(a0.x));
  const counts = Array(n).fill(0); ar.k.forEach(k => counts[k]++);
  check(`N=${n}: every outcome occurs`, counts.every(c => c > 0), counts.join('/'));
  check(`N=${n}: β slider ${n > 2 ? 'disabled' : 'enabled'}`, (await D(() => document.getElementById('beta').disabled)) === (n > 2));
}

// --- focus & keyboard
await setRange('nout', 3); await wait(300);
await page.click('#branches .branch[data-focus="2"]'); await wait(200);
check('clicking branch B focuses it', (await D(() => CHRONO_DEBUG.state().focus)) === 2);
await page.locator('body').press('Escape');
await page.mouse.click(5, 450); // neutral click
await page.keyboard.press('4'); await wait(150);
check('key 4 focuses branch C', (await D(() => CHRONO_DEBUG.state().focus)) === 3);
await page.keyboard.press('9'); await wait(150);
check('key 9 with N=3 is ignored', (await D(() => CHRONO_DEBUG.state().focus)) === 3);
await setRange('nout', 2); await wait(300);
check('reducing N below the focused branch resets focus to Σ', (await D(() => CHRONO_DEBUG.state().focus)) === 0);
const pressed = await D(() => [...document.querySelectorAll('#branches .branch')].map(b => b.getAttribute('aria-pressed')).join(','));
check('branch buttons reflect focus after rebuild', pressed === 'true,false,false', pressed);

// --- κ moves hits, frame/warp/mode do not touch the archive
await setRange('kappa', 0.5); await wait(300);
const a3 = await D(() => CHRONO_DEBUG.archive());
check('changing κ moves hits', JSON.stringify(a3.x) !== JSON.stringify(a0.x));
await setRange('kappa', 0); await wait(300);
check('returning κ restores the archive', (await D(() => CHRONO_DEBUG.archive().hash)) === a0.hash);
await setRange('frame', 1); await wait(300);
await page.click('#warpChips [data-warp="3"]'); await wait(1100);
await page.click('#modes [data-mode="1"]'); await wait(300);
check('clock frame, fold warp and BLOCK mode keep the archive', (await D(() => CHRONO_DEBUG.archive().hash)) === a0.hash);
const warpNote = await D(() => document.getElementById('warpNote').textContent);
check('fold relabel is reported as not injective', /非单射/.test(warpNote), warpNote.slice(0, 30));
await page.click('#warpChips [data-warp="1"]'); await wait(1100);
check('log relabel is reported injective', /单射 ✓/.test(await D(() => document.getElementById('warpNote').textContent)));
await setRange('warpK', 0); await wait(200);
check('relabel at strength 0 is still injective', /单射 ✓/.test(await D(() => document.getElementById('warpNote').textContent)));
await page.click('#warpChips [data-warp="3"]'); await wait(1000);
await setRange('warpK', 0.1); await wait(200);
const foldWeak = await D(() => document.getElementById('warpNote').textContent);
check('weak fold (strength 0.1) injectivity reported consistently with θ′>0', /单射 ✓/.test(foldWeak), foldWeak.slice(0, 20));
await page.click('#warpChips [data-warp="0"]'); await wait(1000);
await setRange('warpK', 0.6);
await setRange('frame', 0); await page.click('#modes [data-mode="0"]'); await wait(300);

// --- timeline marks & runcard after frame change
await setRange('frame', 0.5); await wait(200);
const marks = await D(() => document.getElementById('marks').textContent);
check('timeline marks shown for mixed clock', marks.length > 0, marks);
await setRange('frame', 0); await wait(200);

// --- selection via histogram and via 3D pick
await setRange('now', 0.9); await wait(300);
const hb = await page.locator('#hist').boundingBox();
await page.mouse.click(hb.x + hb.width * 0.5, hb.y + hb.height * 0.5); await wait(300);
const sel1 = await D(() => CHRONO_DEBUG.state().sel);
check('clicking the histogram selects a run', sel1 >= 0, `sel=${sel1}`);
check('runcard describes the selected run', (await D(() => document.getElementById('runcard').textContent)).includes('RUN #'));
const tr0 = await D(() => document.getElementById('runcard').textContent);
await setRange('tr', 1.5); await wait(200);
const tr1 = await D(() => document.getElementById('runcard').textContent);
check('runcard read time follows T_R', tr0 !== tr1, tr1.slice(0, 80));
await setRange('tr', 2.6);
await page.keyboard.press('Escape'); await wait(150);
check('Esc clears the selection', (await D(() => CHRONO_DEBUG.state().sel)) === -1);
const target = await D(() => { for (let i = 0; i < 480; i++) { const p = CHRONO_DEBUG.project(i); if (p && p.visible > 0.5) return { i, ...p }; } return null; });
const sb = await page.locator('#stage').boundingBox();
if (target) {
  await page.mouse.click(sb.x + target.x, sb.y + target.y); await wait(250);
  const sel2 = await D(() => CHRONO_DEBUG.state().sel);
  check('clicking a hit in 3D selects a run', sel2 >= 0, `clicked run ${target.i}, selected ${sel2}`);
} else check('clicking a hit in 3D selects a run', false, 'no visible hit to click');

// --- drag rotates, does not select
const before = await D(() => CHRONO_DEBUG.state().sel);
await page.mouse.move(sb.x + 300, sb.y + 300); await page.mouse.down(); await page.mouse.move(sb.x + 420, sb.y + 330, { steps: 6 }); await page.mouse.up(); await wait(200);
check('dragging keeps the selection', (await D(() => CHRONO_DEBUG.state().sel)) === before);
check('dragging clears the camera preset highlight', (await D(() => document.querySelectorAll('#camChips [aria-pressed="true"]').length)) === 0);
await page.click('#camChips [data-cam="top"]'); await wait(600);
check('camera preset chip highlights', (await D(() => document.querySelector('#camChips [aria-pressed="true"]')?.dataset.cam)) === 'top');
await page.click('#camChips [data-cam="iso"]'); await wait(300);

// --- transport
await page.click('#play'); await wait(400);
const f1 = await D(() => CHRONO_DEBUG.state().nowFrac); await wait(500);
const f2 = await D(() => CHRONO_DEBUG.state().nowFrac);
check('play advances the clock', f2 > f1, `${f1.toFixed(3)} → ${f2.toFixed(3)}`);
await page.click('#rev'); await wait(500);
const f3 = await D(() => CHRONO_DEBUG.state().nowFrac); await wait(500);
const f4 = await D(() => CHRONO_DEBUG.state().nowFrac);
check('reverse runs the clock backwards', f4 < f3, `${f3.toFixed(3)} → ${f4.toFixed(3)}`);
await page.click('#rev'); await page.click('#play'); await wait(200);
check('pause stops the clock', true);
await page.focus('#kappa'); await page.keyboard.press('Space'); await wait(200);
const playingAfterSpace = await D(() => CHRONO_DEBUG.state().playing);
await page.keyboard.press('Space'); await wait(100);
check('Space toggles play even with a slider focused', playingAfterSpace === true);

// --- LINEAR mode keeps an unread record hidden, then reveals it once τ passes T_R
await page.click('[data-preset="delayed"]'); await wait(200);
if (await D(() => CHRONO_DEBUG.state().playing)) await page.click('#play');
await page.click('#modes [data-mode="0"]');
await setRange('now', 1.6 / 3.5); await wait(300);
check('applying a preset clears the run card', /点击落点/.test(await D(() => document.getElementById('runcard').textContent)));
const hb2 = await page.locator('#hist').boundingBox();
const xRun = await D(() => CHRONO_DEBUG.archive().x[7]);
const pad = await D(() => ({ l: 34, r: 10 }));
await page.mouse.click(hb2.x + pad.l + (xRun + 1) / 2 * (hb2.width - pad.l - pad.r), hb2.y + hb2.height * 0.85); await wait(300);
const cardUnread = await D(() => document.getElementById('runcard').textContent);
check('LINEAR: an unread record is not revealed', /尚未读取/.test(cardUnread) && !/p\(e/.test(cardUnread), cardUnread.slice(0, 70));
await setRange('now', 3.0 / 3.5); await wait(400);
const cardRead = await D(() => document.getElementById('runcard').textContent);
check('LINEAR: the record appears once τ passes T_R', /p\(e/.test(cardRead), cardRead.slice(0, 70));
await setRange('now', 1.6 / 3.5); await wait(400);
check('LINEAR: scrubbing back hides it again', /尚未读取/.test(await D(() => document.getElementById('runcard').textContent)));
await page.keyboard.press('Escape');
// --- dragging the clock pauses the automatic advance
await page.click('#play'); await wait(200);
const nb = await page.locator('#now').boundingBox();
await page.mouse.move(nb.x + nb.width * 0.3, nb.y + nb.height / 2); await page.mouse.down(); await wait(100);
const g1 = await D(() => CHRONO_DEBUG.state().nowFrac); await wait(700);
const g2 = await D(() => CHRONO_DEBUG.state().nowFrac);
await page.mouse.up(); await wait(600);
const g3 = await D(() => CHRONO_DEBUG.state().nowFrac);
check('holding the clock slider stops playback from moving it', Math.abs(g2 - g1) < 1e-6, `${g1.toFixed(4)} → ${g2.toFixed(4)}`);
check('playback resumes after releasing the slider', g3 > g2, `${g2.toFixed(4)} → ${g3.toFixed(4)}`);
await page.click('#play');

// --- presets
for (const p of ['young', 'whichway', 'eraser', 'delayed', 'partial', 'quarter', 'trine', 'octet']) {
  await page.click(`[data-preset="${p}"]`); await wait(250);
  const st = await D(() => CHRONO_DEBUG.state());
  const note = await D(() => document.getElementById('presetNote').textContent);
  check(`preset ${p} applies and explains itself`, st.preset === p && note.length > 10);
}
// split with 8 branches, both modes
await setRange('split', 1); await page.click('#modes [data-mode="1"]'); await setRange('now', 0.2); await wait(900);
check('octet split renders without errors', errors.length === 0, errors.join(' | '));

// --- language
await page.click('[data-preset="delayed"]'); await wait(200);
await setRange('kappa', 0.3); await wait(200); // custom note
await page.click('[data-lang-set="en"]'); await wait(900);
const custom = await D(() => document.getElementById('presetNote').textContent);
check('custom-settings note switches to English', /Custom/.test(custom), custom);
const leftovers = await D(() => {
  const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
  while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
  return bad;
});
check('no visible Chinese left in English mode', leftovers.length === 0, leftovers.join(' | '));
const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels are English', !/[一-鿿]/.test(tags), tags.slice(0, 120));
await page.click('#infoBtn'); await wait(200);
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
await page.keyboard.press('Escape'); await wait(150);
check('Esc closes the drawer', (await D(() => document.getElementById('drawer').hidden)) === true);
check('focus returns to the drawer button', (await D(() => document.activeElement?.id)) === 'infoBtn');
await page.click('[data-lang-set="zh"]'); await wait(200);

// --- persistence across pages
await page.click('[data-lang-set="en"]'); await wait(100);
await page.click('.crumb'); await page.waitForLoadState('load'); await wait(800);
check('language choice carries to the index', (await D(() => document.documentElement.dataset.lang)) === 'en');
check('index lists the visualization', (await D(() => document.querySelectorAll('.card').length)) === 1);
await page.click('.card .enter'); await page.waitForLoadState('load'); await wait(1200);
check('index card opens the page', (await D(() => document.body.dataset.vizId)) === 'chrono-slit');

// --- resize
await page.setViewportSize({ width: 820, height: 1000 }); await wait(700);
check('no horizontal scroll at 820px', (await D(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
await page.setViewportSize({ width: 390, height: 844 }); await wait(700);
check('no horizontal scroll at 390px', (await D(() => document.documentElement.scrollWidth - document.documentElement.clientWidth)) === 0);
check('no script errors during the whole session', errors.length === 0, errors.join(' | '));

const failed = results.filter(r => !r.ok);
console.log(`\n${results.length - failed.length}/${results.length} passed`);
await browser.close(); server.close();
if (failed.length) process.exit(1);
