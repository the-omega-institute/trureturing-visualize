#!/usr/bin/env node
// Browser regression suite for viz/ledger-growth (Playwright + Chromium with software WebGL).
//   node tests/ledger-growth.test.mjs
// Loads viz/ledger-growth/data.js in a separate VM context and checks its internal identities (strata and areas add up to the
// Lean count, area frozen counts add up to the state files, the calendar adds up to the dossiers present each day). Then reads
// page state through the read-only window.LG_DEBUG probe and compares it with values recomputed here: the frozen-count rule,
// ribbon heights on both scales, area ranks, digestion shares, cumulative dossiers by kind, and calendar positions from
// Zeller's congruence and month lengths. Preset notes are checked against numbers taken from the data independently.
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
const D = (expr, arg) => page.evaluate(expr, arg);
const settle = async () => {
  const start = await page.evaluate(() => LG_DEBUG.frames());
  await page.waitForFunction((f0) => !LG_DEBUG.pending() && LG_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D(() => LG_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setFrac = async (f) => { await D((f) => LG_DEBUG.setFrac(f), f); await settle(); };
const info = () => D(() => LG_DEBUG.info());
const state = () => D(() => LG_DEBUG.state());
const text = (id) => D((id) => document.getElementById(id).textContent, id);
const visible = (id) => D((id) => !document.getElementById(id).hidden, id);
const slide = async (id, v) => { await D(([id, v]) => { const el = document.getElementById(id); el.value = v; el.dispatchEvent(new Event('input')); }, [id, v]); await settle(); };
const waitFrames = async (n) => {
  const f0 = await page.evaluate(() => LG_DEBUG.frames());
  await page.waitForFunction(([f0, n]) => LG_DEBUG.frames() >= f0 + n, [f0, n], { timeout: 90000 });
};
const waitToast = async (re) => {
  try { await page.waitForFunction((src) => document.getElementById('toast').style.opacity === '1' && new RegExp(src).test(document.getElementById('toast').textContent), re.source, { timeout: 90000 }); return true; } catch { return false; }
};


/* ---------- independent implementation ---------- */
// data.js is evaluated in its own VM context; derived quantities are recomputed here: the frozen count (state files where they
// exist, accepted events before), ribbon heights (own maximum, or log10 over 2·10⁵), area ranks, closed share, cumulative
// dossiers by kind, thousands grouping, and calendar positions from Zeller's congruence with week numbers from month lengths
const fs = await import('node:fs'), vm = await import('node:vm');
const ctxD = { window: {} }; vm.runInNewContext(fs.readFileSync(new URL('../viz/ledger-growth/data.js', import.meta.url), 'utf8'), ctxD);
const LD = ctxD.window.LEDGER, N = LD.days.length, H = 3.6;
const grp = (x) => (x < 0 ? '−' : '') + String(Math.abs(x)).replace(/\B(?=(\d{3})+(?!\d))/g, ' ');
const frozenAt = (i) => (LD.frozenState[i] > 0 ? LD.frozenState[i] : LD.frozenAccepted[i]);
const SER = { d5: LD.d5, frozen: LD.days.map((_, i) => frozenAt(i)), reg: LD.reg, problems: LD.problems, theory: LD.theory, closed: LD.absorbed.map((a, i) => a + LD.nonprop[i]), merges: LD.prs };
const cumKind = (k, i) => LD.problemsNew[k].slice(0, i + 1).reduce((s, x) => s + x, 0);
const MLEN = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
const ordinal = (d) => { const [y, m, dd] = d.split('-').map(Number); let n = dd; for (let k = 1; k < m; k++) n += MLEN[k - 1] + (k === 2 && y % 4 === 0 ? 1 : 0); return n; };
function zellerMon0(d) {   // weekday with Monday = 0, by Zeller's congruence
  let [y, m, q] = d.split('-').map(Number); if (m < 3) { m += 12; y -= 1; }
  const K = y % 100, J = Math.floor(y / 100), h = (q + Math.floor(13 * (m + 1) / 5) + K + Math.floor(K / 4) + Math.floor(J / 4) + 5 * J) % 7;   // 0 = Saturday
  return (h + 5) % 7;
}
const week = (d) => Math.floor((ordinal(d) - ordinal(LD.days[0]) + zellerMon0(LD.days[0])) / 7);
const day = (d) => LD.days.indexOf(d);
const near = (a, b, tol = 1e-6) => Math.abs(a - b) <= tol;
const D_blur = () => D(() => document.activeElement && document.activeElement.blur());

/* ---------- the data ---------- */
let consecutive = LD.sha.length === N && LD.tip === LD.sha[N - 1] && LD.asOf === LD.days[N - 1];
for (let i = 1; i < N; i++) if (ordinal(LD.days[i]) - ordinal(LD.days[i - 1]) !== 1 || LD.prs[i] <= LD.prs[i - 1]) consecutive = false;
check(`data: ${N} consecutive UTC days ${LD.days[0]} … ${LD.asOf}, one sampled commit each, merges strictly increasing, the tip is the last sample`, consecutive && N === 111);
check('data: on every day the strata S0 + S1 + S3 + other add up to the Lean module count', LD.days.every((_, i) => LD.S0[i] + LD.S1[i] + LD.S3[i] + LD.other[i] === LD.d5[i]));
check('data: on every day the 13 areas add up to the Lean modules, and their frozen counts to the state files', LD.areas.length === 13 && LD.days.every((_, i) => LD.areas.reduce((s, a) => s + a.d5[i], 0) === LD.d5[i] && LD.areas.reduce((s, a) => s + a.frozen[i], 0) === LD.frozenState[i]));
check('data: the calendar adds up to the dossiers present on every day, and the resolution kinds to today’s 1 492', LD.days.every((_, i) => cumKind('proved', i) + cumKind('refuted', i) + cumKind('none', i) === LD.problems[i]) && LD.resolutions.proved + LD.resolutions.refuted + LD.resolutions.none === LD.problems[N - 1] && ['proved', 'refuted', 'none'].every((k) => cumKind(k, N - 1) === LD.resolutions[k]));

await page.goto(origin + BASE + 'viz/ledger-growth/');
await page.waitForFunction(() => window.LG_DEBUG && LG_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle(); await pause();
let i = await info();

/* ---------- growth ribbons ---------- */
check('opens on the “today” preset: growth ribbons scaled to their own maxima, at the last day and the tip commit', i.mode === 'growth' && i.scale === 'norm' && i.i === N - 1 && i.day === LD.asOf && i.sha === LD.tip && (await state()).preset === 'now');
check('…the readouts give the date, commit, Lean and Reg modules, state files, dossiers, theory files and merges', (await text('ro1')) === `${LD.asOf} · ${LD.tip}` && (await text('ro2')) === `${grp(LD.d5[N - 1])} · ${grp(LD.reg[N - 1])}` && (await text('ro3')).includes(grp(LD.frozenState[N - 1])) && (await text('ro4')) === `${grp(LD.problems[N - 1])} · ${grp(LD.theory[N - 1])}` && (await text('ro5')) === `${grp(LD.prs[N - 1])} · ${grp(LD.prs[N - 1] - LD.prs[N - 2])}`);
check('…seven ribbons, each at the height of its value over its own maximum', i.ribbons.length === 7 && i.ribbons.every((r) => SER[r.key] && r.value === SER[r.key][N - 1] && near(r.height, H * SER[r.key][N - 1] / Math.max(...SER[r.key]))));
let frozenOK = true, detail = '';
for (const d of ['2026-08-12', '2026-08-13', '2026-09-03', '2026-09-04', '2026-10-11', '2026-10-12', LD.asOf]) {
  await setFrac(day(d) / (N - 1)); const j = await info();
  if (j.day !== d || j.frozen !== frozenAt(day(d))) { frozenOK = false; detail += `${d}:${j.frozen} `; }
}
check('the frozen count is the state files where they exist and the accepted events before (seven days across both formats)', frozenOK, detail);
await setFrac(day('2026-09-04') / (N - 1));
check('…on 2026-09-04 the readout counts state files, the day before it counts events', /个状态片/.test(await text('ro3')) && (await text('ro3')).includes(grp(LD.frozenState[day('2026-09-04')])) && (await (async () => { await setFrac(day('2026-09-03') / (N - 1)); return /个事件/.test(await text('ro3')) && (await text('ro3')).includes(grp(LD.frozenAccepted[day('2026-09-03')])); })()));
let idxOK = true;
for (const f of [0, 0.123, 0.5, 0.777, 1]) { await setFrac(f); const j = await info(); if (j.i !== Math.round(f * (N - 1)) || j.perDay !== (j.i ? LD.prs[j.i] - LD.prs[j.i - 1] : LD.prs[0])) idxOK = false; }
check('the time axis picks day round(f·(N − 1)) and the merges of that day', idxOK);
await click('#scaleChips [data-scale="log"]'); await setFrac(0.6); i = await info();
check('the log chip puts all ribbons on log10 over 2·10⁵ (zero stays zero), and the settings become custom', i.scale === 'log' && i.ribbons.every((r) => near(r.height, r.value > 0 ? H * Math.log10(r.value) / Math.log10(2e5) : 0)) && (await state()).preset === null && /自定义/.test(await text('presetNote')));
await D_blur(); await page.keyboard.press('ArrowRight'); await settle();
check('→ moves one day forward', (await info()).i === Math.round(0.6 * (N - 1)) + 1);
await page.keyboard.press('ArrowLeft'); await page.keyboard.press('ArrowLeft'); await settle();
check('← moves one day back', (await info()).i === Math.round(0.6 * (N - 1)) - 1);
await page.keyboard.press('e'); await settle();
check('E jumps to the last day and pauses', (await info()).i === N - 1 && (await state()).playing === false);
check('the rail marks the first day, the month starts and the last day', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' '))) === `${LD.days[0].slice(5)} 8 月 9 月 10 月 ${LD.asOf.slice(5)}`);
check('only the growth view shows the scale chips', (await visible('scaleChips')) && !(await visible('areaChips')));

/* ---------- areas ---------- */
await click('#modeChips [data-mode="areas"]'); i = await info();
const mxD5 = Math.max(...LD.areas.flatMap((a) => a.d5));
check('areas view: 13 ribbons in data order, each at its Lean count over the largest area count of any day', i.ribbons.length === 13 && i.ribbons.every((r, k) => r.key === LD.areas[k].name && r.value === LD.areas[k].d5[N - 1] && near(r.height, H * LD.areas[k].d5[N - 1] / mxD5)) && (await visible('areaChips')) && !(await visible('scaleChips')));
const named = LD.areas.filter((a) => a.name !== 'other').sort((p, q) => q.d5[N - 1] - p.d5[N - 1]);
const fzSum = LD.areas.reduce((s, a) => s + a.frozen[N - 1], 0);
check('…the largest named area and the frozen share over all areas match an independent sort and sum', (await text('ro2')) === `${named[0].name} · ${grp(named[0].d5[N - 1])}` && (await text('ro3')) === `${grp(fzSum)} / ${grp(LD.d5[N - 1])} · ${(100 * fzSum / LD.d5[N - 1]).toFixed(1)}%` && (await text('ro4')) === `${grp(LD.S0[N - 1])} · ${grp(LD.S1[N - 1])} · ${grp(LD.S3[N - 1])}`);
await click('#areaChips [data-area="frozen"]'); i = await info();
const mxFz = Math.max(...LD.areas.flatMap((a) => a.frozen));
check('…the frozen chip switches every ribbon to its frozen count over the largest frozen area count', i.area === 'frozen' && i.ribbons.every((r, k) => r.value === LD.areas[k].frozen[N - 1] && near(r.height, H * LD.areas[k].frozen[N - 1] / mxFz)));
await setFrac(day('2026-08-20') / (N - 1));
check('…before the state files exist, every area’s frozen ribbon is zero and the readout says why', (await info()).ribbons.every((r) => r.value === 0) && /没有状态片/.test(await text('ro5')));

/* ---------- digestion ---------- */
await click('#modeChips [data-mode="digest"]'); await setFrac(day('2026-10-20') / (N - 1)); i = await info();
const k20 = day('2026-10-20'), ent = LD.open[k20] + LD.partial[k20] + LD.absorbed[k20] + LD.nonprop[k20], cl = LD.absorbed[k20] + LD.nonprop[k20];
check('digestion view: closed = absorbed + nonpropositional, over all entries in the four directories, recomputed', i.closed === cl && i.entries === ent && near(i.share, cl / ent) && (await text('ro4')) === `${grp(cl)} / ${grp(ent)} = ${(100 * cl / ent).toFixed(1)}%`);
check('…the readouts give the atom store, the four directories and the change from the day before', (await text('ro2')) === grp(LD.atoms[k20]) && (await text('ro3')) === `${grp(LD.open[k20])} · ${grp(LD.absorbed[k20])} · ${grp(LD.nonprop[k20])} · ${grp(LD.partial[k20])}` && (await text('ro5')).startsWith(LD.open[k20] - LD.open[k20 - 1] > 0 ? '+' : '−'));

/* ---------- problems ---------- */
await click('#modeChips [data-mode="problems"]');
let calOK = true;
for (const d of [LD.days[0], '2026-08-31', '2026-09-15', '2026-10-01', LD.asOf]) {
  await setFrac(day(d) / (N - 1)); const j = await info(), k = day(d);
  if (j.cal.wd !== zellerMon0(d) || j.cal.week !== week(d) || j.cum.proved !== cumKind('proved', k) || j.cum.refuted !== cumKind('refuted', k) || j.cum.none !== cumKind('none', k)) { calOK = false; detail = `${d} ${JSON.stringify(j.cal)}`; }
}
check('problem calendar: weekday by Zeller’s congruence, week from month lengths, cumulative proved / refuted / no record (five days)', calOK, detail);
check('…17 weeks, starting from the Monday on or before the first day', (await info()).cal.weeks === week(LD.asOf) + 1 && week(LD.asOf) + 1 === 17);
check('…today: 848 proved, 495 refuted, 149 without a record; refuted share among recorded', (await text('ro3')) === `${grp(LD.resolutions.proved)} · ${grp(LD.resolutions.refuted)} · ${grp(LD.resolutions.none)}` && (await text('ro5')) === `${(100 * LD.resolutions.refuted / (LD.resolutions.proved + LD.resolutions.refuted)).toFixed(1)}%` && LD.resolutions.proved === 848 && LD.resolutions.refuted === 495);

/* ---------- presets ---------- */
const note = () => text('presetNote');
await page.click('[data-preset="dayOne"]'); const st1 = await state(); await settle(); await pause(); await setFrac(0); i = await info();
check('day-one preset: starts playing from the first day on the log scale; its note gives the commit, theory and Lean counts of that day and the next', st1.preset === 'dayOne' && st1.playing === true && st1.nowFrac < 0.02 && st1.scale === 'log' && i.i === 0 && (await note()).includes(`dev 上有 ${grp(LD.prs[0])} 个提交、${grp(LD.theory[0])} 份理论卷文件、${grp(LD.d5[0])} 个 Lean 模块`) && (await note()).includes(`第二天已有 ${grp(LD.d5[1])} 个 Lean 模块`) && (await note()).includes(`全部 ${N} 天`), JSON.stringify(st1).slice(0, 120));
await preset('firstFreeze'); i = await info();
const f13 = day('2026-08-13');
check('first-freeze preset: 2026-08-13 is the first day with accepted events, 629 of them, with 559 Lean modules', i.day === '2026-08-13' && LD.frozenAccepted.findIndex((x) => x > 0) === f13 && LD.frozenAccepted[f13] === 629 && (await note()).includes('629 个 accepted') && (await note()).includes(`${grp(LD.d5[f13])} 个 Lean 模块`));
await preset('migration'); i = await info();
const f04 = day('2026-09-04');
check('migration preset: 2026-09-04 is the first day with state files, 3 318 events and 3 309 state files, and 10-11 the last day with events', i.day === '2026-09-04' && LD.frozenState.findIndex((x) => x > 0) === f04 && LD.frozenAccepted[f04] === 3318 && LD.frozenState[f04] === 3309 && LD.days[LD.frozenAccepted.map((x, k) => (x > 0 ? k : -1)).filter((k) => k >= 0).pop()] === '2026-10-11' && (await note()).includes('3 318 个事件、3 309 个状态片'));
await preset('areas');
check('areas preset: the areas view at the last day, naming the three largest areas', (await info()).mode === 'areas' && (await note()).includes(`${LD.areas[0].name} ${grp(LD.areas[0].d5[N - 1])}`) && (await note()).includes(LD.areas[2].name));
await preset('ingest'); i = await info();
const openUp = LD.open.map((x, k) => (k ? x - LD.open[k - 1] : x)), k27 = day('2026-09-27');
check('ingest preset: 2026-09-27 is the largest one-day rise of residual-open (+11 865), with the atom store and the merges of that day', i.mode === 'digest' && i.day === '2026-09-27' && openUp.indexOf(Math.max(...openUp)) === k27 && openUp[k27] === 11865 && (await note()).includes('增加 11 865') && (await note()).includes(`增加 ${grp(LD.atoms[k27] - LD.atoms[k27 - 1])}`) && (await note()).includes(`合并 ${grp(LD.prs[k27] - LD.prs[k27 - 1])} 次`));
await preset('settle'); i = await info();
const k14 = day('2026-10-14');
check('settle preset: on 2026-10-14 nonpropositional grows by 3 572 and residual-open shrinks, both from the data', i.day === '2026-10-14' && LD.nonprop[k14] - LD.nonprop[k14 - 1] === 3572 && (await note()).includes('增加 3 572') && (await note()).includes(`减少 ${grp(LD.open[k14 - 1] - LD.open[k14])}`));
await preset('problems');
check('problems preset: the calendar view, quoting today’s 848 / 495 / 149', (await info()).mode === 'problems' && (await note()).includes('848 份被证明') && (await note()).includes('495 份被反驳') && (await note()).includes('149 份没有结算记录'));

/* ---------- playing ---------- */
await preset('now'); await setFrac(0.97); await D(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing to the last day raises the reached toast', await waitToast(/到了/));
await pause(); await D(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');

/* ---------- language ---------- */
await click('#modeChips [data-mode="digest"]');
await page.click('[data-lang-set="en"]');
await page.waitForFunction(() => /Custom/.test(document.getElementById('presetNote').textContent), null, { timeout: 30000 }).catch(() => {}); await waitFrames(3);
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
for (const p of ['now', 'areas', 'settle', 'problems']) {
  await preset(p); await setFrac(0.6);
  const leftovers = await D(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags.slice(0, 120));
}
check('English title', (await D(() => document.title)).startsWith('LEDGER//GROWTH · How the truth ledger grows'));
check('English rail marks use month names', (await D(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' '))) === `${LD.days[0].slice(5)} Aug Sep Oct ${LD.asOf.slice(5)}`);
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D(() => document.getElementById('drawer').hidden)) === false);
check('drawer links CLAUDE.md and the five counted directories', (await D(() => { const h = [...document.querySelectorAll('#drawer .en a')].map((a) => a.href).join(' '); return ['trureturing/blob/dev/CLAUDE.md', 'tree/dev/D5', 'tree/dev/Golden/Frozen/state', 'tree/dev/Problems', 'tree/dev/Meta/Digestion', 'tree/dev/docs/develop/theory'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="ledger-growth"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.LG_DEBUG && LG_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D(() => document.body.dataset.vizId)) === 'ledger-growth');

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
