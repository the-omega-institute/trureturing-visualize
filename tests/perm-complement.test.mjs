#!/usr/bin/env node
// Browser regression suite for viz/perm-complement (Playwright + Chromium with software WebGL).
//   node tests/perm-complement.test.mjs
// Reads page state through the read-only window.PC_DEBUG probe and checks it against an independent implementation: Lean's
// Definitions 4.1 and 4.3 evaluated on the 0/1 matrices themselves (no involution criterion), an exhaustive search over all
// permutations for n ≤ 8, and the tiling of the grid by the family's supports.
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
  const start = await page.evaluate(() => PC_DEBUG.frames());
  await page.waitForFunction((f0) => !PC_DEBUG.pending() && PC_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D2(() => PC_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D2((t) => PC_DEBUG.setT(t), t); await settle(); };
const info = () => D2(() => PC_DEBUG.info());
const state = () => D2(() => PC_DEBUG.state());
const text = (id) => D2((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D2(() => PC_DEBUG.frames()); await page.waitForFunction((t) => PC_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */

/* ---------- independent implementation: the matrix definitions ---------- */
/* P_ij = 1 exactly when σ(i) = j, as in Lean's entry_one */
const mat = (s) => s.map((x) => Array.from({ length: s.length }, (_, j) => (x === j ? 1 : 0)));
/* Definition 4.1: P_ij = P_hk = Q_ik = 1 ⇒ Q_hj = 1, over every i, h (j, k range over the 1s of P in rows i, h) */
function complementary(P, Q) { const n = P.length; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (P[i][j] === 1) for (let h = 0; h < n; h++) for (let k = 0; k < n; k++) if (P[h][k] === 1 && Q[i][k] === 1 && Q[h][j] !== 1) return false; return true; }
/* Definition 4.3: complementary with disjoint supports */
const strong = (P, Q) => complementary(P, Q) && P.every((r, i) => r.every((x, j) => x !== 1 || Q[i][j] === 0));
const isPerm = (s) => new Set(s).size === s.length && s.every((x) => x >= 0 && x < s.length);
const v2 = (n) => { let a = 0; while (n % 2 === 0) { n /= 2; a++; } return a; };
function* perms(n) { const a = Array.from({ length: n }, (_, i) => i), c = new Array(n).fill(0); yield a.slice(); let i = 0; while (i < n) { if (c[i] < i) { const j = i % 2 ? c[i] : 0; [a[j], a[i]] = [a[i], a[j]]; yield a.slice(); c[i]++; i = 0; } else { c[i] = 0; i++; } } }
const pairwise = (F) => { const M = F.map(mat); for (let a = 0; a < M.length; a++) for (let b = 0; b < M.length; b++) if (a !== b && !strong(M[a], M[b])) return false; return true; };
/* the largest family containing the identity, searched over all n! permutations with the matrix definitions */
function largest(n) {
  const id = Array.from({ length: n }, (_, i) => i), I = mat(id), cand = [];
  for (const s of perms(n)) { const M = mat(s); if (strong(I, M) && strong(M, I)) cand.push(M); }
  const ok = cand.map((A) => cand.map((B) => A !== B && strong(A, B) && strong(B, A)));
  let best = 0; const grow = (size, list) => { if (size + list.length <= best) return; if (!list.length) { best = size; return; } for (let x = 0; x < list.length; x++) { if (size + list.length - x <= best) return; grow(size + 1, list.slice(x + 1).filter((y) => ok[list[x]][y])); } };
  grow(0, cand.map((_, i) => i)); return { max: best + 1, cand: cand.length };
}
const compose = (s, t) => t.map((x) => s[x]), invP = (s) => { const r = []; s.forEach((x, i) => { r[x] = i; }); return r; };

await page.goto(`${origin}${BASE}viz/perm-complement/`);
await page.waitForFunction(() => window.PC_DEBUG && PC_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();

/* ---------- the theorem ---------- */
check('opens on n = 8 with the translation family of k(8) = 8', st.preset === 'lean' && i.n === 8 && i.K === 8 && i.a === 3 && i.m === 1);
let famOK = true; const famBad = [];
for (let n = 1; n <= 32; n++) { const F = await D2((n) => PC_DEBUG.family(n), n); const ok = F.length === 2 ** v2(n) && F.every(isPerm) && new Set(F.map((s) => s.join())).size === F.length && pairwise(F) && F[0].every((x, k) => x === k); if (!ok) { famOK = false; famBad.push(n); } }
check('for n = 1 … 32 the page’s family has 2^v₂(n) distinct permutation matrices, pairwise strongly complementary by Definitions 4.1 and 4.3 (both orders), starting with the identity', famOK, famBad.join(' '));
let relab = true; const rr = (() => { let s = 7; return () => { s = (s * 16807) % 2147483647; return s / 2147483647; }; })();
for (let t = 0; t < 60; t++) { const n = 4 + (t % 5), rand = () => { const a = Array.from({ length: n }, (_, k) => k); for (let k = n - 1; k > 0; k--) { const j = Math.floor(rr() * (k + 1)); [a[k], a[j]] = [a[j], a[k]]; } return a; }; const s = rand(), u = rand(), r = rand(), ri = invP(r); if (strong(mat(s), mat(u)) !== strong(mat(compose(s, ri)), mat(compose(u, ri)))) relab = false; }
check('relabelling (Lean’s row_relabelling): replacing σ, τ by σρ⁻¹, τρ⁻¹ never changes strong complementarity (60 random triples)', relab);
const L = [1, 2, 3, 4, 5, 6, 7, 8].map(largest);
check('an exhaustive search over all n! permutations with the matrix definitions gives maxima 1, 2, 1, 4, 1, 2, 1, 8 for n = 1 … 8', L.every((r, k) => r.max === 2 ** v2(k + 1)), L.map((r) => r.max).join(' '));
const pe = await D2(() => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((n) => PC_DEBUG.exhaustive(n)));
check('the page’s own exhaustive maxima for n ≤ 10 are 2^v₂(n), its candidate counts are those of the test (n ≤ 8) and (n − 1)!!', pe.every((r, k) => r.max === 2 ** v2(k + 1)) && L.every((r, k) => (k + 1) % 2 === 1 || r.cand === pe[k].cand) && [3, 15, 105, 945].every((c, q) => pe[2 * q + 3].cand === c));
await pause(); await setT(1); i = await info();
const cover = Array.from({ length: 8 }, () => new Array(8).fill(0)); i.F.forEach((s) => s.forEach((j, r) => { cover[r][j]++; }));
check('for n = 8 the supports tile the 8 × 8 grid exactly once: a Latin square, the XOR table', cover.every((row) => row.every((c) => c === 1)) && i.F.every((s, v) => s.every((j, r) => j === (r ^ v))));
check('the page’s relative permutation of the newest member is σ₀⁻¹σ, a fixed-point-free involution', i.j === 8 && i.rel.join() === compose(invP(i.F[0]), i.cur).join() && i.rel.every((x, k) => x !== k && i.rel[x] === k) && i.relFPF);

/* ---------- presets ---------- */
const facts = { twelve: [12, 4, 3], six: [6, 2, 3], odd: [9, 1, 9], sixteen: [16, 16, 1], mixed: [24, 8, 3] };
for (const [p, [n, K, m]] of Object.entries(facts)) {
  await preset(p); await setT(1); i = await info();
  const extra = p === 'six' ? i.exh && i.exh.max === 2 && i.exh.cand === 15 : p === 'mixed' ? i.cells === 192 : p === 'sixteen' ? i.cells === 256 : true;
  check(`${p} preset: n = ${n} = ${K} · ${m}, k = ${K}, all members pairwise strongly complementary${p === 'six' ? ', exhaustive maximum 2 of 15 candidates' : p === 'mixed' ? ', 192 cells used' : p === 'sixteen' ? ', all 256 cells' : ''}`, i.n === n && i.K === K && i.m === m && i.j === K && pairwise(i.F) && extra);
}
for (const p of ['lean', 'twelve', 'six', 'odd', 'sixteen', 'mixed']) { await preset(p); const pressed = await D2((n) => document.querySelector(`[data-preset="${n}"]`).getAttribute('aria-pressed'), p); check(`preset ${p} applies and explains itself`, pressed === 'true' && (await text('presetNote')).length > 60); }

/* ---------- readouts and controls ---------- */
await preset('lean'); await setT(1);
check('the readouts give the factorization, the member, the relative permutation, the cells and the search', (await text('ro1')) === '8 = 8 · 1 · 8 · 8' && /^7 6 5 4 3 2 1 0$/.test(await text('ro2')) && /7 6 5 4 3 2 1 0 · 是 · 是/.test(await text('ro3')) && /64 · 64（铺满：拉丁方）/.test(await text('ro4')) && (await text('ro5')) === '8 · 105');
check('the rail marks one member and k(n) members', (await D2(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === '1 个 | 8 个 = k(n)');
await setT(0); await D2(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ adds one member and marks the settings custom', (await info()).j === 2 && (await state()).preset === null && /自定义|Custom/.test(await text('presetNote')));
await page.keyboard.press('e'); await settle();
check('E shows every member and pauses', (await info()).j === 8 && (await state()).playing === false);
await D2(() => { const e = document.getElementById('nIn'); e.value = 20; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the n slider sets n = 20 = 4 · 5: k = 4', i.n === 20 && i.K === 4 && i.m === 5 && i.exh === null);
await preset('twelve'); await D2(() => document.querySelector('#speedChips [data-speed="2.5"]').click()); await click('#play');
check('playing reports the full family', await waitToast(/4 个.*k\(12\) = 2\^2/));
await pause(); await D2(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['front', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D2(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await preset('lean'); await setT(0.6);
const lit = await D2(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'mixed']) {
  await preset(p); await setT(0.5);
  const leftovers = await D2(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await D2(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D2(() => document.title)).startsWith('PERM//COMPLEMENT · At most 2^v₂(n) pairwise strongly complementary permutation matrices'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D2(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D2(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['rajchel-gasiorowski-zyczkowski-2018-strongly-complementary-permutations.md', 'D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.lean', 'Blueprint/D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.md', 'Library/FiniteGroups/rajchelgasiorowskizyczkowski2018robust.md', 'doi.org/10.1007/s11786-018-0384-y', 'arxiv.org/abs/1804.10715'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="perm-complement"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.PC_DEBUG && PC_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D2(() => document.body.dataset.vizId)) === 'perm-complement');

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
