#!/usr/bin/env node
// Browser regression suite for viz/exit-disk (Playwright + Chromium with software WebGL).
//   node tests/exit-disk.test.mjs
// Reads page state through the read-only window.EX_DEBUG probe and checks it against independent implementations: the integer
// certificates transcribed from the Lean module (checked with BigInt), an exact fraction-free (Bareiss) solve of t = 1 + P t,
// Gauss–Seidel iteration, breadth-first connectivity, and a direct recomputation of P^k 1.
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
  const start = await page.evaluate(() => EX_DEBUG.frames());
  await page.waitForFunction((f0) => !EX_DEBUG.pending() && EX_DEBUG.frames() >= f0 + 2, start, { timeout: 120000 });
};
const click = async (sel) => { await page.click(sel); await settle(); };
const pause = async () => { if (await D2(() => EX_DEBUG.state().playing)) await click('#play'); };
const preset = async (p) => { await click(`[data-preset="${p}"]`); await pause(); };
const setT = async (t) => { await D2((t) => EX_DEBUG.setT(t), t); await settle(); };
const info = () => D2(() => EX_DEBUG.info());
const state = () => D2(() => EX_DEBUG.state());
const text = (id) => D2((id) => document.getElementById(id).textContent, id);
const waitFrames = async (n) => { const f0 = await D2(() => EX_DEBUG.frames()); await page.waitForFunction((t) => EX_DEBUG.frames() >= t, f0 + n, { timeout: 60000 }); };
const waitToast = async (re) => { try { await page.waitForFunction((src) => new RegExp(src).test(document.getElementById('toast').textContent) && getComputedStyle(document.getElementById('toast')).opacity === '1', re.source, { timeout: 60000 }); return true; } catch { return false; } };

/* ---------- exact rationals ---------- */

const babs = (a) => (a < 0n ? -a : a), bgcd = (a, b) => { a = babs(a); b = babs(b); while (b) [a, b] = [b, a % b]; return a; };
const red = (n, d) => { const g = bgcd(n, d); return [n / g, d / g]; };
const DIRS = [[1, 0], [-1, 0], [0, 1], [0, -1]];
const key = (x, y) => `${x},${y}`;
/* fraction-free Gaussian elimination (Bareiss) on (4I − adjacency) t = 4·1; returns τ = Σt / N as a reduced fraction */
function exactTau(cells) {
  const N = cells.length, idx = new Map(cells.map((c, i) => [key(c[0], c[1]), i]));
  const M = cells.map(([x, y], i) => { const r = new Array(N + 1).fill(0n); r[i] = 4n; for (const [dx, dy] of DIRS) { const j = idx.get(key(x + dx, y + dy)); if (j !== undefined) r[j] -= 1n; } r[N] = 4n; return r; });
  let prev = 1n;
  for (let k = 0; k < N; k++) { for (let i = k + 1; i < N; i++) { if (M[i][k] === 0n) { for (let j = k + 1; j <= N; j++) M[i][j] = M[i][j] * M[k][k] / prev; continue; } for (let j = k + 1; j <= N; j++) M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) / prev; M[i][k] = 0n; } prev = M[k][k]; }
  const det = M[N - 1][N - 1], X = new Array(N).fill(0n);
  for (let i = N - 1; i >= 0; i--) { let s = M[i][N] * det; for (let j = i + 1; j < N; j++) s -= M[i][j] * X[j]; X[i] = s / M[i][i]; }
  return red(X.reduce((a, b) => a + b, 0n), BigInt(N) * det);
}
const fval = ([n, d]) => Number(n * 10n ** 15n / d) / 1e15;
const fless = ([a, b], [c, d]) => a * d < c * b;
/* Gauss–Seidel for t = 1 + P t */
function gsTau(cells) {
  const N = cells.length, idx = new Map(cells.map((c, i) => [key(c[0], c[1]), i])), nb = cells.map(([x, y]) => DIRS.map(([dx, dy]) => idx.get(key(x + dx, y + dy))).filter((j) => j !== undefined));
  const t = new Float64Array(N);
  for (let it = 0; it < 200000; it++) { let ch = 0; for (let i = 0; i < N; i++) { let s = 1; for (const j of nb[i]) s += t[j] / 4; ch = Math.max(ch, Math.abs(s - t[i])); t[i] = s; } if (ch < 1e-13) break; }
  return { tau: t.reduce((a, b) => a + b, 0) / N, t };
}
const connectedNode = (cells) => { const s = new Set(cells.map((c) => key(c[0], c[1]))), seen = new Set([key(...cells[0])]), st = [cells[0]]; while (st.length) { const [x, y] = st.pop(); for (const [dx, dy] of DIRS) { const k = key(x + dx, y + dy); if (s.has(k) && !seen.has(k)) { seen.add(k); st.push([x + dx, y + dy]); } } } return seen.size === cells.length; };
const sameSet = (a, b) => a.length === b.length && new Set(a.map((c) => key(c[0], c[1]))).size === a.length && b.every((c) => a.some((d) => d[0] === c[0] && d[1] === c[1]));
/* the Lean certificates (diskNumerator / squareNumerator), constant on dihedral orbits */
const orbit = (x, y) => [Math.max(Math.abs(x), Math.abs(y)), Math.min(Math.abs(x), Math.abs(y))].join(',');
const DISK_NUM = { '0,0': 2955311541n, '1,0': 2886399328n, '1,1': 2816841781n, '2,0': 2680953357n, '2,1': 2609459808n, '2,2': 2396809064n, '3,0': 2342845632n, '3,1': 2267586178n, '3,2': 2046333894n, '3,3': 1689887568n, '4,0': 1879607963n, '4,1': 1796056526n, '4,2': 1555403914n, '4,3': 1195616816n, '4,4': 666720621n, '5,0': 1307824316n, '5,1': 1205979197n, '5,2': 907959568n, '5,3': 594806309n, '6,0': 664082055n, '6,1': 536427526n };
const SQ_NUM = { '0,0': 83246922n, '1,0': 81274462n, '1,1': 79361003n, '2,0': 75239080n, '2,1': 73502624n, '2,2': 68176671n, '3,0': 64786770n, '3,1': 63343902n, '3,2': 58905798n, '3,3': 51131799n, '4,0': 49330356n, '4,1': 48290576n, '4,2': 45080980n, '4,3': 39412880n, '4,4': 30737643n, '5,0': 28063662n, '5,1': 27517226n, '5,2': 25824826n, '5,3': 22811258n, '5,4': 18117486n, '5,5': 11031203n };
const diskA = (x, y) => (x * x + y * y <= 37 ? DISK_NUM[orbit(x, y)] ?? 0n : 0n), squareA = (x, y) => (x >= 0 && x < 11 && y >= 0 && y < 11 ? SQ_NUM[orbit(x - 5, y - 5)] ?? 0n : 0n);
const DD = 68912213n, DQ = 1972460n;
const certOK = (cells, A, D) => cells.every(([x, y]) => { const a = A(x, y), s = DIRS.reduce((acc, [dx, dy]) => acc + A(x + dx, y + dy), 0n); return D <= a && a <= 43n * D && 4n * a === 4n * D + s; });

await page.goto(`${origin}${BASE}viz/exit-disk/`);
await page.waitForFunction(() => window.EX_DEBUG && EX_DEBUG.frames() > 3, null, { timeout: 120000 });
await settle();
let i = await info(), st = await state();
check('starts on the Lean preset, playing from k = 0', st.preset === 'lean' && st.playing === true && i.m === 11);
await pause(); await setT(0.6); i = await info();

/* ---------- the Lean counterexample ---------- */
const disk37 = [];
for (let x = -7; x <= 7; x++) for (let y = -7; y <= 7; y++) if (x * x + y * y <= 37) disk37.push([x, y]);
check('the Lean preset’s challenger is exactly the disk x² + y² ≤ 37, with 121 cells', sameSet(i.cells, disk37) && i.N === 121 && disk37.length === 121);
check('it is connected (independent breadth-first search) and the page agrees', connectedNode(i.cells) && i.conn === true);
check('the Lean disk certificate satisfies 4A = 4D + Σ A(neighbours) and D ≤ A ≤ 43D on every cell (BigInt)', certOK(disk37, diskA, DD));
const sq11 = []; for (let x = 0; x < 11; x++) for (let y = 0; y < 11; y++) sq11.push([x, y]);
check('the Lean square certificate satisfies the same on the 11 × 11 square (BigInt)', certOK(sq11, squareA, DQ));
const sumD = disk37.reduce((a, [x, y]) => a + diskA(x, y), 0n), sumQ = sq11.reduce((a, [x, y]) => a + squareA(x, y), 0n);
check('the certificates average to 198008236169/8338377773 and 2811118983/119333830', sumD * 8338377773n === 198008236169n * 121n * DD && sumQ * 119333830n === 2811118983n * 121n * DQ);
const exD = exactTau(disk37), exQ = exactTau(sq11);
check('an exact Bareiss solve gives the same two fractions', exD[0] === 198008236169n && exD[1] === 8338377773n && exQ[0] === 2811118983n && exQ[1] === 119333830n, `${exD} ${exQ}`);
check('and the disk is strictly larger: 198008236169 · 119333830 > 2811118983 · 8338377773', fless(exQ, exD));
check('the page’s τ(C), τ(Q) agree with the fractions to 10⁻⁹', Math.abs(i.tauC - 198008236169 / 8338377773) < 1e-9 && Math.abs(i.tauQ - 2811118983 / 119333830) < 1e-9, `${i.tauC} ${i.tauQ}`);
const tErr = Math.max(...i.cells.map(([x, y], j) => Math.abs(i.tC[j] - Number(diskA(x, y)) / Number(DD))));
check('every one of the page’s 121 values t(p) on the disk matches the Lean certificate to 10⁻⁹', tErr < 1e-9, `max err ${tErr}`);
check('the page shows the exact fractions in the note under the readouts', /198008236169\/8338377773/.test(await text('roNote')) && /2811118983\/119333830/.test(await text('roNote')));
check('HUD states τ(C) = 23.7466 > τ(Q) = 23.5568', (await text('hudBig')) === 'τ(C) = 23.7466 > τ(Q) = 23.5568');
check('readouts: N, connected, τ(C); the square; the difference and the verdict', (await text('ro1')) === '121 · 是 · 23.7466' && (await text('ro2')) === '11 × 11 · 23.5568' && (await text('ro3')) === '+0.1898 · C 胜过正方形：猜想的反例');
check('pills show N = 11², τ(C) and the difference', /121 = 11²/.test(await text('pillA')) && /23\.7466/.test(await text('pillB')) && /\+0\.1898/.test(await text('pillC')));

/* ---------- survival and walkers ---------- */
const P1 = (cells, K) => { const idx = new Map(cells.map((c, j) => [key(c[0], c[1]), j])); let u = cells.map(() => 1); const out = [1]; for (let k = 1; k <= K; k++) { u = cells.map(([x, y]) => DIRS.reduce((a, [dx, dy]) => { const j = idx.get(key(x + dx, y + dy)); return a + (j === undefined ? 0 : u[j]); }, 0) / 4); out.push(u.reduce((a, b) => a + b, 0) / cells.length); } return out; };
const sv = P1(disk37, i.K);
check('S_C(k) matches a direct recomputation of the mean of Pᵏ1 for every k ≤ K', i.survC.length === i.K + 1 && sv.every((v, k) => Math.abs(v - i.survC[k]) < 1e-12));
check('S(0) = 1 and S(k) decreases strictly', i.survC[0] === 1 && i.survQ[0] === 1 && i.survC.every((v, k) => k === 0 || v < i.survC[k - 1]) && i.survQ.every((v, k) => k === 0 || v < i.survQ[k - 1]));
const longC = await D2((c) => EX_DEBUG.survival(c, 3000), disk37), areaC = longC.reduce((a, b) => a + b, 0);
check('the area under the survival curve is τ: Σ_{k ≤ 3000} S_C(k) = 23.7466… to 10⁻⁹', Math.abs(areaC - 198008236169 / 8338377773) < 1e-9, `${areaC}`);
check('readout k and S_C(k) follow the rail: k = ⌊0.6 K⌋', i.s === Math.floor(0.6 * i.K) && Math.abs(i.SC - i.survC[i.s]) < 1e-15 && (await text('ro4')).startsWith(i.SC.toFixed(4)));
check('the walkers still inside are those whose exit step exceeds k', i.inC === i.walkersT[0].filter((T) => T > i.s).length && i.inQ === i.walkersT[1].filter((T) => T > i.s).length);
check('the Monte Carlo estimates are within 4 standard errors of τ (4000 walkers each)', Math.abs(i.mcC[0] - i.tauC) < 4 * i.mcC[1] && Math.abs(i.mcQ[0] - i.tauQ) < 4 * i.mcQ[1], `${i.mcC} ${i.mcQ}`);
check('every walker leaves after at least one step', i.walkersT.flat().every((T) => T >= 1));
const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
check('3D labels name C and Q with their τ and the walkers inside', tags.includes('C · τ = 23.7466') && tags.includes('Q = 11 × 11 · τ = 23.5568') && tags.includes(`还在里面 ${i.inC} / 160`), tags);

/* ---------- the other presets, checked exactly or by an independent iteration ---------- */
const rows = (r) => { const out = []; r.forEach((s, k) => [...s].forEach((ch, x) => { if (ch === '#') out.push([x, r.length - 1 - k]); })); return out; };
await preset('m7'); i = await info();
const m7 = rows(['.######.', '.#######', '########', '########', '########', '.#######', '..#####.']);
const sq = (m) => { const o = []; for (let x = 0; x < m; x++) for (let y = 0; y < m; y++) o.push([x, y]); return o; };
const e7 = exactTau(m7), q7 = exactTau(sq(7));
check('N = 49: the shape has 49 cells, is connected, and beats the 7 × 7 square exactly (Bareiss)', i.N === 49 && sameSet(i.cells, m7) && connectedNode(m7) && fless(q7, e7), `${fval(e7)} > ${fval(q7)}`);
check('…and the page’s values 11.2324 > 11.1756 agree with the exact ones to 10⁻⁹', Math.abs(i.tauC - fval(e7)) < 1e-9 && Math.abs(i.tauQ - fval(q7)) < 1e-9 && (await text('hudBig')) === 'τ(C) = 11.2324 > τ(Q) = 11.1756');
let cs = await D2((c) => EX_DEBUG.climbStep(c), m7);
check('no single-cell move raises τ for the 49-cell shape: it is a local maximum', cs.best === null && cs.tried > 0, `tried ${cs.tried}`);
let cells = await D2(() => { const N = 49, cx = 0.4, cy = 0.15, p = []; for (let x = -8; x <= 8; x++) for (let y = -8; y <= 8; y++) p.push([x, y, (x - cx) ** 2 + (y - cy) ** 2]); p.sort((a, b) => a[2] - b[2]); return p.slice(0, N).map((q) => [q[0], q[1]]); });
let steps = 0;
for (;;) { const r = await D2((c) => EX_DEBUG.climbStep(c), cells); if (!r.best) break; cells = r.best.cells; steps++; if (steps > 60) break; }
check('climbing from the 49 points nearest to (0.4, 0.15) ends at τ = 11.232381… (the preset’s value)', Math.abs((await D2((c) => EX_DEBUG.tau(c).mean, cells)) - fval(e7)) < 1e-9, `${steps} steps`);
await preset('m6'); i = await info();
const m6 = rows(['.####..', '######.', '#######', '#######', '#######', '.#####.']), e6 = exactTau(m6), q6 = exactTau(sq(6));
check('N = 36: the shape (36 cells, connected) loses to the 6 × 6 square exactly: 8.7220 < 8.7816', sameSet(i.cells, m6) && connectedNode(m6) && fless(e6, q6) && Math.abs(i.tauC - fval(e6)) < 1e-9 && /8\.7220 < τ\(Q\) = 8\.7816/.test(await text('hudBig')));
check('the verdict says the square is larger', (await text('ro3')).endsWith('正方形更大'));
/* the test's own restart search at 6 × 6: hill climbing from ellipse-shaped starts never passes the square */
let best6 = 0; const rnd = ((a) => () => { a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; })(99);
for (let r = 0; r < 24; r++) {
  const cx = rnd(), cy = rnd(), a = 0.7 + 0.7 * rnd(), pts = []; for (let x = -9; x <= 9; x++) for (let y = -9; y <= 9; y++) pts.push([x, y, (x - cx) ** 2 / a + (y - cy) ** 2 * a]);
  pts.sort((p, q) => p[2] - q[2]); let c = pts.slice(0, 36).map((p) => [p[0], p[1]]); if (!connectedNode(c)) continue;
  for (let k = 0; k < 60; k++) { const res = await D2((cc) => EX_DEBUG.climbStep(cc), c); if (!res.best) { best6 = Math.max(best6, res.base); break; } c = res.best.cells; }
}
check('24 further hill climbs at 6 × 6 (test’s own starts) stay below the square', best6 > 0 && best6 < fval(q6), `best ${best6}`);
await preset('local'); i = await info();
const loc = sq11.filter(([x, y]) => !(x === 0 && y === 10)).concat([[5, -1]]), eL = exactTau(loc);
check('the one-move preset: corner (0, 10) moved to (5, −1), exactly smaller than the square', sameSet(i.cells, loc) && fless(eL, exQ) && Math.abs(i.tauC - fval(eL)) < 1e-9 && Math.abs(i.tauC - 23.531197871385) < 1e-9);
cs = await D2((c) => EX_DEBUG.climbStep(c), sq11);
check('from the 11 × 11 square: 5280 connected single-cell moves, none raises τ, the best gives 23.531197871…', cs.tried === 5280 && cs.best === null && Math.abs(cs.top.tau - fval(eL)) < 1e-9, `tried ${cs.tried} top ${cs.top && cs.top.tau}`);
await preset('m15'); i = await info();
const d72 = []; for (let x = -9; x <= 9; x++) for (let y = -9; y <= 9; y++) if (x * x + y * y <= 72) d72.push([x, y]);
const g15 = gsTau(d72), gq15 = gsTau(sq(15));
check('N = 225: the disk x² + y² ≤ 72 has 225 cells; Gauss–Seidel gives 42.1002 > 40.4316, as on the page', d72.length === 225 && sameSet(i.cells, d72) && Math.abs(g15.tau - i.tauC) < 1e-8 && Math.abs(gq15.tau - i.tauQ) < 1e-8 && g15.tau.toFixed(4) === '42.1002' && gq15.tau.toFixed(4) === '40.4316');
check('the climb button is disabled above 144 cells', await D2(() => document.getElementById('climbBtn').disabled));
await preset('eden'); i = await info();
check('the Eden cluster has 121 connected cells and τ below 10 (Gauss–Seidel agrees)', i.N === 121 && connectedNode(i.cells) && i.tauC < 10 && Math.abs(gsTau(i.cells).tau - i.tauC) < 1e-8, `${i.tauC}`);

/* ---------- the dossier's table and the page's disks ---------- */
const table = await D2(() => { const win = []; for (let m = 5; m <= 24; m++) { const N = m * m, tq = EX_DEBUG.tau(EX_DEBUG.shapes.square(m)).mean; let ok = false; for (const [cx, cy] of [[0, 0], [0.5, 0], [0.5, 0.5]]) for (let r4 = 0; r4 < 4 * 200; r4++) { const d = EX_DEBUG.shapes.disk(r4 / 4, cx, cy); if (d.length > N) break; if (d.length === N && EX_DEBUG.tau(d).mean > tq) ok = true; } if (ok) win.push(m); } return win; });
check('disks centred at (0,0), (½,0), (½,½) with exactly m² cells win for m = 11, 13–16, 18, 20–24 (the dossier’s list)', table.join(',') === '11,13,14,15,16,18,20,21,22,23,24', table.join(','));
const bd = await D2(() => [7, 8, 11].map((m) => EX_DEBUG.bestDisk(m)));
const nearestNode = (N, cx, cy) => { const p = []; for (let x = -20; x <= 20; x++) for (let y = -20; y <= 20; y++) p.push([x, y, (x - cx) ** 2 + (y - cy) ** 2]); p.sort((a, b) => a[2] - b[2]); return p.slice(0, N).map((q) => [q[0], q[1]]); };
check('the slider’s best disks are the m² lattice points nearest to their centre, connected', bd.every((b, j) => sameSet(b.cells, nearestNode([7, 8, 11][j] ** 2, b.cx, b.cy)) && connectedNode(b.cells)));
const bd8 = exactTau(bd[1].cells), q8 = exactTau(sq(8));
check('m = 8: the best disk beats the 8 × 8 square exactly (13.8817 > 13.8499); m = 7: it does not', fless(q8, bd8) && fval(bd8).toFixed(4) === '13.8817' && bd[0].tau < fval(q7) && bd[0].tau.toFixed(4) === '11.0474', `${fval(bd8)} ${bd[0].tau}`);
check('m = 11: the best disk reaches 24.4803', bd[2].tau.toFixed(4) === '24.4803');
await D2(() => { const e = document.getElementById('mIn'); e.value = 8; e.dispatchEvent(new Event('input')); }); await settle(); i = await info();
check('the size slider at m = 8 loads that disk and reports a counterexample', i.m === 8 && sameSet(i.cells, bd[1].cells) && (await state()).preset === null && (await text('ro3')).endsWith('C 胜过正方形：猜想的反例') && /圆心 \(/.test(await text('sysNote')));

/* ---------- editing ---------- */
await preset('lean');
const clickCell = async (x, y) => { const p = await D2(([x, y]) => { const c = EX_DEBUG.cellCss(x, y), r = document.getElementById('c1').getBoundingClientRect(); return { x: r.left + c.x, y: r.top + c.y }; }, [x, y]); await page.mouse.click(p.x, p.y); await settle(); };
await clickCell(4, 6);
check('clicking an empty cell with nothing picked up does nothing', (await state()).sel === null);
await clickCell(0, 6);
check('clicking a cell of C picks it up', JSON.stringify((await state()).sel) === '[0,6]' && /\(0, 6\)/.test(await text('editNote')));
await clickCell(0, 6);
check('clicking it again puts it back', (await state()).sel === null);
await clickCell(0, 6); await clickCell(0, 7);
check('a move that would disconnect C is refused', (await info()).N === 121 && sameSet((await info()).cells, disk37) && await waitToast(/断开/));
check('the picked-up cell stays picked up after a refused move', JSON.stringify((await state()).sel) === '[0,6]');
await clickCell(2, 6); i = await info();
const moved = disk37.filter(([x, y]) => !(x === 0 && y === 6)).concat([[2, 6]]), eM = exactTau(moved);
check('moving (0, 6) to (2, 6) keeps 121 cells and recomputes τ exactly', i.N === 121 && sameSet(i.cells, moved) && Math.abs(i.tauC - fval(eM)) < 1e-9 && (await state()).preset === null && await waitToast(/→ \(2,6\)/));
await preset('local'); await click('#climbBtn'); i = await info();
const two = sq11.filter(([x, y]) => !(y === 10 && (x === 0 || x === 10))).concat([[5, -1], [6, -1]]), eT = exactTau(two);
check('“Climb one step” from the one-move preset moves (10, 10) to (6, −1): two moves beat the square exactly (23.6668 > 23.5568)', sameSet(i.cells, two) && fless(exQ, eT) && Math.abs(i.tauC - fval(eT)) < 1e-9 && fval(eT).toFixed(4) === '23.6668' && await waitToast(/\(10,10\) → \(6,-1\)/), `${i.tauC}`);
await preset('m7'); await click('#climbBtn');
check('…and on the 49-cell shape reports a local maximum', (await info()).tauC === (await D2((c) => EX_DEBUG.tau(c).mean, m7)) && await waitToast(/局部最大/));
await click('#squareBtn'); i = await info();
check('“Start from the square” makes C the square: equal τ', sameSet(i.cells, sq(7)) && i.tauC === i.tauQ && (await text('ro3')).endsWith('相等'));

/* ---------- labels, rail, keys, playback ---------- */
const boxes = await D2(() => [...document.querySelectorAll('.side .lean')].map((b) => [b.className, b.querySelector('.ok').textContent, b.textContent]));
check('label boxes: two LEAN ✓, NUM, dossier ARGUED, page ARGUED (dashed), OPEN, LIT', boxes.map((b) => b[1]).join(' ') === 'LEAN ✓ LEAN ✓ NUM ARGUED ARGUED OPEN LIT' && /theory/.test(boxes[3][0]) && /page/.test(boxes[4][0]));
check('the LEAN boxes name the frozen declarations', boxes[0][2].includes('SquareClusterExitTimeRefutation.result') && boxes[1][2].includes('integer_certificate'));
check('the LIT box cites the DOI and arXiv number', boxes[6][2].includes('10.1088/2632-072X/aeb36a') && boxes[6][2].includes('2308.07880'));
await preset('lean');
check('the rail marks 0, τ(Q) and K steps', (await D2(() => [...document.querySelectorAll('#marks i')].map((m) => m.textContent).join(' | '))) === `0 步 | τ(Q) | ${(await info()).K} 步`);
await setT(0); await D2(() => document.activeElement && document.activeElement.blur()); await page.keyboard.press('ArrowRight'); await settle();
check('→ advances one step', (await info()).s === 1 && /k = 1 步/.test(await text('clock')));
await page.keyboard.press('ArrowLeft'); await settle();
check('← goes back one step', (await info()).s === 0);
await page.keyboard.press('e'); await settle(); i = await info();
check('E jumps to the last step and pauses', i.s === i.K && (await state()).playing === false);
await page.keyboard.press(' '); await settle();
check('Space toggles playback', (await state()).playing === true);
await D2(() => document.querySelector('#speedChips [data-speed="2.5"]').click());
check('playing to the end reports both areas', await waitToast(/τ\(C\) = 23\.7466 > τ\(Q\) = 23\.5568/));
await pause(); await D2(() => document.querySelector('#speedChips [data-speed="1"]').click());
for (const cam of ['side', 'top', 'iso']) await click(`#camChips [data-cam="${cam}"]`);
check('camera chips switch views', (await D2(() => document.querySelector('#camChips [aria-pressed="true"]').dataset.cam)) === 'iso');
await setT(0.3);
const lit = await D2(() => ['c1', 'c2'].map((id) => { const c = document.getElementById(id), x = c.getContext('2d').getImageData(0, 0, c.width, c.height).data; let n = 0; for (let j = 3; j < x.length; j += 4) if (x[j] > 0) n++; return n; }));
check('both charts are drawn', lit.every((n) => n > 1500), `${lit}`);
await D2(() => window.TRV_THUMB()); await settle();
check('the thumbnail state is the paused Lean preset', (await state()).preset === 'lean' && (await state()).playing === false);
/* ---------- language ---------- */
await page.click('[data-lang-set="en"]'); await waitFrames(3);
for (const p of ['lean', 'm15']) {
  await preset(p); await setT(0.5);
  const leftovers = await D2(() => {
    const bad = []; const w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT); let n;
    while ((n = w.nextNode())) { const t = n.textContent.trim(); if (!/[一-鿿]/.test(t)) continue; const el = n.parentElement; if (!el || el.closest('[hidden]') || el.closest('.langs')) continue; let hiddenByOpacity = false; for (let a = el; a; a = a.parentElement) if (getComputedStyle(a).opacity === '0') { hiddenByOpacity = true; break; } const st = getComputedStyle(el); if (st.display === 'none' || hiddenByOpacity || el.offsetParent === null) continue; bad.push(t.slice(0, 40)); }
    return bad;
  });
  const tags = await D2(() => [...document.querySelectorAll('#tags .tag')].filter(t => t.style.display !== 'none').map(t => t.textContent).join(' | '));
  check(`no visible Chinese left in English mode (${p}), 3D labels included`, leftovers.length === 0 && !/[一-鿿]/.test(tags), leftovers.join(' | ') + ' ' + tags);
}
await click('#squareBtn');
check('custom-settings note switches to English', /Custom/.test(await text('presetNote')));
check('English title', (await D2(() => document.title)).startsWith('EXIT//DISK · A lattice disk outlasts the square: squares do not maximize the mean exit time'));
await page.click('#infoBtn'); await page.waitForFunction(() => document.getElementById('drawer').hidden === false, null, { timeout: 10000 }).catch(() => {});
check('drawer opens', (await D2(() => document.getElementById('drawer').hidden)) === false);
check('drawer links the dossier, the Lean file, the Blueprint, the literature note, the DOI and arXiv', (await D2(() => { const h = [...document.querySelectorAll('#drawer div.en a')].map((a) => a.href).join(' '); return ['rognone-nicosia-2023-square-cluster-exit-time-refutation.md', 'D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.lean', 'Blueprint/D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.md', 'Library/StatisticalMechanics/rognonenicosia2023clusters.md', 'doi.org/10.1088/2632-072X/aeb36a', 'arxiv.org/abs/2308.07880'].every((s) => h.includes(s)); })));
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
await page.click('.card:has(a[href*="exit-disk"]) .enter'); await page.waitForLoadState('load');
await page.waitForFunction(() => window.EX_DEBUG && EX_DEBUG.frames() > 3, null, { timeout: 120000 }).catch(() => {});
check('index card opens this page', (await D2(() => document.body.dataset.vizId)) === 'exit-disk');

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
