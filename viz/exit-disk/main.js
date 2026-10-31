/* EXIT//DISK · squares do not maximize the mean exit time of lattice clusters
   Rognone and Nicosia (2023) define the mean exit time τ(S) of a cluster S of the square lattice: start a simple random walk at
   a uniformly chosen cell of S and count the steps until it first stands outside S. They conjecture that among connected
   clusters of N = m² cells the m × m square maximizes τ. Refuted in trureturing (SquareClusterExitTimeRefutation.result): the
   lattice disk x² + y² ≤ 37 has 121 cells and τ = 198008236169/8338377773 = 23.7466… > τ(11 × 11) = 23.5568….
   The page solves t = 1 + P t on any cluster, draws t as a dome, lets walkers run on it, plots the survival curve whose area
   is τ, and lets the reader move cells.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Clusters, the exit-time system t = 1 + P t, survival and walkers
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const WHITE = [0.95, 0.97, 1];
const DIRS = [[1, 0], [-1, 0], [0, 1], [0, -1]];
const NW = 160, NEST = 4000, CLIMB_MAX = 144;
const LEAN = { tauC: '198008236169/8338377773', tauQ: '2811118983/119333830', vC: 198008236169 / 8338377773, vQ: 2811118983 / 119333830 };
const ck = (x, y) => `${x},${y}`;
function makeCluster(cells) {
  const idx = new Map(); cells.forEach((c, i) => idx.set(ck(c[0], c[1]), i));
  const nb = cells.map(([x, y]) => DIRS.map(([dx, dy]) => { const j = idx.get(ck(x + dx, y + dy)); return j === undefined ? -1 : j; }));
  return { cells, idx, nb, N: cells.length };
}
function isConnected(cl) {
  if (!cl.N) return false;
  const seen = new Uint8Array(cl.N), st = [0]; seen[0] = 1; let c = 1;
  while (st.length) { const i = st.pop(); for (const j of cl.nb[i]) if (j >= 0 && !seen[j]) { seen[j] = 1; c++; st.push(j); } }
  return c === cl.N;
}
/* conjugate gradients for (I − P) t = 1, where P averages over the four neighbours and counts those outside S as 0 */
function solve(cl, x0) {
  const N = cl.N, nb = cl.nb, x = new Float64Array(N), r = new Float64Array(N), p = new Float64Array(N), Ap = new Float64Array(N);
  const A = (v, out) => { for (let i = 0; i < N; i++) { let s = v[i]; const n = nb[i]; for (let d = 0; d < 4; d++) if (n[d] >= 0) s -= 0.25 * v[n[d]]; out[i] = s; } };
  if (x0) x.set(x0);
  A(x, Ap); let rr = 0;
  for (let i = 0; i < N; i++) { r[i] = 1 - Ap[i]; p[i] = r[i]; rr += r[i] * r[i]; }
  const tol = 1e-26 * N;
  for (let it = 0; it < 6 * N + 50 && rr > tol; it++) {
    A(p, Ap); let pAp = 0; for (let i = 0; i < N; i++) pAp += p[i] * Ap[i];
    const al = rr / pAp; let rr2 = 0;
    for (let i = 0; i < N; i++) { x[i] += al * p[i]; r[i] -= al * Ap[i]; rr2 += r[i] * r[i]; }
    const be = rr2 / rr; rr = rr2;
    for (let i = 0; i < N; i++) p[i] = r[i] + be * p[i];
  }
  return x;
}
const mean = (a) => { let s = 0; for (const v of a) s += v; return s / a.length; };
const tauOf = (cells) => { const cl = makeCluster(cells); return mean(solve(cl)); };
/* S(k) = mean over S of (P^k 1): the probability that a walker from a uniform start is still inside after k steps */
function survival(cl, K) {
  const N = cl.N, out = new Float64Array(K + 1); let u = new Float64Array(N).fill(1), v = new Float64Array(N);
  out[0] = 1;
  for (let k = 1; k <= K; k++) {
    for (let i = 0; i < N; i++) { let s = 0; const n = cl.nb[i]; for (let d = 0; d < 4; d++) if (n[d] >= 0) s += u[n[d]]; v[i] = s / 4; }
    [u, v] = [v, u]; out[k] = mean(u);
  }
  return out;
}
/* Monte Carlo: NEST walkers estimate τ; the first NW keep their paths for the 3D view */
function walkers(cl, seed) {
  const rnd = TRV.mulberry32(seed), Tx = new Int32Array(NEST), off = [0], path = [], ex = [];
  let sum = 0, sum2 = 0;
  for (let w = 0; w < NEST; w++) {
    let i = Math.floor(rnd() * cl.N), s = 0;
    for (;;) {
      if (w < NW) path.push(i);
      const d = Math.floor(rnd() * 4), j = cl.nb[i][d]; s++;
      if (j < 0) { if (w < NW) ex.push([cl.cells[i][0] + DIRS[d][0], cl.cells[i][1] + DIRS[d][1]]); break; }
      i = j;
    }
    Tx[w] = s; sum += s; sum2 += s * s;
    if (w < NW) off.push(path.length);
  }
  const m = sum / NEST, se = Math.sqrt(Math.max(0, sum2 / NEST - m * m) / NEST);
  return { T: Tx, off, path, ex, mean: m, se };
}
/* shapes */
const square = (m) => { const out = []; for (let x = 0; x < m; x++) for (let y = 0; y < m; y++) out.push([x, y]); return out; };
function diskR(R2, cx = 0, cy = 0) { const out = [], B = Math.ceil(Math.sqrt(R2)) + 2; for (let x = -B; x <= B; x++) for (let y = -B; y <= B; y++) if ((x - cx) ** 2 + (y - cy) ** 2 <= R2 + 1e-9) out.push([x, y]); return out; }
/* the N lattice points nearest to (cx, cy); null when the N-th and (N+1)-th distances tie */
function nearest(N, cx, cy) {
  const B = Math.ceil(Math.sqrt(N / Math.PI)) + 4, pts = [];
  for (let x = -B; x <= B; x++) for (let y = -B; y <= B; y++) pts.push([x, y, (x - cx) ** 2 + (y - cy) ** 2]);
  pts.sort((a, b) => a[2] - b[2]);
  if (Math.abs(pts[N - 1][2] - pts[N][2]) < 1e-9) return null;
  return pts.slice(0, N).map((p) => [p[0], p[1]]);
}
const BEST = new Map();
/* the best disk of exactly m² cells over centres on the 0.05 grid of the triangle 0 ≤ cy ≤ cx ≤ ½ */
function bestDisk(m) {
  if (BEST.has(m)) return BEST.get(m);
  let best = null;
  for (let i = 0; i <= 10; i++) for (let j = 0; j <= i; j++) {
    const cx = i * 0.05, cy = j * 0.05, d = nearest(m * m, cx, cy);
    if (!d) continue;
    const cl = makeCluster(d); if (!isConnected(cl)) continue;
    const tau = mean(solve(cl));
    if (!best || tau > best.tau) best = { tau, cx: Math.round(cx * 100) / 100, cy: Math.round(cy * 100) / 100, cells: d };
  }
  BEST.set(m, best); return best;
}
function fromRows(rows) { const out = []; rows.forEach((r, k) => [...r].forEach((ch, x) => { if (ch === '#') out.push([x, rows.length - 1 - k]); })); return out; }
/* Eden growth: add a uniformly chosen empty neighbour of the cluster until it has N cells */
function eden(N, seed) {
  const rnd = TRV.mulberry32(seed), have = new Set([ck(0, 0)]), cells = [[0, 0]], per = new Map();
  const addPer = (x, y) => DIRS.forEach(([dx, dy]) => { const k = ck(x + dx, y + dy); if (!have.has(k)) per.set(k, [x + dx, y + dy]); });
  addPer(0, 0);
  while (cells.length < N) {
    const keys = [...per.keys()].sort(), k = keys[Math.floor(rnd() * keys.length)], c = per.get(k);
    per.delete(k); have.add(k); cells.push(c); addPer(c[0], c[1]);
  }
  return cells;
}
/* one hill-climbing step: the single-cell move that raises τ the most while keeping the cluster connected */
function climbStep(cells) {
  const cl = makeCluster(cells), t0 = solve(cl), base = mean(t0), border = new Map();
  cells.forEach(([x, y]) => DIRS.forEach(([dx, dy]) => { const k = ck(x + dx, y + dy); if (!cl.idx.has(k)) border.set(k, [x + dx, y + dy]); }));
  const bs = [...border.values()].sort((a, b) => a[0] - b[0] || a[1] - b[1]);
  let top = null, tried = 0;
  for (let r = 0; r < cells.length; r++) for (const a of bs) {
    const nc = cells.filter((_, i) => i !== r).concat([a]), ncl = makeCluster(nc);
    if (!isConnected(ncl)) continue;
    tried++;
    const x0 = new Float64Array(nc.length); for (let i = 0; i < nc.length - 1; i++) x0[i] = t0[i < r ? i : i + 1]; x0[nc.length - 1] = 1;
    const tau = mean(solve(ncl, x0));
    if (!top || tau > top.tau) top = { tau, from: cells[r].slice(), to: a.slice(), cells: nc };
  }
  return { base, tried, top, best: top && top.tau > base + 1e-11 ? top : null };
}

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean', m: 11, cells: [], cver: 0, sel: null, origin: null, seed: 1 };
const PRESETS = {
  lean: { m: 11, cells: () => diskR(37), origin: ['圆盘 x² + y² ≤ 37（Lean 的反例）', 'the disk x² + y² ≤ 37 (Lean’s counterexample)'],
    zh: 'Lean 的反例：圆盘 x² + y² ≤ 37 有 121 个格子，和 11 × 11 的正方形一样多，并且连通。从圆盘上均匀起步，平均 23.7466 步离开；正方形只要 23.5568 步。穹顶的高度是每个起点的期望步数：正方形的四个角很低。',
    en: 'Lean’s counterexample: the disk x² + y² ≤ 37 has 121 cells, as many as the 11 × 11 square, and is connected. From a uniform start on the disk a walker needs 23.7466 steps on average to leave; on the square only 23.5568. The height of the dome is the expected number of steps from each start: the four corners of the square sit low.' },
  m7: { m: 7, cells: () => fromRows(['.######.', '.#######', '########', '########', '########', '.#######', '..#####.']), origin: ['页面爬山找到的 49 格形状', 'a 49-cell shape found by the page’s hill climbing'],
    zh: '页面找到的更小反例：49 个格子。从圆心 (0.4, 0.15) 最近的 49 个格点出发，每次做最好的单格移动，直到没有改进：τ = 11.2324 > 7 × 7 正方形的 11.1756。页面数值，未形式化。按「爬一步」可以看到这里已经没有能提高 τ 的单格移动。',
    en: 'A smaller counterexample found by the page: 49 cells. Starting from the 49 lattice points nearest to (0.4, 0.15) and making the best single-cell move until nothing improves gives τ = 11.2324 > 11.1756 for the 7 × 7 square. Page numbers, not formalized. Press “Climb one step” to see that no single-cell move raises τ here.' },
  m15: { m: 15, cells: () => diskR(72), origin: ['圆盘 x² + y² ≤ 72', 'the disk x² + y² ≤ 72'],
    zh: 'N = 225 是原文用 Eden 生长抽样的规模。圆盘 x² + y² ≤ 72 有 225 个格子：τ = 42.1002 > 15 × 15 正方形的 40.4316（卷宗记录，页面复算）。规模越大，圆盘领先越多。',
    en: 'N = 225 is the size the source sampled by Eden growth. The disk x² + y² ≤ 72 has 225 cells: τ = 42.1002 > 40.4316 for the 15 × 15 square (recorded in the dossier, recomputed by the page). The larger the size, the further the disk pulls ahead.' },
  m6: { m: 6, cells: () => fromRows(['.####..', '######.', '#######', '#######', '#######', '.#####.']), origin: ['页面爬山在 6 × 6 找到的最好形状', 'the best shape the page’s hill climbing found at 6 × 6'],
    zh: '6 × 6：为这个页面离线做的搜索——从 120 个随机的椭圆形出发做单格爬山——找到的最好形状就是这个，τ = 8.7220，仍小于正方形的 8.7816。这只说明没找到更好的，不是证明正方形在这里最大。',
    en: '6 × 6: an offline search made for this page — hill climbing from 120 random elliptical starts — finds this shape as its best, τ = 8.7220, still below 8.7816 for the square. This only says nothing better was found; it does not prove that the square is the maximum here.' },
  local: { m: 11, cells: () => square(11).filter(([x, y]) => !(x === 0 && y === 10)).concat([[5, -1]]), origin: ['11 × 11 正方形搬走一个角', 'the 11 × 11 square with one corner moved'],
    zh: '把 11 × 11 正方形的角 (0, 10) 搬到下边中点之外 (5, −1)：τ = 23.5312，比正方形小。页面检查了全部 5280 个保持连通的单格移动，最好的就是这一个，仍小于 23.5568：正方形是局部最大。但在这里按「爬一步」：再把另一个上角 (10, 10) 搬到 (6, −1)，τ 升到 23.6668，超过正方形——只动两个格子就够了（页面数值）。',
    en: 'Move the corner (0, 10) of the 11 × 11 square to (5, −1), just below the middle of the bottom edge: τ = 23.5312, less than the square. The page checks all 5280 single-cell moves that keep the cluster connected; this is the best one, and it still stays below 23.5568. The square is a local maximum. But press “Climb one step” here: moving the other top corner (10, 10) to (6, −1) lifts τ to 23.6668, above the square — moving two cells is already enough (page numbers).' },
  eden: { m: 11, cells: () => eden(121, 1), origin: ['121 格的 Eden 团簇（种子 1）', 'a 121-cell Eden cluster (seed 1)'],
    zh: 'Eden 生长：从一个格子开始，每次在边界上随机加一个格子，直到 121 个——原文用这种方法抽样团簇。长出来的团簇枝杈多、边界长，τ 不到 10，远小于正方形；在这样的样本里正方形确实总是最大。',
    en: 'Eden growth: start from one cell and keep adding a random empty neighbour until there are 121 — the way the source samples clusters. The result is branched with a long boundary and τ is below ten, far below the square; among such samples the square is indeed always the largest.' }
};
let GEO = null, geoId = 0, MODEL = null, dirty = true;
function geometry() {
  const key = `${S.m}|${S.cver}|${S.seed}`;
  if (GEO && GEO.key === key) return GEO;
  const C = makeCluster(S.cells), Q = makeCluster(square(S.m)), tC = solve(C), tQ = solve(Q), tauC = mean(tC), tauQ = mean(tQ);
  const K = Math.min(600, Math.ceil(5 * Math.max(tauC, tauQ)));
  const exact = S.preset === 'lean' ? LEAN : null;
  GEO = { key, id: ++geoId, m: S.m, C, Q, tC, tQ, tauC, tauQ, K, conn: isConnected(C), N: C.N,
    tmax: Math.max(...tC, ...tQ), survC: survival(C, K), survQ: survival(Q, K), wC: walkers(C, 1000 + S.seed), wQ: walkers(Q, 2000 + S.seed), exact };
  GEO.Fr = frameOf(GEO);
  return GEO;
}
function build() {
  const G = geometry(), k = S.t * G.K, s = Math.min(G.K, Math.floor(k));
  const inside = (w) => { let c = 0; for (let i = 0; i < NW; i++) if (w.T[i] > s) c++; return c; };
  MODEL = Object.assign({}, G, { k, s, SC: G.survC[s], SQ: G.survQ[s], inC: inside(G.wC), inQ: inside(G.wQ) });
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const css = (c, a = 1) => `rgba(${c.map((x) => Math.round(255 * Math.min(1, x))).join(',')},${a})`;
const f4 = (x) => x.toFixed(4);
const cmp = (a, b) => (a > b + 1e-12 ? '>' : a < b - 1e-12 ? '<' : '=');

/* =====================================================================
   4. 3D scene: two domes of height t(p) side by side, the walkers riding on them
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const OFF = 2.75, SPAN = 4.5, HMAX = 2.3, LINES_MAX = 14000, PTS_MAX = 1700;
const CAMS = { iso: [0.0001, 0.98, 12.5], side: [0.0001, 1.42, 11.5], top: [0.0001, 0.05, 12.5] };
const cam = { theta: 0.0001, phi: 0.98, r: 12.5, tTheta: 0.0001, tPhi: 0.98, tR: 12.5 };
const VS = `
attribute vec3 aColor; attribute float aAlpha; attribute float aSize;
uniform float uScale;
varying vec3 vCol; varying float vA;
void main(){
  vec4 mv = modelViewMatrix * vec4(position, 1.0);
  gl_Position = projectionMatrix * mv;
  gl_PointSize = aAlpha < 0.004 ? 0.0 : uScale * aSize / max(0.1, -mv.z);
  vCol = aColor; vA = aAlpha;
}`;
const FS = `
varying vec3 vCol; varying float vA;
void main(){
  vec2 d = gl_PointCoord - 0.5;
  float r = length(d) * 2.0;
  float a = smoothstep(1.0, 0.55, r) * vA;
  if (a < 0.01) discard;
  gl_FragColor = vec4(vCol, a);
}`;
const additive = { transparent: true, depthWrite: false, depthTest: false, blending: window.THREE ? THREE.AdditiveBlending : 2 };
function dyn(g, nm, n, size) { const a = new THREE.BufferAttribute(new Float32Array(n * size), size); a.setUsage(THREE.DynamicDrawUsage); g.setAttribute(nm, a); return a; }
function initGL() {
  try { renderer = new THREE.WebGLRenderer({ canvas: glCanvas, antialias: true, alpha: false, powerPreference: 'high-performance' }); } catch (err) { renderer = null; }
  if (!renderer || !window.THREE) {
    const d = document.createElement('div'); d.className = 'nogl';
    d.textContent = T('这个浏览器没有提供 WebGL，三维视图无法显示。下方的两张图和右侧读数仍然可用。', 'This browser does not provide WebGL, so the 3D view cannot be shown. The two charts below and the readouts still work.');
    stage.appendChild(d); return;
  }
  glOK = true;
  renderer.setPixelRatio(Math.min(2, window.devicePixelRatio || 1));
  renderer.setClearColor(0x02040a, 1);
  scene3 = new THREE.Scene();
  camera = new THREE.PerspectiveCamera(38, 1, 0.05, 100);
  const g = new THREE.BufferGeometry(); dyn(g, 'position', LINES_MAX, 3); dyn(g, 'color', LINES_MAX, 3);
  lines = new THREE.LineSegments(g, new THREE.LineBasicMaterial({ vertexColors: true, ...additive })); lines.frustumCulled = false; scene3.add(lines);
  const gp = new THREE.BufferGeometry(); dyn(gp, 'position', PTS_MAX, 3); dyn(gp, 'aColor', PTS_MAX, 3); dyn(gp, 'aAlpha', PTS_MAX, 1); dyn(gp, 'aSize', PTS_MAX, 1);
  pts = new THREE.Points(gp, new THREE.ShaderMaterial({ vertexShader: VS, fragmentShader: FS, uniforms: { uScale: { value: 60 } }, ...additive }));
  pts.frustumCulled = false; scene3.add(pts);
}
/* one shared cell size, so both clusters are drawn at the same scale; the challenger C on the left, the square Q on the right */
function frameOf(G) {
  const box = (cl) => { const xs = cl.cells.map((c) => c[0]), ys = cl.cells.map((c) => c[1]); return { x0: Math.min(...xs), x1: Math.max(...xs), y0: Math.min(...ys), y1: Math.max(...ys) }; };
  const bC = box(G.C), bQ = box(G.Q), span = Math.max(6, bC.x1 - bC.x0 + 1, bC.y1 - bC.y0 + 1, bQ.x1 - bQ.x0 + 1, bQ.y1 - bQ.y0 + 1);
  return { c: SPAN / span, bC, bQ };
}
const hOf = (G, t) => HMAX * t / G.tmax;
function place(G, Fr, which, x, y, h) {
  const b = which === 'C' ? Fr.bC : Fr.bQ, off = which === 'C' ? -OFF : OFF;
  return [off + (x - (b.x0 + b.x1) / 2) * Fr.c, h, -(y - (b.y0 + b.y1) / 2) * Fr.c];
}
let staticPts = 0;
function updateStatic() {
  const G = MODEL, Fr = G.Fr, Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; for (let k = 0; k < 3; k++) { PT.position.array[3 * np + k] = p[k]; PT.aColor.array[3 * np + k] = c[k]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  for (const [which, cl, t, col] of [['C', G.C, G.tC, COL.amber], ['Q', G.Q, G.tQ, COL.cyan]]) {
    cl.cells.forEach(([x, y], i) => {
      const h = hOf(G, t[i]), top = place(G, Fr, which, x, y, h), b = 0.25 + 0.75 * t[i] / G.tmax;
      seg(place(G, Fr, which, x, y, 0), top, col, 0.13);
      dot(top, col.map((u) => u * b), 0.85, Math.min(2.4, 6 * Fr.c));
      for (const d of [0, 2]) { const j = cl.nb[i][d]; if (j >= 0) seg(top, place(G, Fr, which, cl.cells[j][0], cl.cells[j][1], hOf(G, t[j])), col, 0.22 + 0.4 * (t[i] + t[j]) / (2 * G.tmax)); }
      /* the boundary of the cluster on the floor: a cell edge wherever the neighbour is outside */
      cl.nb[i].forEach((j, d) => {
        if (j >= 0) return;
        const [dx, dy] = DIRS[d], ex = dx ? [x + dx / 2, x + dx / 2] : [x - 0.5, x + 0.5], ey = dy ? [y + dy / 2, y + dy / 2] : [y - 0.5, y + 0.5];
        seg(place(G, Fr, which, ex[0], ey[0], 0.005), place(G, Fr, which, ex[1], ey[1], 0.005), col, 0.85);
      });
    });
  }
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  staticPts = np;
}
/* walkers at step k: between steps s and s + 1 a walker slides from one cell top to the next, or off the dome to the floor */
function walkerPos(G, Fr, which, w, i, k) {
  const cl = which === 'C' ? G.C : G.Q, t = which === 'C' ? G.tC : G.tQ, s = Math.floor(k), f = k - s, Ti = w.T[i];
  if (s > Ti || (s === Ti && f > 0.999)) return null;
  const at = (st) => {
    if (st < Ti) { const c = w.path[w.off[i] + st]; return place(G, Fr, which, cl.cells[c][0], cl.cells[c][1], hOf(G, t[c]) + 0.06); }
    return place(G, Fr, which, w.ex[i][0], w.ex[i][1], 0.03);
  };
  if (s === Ti) return { p: at(Ti), out: true, a: 1 - f };
  const p = at(s), q = at(s + 1), e = f * f * (3 - 2 * f);
  return { p: p.map((u, j) => u + (q[j] - u) * e), out: false, a: 1 };
}
function updateDynamic() {
  const G = MODEL, Fr = G.Fr, PT = pts.geometry.attributes; let np = staticPts;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; for (let k = 0; k < 3; k++) { PT.position.array[3 * np + k] = p[k]; PT.aColor.array[3 * np + k] = c[k]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const size = Math.min(3.2, 8.5 * Fr.c);
  for (const [which, w] of [['C', G.wC], ['Q', G.wQ]]) for (let i = 0; i < NW; i++) {
    const r = walkerPos(G, Fr, which, w, i, G.k); if (!r) continue;
    dot(r.p, r.out ? COL.magenta : WHITE, r.a, r.out ? size * 1.3 : size);
  }
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const a of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) a.needsUpdate = true;
  pts.material.uniforms.uScale.value = 60 * renderer.getPixelRatio() * (stage.clientHeight / 600);
}

/* =====================================================================
   5. Camera
   ===================================================================== */
function updateCamera(dtSec) {
  const k = reduceMotion ? 1 : 1 - Math.pow(0.001, dtSec);
  cam.theta += (cam.tTheta - cam.theta) * k; cam.phi += (cam.tPhi - cam.phi) * k; cam.r += (cam.tR - cam.r) * k;
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.5 : 1);
  camera.position.set(r * sp * Math.sin(cam.theta), r * Math.cos(cam.phi) + 0.6, r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(0, 0.6, 0);
}
function setCamPreset(nm) {
  const p = CAMS[nm]; if (!p) return;
  let d = (p[0] - cam.theta) % (Math.PI * 2);
  if (d > Math.PI) d -= Math.PI * 2; if (d < -Math.PI) d += Math.PI * 2;
  cam.tTheta = cam.theta + d; cam.tPhi = p[1]; cam.tR = p[2];
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.cam === nm)));
}
const proj3 = (p) => { const q = new THREE.Vector3(p[0], p[1], p[2]).project(camera), rect = stage.getBoundingClientRect(); return { x: (q.x * 0.5 + 0.5) * rect.width, y: (-q.y * 0.5 + 0.5) * rect.height, z: q.z }; };
const drag = { x: 0, y: 0, pts: new Map(), pinch: 0 };
stage.addEventListener('pointerdown', (ev) => {
  if (ev.target.closest('.chip')) return;
  stage.setPointerCapture(ev.pointerId);
  drag.pts.set(ev.pointerId, { x: ev.clientX, y: ev.clientY }); drag.x = ev.clientX; drag.y = ev.clientY;
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()]; drag.pinch = Math.hypot(p.x - q.x, p.y - q.y); }
});
stage.addEventListener('pointermove', (ev) => {
  if (!drag.pts.has(ev.pointerId)) return;
  drag.pts.set(ev.pointerId, { x: ev.clientX, y: ev.clientY });
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(30, Math.max(5, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.05, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(30, Math.max(5, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

/* =====================================================================
   6. Tags
   ===================================================================== */
const tagPool = [];
function tagAt(k, cls) { while (tagPool.length <= k) { const el = document.createElement('div'); el.className = 'tag raw'; tagsBox.appendChild(el); tagPool.push(el); } const el = tagPool[k]; el.className = 'tag raw ' + cls; return el; }
function placeTag(el, p) {
  if (!glOK) { el.style.display = 'none'; return; }
  const q = proj3(p); if (q.z > 1 || q.z < -1) { el.style.display = 'none'; return; }
  el.style.display = 'block';
  const w = el.offsetWidth, h = el.offsetHeight, Wd = stage.clientWidth, Hd = stage.clientHeight, hud = document.querySelector('.hud-tl'), top = hud.offsetTop + hud.offsetHeight + 4;
  el.style.left = Math.min(Wd - w / 2 - 6, Math.max(w / 2 + 6, q.x)) + 'px'; el.style.top = Math.min(Hd - h / 2 - 6, Math.max(top + h / 2, q.y)) + 'px';
}
function updateTags() {
  const M = MODEL, Fr = M.Fr; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  const front = (b, which) => place(M, Fr, which, (b.x0 + b.x1) / 2, b.y0 - 1.6, 0);
  put(`C · τ = ${f4(M.tauC)}`, [-OFF, HMAX + 0.5, 0], 'am');
  put(`Q = ${M.m} × ${M.m} · τ = ${f4(M.tauQ)}`, [OFF, HMAX + 0.5, 0], 'cy');
  put(T(`还在里面 ${M.inC} / ${NW}`, `inside ${M.inC} / ${NW}`), front(Fr.bC, 'C'), 'w');
  put(T(`还在里面 ${M.inQ} / ${NW}`, `inside ${M.inQ} / ${NW}`), front(Fr.bQ, 'Q'), 'w');
  for (let i = k; i < tagPool.length; i++) tagPool[i].style.display = 'none';
}

/* =====================================================================
   7. 2D panels
   ===================================================================== */
function frame2d(cv, pl0 = 46) {
  const dpr = fitCanvas(cv), ctx = cv.getContext('2d'), Wd = cv.width, Hh = cv.height;
  ctx.clearRect(0, 0, Wd, Hh);
  const pl = pl0 * dpr, pr = 14 * dpr, pt = 12 * dpr, pb = 22 * dpr;
  ctx.font = `${9.5 * dpr}px ${TRV.fonts.data}`;
  return { dpr, ctx, W: Wd, Hh, pl, pt, iw: Wd - pl - pr, ih: Hh - pt - pb };
}
function lab(ctx, txt, x, y, al, bl, c = DIM) { ctx.fillStyle = c; ctx.textAlign = al; ctx.textBaseline = bl; ctx.fillText(txt, x, y); }
/* top views: brightness = t(p) on the shared scale; the left map is editable */
let HM = null;
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 10); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, Fr = M.Fr;
  const wC = { x0: Fr.bC.x0 - 2, x1: Fr.bC.x1 + 2, y0: Fr.bC.y0 - 2, y1: Fr.bC.y1 + 2 }, wQ = { x0: -1, x1: M.m, y0: -1, y1: M.m };
  const cols = (wC.x1 - wC.x0 + 1) + 2 + (wQ.x1 - wQ.x0 + 1), rows = Math.max(wC.y1 - wC.y0 + 1, wQ.y1 - wQ.y0 + 1), top = pt + 12 * dpr;
  const cs = Math.min(iw / cols, (ih + 6 * dpr) / rows), ox = pl + (iw - cols * cs) / 2, oxQ = ox + ((wC.x1 - wC.x0 + 1) + 2) * cs;
  HM = { ox: ox / dpr, top: top / dpr, cs: cs / dpr, wC };
  const draw = (cl, t, w, x0, col) => {
    for (let x = w.x0; x <= w.x1; x++) for (let y = w.y0; y <= w.y1; y++) {
      const px = x0 + (x - w.x0) * cs, py = top + (w.y1 - y) * cs, i = cl.idx.get(ck(x, y));
      if (i === undefined) { if (cl === M.C) { ctx.strokeStyle = 'rgba(52,80,106,0.55)'; ctx.lineWidth = 1; ctx.strokeRect(px + 0.5, py + 0.5, cs - 1, cs - 1); } continue; }
      const b = 0.18 + 0.82 * t[i] / M.tmax; ctx.fillStyle = css(col.map((u) => u * b)); ctx.fillRect(px + 0.5, py + 0.5, cs - 1, cs - 1);
    }
  };
  draw(M.C, M.tC, wC, ox, COL.amber); draw(M.Q, M.tQ, wQ, oxQ, COL.cyan);
  if (S.sel) { const px = ox + (S.sel[0] - wC.x0) * cs, py = top + (wC.y1 - S.sel[1]) * cs; ctx.strokeStyle = INK; ctx.lineWidth = 2 * dpr; ctx.strokeRect(px + dpr, py + dpr, cs - 2 * dpr, cs - 2 * dpr); }
  lab(ctx, T('C（可点击编辑）', 'C (click to edit)'), ox, pt, 'left', 'top', AM);
  lab(ctx, `Q = ${M.m} × ${M.m}`, oxQ, pt, 'left', 'top', CY);
  $('c1Meta').innerHTML = `<span class="it">${T(`亮度 = t(p)，两图同一刻度，最高 ${M.tmax.toFixed(2)} 步`, `brightness = t(p) on one shared scale, max ${M.tmax.toFixed(2)} steps`)}</span>`;
}
/* the survival curves S(k); τ is the area under each */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 30); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, K = M.K, X = (k) => pl + iw * k / K, Y = (s) => pt + ih * (1 - s);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  for (const [sv, col] of [[M.survQ, COL.cyan], [M.survC, COL.amber]]) {
    ctx.beginPath(); ctx.moveTo(X(0), Y(0)); for (let k = 0; k <= K; k++) ctx.lineTo(X(k), Y(sv[k])); ctx.lineTo(X(K), Y(0)); ctx.closePath(); ctx.fillStyle = css(col, 0.1); ctx.fill();
    ctx.beginPath(); for (let k = 0; k <= K; k++) k ? ctx.lineTo(X(k), Y(sv[k])) : ctx.moveTo(X(k), Y(sv[k])); ctx.strokeStyle = css(col, 0.95); ctx.lineWidth = 1.6 * dpr; ctx.stroke();
  }
  /* the difference S_C − S_Q on its own symmetric scale (right axis); its area is τ(C) − τ(Q) */
  let dm = 1e-12; for (let k = 0; k <= K; k++) dm = Math.max(dm, Math.abs(M.survC[k] - M.survQ[k]));
  const YD = (d) => pt + ih * (0.5 - 0.45 * d / dm);
  ctx.strokeStyle = 'rgba(255,47,208,0.35)'; ctx.setLineDash([2 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(pl, YD(0)); ctx.lineTo(pl + iw, YD(0)); ctx.stroke(); ctx.setLineDash([]);
  ctx.beginPath(); for (let k = 0; k <= K; k++) { const y = YD(M.survC[k] - M.survQ[k]); k ? ctx.lineTo(X(k), y) : ctx.moveTo(X(k), y); } ctx.strokeStyle = MG; ctx.lineWidth = 1.3 * dpr; ctx.stroke();
  lab(ctx, `±${dm.toFixed(4)}`, pl + iw + 2 * dpr, YD(dm), 'right', 'bottom', MG);
  for (const [tau, col, dy] of [[M.tauC, AM, 0], [M.tauQ, CY, 11]]) { ctx.strokeStyle = col; ctx.lineWidth = 1.2 * dpr; ctx.beginPath(); ctx.moveTo(X(tau), pt + ih); ctx.lineTo(X(tau), pt + ih - 6 * dpr); ctx.stroke(); lab(ctx, `τ ${f4(tau)}`, X(tau) + 4 * dpr, pt + 4 * dpr + dy * dpr, 'left', 'top', col); }
  ctx.strokeStyle = INK; ctx.setLineDash([3 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(X(M.k), pt); ctx.lineTo(X(M.k), pt + ih); ctx.stroke(); ctx.setLineDash([]);
  for (const [f, col] of [[M.inC / NW, AM], [M.inQ / NW, CY]]) { ctx.strokeStyle = col; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); ctx.arc(X(M.k), Y(f), 3.5 * dpr, 0, 2 * Math.PI); ctx.stroke(); }
  [0, 0.5, 1].forEach((v) => lab(ctx, String(v), pl - 4 * dpr, Y(v), 'right', 'middle'));
  [0, Math.round(K / 2), K].forEach((k, i) => lab(ctx, String(k), X(k), pt + ih + 4 * dpr, ['left', 'center', 'right'][i], 'top'));
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${AM}"></i>S_C(k)</span><span class="it"><i class="sw" style="--c:${CY}"></i>S_Q(k)</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('S_C − S_Q（右侧刻度）', 'S_C − S_Q (right scale)')}</span><span class="it">· ${T('圆圈：行人', 'rings: walkers')}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function verdict(M) {
  if (M.N !== M.m * M.m) return T('C 的格子数不是 m²', 'C does not have m² cells');
  if (!M.conn) return T('C 不连通：不在猜想的范围内', 'C is not connected: outside the conjecture');
  const c = cmp(M.tauC, M.tauQ);
  return c === '>' ? T('C 胜过正方形：猜想的反例', 'C beats the square: a counterexample to the conjecture') : c === '<' ? T('正方形更大', 'the square is larger') : T('相等', 'equal');
}
function readouts() {
  const M = MODEL, d = M.tauC - M.tauQ;
  pill('pillA', 'N', `${M.N} = ${M.m}²`); pill('pillB', 'τ(C)', f4(M.tauC)); pill('pillC', 'τ(C) − τ(Q)', (d >= 0 ? '+' : '−') + f4(Math.abs(d))); pill('pillD', 'k', String(M.s));
  setRo([
    [T('挑战者 C：格子数 · 连通 · τ(C)', 'Challenger C: cells · connected · τ(C)'), `${M.N} · ${M.conn ? T('是', 'yes') : T('否', 'no')} · ${f4(M.tauC)}`],
    [T('正方形 Q = m × m：τ(Q)', 'Square Q = m × m: τ(Q)'), `${M.m} × ${M.m} · ${f4(M.tauQ)}`],
    [T('τ(C) − τ(Q) · 判定', 'τ(C) − τ(Q) · verdict'), `${d >= 0 ? '+' : '−'}${f4(Math.abs(d))} · ${verdict(M)}`],
    [T(`第 k = ${M.s} 步后仍在里面：精确 S_C(k) · S_Q(k) · 行人 C · Q`, `Still inside after k = ${M.s} steps: exact S_C(k) · S_Q(k) · walkers C · Q`), `${f4(M.SC)} · ${f4(M.SQ)} · ${M.inC}/${NW} · ${M.inQ}/${NW}`],
    [T(`最高的 t（穹顶顶点）C · Q · ${NEST} 个行人估计的 τ`, `Highest t (dome top) C · Q · τ estimated by ${NEST} walkers`), `${Math.max(...M.tC).toFixed(3)} · ${Math.max(...M.tQ).toFixed(3)} · ${M.wC.mean.toFixed(2)} ± ${M.wC.se.toFixed(2)} · ${M.wQ.mean.toFixed(2)} ± ${M.wQ.se.toFixed(2)}`]]);
  $('roNote').innerHTML = M.exact
    ? T(`Lean 算出的精确值：τ(C) = ${M.exact.tauC}，τ(Q) = ${M.exact.tauQ}。页面的浮点解与之相差不到 10⁻⁹。`, `Exact values from Lean: τ(C) = ${M.exact.tauC} and τ(Q) = ${M.exact.tauQ}. The page’s floating-point solution agrees to better than 10⁻⁹.`)
    : T('Lean 只证明了 121 格的圆盘；这里的数是页面解线性方程组得到的。', 'Lean proves only the 121-cell disk; the numbers here come from the page solving the linear system.');
}
const stateKey = () => `${S.m}|${S.cver}|${S.t}|${S.preset}|${S.sel}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; }
  const M = MODEL;
  if (!toasted && S.playing && S.t >= 1) { toasted = true; toast(T(`<b>τ(C) = ${f4(M.tauC)} ${cmp(M.tauC, M.tauQ)} τ(Q) = ${f4(M.tauQ)}</b>：生存曲线下的面积。`, `<b>τ(C) = ${f4(M.tauC)} ${cmp(M.tauC, M.tauQ)} τ(Q) = ${f4(M.tauQ)}</b>: the areas under the survival curves.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('mIn').value = String(S.m); $('mOut').textContent = `${S.m}²`;
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T(`现在的 C：${S.origin[0]}。拖动滑块会换成页面找到的、恰有 m² 个格子的最好圆盘：圆心 (cx, cy) 取 0 ≤ cy ≤ cx ≤ ½ 上间隔 0.05 的点，取离圆心最近的 m² 个格点。`, `Current C: ${S.origin[1]}. Moving the slider replaces it with the best disk of exactly m² cells the page finds: centres (cx, cy) on the 0.05 grid with 0 ≤ cy ≤ cx ≤ ½, taking the m² lattice points nearest to the centre.`);
  $('editNote').innerHTML = S.sel ? T(`已拿起 (${S.sel[0]}, ${S.sel[1]})：点一个空格放下，或再点它取消。`, `Picked up (${S.sel[0]}, ${S.sel[1]}): click an empty cell to put it down, or click it again to cancel.`)
    : T(`在左下热图里点 C 的一个格子把它拿起，再点一个空格放下；如果 C 会断开就拒绝。「爬一步」做使 τ 增加最多的单格移动（N ≤ ${CLIMB_MAX}）。`, `In the lower-left heat map, click a cell of C to pick it up, then click an empty cell to put it down; the move is refused if C would come apart. “Climb one step” makes the single-cell move that raises τ the most (N ≤ ${CLIMB_MAX}).`);
  $('climbBtn').disabled = M.N > CLIMB_MAX;
  $('litNote').innerHTML = T('原文的证据是四格骨牌、矩形和 N = 225 的 10⁴ 个 Eden 样本，没有在全部团簇上优化。', 'The source’s evidence is the tetrominoes, rectangles and 10⁴ Eden samples at N = 225, not an optimization over all clusters.');
  $('c1Title').textContent = T('俯视：每个起点的期望出逃步数 t(p)', 'Top view: expected exit steps t(p) from each start');
  $('c2Title').textContent = T('生存曲线 S(k)：面积 = τ', 'Survival S(k): area = τ');
  $('clock').innerHTML = T(`k = ${M.s} 步`, `k = ${M.s} steps`);
  $('hudBig').textContent = `τ(C) = ${f4(M.tauC)} ${cmp(M.tauC, M.tauQ)} τ(Q) = ${f4(M.tauQ)}`;
  $('hudSub').textContent = T('左 C、右 Q，格子一样多。每根柱子高 t(p)：从 p 出发离开所需的期望步数；τ 是平均高度。白点是行人，走出边界时变成品红', 'C on the left and Q on the right, with the same number of cells. Each column rises to t(p), the expected number of steps to leave from p; τ is the mean height. White dots are walkers, turning magenta as they step out');
}
function syncRail() {
  const M = MODEL, key = `${M.K}|${M.tauQ}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, T('0 步', '0 steps'), 'first'], [M.tauQ / M.K, 'τ(Q)', ''], [1, T(`${M.K} 步`, `${M.K} steps`), 'last']];
  $('marks').innerHTML = marks.map(([f, l, c]) => `<i class="${c}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function setCells(cells, origin) { S.cells = cells.map((c) => c.slice()); S.cver++; S.sel = null; S.origin = origin; dirty = true; toasted = false; }
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  S.m = p.m; S.preset = nm; setCells(p.cells(), p.origin); S.t = 0; S.hold = 0; markPreset();
  S.playing = !reduceMotion; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('mIn').addEventListener('input', () => {
  const m = parseInt($('mIn').value, 10), b = bestDisk(m);
  S.m = m; setCells(b.cells, [`恰有 ${m * m} 个格子的最好圆盘，圆心 (${b.cx}, ${b.cy})`, `the best disk of exactly ${m * m} cells, centre (${b.cx}, ${b.cy})`]); custom();
});
$('squareBtn').addEventListener('click', () => { setCells(square(S.m), [`${S.m} × ${S.m} 正方形本身`, `the ${S.m} × ${S.m} square itself`]); custom(); });
$('climbBtn').addEventListener('click', () => {
  if (S.cells.length > CLIMB_MAX) return;
  const r = climbStep(S.cells);
  if (!r.best) { toast(T(`检查了 ${r.tried} 个保持连通的单格移动：没有一个能提高 τ = ${f4(r.base)}。这是局部最大。`, `Checked ${r.tried} single-cell moves that keep C connected: none raises τ = ${f4(r.base)}. This is a local maximum.`)); return; }
  setCells(r.best.cells, [`爬山得到的形状`, `a shape reached by hill climbing`]); custom();
  toast(T(`(${r.best.from}) → (${r.best.to})：τ ${f4(r.base)} → <b>${f4(r.best.tau)}</b>（检查了 ${r.tried} 个移动）`, `(${r.best.from}) → (${r.best.to}): τ ${f4(r.base)} → <b>${f4(r.best.tau)}</b> (${r.tried} moves checked)`));
});
function clickCell(x, y) {
  const inC = S.cells.some((c) => c[0] === x && c[1] === y);
  if (!S.sel) { if (inC) { S.sel = [x, y]; } return; }
  if (S.sel[0] === x && S.sel[1] === y) { S.sel = null; return; }
  if (inC) { S.sel = [x, y]; return; }
  const sel = S.sel, nc = S.cells.filter((c) => !(c[0] === sel[0] && c[1] === sel[1])).concat([[x, y]]);
  if (!isConnected(makeCluster(nc))) { toast(T('拒绝：这样 C 会断开。', 'Refused: C would come apart.')); return; }
  const before = MODEL.tauC, after = tauOf(nc);
  setCells(nc, ['手动移动后的形状', 'a shape moved by hand']); custom();
  toast(T(`(${sel}) → (${x},${y})：τ ${f4(before)} → <b>${f4(after)}</b>`, `(${sel}) → (${x},${y}): τ ${f4(before)} → <b>${f4(after)}</b>`));
}
cv1.addEventListener('click', (ev) => {
  if (!HM) return;
  const r = cv1.getBoundingClientRect(), gx = Math.floor((ev.clientX - r.left - HM.ox) / HM.cs), gy = Math.floor((ev.clientY - r.top - HM.top) / HM.cs);
  const w = HM.wC; if (gx < 0 || gy < 0 || gx > w.x1 - w.x0 || gy > w.y1 - w.y0) return;
  clickCell(w.x0 + gx, w.y1 - gy);
});
const setT = (t, user) => { S.t = Math.min(1, Math.max(0, t)); $('now').value = S.t; dirty = true; if (user) { S.preset = null; markPreset(); } };
$('now').addEventListener('input', () => { setT(parseFloat($('now').value)); S.hold = 0; });
let scrubbing = false;
$('now').addEventListener('pointerdown', () => { scrubbing = true; });
window.addEventListener('pointerup', () => { scrubbing = false; });
window.addEventListener('pointercancel', () => { scrubbing = false; });
function setPlayUI() { $('play').textContent = S.playing ? '❚❚' : '▶'; $('play').setAttribute('aria-pressed', String(S.playing)); $('rev').setAttribute('aria-pressed', String(S.dir < 0)); }
$('play').addEventListener('click', () => { S.playing = !S.playing; S.hold = 0; setPlayUI(); });
$('rev').addEventListener('click', () => { S.dir = -S.dir; S.playing = true; S.hold = 0; setPlayUI(); });
document.querySelectorAll('#speedChips .chip').forEach((b) => b.addEventListener('click', () => {
  S.speed = parseFloat(b.dataset.speed);
  document.querySelectorAll('#speedChips .chip').forEach((c) => c.setAttribute('aria-pressed', String(c === b)));
}));
const drawer = TRV.drawer({ drawer: $('drawer'), open: $('infoBtn'), close: $('drawerClose') });
const jumpTo = (t) => { S.playing = false; setPlayUI(); setT(t); };
document.addEventListener('keydown', (ev) => {
  if (ev.target && (ev.target.tagName === 'INPUT' && ev.target.type !== 'range')) return;
  if (drawer.isOpen()) return;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); const K = MODEL.K; jumpTo((MODEL.s + (ev.key === 'ArrowRight' ? 1 : -1)) / K); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(1);
});

/* =====================================================================
   9. Main loop
   ===================================================================== */
let lastT = performance.now(), frameCount = 0, glKey = '';
function resize() {
  if (!glOK) return;
  const r = stage.getBoundingClientRect();
  renderer.setSize(Math.max(1, r.width), Math.max(1, r.height), false);
  camera.aspect = Math.max(0.2, r.width / Math.max(1, r.height)); camera.updateProjectionMatrix();
}
/* about 9 seconds per run at 1× for the 121-cell presets, longer for larger clusters */
const runSeconds = (K) => 6 + K / 40;
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : 1); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed / runSeconds(MODEL.K));
      if (S.t >= 1) S.hold = 2.4;
      if (S.t <= 0 && S.dir < 0) S.hold = 1.2;
    }
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    if (glKey !== String(MODEL.id)) { updateStatic(); glKey = String(MODEL.id); }
    updateDynamic();
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.EX_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { m: M.m, N: M.N, conn: M.conn, tauC: M.tauC, tauQ: M.tauQ, K: M.K, k: M.k, s: M.s, SC: M.SC, SQ: M.SQ, inC: M.inC, inQ: M.inQ,
    survC: [...M.survC], survQ: [...M.survQ], tC: [...M.tC], tQ: [...M.tQ], cells: M.C.cells.map((c) => c.slice()), mcC: [M.wC.mean, M.wC.se], mcQ: [M.wQ.mean, M.wQ.se],
    walkersT: [[...M.wC.T.slice(0, NW)], [...M.wQ.T.slice(0, NW)]], exact: M.exact, climbable: M.N <= CLIMB_MAX }; },
  tau: (cells) => { const cl = makeCluster(cells), t = solve(cl); return { mean: mean(t), t: [...t], connected: isConnected(cl) }; },
  survival: (cells, K) => [...survival(makeCluster(cells), K)],
  bestDisk: (m) => { const b = bestDisk(m); return b && { tau: b.tau, cx: b.cx, cy: b.cy, cells: b.cells.map((c) => c.slice()) }; },
  climbStep: (cells) => { const r = climbStep(cells), o = (b) => b && { tau: b.tau, from: b.from, to: b.to, cells: b.cells.map((c) => c.slice()) }; return { base: r.base, tried: r.tried, top: o(r.top), best: o(r.best) }; },
  shapes: { disk: (R2, cx, cy) => diskR(R2, cx, cy), square, eden: (N, seed) => eden(N, seed) },
  cellCss: (x, y) => HM && { x: HM.ox + (x - HM.wC.x0 + 0.5) * HM.cs, y: HM.top + (HM.wC.y1 - y + 0.5) * HM.cs },
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setT(0.12); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 11.5; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
