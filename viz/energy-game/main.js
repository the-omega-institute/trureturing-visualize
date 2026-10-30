/* ENERGY//GAME · the graph energy game and its Shapley value
   A coalition S of vertices is worth the energy of its induced subgraph, w(S) = 𝓔(G[S]) = Σ|λ|. Conjecture 3.10 of Arizmendi
   and Arizmendi: the Shapley value always lies in the core. Frozen in trureturing (ArizmendiEnergyGameShapleyRefutation.result):
   false, because on K₂,ₘ with m ≥ 50 the coalition V∖{a} without one scarce vertex a is worth more than it receives. The page draws
   the deficits 2√(rk) − (rφ_A + kφ_B) of every coalition type on K_{a,b}, and enumerates every coalition of small graphs.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Constants
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG, ok: OK } = TRV.palette;
const VIOLET = [0.62, 0.55, 1], GREY = [0.55, 0.6, 0.68], GREEN = [0.27, 1, 0.7];
const VI = '#9d8cff';
const MODES = ['bip', 'graph'], A_CHOICES = [1, 2, 3, 4], B_CHOICES = [60, 200, 400];
const RUN = { bip: 22, graph: 18 };
const TOL = 1e-9;                                     // a deficit above this counts as blocking
const LEAN_M = 50, COEF = (26 - 18 * Math.SQRT2) / 15; // the frozen threshold; the dossier's symbolic slope (not a Lean theorem)
const SUBS = '₀₁₂₃₄₅₆₇₈₉';
const sub = (n) => String(n).split('').map((c) => SUBS[+c]).join('');
const kname = (a, b) => `K${sub(a)},${sub(b)}`;

/* =====================================================================
   2. Complete bipartite graphs: exact sums over coalition types
   ===================================================================== */
const LF = (() => { const t = [0]; for (let i = 1; i <= 420; i++) t.push(t[i - 1] + Math.log(i)); return t; })();
const lchoose = (n, k) => LF[n] - LF[k] - LF[n - k];
const cutEnergy = (r, k) => 2 * Math.sqrt(r * k);           // the energy of K_{r,k}
/* Shapley value of a vertex on each side of K_{a,b}: Σ over predecessor types (r, k), counted by binomials, weighted s!(n−s−1)!/n! */
function bipShapley(a, b) {
  const n = a + b; let pA = 0, pB = 0;
  for (let r = 0; r <= a; r++) for (let k = 0; k <= b; k++) {
    const s = r + k; if (s >= n) continue;
    const wgt = LF[s] + LF[n - s - 1] - LF[n];
    if (r < a) pA += Math.exp(lchoose(a - 1, r) + lchoose(b, k) + wgt) * (cutEnergy(r + 1, k) - cutEnergy(r, k));
    if (k < b) pB += Math.exp(lchoose(a, r) + lchoose(b - 1, k) + wgt) * (cutEnergy(r, k + 1) - cutEnergy(r, k));
  }
  return { pA, pB };
}
const deficit = (r, k, pA, pB) => cutEnergy(r, k) - r * pA - k * pB;
function bipRow(a, b) {
  const { pA, pB } = bipShapley(a, b);
  let maxD = -Infinity, argR = 0, argK = 0;
  for (let r = 0; r <= a; r++) for (let k = 0; k <= b; k++) { if (r === a && k === b) continue; const D = deficit(r, k, pA, pB); if (D > maxD) { maxD = D; argR = r; argK = k; } }
  return { b, pA, pB, maxD, argR, argK, dLean: deficit(a - 1, b, pA, pB) };
}

/* =====================================================================
   3. Small graphs: every coalition
   ===================================================================== */
const ring = (n, rad = 1, off = -Math.PI / 2) => Array.from({ length: n }, (_, i) => [rad * Math.cos(off + 2 * Math.PI * i / n), rad * Math.sin(off + 2 * Math.PI * i / n)]);
const bipLayout = (a, b) => [...Array.from({ length: a }, (_, i) => [(i - (a - 1) / 2) * 0.7, -0.8]), ...Array.from({ length: b }, (_, i) => [(i - (b - 1) / 2) * 0.55, 0.8])];
const bipEdges = (a, b) => { const e = []; for (let i = 0; i < a; i++) for (let j = 0; j < b; j++) e.push([i, a + j]); return e; };
const GRAPHS = {
  P3: { name: 'P₃', n: 3, edges: [[0, 1], [1, 2]], pos: [[-1, 0], [0, 0], [1, 0]] },
  star: { name: 'K₁,₆', n: 7, edges: [1, 2, 3, 4, 5, 6].map((j) => [0, j]), pos: [[0, 0], ...ring(6)] },
  K24: { name: 'K₂,₄', n: 6, edges: bipEdges(2, 4), pos: bipLayout(2, 4), side: 2 },
  K25: { name: 'K₂,₅', n: 7, edges: bipEdges(2, 5), pos: bipLayout(2, 5), side: 2 },
  K34: { name: 'K₃,₄', n: 7, edges: bipEdges(3, 4), pos: bipLayout(3, 4), side: 3 },
  K33: { name: 'K₃,₃', n: 6, edges: bipEdges(3, 3), pos: bipLayout(3, 3), side: 3 },
  C6: { name: 'C₆', n: 6, edges: [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]], pos: ring(6) },
  petersen: { name: 'Petersen', n: 10, edges: [[0, 1], [1, 2], [2, 3], [3, 4], [4, 0], [0, 5], [1, 6], [2, 7], [3, 8], [4, 9], [5, 7], [7, 9], [9, 6], [6, 8], [8, 5]], pos: [...ring(5), ...ring(5, 0.5)] }
};
/* cyclic Jacobi rotations on a symmetric matrix; returns eigenvalues and eigenvectors (as columns of V) */
function eigSym(A) {
  const n = A.length, M = A.map((r) => r.slice()), V = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => +(i === j)));
  for (let sweep = 0; sweep < 100; sweep++) {
    let off = 0; for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) off += M[p][q] * M[p][q];
    if (off < 1e-28) break;
    for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
      const apq = M[p][q]; if (apq === 0) continue;
      const th = (M[q][q] - M[p][p]) / (2 * apq), t = (th >= 0 ? 1 : -1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), s = t * c;
      for (let k = 0; k < n; k++) { const kp = M[k][p], kq = M[k][q]; M[k][p] = c * kp - s * kq; M[k][q] = s * kp + c * kq; }
      for (let k = 0; k < n; k++) { const pk = M[p][k], qk = M[q][k]; M[p][k] = c * pk - s * qk; M[q][k] = s * pk + c * qk; }
      for (let k = 0; k < n; k++) { const vp = V[k][p], vq = V[k][q]; V[k][p] = c * vp - s * vq; V[k][q] = s * vp + c * vq; }
    }
  }
  return { vals: M.map((r, i) => r[i]), V };
}
const popcount = (x) => { let c = 0; while (x) { c += x & 1; x >>>= 1; } return c; };
const FACT = (() => { const f = [1]; for (let i = 1; i <= 12; i++) f.push(f[i - 1] * i); return f; })();
function graphGame(G) {
  const n = G.n, N = 1 << n, adj = Array.from({ length: n }, () => new Array(n).fill(0));
  for (const [i, j] of G.edges) adj[i][j] = adj[j][i] = 1;
  const w = new Float64Array(N);
  for (let S = 1; S < N; S++) {
    const idx = []; for (let i = 0; i < n; i++) if (S >> i & 1) idx.push(i);
    let edge = false; for (const i of idx) for (const j of idx) if (adj[i][j]) edge = true;
    if (edge) w[S] = eigSym(idx.map((i) => idx.map((j) => adj[i][j]))).vals.reduce((s, l) => s + Math.abs(l), 0);
  }
  const phi = new Array(n).fill(0);
  for (let i = 0; i < n; i++) for (let S = 0; S < N; S++) { if (S >> i & 1) continue; const s = popcount(S); phi[i] += FACT[s] * FACT[n - s - 1] / FACT[n] * (w[S | (1 << i)] - w[S]); }
  const full = eigSym(adj), ve = Array.from({ length: n }, (_, i) => full.vals.reduce((s, l, j) => s + Math.abs(l) * full.V[i][j] * full.V[i][j], 0));   // vertex energies, the diagonal of |A|
  const order = Array.from({ length: N }, (_, S) => S).sort((x, y) => popcount(x) - popcount(y) || x - y);
  const pay = (x, S) => { let t = 0; for (let i = 0; i < n; i++) if (S >> i & 1) t += x[i]; return t; };
  const D = order.map((S) => w[S] - pay(phi, S)), DV = order.map((S) => w[S] - pay(ve, S));
  const best = [], bestV = []; let bi = 0, bv = 0;
  D.forEach((d, j) => { if (d > D[bi]) bi = j; best.push(bi); if (DV[j] > DV[bv]) bv = j; bestV.push(bv); });
  return { n, N, adj, w, phi, ve, order, D, DV, best, bestV };
}

/* =====================================================================
   4. State and presets
   ===================================================================== */
const S = { mode: 'bip', a: 2, bmax: 60, g: 'K25', nowFrac: 0, playing: true, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { mode: 'bip', a: 2, bmax: 60, frac: 49 / 59, play: false,
    zh: 'K₂,₅₀：Lean 里冻结的反例。稀缺侧两个顶点各拿 φₐ ≈ 6.066，大于 2(√2 − 1)√50 ≈ 5.858；由效率，联盟 V∖{a}（一个稀缺点加全部 50 个其他点）只拿到 2√100 − φₐ ≈ 13.934，少于它的价值 2√50 ≈ 14.142，赤字 ≈ 0.208（卷宗的精确区间从 0.20823… 起）。三维视图里琥珀点就是这个联盟；品红是所有正赤字。',
    en: 'K₂,₅₀: the counterexample frozen in Lean. Each of the two scarce vertices receives φₐ ≈ 6.066, more than 2(√2 − 1)√50 ≈ 5.858; by efficiency the coalition V∖{a} (one scarce vertex and all 50 others) receives only 2√100 − φₐ ≈ 13.934, less than its worth 2√50 ≈ 14.142, a deficit of ≈ 0.208 (the dossier’s exact interval starts at 0.20823…). The amber point in the 3D view is this coalition; magenta marks every positive deficit.' },
  sweep: { mode: 'bip', a: 2, bmax: 400, frac: 0, play: true,
    zh: '把 m 从 1 推到 400。最大赤字在 m = 5 冒出零面，此后一直为正并随 √m 增长；右下图是 V∖{a} 的赤字除以 √m，它慢慢爬向 (26 − 18√2)/15 ≈ 0.036——这是卷宗的符号计算，没有 Lean 定理（OPEN）。',
    en: 'Push m from 1 to 400. The largest deficit breaks through the zero level at m = 5 and stays positive, growing like √m; the lower right chart divides the deficit of V∖{a} by √m, which creeps towards (26 − 18√2)/15 ≈ 0.036 — a symbolic calculation in the dossier, with no Lean theorem (OPEN).' },
  k25: { mode: 'graph', g: 'K25', frac: 0, play: true,
    zh: 'K₂,₅ 只有 7 个顶点、2⁷ = 128 个联盟，页面逐个核对。稀缺点各拿 ≈ 1.774，其余各拿 ≈ 0.556；联盟“1 个稀缺点 + 3 个其他点”的价值 2√3 ≈ 3.464，只拿到 ≈ 3.440，赤字 ≈ 0.024。这是页面找到的最小的 K₂,ₘ 反例（数值，不是定理）。',
    en: 'K₂,₅ has only 7 vertices and 2⁷ = 128 coalitions, which the page checks one by one. Each scarce vertex receives ≈ 1.774 and each other vertex ≈ 0.556; the coalition of 1 scarce vertex and 3 others is worth 2√3 ≈ 3.464 but receives ≈ 3.440, a deficit of ≈ 0.024. This is the smallest K₂,ₘ counterexample the page finds (a numerical observation, not a theorem).' },
  k34: { mode: 'graph', g: 'K34', frac: 0, play: true,
    zh: 'K₃,₄ 也离开核，但很勉强：最大赤字只有 ≈ 0.002，来自“2 个三点侧顶点 + 3 个四点侧顶点”的联盟。小于 10⁻⁹ 的赤字页面不算挡住；这个赤字比它大六个数量级。',
    en: 'K₃,₄ also leaves the core, but only just: the largest deficit is ≈ 0.002, from the coalition of 2 vertices of the 3-side and 3 of the 4-side. The page does not count deficits below 10⁻⁹ as blocking; this one is six orders of magnitude larger.' },
  star: { mode: 'bip', a: 1, bmax: 400, frac: 0, play: true,
    zh: '星图 K₁,ₘ：中心一个顶点，m 片叶子。在 m ≤ 400 内，所有联盟的赤字都 ≤ 0——Shapley 值一直在核里（数值）。稀缺侧只有一个顶点时，没有“去掉一个稀缺点”还剩稀缺点的联盟。',
    en: 'The star K₁,ₘ: one centre and m leaves. For m ≤ 400 every coalition deficit is ≤ 0 — the Shapley value stays in the core (numerically). With a single scarce vertex there is no coalition that drops one scarce vertex and keeps another.' },
  p3: { mode: 'graph', g: 'P3', frac: 0, play: true,
    zh: '论文的例 3.9：路 P₃。Shapley 值为中心 (2 + 2√2)/3、两端 (2√2 − 1)/3，8 个联盟全部满足核条件。紫柱是顶点能量（|A| 的对角元），论文定理 3.6 证明这种分配总在核里。',
    en: 'Example 3.9 of the paper: the path P₃. The Shapley value is (2 + 2√2)/3 at the centre and (2√2 − 1)/3 at each end, and all 8 coalitions satisfy the core conditions. The violet bars are the vertex energies (the diagonal of |A|), an allocation that Theorem 3.6 of the paper proves always lies in the core.' }
};

/* =====================================================================
   5. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
const tableCache = new Map(), gameCache = new Map();
function build() {
  if (!MODES.includes(S.mode)) S.mode = 'bip';
  if (!A_CHOICES.includes(S.a)) S.a = 2;
  if (!B_CHOICES.includes(S.bmax)) S.bmax = 60;
  if (!GRAPHS[S.g]) S.g = 'K25';
  const M = { id: ++modelId, mode: S.mode, a: S.a, bmax: S.bmax, g: S.g };
  if (M.mode === 'bip') {
    const key = `${M.a}|${M.bmax}`;
    if (!tableCache.has(key)) {
      const rows = []; for (let b = 1; b <= M.bmax; b++) rows.push(bipRow(M.a, b));
      const firstAny = rows.find((r) => r.maxD > TOL), firstLean = rows.find((r) => r.dLean > TOL);
      tableCache.set(key, { rows, firstAny: firstAny ? firstAny.b : null, firstLean: firstLean ? firstLean.b : null });
    }
    Object.assign(M, tableCache.get(key));
  } else {
    if (!gameCache.has(M.g)) gameCache.set(M.g, graphGame(GRAPHS[M.g]));
    M.game = gameCache.get(M.g); M.G = GRAPHS[M.g];
  }
  MODEL = M;
}
function progress() {
  const M = MODEL;
  if (M.mode === 'bip') { const b = 1 + Math.round(S.nowFrac * (M.bmax - 1)); return { b, row: M.rows[b - 1] }; }
  const gm = M.game, count = Math.max(1, Math.round(S.nowFrac * gm.N)), j = count - 1;
  return { count, j, S: gm.order[j], bestJ: gm.best[j], bestVJ: gm.bestV[j] };
}
function bipGrid(a, row) { const out = []; for (let r = 0; r <= a; r++) { const line = []; for (let k = 0; k <= row.b; k++) line.push(deficit(r, k, row.pA, row.pB)); out.push(line); } return out; }
const members = (S, n) => { const out = []; for (let i = 0; i < n; i++) if (S >> i & 1) out.push(i); return out; };
const setName = (S, n) => `{${members(S, n).map((i) => i + 1).join(', ')}}`;

/* =====================================================================
   6. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const fr = (x, d = 4) => (isFinite(x) ? x.toFixed(d) : '—');
const sg = (x, d = 4) => (isFinite(x) ? (x > 0 ? '+' : x < 0 ? '−' : '') + Math.abs(x).toFixed(d) : '—');

/* =====================================================================
   7. 3D scene
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 20000, PTS_MAX = 3000;
const CAMS = { iso: [0.7, 1.05, 17], front: [0.0001, 1.5707, 16], top: [0.0001, 0.0601, 17] };
const cam = { theta: 0.7, phi: 1.05, r: 17, tTheta: 0.7, tPhi: 1.05, tR: 17 };
const EVT_VS = `
attribute vec3 aColor; attribute float aAlpha; attribute float aSize;
uniform float uScale;
varying vec3 vCol; varying float vA;
void main(){
  vec4 mv = modelViewMatrix * vec4(position, 1.0);
  gl_Position = projectionMatrix * mv;
  gl_PointSize = aAlpha < 0.004 ? 0.0 : uScale * aSize / max(0.1, -mv.z);
  vCol = aColor; vA = aAlpha;
}`;
const DOT_FS = `
varying vec3 vCol; varying float vA;
void main(){
  float r = length(gl_PointCoord - 0.5) * 2.0;
  float a = smoothstep(1.0, 0.35, r) * vA;
  if (a < 0.01) discard;
  gl_FragColor = vec4(vCol, a);
}`;
const additive = { transparent: true, depthWrite: false, depthTest: false, blending: window.THREE ? THREE.AdditiveBlending : 2 };
function dyn(g, name, n, size) { const a = new THREE.BufferAttribute(new Float32Array(n * size), size); a.setUsage(THREE.DynamicDrawUsage); g.setAttribute(name, a); return a; }
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
  pts = new THREE.Points(gp, new THREE.ShaderMaterial({ vertexShader: EVT_VS, fragmentShader: DOT_FS, uniforms: { uScale: { value: 60 } }, ...additive }));
  pts.frustumCulled = false; scene3.add(pts);
}
/* deficits on an asinh scale: 0.02 is one unit near zero, large negative deficits are clamped */
const yOf = (D) => Math.max(-3.4, Math.min(3.8, 2.4 * Math.asinh(D / 0.02) / Math.asinh(50)));
const bipPos = (M, r, k, b, D) => [(k / Math.max(1, b) - 0.5) * 11, yOf(D), (M.a ? (r / M.a - 0.5) : 0) * 6];
const graphPos = (G, i) => [G.pos[i][0] * 4.2, 0, G.pos[i][1] * 4.2];
const BAR = 1.6;
function updateGL() {
  const M = MODEL, pr = progress();
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (a, b, col, k) => { if (v + 2 > LINES_MAX) return; for (const p of [a, b]) { Pp[3 * v] = p[0]; Pp[3 * v + 1] = p[1]; Pp[3 * v + 2] = p[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, a, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = a; PT.aSize.array[np] = size; np++; };
  if (M.mode === 'bip') {
    const row = pr.row, b = row.b, grid = bipGrid(M.a, row);
    for (let r = 0; r <= M.a; r++) {
      seg(bipPos(M, r, 0, b, 0), bipPos(M, r, b, b, 0), GREY, 0.35);
      for (let k = 1; k <= b; k++) {
        const D0 = grid[r][k - 1], D1 = grid[r][k], pos = D0 > TOL || D1 > TOL;
        seg(bipPos(M, r, k - 1, b, D0), bipPos(M, r, k, b, D1), pos ? COL.magenta : COL.cyan, pos ? 1 : 0.6);
      }
      const every = Math.max(1, Math.round(b / 60));
      for (let k = 0; k <= b; k++) {
        const D = grid[r][k];
        if (r === M.a && k === b) continue;
        if (D > TOL) { seg(bipPos(M, r, k, b, 0), bipPos(M, r, k, b, D), COL.magenta, 0.7); dot(bipPos(M, r, k, b, D), COL.magenta, 0.95, 1.2); }
        else if (k % every === 0) dot(bipPos(M, r, k, b, D), COL.cyan, 0.5, 0.7);
      }
    }
    for (let k = 0; k <= b; k += Math.max(1, Math.round(b / 10))) seg(bipPos(M, 0, k, b, 0), bipPos(M, M.a, k, b, 0), GREY, 0.18);
    dot(bipPos(M, M.a, b, b, 0), GREEN, 0.9, 1.6);
    dot(bipPos(M, M.a - 1, b, b, row.dLean), COL.amber, 1, 2.6);
    if (row.maxD > TOL) dot(bipPos(M, row.argR, row.argK, b, row.maxD), [1, 1, 1], 1, 2.2);
  } else {
    const G = M.G, gm = M.game, cur = pr.S, best = gm.order[pr.bestJ], bad = gm.D[pr.bestJ] > TOL;
    const phiMax = Math.max(...gm.phi, ...gm.ve);
    for (const [i, j] of G.edges) {
      const inCur = (cur >> i & 1) && (cur >> j & 1), inBest = bad && (best >> i & 1) && (best >> j & 1);
      seg(graphPos(G, i), graphPos(G, j), inBest ? COL.magenta : inCur ? [1, 1, 1] : COL.cyan, inBest ? 1 : inCur ? 0.8 : 0.4);
    }
    for (let i = 0; i < G.n; i++) {
      const p = graphPos(G, i), hA = BAR * gm.phi[i] / phiMax, hV = BAR * gm.ve[i] / phiMax, pa = [p[0] - 0.12, 0, p[2]], pv = [p[0] + 0.12, 0, p[2]];
      seg(pa, [pa[0], hA, pa[2]], COL.amber, 0.95); seg(pv, [pv[0], hV, pv[2]], VIOLET, 0.85);
      dot([pa[0], hA, pa[2]], COL.amber, 0.9, 0.9); dot([pv[0], hV, pv[2]], VIOLET, 0.8, 0.8);
      const inCur = cur >> i & 1, inBest = bad && (best >> i & 1);
      dot(p, inBest ? COL.magenta : inCur ? [1, 1, 1] : COL.cyan, inCur || inBest ? 1 : 0.6, inBest ? 2.8 : inCur ? 2.4 : 1.8);
    }
  }
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const a of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) a.needsUpdate = true;
  pts.material.uniforms.uScale.value = 60 * renderer.getPixelRatio() * (stage.clientHeight / 600);
}

/* =====================================================================
   8. Camera
   ===================================================================== */
function updateCamera(dtSec) {
  const k = reduceMotion ? 1 : 1 - Math.pow(0.001, dtSec);
  cam.theta += (cam.tTheta - cam.theta) * k; cam.phi += (cam.tPhi - cam.phi) * k; cam.r += (cam.tR - cam.r) * k;
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.5 : 1);
  camera.position.set(r * sp * Math.sin(cam.theta), r * Math.cos(cam.phi), r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(0, 0, 0);
}
function setCamPreset(name) {
  const p = CAMS[name]; if (!p) return;
  let d = (p[0] - cam.theta) % (Math.PI * 2);
  if (d > Math.PI) d -= Math.PI * 2; if (d < -Math.PI) d += Math.PI * 2;
  cam.tTheta = cam.theta + d; cam.tPhi = p[1]; cam.tR = p[2];
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.cam === name)));
}
const proj3 = (p) => { const q = new THREE.Vector3(p[0], p[1], p[2]).project(camera), rect = stage.getBoundingClientRect(); return { x: (q.x * 0.5 + 0.5) * rect.width, y: (-q.y * 0.5 + 0.5) * rect.height, z: q.z }; };
const drag = { x: 0, y: 0, pts: new Map(), pinch: 0 };
stage.addEventListener('pointerdown', (ev) => {
  if (ev.target.closest('.chip')) return;
  stage.setPointerCapture(ev.pointerId);
  drag.pts.set(ev.pointerId, { x: ev.clientX, y: ev.clientY }); drag.x = ev.clientX; drag.y = ev.clientY;
  if (drag.pts.size === 2) { const [a, b] = [...drag.pts.values()]; drag.pinch = Math.hypot(a.x - b.x, a.y - b.y); }
});
stage.addEventListener('pointermove', (ev) => {
  if (!drag.pts.has(ev.pointerId)) return;
  drag.pts.set(ev.pointerId, { x: ev.clientX, y: ev.clientY });
  if (drag.pts.size === 2) { const [a, b] = [...drag.pts.values()], d = Math.hypot(a.x - b.x, a.y - b.y); if (drag.pinch > 0) cam.tR = Math.min(34, Math.max(7, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(34, Math.max(7, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

/* =====================================================================
   9. Tags
   ===================================================================== */
const tagPool = [];
function tagAt(k, cls) { while (tagPool.length <= k) { const el = document.createElement('div'); el.className = 'tag raw'; tagsBox.appendChild(el); tagPool.push(el); } const el = tagPool[k]; el.className = 'tag raw ' + cls; return el; }
function placeTag(el, p) {
  if (!glOK) { el.style.display = 'none'; return; }
  const q = proj3(p); if (q.z > 1 || q.z < -1) { el.style.display = 'none'; return; }
  el.style.display = 'block';
  const w = el.offsetWidth, W = stage.clientWidth, x = Math.min(W - w / 2 - 6, Math.max(w / 2 + 6, q.x));
  el.style.left = x + 'px'; el.style.top = q.y + 'px';
}
function updateTags() {
  const M = MODEL, pr = progress(); let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  if (M.mode === 'bip') {
    const row = pr.row, b = row.b;
    for (let r = 0; r <= M.a; r++) put(`r = ${r}`, bipPos(M, r, 0, b, 0).map((x, i) => (i === 0 ? x - 1.1 : x)), 'cy');
    put('k = 0', bipPos(M, 0, 0, b, 0).map((x, i) => (i === 2 ? x - 1 : x)), 'cy'); put(`k = ${b}`, bipPos(M, 0, b, b, 0).map((x, i) => (i === 2 ? x - 1 : x)), 'cy');
    put(`V∖{a} ${sg(row.dLean, 3)}`, bipPos(M, M.a - 1, b, b, row.dLean).map((x, i) => (i === 1 ? x + 0.45 : x)), 'hot');
    if (row.maxD > TOL && (row.argR !== M.a - 1 || row.argK !== b)) put(`(${row.argR}, ${row.argK}) ${sg(row.maxD, 3)}`, bipPos(M, row.argR, row.argK, b, row.maxD).map((x, i) => (i === 1 ? x + 0.45 : x)), 'mg');
    put(T('赤字 = 0', 'deficit = 0'), bipPos(M, M.a, b, b, 0).map((x, i) => (i === 0 ? x + 0.9 : x)), 'cy');
  } else {
    const G = M.G, gm = M.game;
    for (let i = 0; i < G.n; i++) { const p = graphPos(G, i); put(String(i + 1), [p[0], -0.45, p[2]], 'cy'); }
    const bad = gm.D[pr.bestJ] > TOL;
    put(bad ? T(`挡住：${setName(gm.order[pr.bestJ], G.n)}`, `blocking: ${setName(gm.order[pr.bestJ], G.n)}`) : T('至今无联盟挡住', 'no blocking coalition so far'), [0, BAR + 0.7, -4.4], bad ? 'mg' : 'cy');
  }
  for (let i = k; i < tagPool.length; i++) tagPool[i].style.display = 'none';
}

/* =====================================================================
   10. 2D panels
   ===================================================================== */
function frame2d(cv, pl0 = 46) {
  const dpr = fitCanvas(cv), ctx = cv.getContext('2d'), Wd = cv.width, Hh = cv.height;
  ctx.clearRect(0, 0, Wd, Hh);
  const pl = pl0 * dpr, pr = 12 * dpr, pt = 12 * dpr, pb = 20 * dpr;
  ctx.font = `${9.5 * dpr}px ${TRV.fonts.data}`;
  return { dpr, ctx, W: Wd, Hh, pl, pt, iw: Wd - pl - pr, ih: Hh - pt - pb };
}
function lab(ctx, txt, x, y, al, bl, col = DIM) { ctx.fillStyle = col; ctx.textAlign = al; ctx.textBaseline = bl; ctx.fillText(txt, x, y); }
function vline(ctx, x, top, h, col, dash, dpr) { ctx.strokeStyle = col; ctx.setLineDash(dash ? [4 * dpr, 3 * dpr] : []); ctx.beginPath(); ctx.moveTo(x, top); ctx.lineTo(x, top + h); ctx.stroke(); ctx.setLineDash([]); }
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 40); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress();
  if (M.mode === 'bip') {
    const rows = M.rows, top = Math.max(0.1, ...rows.map((r) => r.maxD)) * 1.1, bot = -0.3;
    const X = (b) => pl + iw * (b - 1) / Math.max(1, M.bmax - 1), Y = (d) => pt + ih * (top - Math.max(bot, Math.min(top, d))) / (top - bot);
    ctx.strokeStyle = FAINT; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
    for (const [key, col] of [['maxD', MG], ['dLean', AM]]) { ctx.strokeStyle = col; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); rows.forEach((r, i) => { const x = X(r.b), y = Y(r[key]); if (i) ctx.lineTo(x, y); else ctx.moveTo(x, y); }); ctx.stroke(); ctx.lineWidth = 1; }
    if (M.firstAny) vline(ctx, X(M.firstAny), pt, ih, MG, true, dpr);
    if (M.firstLean) vline(ctx, X(M.firstLean), pt, ih, AM, true, dpr);
    if (M.a === 2 && LEAN_M <= M.bmax) { vline(ctx, X(LEAN_M), pt, ih, OK, true, dpr); lab(ctx, 'LEAN m ≥ 50', X(LEAN_M) + 3 * dpr, pt, 'left', 'top', OK); }
    vline(ctx, X(pr.b), pt, ih, INK, false, dpr);
    lab(ctx, top.toFixed(2), pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, '0', pl - 4 * dpr, Y(0), 'right', 'middle'); lab(ctx, bot.toFixed(1), pl - 4 * dpr, pt + ih, 'right', 'bottom');
    lab(ctx, 'b = 1', pl, pt + ih + 4 * dpr, 'left', 'top'); lab(ctx, `b = ${M.bmax}`, pl + iw, pt + ih + 4 * dpr, 'right', 'top');
    $('c1Meta').textContent = T(`品红 = 所有联盟里的最大赤字，琥珀 = V∖{a} 的赤字；虚线 = 页面算出各自第一次为正的 b${M.a === 2 ? '，绿 = Lean 证明的范围' : ''}；白 = 当前的 b`,
      `magenta = the largest deficit over all coalitions, amber = the deficit of V∖{a}; dashes = the first b where each is positive (page numbers)${M.a === 2 ? ', green = the range proved in Lean' : ''}; white = the current b`);
  } else {
    const gm = M.game, n = gm.n, lim = Math.max(0.03, Math.max(...gm.D.map(Math.abs)));
    const A = (d) => Math.asinh(d / 0.01) / Math.asinh(lim / 0.01), X = (s, S) => pl + iw * (s + 0.5 + 0.7 * ((((S * 2654435761) >>> 0) % 1000) / 1000 - 0.5)) / (n + 1), Y = (d) => pt + ih / 2 - (ih / 2 - 3 * dpr) * A(d);
    ctx.strokeStyle = FAINT; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
    for (let j = 0; j <= pr.j; j++) { const Sx = gm.order[j], d = gm.D[j]; ctx.fillStyle = d > TOL ? MG : 'rgba(25,224,255,0.6)'; ctx.beginPath(); ctx.arc(X(popcount(Sx), Sx), Y(d), (d > TOL ? 3 : 1.8) * dpr, 0, 2 * Math.PI); ctx.fill(); }
    const Sc = gm.order[pr.j]; ctx.strokeStyle = AM; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); ctx.arc(X(popcount(Sc), Sc), Y(gm.D[pr.j]), 5 * dpr, 0, 2 * Math.PI); ctx.stroke(); ctx.lineWidth = 1;
    for (let s = 0; s <= n; s++) lab(ctx, String(s), pl + iw * (s + 0.5) / (n + 1), pt + ih + 4 * dpr, 'center', 'top');
    lab(ctx, `+${lim.toFixed(2)}`, pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, '0', pl - 4 * dpr, Y(0), 'right', 'middle'); lab(ctx, `−${lim.toFixed(2)}`, pl - 4 * dpr, pt + ih, 'right', 'bottom');
    $('c1Meta').textContent = T('横轴 = 联盟大小 |S|，纵轴 = 赤字 w(S) − Σφ（asinh 刻度）；品红 = 挡住 Shapley 分配的联盟；琥珀圈 = 当前联盟', 'across = coalition size |S|, up = deficit w(S) − Σφ (asinh scale); magenta = coalitions that block the Shapley allocation; amber ring = the current coalition');
  }
}
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 40); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress();
  if (M.mode === 'bip') {
    const rows = M.rows, vals = rows.map((r) => r.dLean / Math.sqrt(r.b)), top = Math.max(0.05, ...vals) * 1.15, bot = Math.min(-0.25, ...vals);
    const X = (b) => pl + iw * (b - 1) / Math.max(1, M.bmax - 1), Y = (d) => pt + ih * (top - d) / (top - bot);
    ctx.strokeStyle = FAINT; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
    if (M.a === 2) { ctx.strokeStyle = VI; ctx.setLineDash([5 * dpr, 4 * dpr]); ctx.beginPath(); ctx.moveTo(pl, Y(COEF)); ctx.lineTo(pl + iw, Y(COEF)); ctx.stroke(); ctx.setLineDash([]); lab(ctx, `(26 − 18√2)/15 · OPEN`, pl + iw, Y(COEF) - 3 * dpr, 'right', 'bottom', VI); }
    ctx.strokeStyle = AM; ctx.lineWidth = 1.6 * dpr; ctx.beginPath(); vals.forEach((q, i) => { const x = X(rows[i].b), y = Y(q); if (i) ctx.lineTo(x, y); else ctx.moveTo(x, y); }); ctx.stroke(); ctx.lineWidth = 1;
    vline(ctx, X(pr.b), pt, ih, INK, false, dpr);
    lab(ctx, top.toFixed(3), pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, '0', pl - 4 * dpr, Y(0), 'right', 'middle'); lab(ctx, bot.toFixed(2), pl - 4 * dpr, pt + ih, 'right', 'bottom');
    lab(ctx, 'b = 1', pl, pt + ih + 4 * dpr, 'left', 'top'); lab(ctx, `b = ${M.bmax}`, pl + iw, pt + ih + 4 * dpr, 'right', 'top');
    $('c2Meta').textContent = T(`琥珀 = V∖{a} 的赤字 ÷ √b${M.a === 2 ? '；紫虚线 = 卷宗符号计算给出的极限候选，没有 Lean 定理' : ''}`, `amber = the deficit of V∖{a} divided by √b${M.a === 2 ? '; violet dashes = the limit candidate from the dossier’s symbolic calculation, with no Lean theorem' : ''}`);
  } else {
    const gm = M.game, n = gm.n, top = Math.max(...gm.phi, ...gm.ve) * 1.12, bw = iw / n;
    const Y = (v) => pt + ih - ih * v / top;
    for (let i = 0; i < n; i++) {
      const x = pl + i * bw;
      ctx.fillStyle = AM; ctx.fillRect(x + bw * 0.12, Y(gm.phi[i]), bw * 0.36, pt + ih - Y(gm.phi[i]));
      ctx.fillStyle = VI; ctx.fillRect(x + bw * 0.52, Y(gm.ve[i]), bw * 0.36, pt + ih - Y(gm.ve[i]));
      lab(ctx, String(i + 1), x + bw / 2, pt + ih + 4 * dpr, 'center', 'top');
    }
    lab(ctx, top.toFixed(2), pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, '0', pl - 4 * dpr, pt + ih, 'right', 'bottom');
    $('c2Meta').textContent = T('每个顶点：琥珀 = Shapley 值，紫 = 顶点能量（|A| 的对角元；论文定理 3.6：这种分配总在核里）', 'each vertex: amber = Shapley value, violet = vertex energy (the diagonal of |A|; Theorem 3.6 of the paper: this allocation always lies in the core)');
  }
}

/* =====================================================================
   11. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const verdict = (d) => (d > TOL ? T('离开核', 'OUTSIDE CORE') : T('在核里', 'IN CORE'));
function readouts() {
  const M = MODEL, pr = progress();
  if (M.mode === 'bip') {
    const r = pr.row, a = M.a, b = r.b, wN = cutEnergy(a, b);
    setRo([[T('图 · 顶点数', 'Graph · vertices'), `${kname(a, b)} · n = ${a + b}`],
      [T('Shapley 值：稀缺侧 φ_A · 另一侧 φ_B', 'Shapley value: scarce side φ_A · other side φ_B'), `${fr(r.pA, 5)} · ${fr(r.pB, 5)}`],
      [T('最大赤字 · 联盟类型 (r, k)', 'Largest deficit · coalition type (r, k)'), r.maxD > TOL ? `${sg(r.maxD, 5)} · (${r.argR}, ${r.argK})` : `${sg(r.maxD, 5)} · ${T('无联盟挡住', 'no blocking coalition')}`],
      [T('V∖{a} 的赤字 = φ_A − 2√(ab) + 2√((a − 1)b)', 'Deficit of V∖{a} = φ_A − 2√(ab) + 2√((a − 1)b)'), a === 2 ? `${sg(r.dLean, 5)} · φ_A ${r.pA > 2 * (Math.SQRT2 - 1) * Math.sqrt(b) ? '>' : '≤'} 2(√2 − 1)√b = ${fr(2 * (Math.SQRT2 - 1) * Math.sqrt(b))}` : sg(r.dLean, 5)],
      [T('效率：aφ_A + bφ_B 与 w(V) = 2√(ab)', 'Efficiency: aφ_A + bφ_B against w(V) = 2√(ab)'), `${fr(a * r.pA + b * r.pB, 6)} · ${fr(wN, 6)}`]]);
    pill('pillA', 'a', String(a)); pill('pillB', 'b', String(b)); pill('pillC', T('最大赤字', 'MAX DEFICIT'), sg(r.maxD, 3)); pill('pillD', T('核', 'CORE'), verdict(r.maxD));
    $('roNote').innerHTML = T(`在 b ≤ ${M.bmax} 内，页面算出 ${kname(a, 'b')} 第一次离开核是 b = ${M.firstAny ?? '—'}，V∖{a} 第一次挡住是 b = ${M.firstLean ?? '—'}${a === 2 ? '；Lean 证明的是 b ≥ 50' : ''}。赤字 ≤ 10⁻⁹ 不算挡住。`,
      `For b ≤ ${M.bmax} the page finds that ${kname(a, 'b')} first leaves the core at b = ${M.firstAny ?? '—'}, and that V∖{a} first blocks at b = ${M.firstLean ?? '—'}${a === 2 ? '; Lean proves b ≥ 50' : ''}. Deficits ≤ 10⁻⁹ do not count as blocking.`);
  } else {
    const gm = M.game, G = M.G, d = gm.D[pr.bestJ], sumPhi = gm.phi.reduce((s, x) => s + x, 0), maxV = gm.DV[pr.bestVJ];
    setRo([[T('图 · 顶点数 · 边数', 'Graph · vertices · edges'), `${G.name} · n = ${G.n} · ${G.edges.length}`],
      [T('已核对的联盟', 'Coalitions checked'), `${pr.count} / ${gm.N}`],
      [T('至此最大赤字 · 联盟', 'Largest deficit so far · coalition'), `${sg(d, 5)} · ${setName(gm.order[pr.bestJ], G.n)}`],
      [T('能量 𝓔(G) 与 Σφ', 'Energy 𝓔(G) and Σφ'), `${fr(gm.w[gm.N - 1], 6)} · ${fr(sumPhi, 6)}`],
      [T('顶点能量分配：至此最大赤字', 'Vertex-energy allocation: largest deficit so far'), sg(maxV, 6)]]);
    pill('pillA', 'n', String(G.n)); pill('pillB', T('联盟', 'COALITIONS'), `${pr.count}/${gm.N}`); pill('pillC', T('最大赤字', 'MAX DEFICIT'), sg(d, 3)); pill('pillD', T('核', 'CORE'), pr.count === gm.N ? verdict(d) : (d > TOL ? verdict(d) : '…'));
    $('roNote').innerHTML = T(`联盟按大小排序逐个核对：赤字 = w(S) − Σ_{i∈S} φᵢ，w(S) 是诱导子图的能量。全部 ${gm.N} 个联盟核对完，Shapley 值${gm.D[gm.best[gm.N - 1]] > TOL ? '离开核' : '在核里'}；顶点能量分配的最大赤字为 ${sg(gm.DV[gm.bestV[gm.N - 1]], 6)}。`,
      `Coalitions are checked one by one in order of size: deficit = w(S) − Σ_{i∈S} φᵢ, where w(S) is the energy of the induced subgraph. Over all ${gm.N} coalitions the Shapley value ${gm.D[gm.best[gm.N - 1]] > TOL ? 'leaves the core' : 'stays in the core'}; the vertex-energy allocation has largest deficit ${sg(gm.DV[gm.bestV[gm.N - 1]], 6)}.`);
  }
}
function syncControls() {
  const M = MODEL;
  document.querySelectorAll('#modeChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.mode === M.mode)));
  document.querySelectorAll('#aChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.a === M.a)));
  document.querySelectorAll('#bChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.bmax === M.bmax)));
  document.querySelectorAll('#gChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.g === M.g)));
  $('aChips').hidden = M.mode !== 'bip'; $('bChips').hidden = M.mode !== 'bip'; $('gChips').hidden = M.mode !== 'graph';
}
const stateKey = () => `${S.mode}|${S.a}|${S.bmax}|${S.g}|${S.nowFrac}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; toasted = false; syncControls(); $('marks').dataset.key = ''; }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  const M = MODEL, pr = progress();
  readouts();
  $('formula').innerHTML = M.mode === 'bip' ? 'w(r, k) = 2√(rk), &nbsp; D(r, k) = 2√(rk) − rφ<sub>A</sub> − kφ<sub>B</sub>' : 'φ<sub>i</sub> = Σ<sub>S∌i</sub> |S|!(n − |S| − 1)!/n! · (w(S ∪ i) − w(S))';
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('modeNote').innerHTML = M.mode === 'bip' ? T(`时间轴 = 另一侧的顶点数 b，从 1 到 ${M.bmax}；同侧顶点对称，联盟只按 (r, k) 分类，Shapley 值按类型精确求和。`, `The time axis is the size b of the other side, from 1 to ${M.bmax}; vertices on one side are symmetric, so coalitions are classified by (r, k) and the Shapley value is summed exactly by type.`)
    : T(`时间轴 = 已核对的联盟数，从 1 到 2ⁿ = ${M.game.N}（按大小排序）。`, `The time axis is the number of coalitions checked, from 1 to 2ⁿ = ${M.game.N} (ordered by size).`);
  $('litNote').innerHTML = T('赤字、Shapley 值与顶点能量都由页面按定义算出；冻结的是 K₂,ₘ（m ≥ 50）的反驳。', 'The deficits, Shapley values and vertex energies are computed on the page from the definitions; what is frozen is the refutation through K₂,ₘ for m ≥ 50.');
  $('c1Title').textContent = M.mode === 'bip' ? T('赤字随 b 的变化', 'Deficits as b grows') : T('每个联盟的赤字', 'The deficit of every coalition');
  $('c2Title').textContent = M.mode === 'bip' ? T('V∖{a} 的赤字 ÷ √b', 'Deficit of V∖{a} divided by √b') : T('两种分配', 'Two allocations');
  $('clock').innerHTML = M.mode === 'bip' ? `b ${pr.b}` : `S ${pr.count}`;
  if (M.mode === 'bip') {
    $('hudBig').textContent = `${kname(M.a, pr.b)} · ${T('最大赤字', 'max deficit')} ${sg(pr.row.maxD, 3)} · ${verdict(pr.row.maxD)}`;
    $('hudSub').textContent = T('每条曲线是一个 r（稀缺侧在联盟里的顶点数），横向是 k（另一侧的顶点数），高度是赤字（asinh 刻度）；青 = ≤ 0，品红 = 挡住 Shapley 分配；琥珀点 = V∖{a}，白点 = 最大赤字，绿点 = 全体', 'each curve is one r (scarce vertices in the coalition), across is k (vertices of the other side), height is the deficit (asinh scale); cyan = ≤ 0, magenta = blocks the Shapley allocation; amber point = V∖{a}, white point = the largest deficit, green point = everyone');
  } else {
    $('hudBig').textContent = `${M.G.name} · ${T('已核对', 'checked')} ${pr.count}/${M.game.N}`;
    $('hudSub').textContent = T('琥珀柱 = Shapley 值，紫柱 = 顶点能量；白 = 当前联盟，品红 = 至此赤字最大且为正的联盟', 'amber bars = Shapley value, violet bars = vertex energy; white = the current coalition, magenta = the coalition with the largest positive deficit so far');
  }
  if (!toasted && S.playing && S.nowFrac >= 1) {
    toasted = true;
    if (M.mode === 'bip') toast(T(`<b>b = ${M.bmax}</b>：最大赤字 ${sg(pr.row.maxD, 4)}；V∖{a} 的赤字 ÷ √b = ${sg(pr.row.dLean / Math.sqrt(pr.row.b), 4)}${M.a === 2 ? `（符号计算的极限候选 ${COEF.toFixed(4)}）` : ''}。`, `<b>b = ${M.bmax}</b>: largest deficit ${sg(pr.row.maxD, 4)}; deficit of V∖{a} ÷ √b = ${sg(pr.row.dLean / Math.sqrt(pr.row.b), 4)}${M.a === 2 ? ` (the symbolic limit candidate is ${COEF.toFixed(4)})` : ''}.`));
    else { const gm = M.game, d = gm.D[gm.best[gm.N - 1]]; toast(T(`<b>${gm.N} 个联盟核对完</b>：最大赤字 ${sg(d, 5)}，联盟 ${setName(gm.order[gm.best[gm.N - 1]], gm.n)}——Shapley 值${d > TOL ? '离开核' : '在核里'}。`, `<b>All ${gm.N} coalitions checked</b>: largest deficit ${sg(d, 5)}, coalition ${setName(gm.order[gm.best[gm.N - 1]], gm.n)} — the Shapley value ${d > TOL ? 'leaves the core' : 'stays in the core'}.`)); }
  }
}
function syncRail() {
  const M = MODEL, key = `${M.id}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  let marks;
  if (M.mode === 'bip') {
    const f = (b) => (b - 1) / Math.max(1, M.bmax - 1);
    marks = [[0, 'b = 1']];
    const cand = [];
    if (M.firstAny) cand.push([f(M.firstAny), T(`离开核 ${M.firstAny}`, `leaves ${M.firstAny}`)]);
    if (M.a === 2 && LEAN_M <= M.bmax) cand.push([f(LEAN_M), 'LEAN 50']);
    for (const c of cand) if (c[0] - marks[marks.length - 1][0] > 0.12 && 1 - c[0] > 0.12) marks.push(c);
    marks.push([1, `b = ${M.bmax}`]);
  } else {
    const gm = M.game, fb = (gm.best[gm.N - 1] + 1) / gm.N;
    marks = [[0, '1']];
    if (gm.D[gm.best[gm.N - 1]] > TOL && fb > 0.12 && fb < 0.88) marks.push([fb, T('最大赤字', 'max deficit')]);
    marks.push([1, String(gm.N)]);
  }
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
function custom() { S.preset = null; markPreset(); dirty = true; }
document.querySelectorAll('#modeChips .chip').forEach((b) => b.addEventListener('click', () => { const m = MODES.includes(b.dataset.mode) ? b.dataset.mode : 'bip'; if (S.mode === m) return; S.mode = m; S.nowFrac = 0; $('now').value = 0; custom(); }));
document.querySelectorAll('#aChips .chip').forEach((b) => b.addEventListener('click', () => { S.a = A_CHOICES.includes(+b.dataset.a) ? +b.dataset.a : 2; custom(); }));
document.querySelectorAll('#bChips .chip').forEach((b) => b.addEventListener('click', () => { S.bmax = B_CHOICES.includes(+b.dataset.bmax) ? +b.dataset.bmax : 60; custom(); }));
document.querySelectorAll('#gChips .chip').forEach((b) => b.addEventListener('click', () => { S.g = GRAPHS[b.dataset.g] ? b.dataset.g : 'K25'; S.nowFrac = 0; $('now').value = 0; custom(); }));
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.mode = p.mode; if (p.a) S.a = p.a; if (p.bmax) S.bmax = p.bmax; if (p.g) S.g = p.g;
  S.preset = name; markPreset(); dirty = true;
  S.nowFrac = p.frac; S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.nowFrac;
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));

$('now').addEventListener('input', () => { S.nowFrac = parseFloat($('now').value); S.hold = 0; });
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
const jumpTo = (f) => { S.playing = false; setPlayUI(); S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; };
const stepSize = () => (MODEL.mode === 'bip' ? 1 / Math.max(1, MODEL.bmax - 1) : 1 / MODEL.game.N);
document.addEventListener('keydown', (ev) => {
  if (ev.target && (ev.target.tagName === 'INPUT' && ev.target.type !== 'range')) return;
  if (drawer.isOpen()) return;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(S.nowFrac + (ev.key === 'ArrowRight' ? 1 : -1) * stepSize()); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(1);
});

/* =====================================================================
   12. Main loop
   ===================================================================== */
let lastT = performance.now(), frameCount = 0;
function resize() {
  if (!glOK) return;
  const r = stage.getBoundingClientRect();
  renderer.setSize(Math.max(1, r.width), Math.max(1, r.height), false);
  camera.aspect = Math.max(0.2, r.width / Math.max(1, r.height)); camera.updateProjectionMatrix();
}
let glKey = '';
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { S.nowFrac = S.dir > 0 ? 0 : 1; toasted = false; } }
    else {
      S.nowFrac += S.dir * dtSec * S.speed / RUN[MODEL.mode];
      if (S.nowFrac >= 1) { S.nowFrac = 1; S.hold = 2.4; }
      if (S.nowFrac <= 0) { S.nowFrac = 0; S.hold = 1.2; }
    }
    $('now').value = S.nowFrac;
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    const pr = progress(), k = `${MODEL.id}|${MODEL.mode === 'bip' ? pr.b : pr.j}`;
    if (k !== glKey) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.EG_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => {
    const M = MODEL, pr = progress();
    if (M.mode === 'bip') return { mode: 'bip', a: M.a, bmax: M.bmax, b: pr.b, row: pr.row, grid: bipGrid(M.a, pr.row), firstAny: M.firstAny, firstLean: M.firstLean, rows: M.rows, tol: TOL, coef: COEF };
    const gm = M.game;
    return { mode: 'graph', g: M.g, n: gm.n, N: gm.N, edges: M.G.edges, w: Array.from(gm.w), phi: gm.phi, ve: gm.ve, order: gm.order, D: gm.D, DV: gm.DV, count: pr.count, j: pr.j, bestJ: pr.bestJ, bestVJ: pr.bestVJ, tol: TOL };
  },
  setFrac: (f) => { S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; }
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 15; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
applyPreset('lean');
setPlayUI();
requestAnimationFrame(frame);
})();
