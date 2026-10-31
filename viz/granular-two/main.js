/* GRANULAR//TWO · one set of positive rates, two physical steady states of the granular cell-order dynamics (C = 10)
   Myhill and Blumenfeld (J. Phys. A 56, 345001, 2023) study the fractions Q_3 … Q_C of cells of each order in a 2D granular
   packing: cells of orders i and j merge into one of order i + j − 2 at rate p_ij and split back at rate q_ij, with net flux
   η_ij = p_ij Q_i Q_j − q_ij Q_{i+j−2}. They conjecture that the physical steady state is unique for any constant rates.
   Refuted in trureturing (GranularCellOrderSteadyStateRefutation.result): for C = 10 and sixteen explicit positive rates, the
   states X = (3,2,5,1,2,1,1,1)/16 and Y = (12,6,5,4,4,1,1,1)/34 are both stationary. The page checks both certificates in exact
   rational arithmetic, integrates the dynamics with a stiff Rosenbrock scheme, finds the third state Z of the dossier by
   Newton's method, and shows Y as the saddle between the basins of X and Z.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Rates, states, exact certificates and the dynamics
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const C = 10, NK = 8, KS = [3, 4, 5, 6, 7, 8, 9, 10];
/* the processes 3 ≤ i ≤ j with i + j − 2 ≤ C, in the dossier's order; each entry is [i, j, product order] */
const PROC = [];
for (let i = 3; i <= C; i++) for (let j = i; j <= C; j++) if (i + j - 2 <= C) PROC.push([i, j, i + j - 2]);
const PIDX = new Map(PROC.map(([i, j], e) => [`${i},${j}`, e]));
/* exact fractions over BigInt */
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const fr = (n, d = 1n) => { n = BigInt(n); d = BigInt(d); if (d < 0n) { n = -n; d = -d; } const g = gcd(n, d) || 1n; return { n: n / g, d: d / g }; };
const fadd = (a, b) => fr(a.n * b.d + b.n * a.d, a.d * b.d), fsub = (a, b) => fr(a.n * b.d - b.n * a.d, a.d * b.d), fmul = (a, b) => fr(a.n * b.n, a.d * b.d);
const fstr = (a) => `${a.n < 0n ? '−' : ''}${a.n < 0n ? -a.n : a.n}${a.d === 1n ? '' : '/' + a.d}`;
const fnum = (a) => Number(a.n) / Number(a.d);
const ZERO = fr(0), HALF = fr(1, 2);
/* the rates of the frozen certificate, p10 and q10 */
const PF = [[10, 3], [2, 3], [4, 15], [4, 3], [2, 3], [2, 1], [509018, 225], [1, 1], [35579, 175], [2, 1], [422, 5], [2, 1], [386, 225], [30416, 25], [255689, 25], [4, 1]].map(([a, b]) => fr(a, b));
const QF = [[1, 1], [2, 5], [2, 1], [972, 5], [2, 1], [2, 1], [2138, 75], [141, 10], [1, 1], [2, 1], [2, 1], [3967, 35], [35878, 315], [2, 1], [233557, 35], [2, 1]].map(([a, b]) => fr(a, b));
const P = PF.map(fnum), QR = QF.map(fnum);
const span = (A) => { let lo = A[0], hi = A[0]; for (const a of A) { if (fnum(a) < fnum(lo)) lo = a; if (fnum(a) > fnum(hi)) hi = a; } return [lo, hi]; };
const PSPAN = span(PF), QSPAN = span(QF);
/* the two certified states, orders 3 … 10 */
const XE = [3, 2, 5, 1, 2, 1, 1, 1].map((v) => fr(v, 16)), YE = [12, 6, 5, 4, 4, 1, 1, 1].map((v) => fr(v, 34));
const XS = XE.map(fnum), YS = YE.map(fnum);
/* Lean's flux and right-hand side, literally, in exact arithmetic: gain over the processes making k, loss over those using k,
   and Q_k times the total flux */
const fluxE = (Q, i, j) => { const e = PIDX.get(`${Math.min(i, j)},${Math.max(i, j)}`); return fsub(fmul(fmul(PF[e], Q[i - 3]), Q[j - 3]), fmul(QF[e], Q[i + j - 5])); };
const delta = (i, j) => (i === j ? fr(1) : ZERO);
function rhsE(Q, k) {
  let gain = ZERO, loss = ZERO, tot = ZERO;
  for (let i = 3; i <= k - 1; i++) gain = fadd(gain, fmul(fluxE(Q, i, k - i + 2), fadd(fr(1), delta(i, k - i + 2))));
  gain = fmul(HALF, gain);
  for (let i = k + 1; i <= C; i++) loss = fadd(loss, fmul(fluxE(Q, k, i - k + 2), fadd(fr(1), delta(i, 2 * k - 2))));
  for (const [i, j] of PROC) tot = fadd(tot, fluxE(Q, i, j));
  const norm = fmul(Q[k - 3], tot);
  return { gain, loss, norm, rhs: fadd(fsub(gain, loss), norm), tot };
}
function certificate(Q) {
  const rows = KS.map((k) => rhsE(Q, k)), etas = PROC.map(([i, j]) => fluxE(Q, i, j));
  let sum = ZERO; for (const q of Q) sum = fadd(sum, q);
  return { rows, etas, tot: rows[0].tot, sum, positive: Q.every((q) => q.n > 0n) };
}
const CERT = { X: certificate(XE), Y: certificate(YE) };
/* detailed balance would need θ_33 θ_44 = θ_34 θ_35 with θ = p/q */
const theta = (e) => fr(PF[e].n * QF[e].d, PF[e].d * QF[e].n);
const DB = { left: fmul(theta(PIDX.get('3,3')), theta(PIDX.get('4,4'))), right: fmul(theta(PIDX.get('3,4')), theta(PIDX.get('3,5'))) };
/* floating point: Q̇ = A η + Q Σ η, where each process adds one cell of its product order and removes its two inputs */
const eta = (x) => PROC.map(([i, j, k], e) => P[e] * x[i - 3] * x[j - 3] - QR[e] * x[k - 3]);
function f(x) {
  const h = eta(x); let tot = 0; for (const v of h) tot += v;
  const out = x.map((v) => v * tot);
  PROC.forEach(([i, j, k], e) => { out[k - 3] += h[e]; out[i - 3] -= h[e]; out[j - 3] -= h[e]; });
  return out;
}
function jac(x) {
  const h = eta(x); let tot = 0; for (const v of h) tot += v;
  const Jm = Array.from({ length: NK }, () => new Array(NK).fill(0)), dtot = new Array(NK).fill(0);
  PROC.forEach(([i, j, k], e) => {
    const d = new Map(); const put = (m, v) => d.set(m, (d.get(m) || 0) + v);
    put(i - 3, P[e] * x[j - 3]); put(j - 3, P[e] * x[i - 3]); put(k - 3, -QR[e]);
    for (const [m, v] of d) { Jm[k - 3][m] += v; Jm[i - 3][m] -= v; Jm[j - 3][m] -= v; dtot[m] += v; }
  });
  for (let a = 0; a < NK; a++) { Jm[a][a] += tot; for (let m = 0; m < NK; m++) Jm[a][m] += x[a] * dtot[m]; }
  return Jm;
}
function solve(A, b) {
  const n = b.length, M = A.map((r, i) => [...r, b[i]]);
  for (let c = 0; c < n; c++) {
    let p = c; for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
    [M[c], M[p]] = [M[p], M[c]];
    for (let r = c + 1; r < n; r++) { const k = M[r][c] / M[c][c]; for (let q = c; q <= n; q++) M[r][q] -= k * M[c][q]; }
  }
  const x = new Array(n).fill(0);
  for (let r = n - 1; r >= 0; r--) { let s = M[r][n]; for (let q = r + 1; q < n; q++) s -= M[r][q] * x[q]; x[r] = s / M[r][r]; }
  return x;
}
/* the two-stage Rosenbrock scheme ROS2 (γ = 1 + 1/√2), L-stable, so the stiff rates of order 10⁴ need no tiny step */
const GAM = 1 + 1 / Math.SQRT2;
function ros2Step(x, h) {
  const Jm = jac(x), A = Jm.map((r, a) => r.map((v, b) => (a === b ? 1 : 0) - GAM * h * v));
  const k1 = solve(A, f(x)), f1 = f(x.map((v, a) => v + h * k1[a])), k2 = solve(A, f1.map((v, a) => v - 2 * k1[a]));
  return x.map((v, a) => v + 1.5 * h * k1[a] + 0.5 * h * k2[a]);
}
const TMAX = 14;
/* samples every `every` steps of size h up to TMAX */
function trajectory(x0, h, every) {
  let x = x0.slice(); const pts = [x.slice()], n = Math.round(TMAX / h);
  for (let s = 1; s <= n; s++) { x = ros2Step(x, h); if (s % every === 0) pts.push(x.slice()); }
  return { pts, dt: h * every, end: x };
}
/* Newton's method on the simplex: seven rows of Q̇ = 0 and Σ Q = 1 */
function newtonSimplex(x0) {
  let x = x0.slice();
  for (let it = 0; it < 60; it++) {
    const r = f(x), Jm = jac(x), A = Jm.slice(0, NK - 1).concat([new Array(NK).fill(1)]);
    const d = solve(A, r.slice(0, NK - 1).concat([x.reduce((a, c) => a + c, 0) - 1]));
    x = x.map((v, a) => v - d[a]); if (Math.max(...d.map(Math.abs)) < 1e-17) break;
  }
  return x;
}
/* the dossier's third state, printed to five digits, refined */
const ZD = [0.43995, 0.50554, 0.0050850, 0.044208, 0.0041825, 0.00048549, 0.00045463, 0.000099506];
const ZS = newtonSimplex(ZD);
/* inverse iteration with shift 1/2 on the simplex's tangent space (Σ δQ = 0, which J preserves): the eigenvalue nearest 1/2 */
function nearEigen(x) {
  const Jm = jac(x), A = Jm.map((r, a) => r.map((v, b) => v - (a === b ? 0.5 : 0)));
  let v = [1, -1, 1, -1, 1, -1, 1, -1].map((c) => c / Math.sqrt(8)), lam = 0;
  for (let it = 0; it < 400; it++) {
    let w = solve(A, v); const m = w.reduce((a, b) => a + b, 0) / NK; w = w.map((c) => c - m);
    const nr = Math.hypot(...w); v = w.map((c) => c / nr);
  }
  const Jv = Jm.map((r) => r.reduce((s, val, b) => s + val * v[b], 0)); lam = v.reduce((s, c, a) => s + c * Jv[a], 0);
  const res = Math.max(...Jv.map((c, a) => Math.abs(c - lam * v[a])));
  if (v[0] < 0) v = v.map((c) => -c);
  return { lam, v, res };
}
const EIG = { X: nearEigen(XS), Y: nearEigen(YS), Z: nearEigen(ZS) };
const dist = (a, b) => { let m = 0; for (let q = 0; q < NK; q++) m = Math.max(m, Math.abs(a[q] - b[q])); return m; };
const STATES = { X: XS, Y: YS, Z: ZS };
function nearest(x) { let best = 'X', bd = Infinity; for (const nm of ['X', 'Y', 'Z']) { const d = dist(x, STATES[nm]); if (d < bd) { bd = d; best = nm; } } return { name: best, d: bd }; }
/* the sweep of starts: Q_3 = a, Q_4 = b on a grid, the rest spread evenly over orders 5 … 10 */
const SWEEP = [];
for (let bi = 0; bi < 9; bi++) for (let ai = 0; ai < 9; ai++) { const a = 0.05 + 0.1 * ai, b = 0.05 + 0.1 * bi; if (a + b > 0.96) continue; const r = (1 - a - b) / 6; SWEEP.push([a, b, r, r, r, r, r, r]); }

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean', mode: 'saddle', side: -1, lgEps: -3, start: null, cert: 'X' };
const PRESETS = {
  lean: { mode: 'saddle', side: -1, lgEps: -3, cert: 'X',
    zh: '从 Y 出发，沿它唯一的不稳定方向朝 X 一侧推 10⁻³：轨道离开 Y，停在 X。X 与 Y 都是这组正速率下的物理稳态，Lean 用精确有理数验证了两者的 8 行方程全为 0，而 X₃ = 3/16 ≠ 6/17 = Y₃，所以唯一性猜想不成立。',
    en: 'Start at Y and push it by 10⁻³ along its single unstable direction, towards X: the trajectory leaves Y and settles at X. X and Y are both physical steady states of these positive rates; Lean checks all eight equations at each in exact rationals, and X₃ = 3/16 ≠ 6/17 = Y₃, so the uniqueness conjecture fails.' },
  toz: { mode: 'saddle', side: 1, lgEps: -3, cert: 'Y',
    zh: '同样从 Y 出发，推向另一侧：轨道停在第三个稳态 Z（卷宗的数值解，页面用牛顿法求精）。同一组速率，终点由初始条件决定。',
    en: 'Start at Y again and push it the other way: the trajectory settles at a third steady state Z (the dossier\'s numerical solution, refined by Newton\'s method on the page). Same rates; the endpoint depends on the initial condition.' },
  sweep: { mode: 'sweep', cert: 'X',
    zh: '45 个起点：Q₃ 与 Q₄ 取网格上的值，其余的质量平分给 5 到 10 阶。Q₃ 大的起点流向 Z，其余流向 X——两个吸引域被 Y 隔开。',
    en: '45 starts: Q₃ and Q₄ on a grid, the remaining mass split evenly over orders 5 to 10. Starts with a large Q₃ flow to Z, the rest to X — two basins, separated through Y.' },
  corner: { mode: 'point', start: [0.45, 0.45, 0.02, 0.02, 0.02, 0.02, 0.01, 0.01], cert: 'Y',
    zh: '三角形与四边形占九成的起点：直接流向 Z。Z 里 3 阶和 4 阶胞占 94.5%，与 X、Y 都很不一样。',
    en: 'A start in which triangles and quadrilaterals make up 90%: it flows straight to Z. In Z, cells of orders 3 and 4 make up 94.5%, unlike X or Y.' },
  nearx: { mode: 'point', start: [0.2075, 0.105, 0.3125, 0.0625, 0.125, 0.0625, 0.0625, 0.0625], cert: 'X',
    zh: '从 X 附近出发（Q₃ 多 0.02、Q₄ 少 0.02）：轨道回到 X。页面算出 X 处 Jacobian 离 0 最近的特征值是 −2.613，扰动按 e^(−2.613 t) 衰减。',
    en: 'Start near X (Q₃ up by 0.02, Q₄ down by 0.02): the trajectory returns to X. The page finds the Jacobian\'s eigenvalue nearest 0 at X to be −2.613, so the perturbation decays like e^(−2.613 t).' },
  slow: { mode: 'saddle', side: -1, lgEps: -6, cert: 'Y',
    zh: '推得更轻（10⁻⁶）：轨道在 Y 附近停留更久，因为偏离按 e^(2.350 t) 增长，要约 ln(10⁶)/2.350 ≈ 5.9 的时间才离开。',
    en: 'A gentler push (10⁻⁶): the trajectory lingers near Y longer, since the deviation grows like e^(2.350 t) and needs about ln(10⁶)/2.350 ≈ 5.9 time units to leave.' }
};
const startOf = () => (S.mode === 'saddle' ? YS.map((v, a) => v + S.side * 10 ** S.lgEps * EIG.Y.v[a]) : S.start.slice());
const CACHE = new Map();
function compute(key, fn) { if (!CACHE.has(key)) CACHE.set(key, fn()); return CACHE.get(key); }
/* Y's unstable manifold, both branches */
const MANI = [-1, 1].map((sg) => trajectory(YS.map((v, a) => v + sg * 1e-7 * EIG.Y.v[a]), 0.004, 5));
let MODEL = null, dirty = true, modelId = 0, modelKey = '';
function build() {
  const key = S.mode === 'sweep' ? 'sweep' : `${S.mode}|${S.side}|${S.lgEps}|${S.start}`;
  if (key !== modelKey) { modelKey = key; modelId++; }
  let trajs;
  if (S.mode === 'sweep') trajs = compute('sweep', () => SWEEP.map((x0) => trajectory(x0, 0.01, 5)));
  else trajs = [compute(key, () => trajectory(startOf(), 0.004, 5))];
  const ends = trajs.map((tr) => nearest(tr.end)), tau = S.t * TMAX;
  const at = (tr) => { const u = tau / tr.dt, i = Math.min(tr.pts.length - 2, Math.floor(u)), w = Math.min(1, u - i); return tr.pts[i].map((v, a) => v + w * (tr.pts[i + 1][a] - v)); };
  const cur = at(trajs[0]);
  MODEL = { id: modelId, mode: S.mode, trajs, ends, tau, cur, near: nearest(cur), start: trajs[0].pts[0], at,
    counts: { X: ends.filter((e) => e.name === 'X' && e.d < 1e-6).length, Z: ends.filter((e) => e.name === 'Z' && e.d < 1e-6).length } };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const sup = (e) => String(e).replace(/-/g, '⁻').replace(/[0-9]/g, (d) => '⁰¹²³⁴⁵⁶⁷⁸⁹'[d]);
const sci = (v) => { if (v === 0) return '0'; const e = Math.floor(Math.log10(Math.abs(v))), m = v / 10 ** e; return `${m.toFixed(1)}×10${sup(e)}`; };

/* =====================================================================
   4. 3D scene: the projection (Q₃, Q₄, Q₅) of the simplex, the three steady states, trajectories and Y's unstable manifold
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const SC = 9, CEN = [0.32, 0.3, 0.13], LINES_MAX = 60000, PTS_MAX = 400;
const CAMS = { iso: [0.55, 1.05, 12.5], side: [0.0001, 1.5, 12], top: [0.0001, 0.05, 12] };
const cam = { theta: 0.55, phi: 1.05, r: 12.5, tTheta: 0.55, tPhi: 1.05, tR: 12.5 };
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
  float a = smoothstep(1.0, 0.6, r) * vA;
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
/* (Q₃, Q₄, Q₅) → world: Q₃ to the right, Q₄ into the screen, Q₅ up */
const W = (q) => [(q[0] - CEN[0]) * SC, (q[2] - CEN[2]) * SC, -(q[1] - CEN[1]) * SC];
const STCOL = { X: COL.cyan, Y: COL.amber, Z: COL.magenta };
function updateGL() {
  const M = MODEL, Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, col, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, al, size) => { if (np >= PTS_MAX) return; for (let k = 0; k < 3; k++) { PT.position.array[3 * np + k] = p[k]; PT.aColor.array[3 * np + k] = col[k]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const gray = [0.5, 0.6, 0.72];
  /* the tetrahedron Q₃, Q₄, Q₅ ≥ 0, Q₃ + Q₄ + Q₅ ≤ 1 and a grid on its floor */
  const O = [0, 0, 0], E3 = [1, 0, 0], E4 = [0, 1, 0], E5 = [0, 0, 1];
  for (const [a, b] of [[O, E3], [O, E4], [O, E5], [E3, E4], [E3, E5], [E4, E5]]) seg(W(a), W(b), gray, 0.35);
  for (let s = 0.1; s < 0.95; s += 0.1) { seg(W([s, 0, 0]), W([s, 1 - s, 0]), gray, 0.08); seg(W([0, s, 0]), W([1 - s, s, 0]), gray, 0.08); }
  /* Y's unstable manifold: towards X and towards Z */
  MANI.forEach((tr) => { for (let q = 0; q + 1 < tr.pts.length; q++) seg(W(tr.pts[q]), W(tr.pts[q + 1]), COL.amber, 0.28); });
  /* trajectories: the travelled part bright, the rest faint (the sweep shows only the travelled part) */
  const tau = M.tau;
  M.trajs.forEach((tr, n) => {
    const endCol = M.ends[n].name === 'Z' ? COL.magenta : COL.cyan, col = M.mode === 'sweep' ? endCol : [0.95, 0.97, 1];
    const last = Math.min(tr.pts.length - 1, Math.floor(tau / tr.dt));
    for (let q = 0; q + 1 < tr.pts.length; q++) {
      if (q < last) seg(W(tr.pts[q]), W(tr.pts[q + 1]), col, M.mode === 'sweep' ? 0.55 : 0.95);
      else if (M.mode !== 'sweep') seg(W(tr.pts[q]), W(tr.pts[q + 1]), col, 0.12);
    }
    const head = M.at(tr); dot(W(head), col, 1, (M.mode === 'sweep' ? 1.6 : 3) * 1.1);
    if (M.mode === 'sweep') dot(W(tr.pts[0]), endCol, 0.35, 1.2);
  });
  /* the three steady states, with drop lines to the floor */
  for (const nm of ['X', 'Y', 'Z']) { const q = STATES[nm]; dot(W(q), STCOL[nm], 1, 5.5); seg(W(q), W([q[0], q[1], 0]), STCOL[nm], 0.35); }
  if (M.mode !== 'sweep') dot(W(M.start), [0.95, 0.97, 1], 0.6, 2.4);
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const at of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) at.needsUpdate = true;
  pts.material.uniforms.uScale.value = 60 * renderer.getPixelRatio() * (stage.clientHeight / 600);
}

/* =====================================================================
   5. Camera
   ===================================================================== */
function updateCamera(dtSec) {
  const k = reduceMotion ? 1 : 1 - Math.pow(0.001, dtSec);
  cam.theta += (cam.tTheta - cam.theta) * k; cam.phi += (cam.tPhi - cam.phi) * k; cam.r += (cam.tR - cam.r) * k;
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.45 : 1);
  camera.position.set(r * sp * Math.sin(cam.theta), r * Math.cos(cam.phi), r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(0, 0, 0);
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
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(30, Math.max(4, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.05, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(30, Math.max(4, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

/* =====================================================================
   6. Tags
   ===================================================================== */
const tagPool = [];
function tagAt(k, cls) { while (tagPool.length <= k) { const el = document.createElement('div'); el.className = 'tag raw'; tagsBox.appendChild(el); tagPool.push(el); } const el = tagPool[k]; el.className = 'tag raw ' + cls; return el; }
function placeTag(el, p, hideOff = false) {
  if (!glOK) { el.style.display = 'none'; return; }
  const q = proj3(p); if (q.z > 1 || q.z < -1 || (hideOff && (q.x < 0 || q.y < 0 || q.x > stage.clientWidth || q.y > stage.clientHeight))) { el.style.display = 'none'; return; }
  el.style.display = 'block';
  const w = el.offsetWidth, h = el.offsetHeight, Wd = stage.clientWidth, Hd = stage.clientHeight, hud = document.querySelector('.hud-tl'), top = hud.offsetTop + hud.offsetHeight + 4;
  el.style.left = Math.min(Wd - w / 2 - 6, Math.max(w / 2 + 6, q.x)) + 'px'; el.style.top = Math.min(Hd - h / 2 - 6, Math.max(top + h / 2, q.y)) + 'px';
}
function updateTags() {
  let k = 0;
  const put = (text, p, cls, hideOff) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p, hideOff); };
  const lift = (q, d) => { const w = W(q); return [w[0], w[1] + d, w[2]]; };
  put(T('X（Lean）', 'X (Lean)'), lift(XS, 0.55), 't');
  put(T('Y（Lean · 鞍点）', 'Y (Lean · saddle)'), lift(YS, 0.55), 'am');
  put(T('Z（数值）', 'Z (numeric)'), lift(ZS, 0.55), 'mg');
  put('Q₃ = 1', W([1, 0, 0]), 'w', true); put('Q₄ = 1', W([0, 1, 0]), 'w', true); put('Q₅ = 1', W([0, 0, 1]), 'w', true);
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
/* distances to X, Y, Z along the trajectory (log scale); for the sweep, how many starts are within 10⁻⁶ of X and of Z */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 40); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, X0 = (tt) => pl + iw * tt / TMAX;
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  if (M.mode === 'sweep') {
    const n = M.trajs.length, Y0 = (c) => pt + ih * (1 - c / n);
    for (const [nm, col] of [['X', CY], ['Z', MG]]) {
      ctx.beginPath();
      for (let q = 0; q < M.trajs[0].pts.length; q++) { let c = 0; for (const tr of M.trajs) if (dist(tr.pts[Math.min(q, tr.pts.length - 1)], STATES[nm]) < 1e-6) c++; const x = X0(q * M.trajs[0].dt), y = Y0(c); q ? ctx.lineTo(x, y) : ctx.moveTo(x, y); }
      ctx.strokeStyle = col; ctx.lineWidth = 1.5 * dpr; ctx.stroke();
    }
    lab(ctx, String(n), pl - 4 * dpr, Y0(n), 'right', 'middle'); lab(ctx, '0', pl - 4 * dpr, Y0(0), 'right', 'middle');
    $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('距 X < 10⁻⁶', 'within 10⁻⁶ of X')}</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('距 Z < 10⁻⁶', 'within 10⁻⁶ of Z')}</span>`;
  } else {
    const tr = M.trajs[0], Y0 = (d) => pt + ih * (1 - (Math.log10(Math.max(1e-16, d)) + 16) / 16);
    for (const [nm, col] of [['X', CY], ['Y', AM], ['Z', MG]]) {
      ctx.beginPath(); tr.pts.forEach((x, q) => { const px = X0(q * tr.dt), py = Y0(dist(x, STATES[nm])); q ? ctx.lineTo(px, py) : ctx.moveTo(px, py); });
      ctx.strokeStyle = col; ctx.lineWidth = 1.4 * dpr; ctx.stroke();
    }
    [0, -8, -16].forEach((e) => lab(ctx, `10${sup(e)}`, pl - 4 * dpr, Y0(10 ** e), 'right', 'middle'));
    $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('到 X', 'to X')}</span><span class="it"><i class="sw" style="--c:${AM}"></i>${T('到 Y', 'to Y')}</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('到 Z', 'to Z')}</span>`;
  }
  [0, 7, 14].forEach((tt, q) => lab(ctx, String(tt), X0(tt), pt + ih + 4 * dpr, ['left', 'center', 'right'][q], 'top'));
  ctx.strokeStyle = 'rgba(255,200,61,0.8)'; ctx.lineWidth = 1 * dpr; ctx.beginPath(); ctx.moveTo(X0(M.tau), pt); ctx.lineTo(X0(M.tau), pt + ih); ctx.stroke();
}
/* the sixteen net fluxes at the chosen certified state, on a signed log scale */
function drawSide() {
  const cert = CERT[S.cert], F2 = frame2d(cv2, 34); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, n = PROC.length, bw = iw / n, sl = (v) => Math.sign(v) * Math.log10(1 + Math.abs(v) / 0.01), top = sl(30), Y0 = (v) => pt + ih / 2 - (ih / 2) * sl(v) / top;
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.moveTo(pl, Y0(0)); ctx.lineTo(pl + iw, Y0(0)); ctx.stroke();
  cert.etas.forEach((e, q) => {
    const v = fnum(e), x = pl + q * bw;
    ctx.fillStyle = v > 0 ? 'rgba(25,240,255,0.7)' : 'rgba(255,47,208,0.6)';
    const y0 = Y0(0), y1 = Y0(v); ctx.fillRect(x + bw * 0.15, Math.min(y0, y1), bw * 0.7, Math.abs(y1 - y0));
    const [i, j] = PROC[q]; lab(ctx, `${i}${j}`, x + bw / 2, pt + ih + 4 * dpr, 'center', 'top', DIM);
  });
  [10, 0.1, -0.1, -10].forEach((v) => lab(ctx, String(v).replace('-', '−'), pl - 4 * dpr, Y0(v), 'right', 'middle'));
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>η > 0</span><span class="it"><i class="sw" style="--c:${MG}"></i>η &lt; 0</span><span class="it">· ${T(`ij：i 阶与 j 阶合并 · Σ η = ${fstr(cert.tot)}`, `ij: orders i and j merge · Σ η = ${fstr(cert.tot)}`)}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const startText = () => (S.mode === 'saddle' ? `Y ${S.side > 0 ? '+' : '−'} 10${sup(S.lgEps)}·v` : S.mode === 'sweep' ? T('45 个网格起点', '45 grid starts') : `(${S.start.map((v) => +v.toFixed(4)).join(', ')})`);
const sgn = (v) => (v >= 0 ? '+' : '−') + Math.abs(v).toFixed(3);
function readouts() {
  const M = MODEL, cert = CERT[S.cert], e0 = M.ends[0];
  pill('pillA', 'C', '10'); pill('pillB', T('过程', 'processes'), '16'); pill('pillC', T('物理稳态', 'steady states'), 'X ≠ Y'); pill('pillD', 't', M.tau.toFixed(2));
  const rowsZero = cert.rows.every((r) => r.rhs.n === 0n), nz = cert.etas.filter((e) => e.n !== 0n).length;
  setRo([
    [T('过程数 · p 的范围 · q 的范围（全为正）', 'Processes · range of p · range of q (all positive)'), `16 · ${fstr(PSPAN[0])} … ${fstr(PSPAN[1])} · ${fstr(QSPAN[0])} … ${fstr(QSPAN[1])}`],
    [T('两个稳态在 3 阶处不同（Lean）', 'The two steady states differ at order 3 (Lean)'), `X₃ = ${fstr(XE[0])} · Y₃ = ${fstr(YE[0])} · ${fnum(XE[0]) === fnum(YE[0]) ? '=' : '≠'}`],
    [T(`${S.cert} 处：8 行右端 · Σ η · ΣQ · 非零 η（精确）`, `At ${S.cert}: the 8 right-hand sides · Σ η · Σ Q · nonzero η (exact)`), `${rowsZero ? T('全为 0', 'all 0') : T('不全为 0', 'not all 0')} · ${fstr(cert.tot)} · ${fstr(cert.sum)} · ${nz} / 16`],
    [T(`${S.cert} 处最大的净通量`, `The largest net flux at ${S.cert}`), (() => { let b = 0; cert.etas.forEach((e, q) => { if (Math.abs(fnum(e)) > Math.abs(fnum(cert.etas[b]))) b = q; }); const [i, j] = PROC[b]; return `η(${i}, ${j}) = ${fstr(cert.etas[b])} ≈ ${fnum(cert.etas[b]).toFixed(3).replace('-', '−')}`; })()],
    [T('起点 · t · 终点 · 终点误差', 'Start · t · end · error at the end'), M.mode === 'sweep' ? `${startText()} · ${M.tau.toFixed(2)} · X ${M.counts.X} / Z ${M.counts.Z}` : `${startText()} · ${M.tau.toFixed(2)} · ${e0.name} · ${sci(e0.d)}`],
    [T('Jacobian 在单纯形上离 1/2 最近的特征值：X · Y · Z', 'Jacobian eigenvalue nearest 1/2 on the simplex: X · Y · Z'), `${sgn(EIG.X.lam)} · ${sgn(EIG.Y.lam)} · ${sgn(EIG.Z.lam)}`]]);
  $('roNote').innerHTML = T(`θ = p/q：θ₃₃·θ₄₄ = ${fstr(DB.left)}，θ₃₄·θ₃₅ = ${fstr(DB.right)}，两者不等，所以这组速率下没有细致平衡态；X、Y、Z 都带着循环的净通量。`, `θ = p/q: θ₃₃·θ₄₄ = ${fstr(DB.left)} and θ₃₄·θ₃₅ = ${fstr(DB.right)} differ, so these rates have no detailed-balance state; X, Y and Z all carry circulating net fluxes.`);
}
const stateKey = () => `${S.mode}|${S.side}|${S.lgEps}|${S.start}|${S.cert}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; }
  const M = MODEL;
  if (!toasted && S.playing && S.t >= 1) {
    toasted = true;
    if (M.mode === 'sweep') toast(T(`<b>45 个起点</b>：${M.counts.X} 个停在 X，${M.counts.Z} 个停在 Z。`, `<b>45 starts</b>: ${M.counts.X} settle at X, ${M.counts.Z} at Z.`));
    else toast(T(`<b>停在 ${M.ends[0].name}</b>：t = 14 时距离 ${sci(M.ends[0].d)}。`, `<b>Settled at ${M.ends[0].name}</b>: distance ${sci(M.ends[0].d)} at t = 14.`));
  }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('epsIn').value = String(S.lgEps); $('epsOut').textContent = `10${sup(S.lgEps)}`;
  document.querySelectorAll('#sideChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(S.mode === 'saddle' && Number(b.dataset.side) === S.side)));
  document.querySelectorAll('#certChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.cert === S.cert)));
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T('v 是 Y 处唯一的不稳定方向（页面用反幂迭代求出）。沿 +v 推向 Z，沿 −v 推向 X；ε 越小，轨道在 Y 附近停得越久。', 'v is the single unstable direction at Y (found on the page by inverse iteration). Pushing along +v leads to Z, along −v to X; the smaller ε, the longer the trajectory lingers near Y.');
  $('litNote').innerHTML = T('原文的数值检验只用了相差不超过 30 倍的速率；这里的速率跨了四个多数量级。', 'The paper\'s numerical tests used rates within a factor of 30 of each other; the rates here span more than four orders of magnitude.');
  $('c1Title').textContent = M.mode === 'sweep' ? T('到达 X 与 Z 的起点数', 'Starts that have reached X and Z') : T('到三个稳态的距离（对数刻度）', 'Distance to the three steady states (log scale)');
  $('c2Title').textContent = T(`${S.cert} 处的 16 个净通量`, `The 16 net fluxes at ${S.cert}`);
  $('clock').innerHTML = `t = ${M.tau.toFixed(2)}`;
  $('hudBig').textContent = M.mode === 'sweep' ? `X ${M.counts.X} · Z ${M.counts.Z}` : `${startText()} → ${M.ends[0].name}`;
  $('hudSub').textContent = T(`投影到 (Q₃, Q₄, Q₅)。青点 X 与琥珀点 Y 是 Lean 验证过的两个稳态，品红点 Z 是数值找到的第三个。琥珀细线是 Y 的不稳定流形：一支通向 X，一支通向 Z。${M.mode === 'sweep' ? '青线是流向 X 的起点，品红线是流向 Z 的起点' : '白线是当前轨道'}`, `Projected to (Q₃, Q₄, Q₅). The cyan X and amber Y are the two steady states checked in Lean, the magenta Z a third found numerically. The thin amber lines are Y's unstable manifold: one branch leads to X, the other to Z. ${M.mode === 'sweep' ? 'Cyan paths flow to X, magenta paths to Z' : 'The white line is the current trajectory'}`);
}
function syncRail() {
  const key = TRV.lang(); if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  $('marks').innerHTML = [[0, 't = 0', 'first'], [0.5, 't = 7', 'mid'], [1, 't = 14', 'last']].map(([f0, l, c]) => `<i class="${c}" style="left:${(f0 * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { mode: p.mode, cert: p.cert, t: 0, hold: 0 });
  if (p.mode === 'saddle') Object.assign(S, { side: p.side, lgEps: p.lgEps, start: null });
  if (p.mode === 'point') S.start = p.start.slice();
  if (p.mode === 'sweep') S.start = null;
  S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('epsIn').addEventListener('input', () => { S.lgEps = parseFloat($('epsIn').value); S.mode = 'saddle'; S.start = null; custom(); });
document.querySelectorAll('#sideChips .chip').forEach((b) => b.addEventListener('click', () => { S.side = Number(b.dataset.side); S.mode = 'saddle'; S.start = null; custom(); }));
document.querySelectorAll('#certChips .chip').forEach((b) => b.addEventListener('click', () => { S.cert = b.dataset.cert; custom(); }));
const setT = (t) => { S.t = Math.min(1, Math.max(0, t)); $('now').value = S.t; dirty = true; };
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo((Math.round(S.t * TMAX) + (ev.key === 'ArrowRight' ? 1 : -1)) / TMAX); }
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
const RUN_SECONDS = 12;
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : 1); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed / RUN_SECONDS);
      if (S.t >= 1) S.hold = 2.4;
      if (S.t <= 0 && S.dir < 0) S.hold = 1.2;
    }
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    const k = `${MODEL.id}|${MODEL.tau}`;
    if (glKey !== k) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.GR_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { mode: M.mode, tau: M.tau, cur: M.cur.slice(), start: M.start.slice(), near: { ...M.near }, ends: M.ends.map((e) => ({ ...e })), counts: { ...M.counts },
    n: M.trajs.length, endPts: M.trajs.map((tr) => tr.end.slice()), starts: M.trajs.map((tr) => tr.pts[0].slice()) }; },
  PROC: PROC.map((p) => p.slice()),
  rates: () => ({ p: PF.map(fstr), q: QF.map(fstr) }),
  states: () => ({ X: XE.map(fstr), Y: YE.map(fstr), Z: ZS.slice() }),
  cert: (nm) => { const c = CERT[nm]; return { rows: c.rows.map((r) => ({ gain: fstr(r.gain), loss: fstr(r.loss), norm: fstr(r.norm), rhs: fstr(r.rhs) })), etas: c.etas.map(fstr), tot: fstr(c.tot), sum: fstr(c.sum), positive: c.positive }; },
  db: () => ({ left: fstr(DB.left), right: fstr(DB.right) }),
  eig: () => ({ X: { lam: EIG.X.lam, v: EIG.X.v.slice() }, Y: { lam: EIG.Y.lam, v: EIG.Y.v.slice() }, Z: { lam: EIG.Z.lam, v: EIG.Z.v.slice() } }),
  f: (x) => f(x),
  manifold: () => MANI.map((tr) => tr.end.slice()),
  sweep: () => SWEEP.map((x) => x.slice()),
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('sweep'); S.playing = false; setPlayUI(); setT(0.6); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 11.5; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
