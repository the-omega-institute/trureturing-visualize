/* OQW//RUIN · the gambler's ruin of an open quantum walk sees Im ρ₀₁
   Jacq and Lardizabal (2017, Remark 5.3) conjectured that for every normalized pair L, R (L*L + R*R = I) the mean
   absorption time on {0, …, M} from site k with internal state ρ is 1 + h(M, M − k)ρ₀₀ + h(M, k)ρ₁₁ + j(M, k)·Re ρ₀₁
   with j(M, k) = −j(M, M − k). Frozen in trureturing (OpenQuantumWalkGamblerHittingTimeRefutation.result): false.
   With u = (1, i), v = (1, −i), L = ½vu*, R = ½vv*, the states ρ = ½uu* and σ = ½vv* agree in ρ₀₀, ρ₁₁ and Re ρ₀₁
   but have mean times 1 and 2 at M = 3, k = 1. The page runs the walk, solves for the hitting-time operators A_k
   (E_k(ρ) = tr(A_k ρ)) and plots the three equations the conjectured form needs at every k.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Constants and 2 × 2 complex matrices
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.5, 0.58, 0.68], WHITE = [0.92, 0.95, 1];
const MMIN = 3, MMAX = 12, TOL = 1e-14, CAP = 20000, TV_MAX = 60;
const fr = (x, d = 4) => (isFinite(x) ? (Math.abs(x) < 5e-13 ? 0 : x).toFixed(d) : '—');
/* a matrix is [re00, im00, re01, im01, re10, im10, re11, im11] */
const ix = (i, j) => 2 * (2 * i + j);
const Z2 = () => new Float64Array(8);
function mul(A, B) {
  const C = Z2();
  for (let i = 0; i < 2; i++) for (let j = 0; j < 2; j++) {
    let re = 0, im = 0;
    for (let k = 0; k < 2; k++) { const a = ix(i, k), b = ix(k, j); re += A[a] * B[b] - A[a + 1] * B[b + 1]; im += A[a] * B[b + 1] + A[a + 1] * B[b]; }
    C[ix(i, j)] = re; C[ix(i, j) + 1] = im;
  }
  return C;
}
function adj(A) { const C = Z2(); for (let i = 0; i < 2; i++) for (let j = 0; j < 2; j++) { C[ix(i, j)] = A[ix(j, i)]; C[ix(i, j) + 1] = -A[ix(j, i) + 1]; } return C; }
const add = (A, B) => A.map((v, i) => v + B[i]);
const trRe = (A) => A[0] + A[6];
const sand = (X, S) => mul(mul(X, S), adj(X));
const mat = (rows) => Float64Array.from(rows.flat(2));
/* density matrix from a Bloch vector: ρ = (I + xX + yY + zZ)/2, so ρ₀₁ = (x − iy)/2 */
const rhoOf = ([x, y, z]) => mat([[[(1 + z) / 2, 0], [x / 2, -y / 2]], [[x / 2, y / 2], [(1 - z) / 2, 0]]]);
const blochOf = (S, m = trRe(S)) => [2 * S[2] / m, -2 * S[3] / m, (S[0] - S[6]) / m];

/* =====================================================================
   2. The pairs
   ===================================================================== */
/* Lean's pair: u = (1, i), v = (1, −i), L = ½vu*, R = ½vv* */
const RESET = { L: mat([[[0.5, 0], [0, -0.5]], [[0, -0.5], [-0.5, 0]]]), R: mat([[[0.5, 0], [0, 0.5]], [[0, -0.5], [0.5, 0]]]) };
const FAIR = { L: mat([[[Math.SQRT1_2, 0], [0, 0]], [[0, 0], [Math.SQRT1_2, 0]]]), R: mat([[[Math.SQRT1_2, 0], [0, 0]], [[0, 0], [Math.SQRT1_2, 0]]]) };
/* a seeded random isometry V (4 × 2): Gaussian columns, Gram–Schmidt; L = rows 0–1, R = rows 2–3, so L*L + R*R = V*V = I */
function randomPair(seed, real) {
  const rnd = TRV.mulberry32(seed), gauss = () => Math.sqrt(-2 * Math.log(1 - rnd())) * Math.cos(2 * Math.PI * rnd());
  const col = () => Array.from({ length: 4 }, () => [gauss(), real ? 0 : gauss()]);
  const dot = (a, b) => a.reduce((s, [ar, ai], i) => [s[0] + ar * b[i][0] + ai * b[i][1], s[1] + ar * b[i][1] - ai * b[i][0]], [0, 0]);
  const scale = (a, s) => a.map(([r, i]) => [r * s, i * s]);
  let c0 = col(), c1 = col();
  c0 = scale(c0, 1 / Math.sqrt(dot(c0, c0)[0]));
  const p = dot(c0, c1); c1 = c1.map(([r, i], n) => [r - (p[0] * c0[n][0] - p[1] * c0[n][1]), i - (p[0] * c0[n][1] + p[1] * c0[n][0])]);
  c1 = scale(c1, 1 / Math.sqrt(dot(c1, c1)[0]));
  const block = (o) => mat([[c0[o], c1[o]], [c0[o + 1], c1[o + 1]]]);
  return { L: block(0), R: block(2) };
}
function pairOf(name, seed) { return name === 'reset' ? RESET : name === 'fair' ? FAIR : randomPair(seed, name === 'real'); }

/* =====================================================================
   3. The walk and the hitting-time operators
   ===================================================================== */
/* advance the unnormalized states ρₓ(t + 1) = Rρₓ₋₁(t)R* + Lρₓ₊₁(t)L*, absorbing at 0 and M */
function walk(P, M, k, rho, keepRows) {
  let st = new Array(M + 1).fill(null); st[k] = rho;
  const abs0 = [0], absM = [0], rows = [];
  const snap = (st, flows) => st.map((S, x) => (S && x > 0 && x < M ? { m: trRe(S), b: trRe(S) > 1e-12 ? blochOf(S) : [0, 0, 0], l: flows ? flows[x][0] : 0, r: flows ? flows[x][1] : 0 } : null));
  let mean = 0, p0 = 0, pM = 0, rem = trRe(rho), t = 0;
  while (t < CAP && rem >= TOL) {
    t++;
    const nx = new Array(M + 1).fill(null), flows = new Array(M + 1).fill(null); let a0 = 0, aM = 0;
    for (let x = 1; x < M; x++) {
      const S = st[x]; if (!S) continue;
      const Ls = sand(P.L, S), Rs = sand(P.R, S); flows[x] = [trRe(Ls), trRe(Rs)];
      if (x - 1 === 0) a0 += trRe(Ls); else nx[x - 1] = nx[x - 1] ? add(nx[x - 1], Ls) : Ls;
      if (x + 1 === M) aM += trRe(Rs); else nx[x + 1] = nx[x + 1] ? add(nx[x + 1], Rs) : Rs;
    }
    if (rows.length < keepRows) rows.push(snap(st, flows));
    abs0.push(a0); absM.push(aM); mean += t * (a0 + aM); p0 += a0; pM += aM;
    st = nx; rem = st.reduce((s, S) => s + (S ? trRe(S) : 0), 0);
  }
  if (rows.length < keepRows) rows.push(snap(st, null));
  return { mean, p0, pM, rem, steps: t, abs0, absM, rows };
}
/* A_k = I + L*A_{k−1}L + R*A_{k+1}R with A₀ = A_M = 0: a complex linear system in the 4(M − 1) entries */
function hittingOperators(P, M) {
  const n = 4 * (M - 1), re = Array.from({ length: n }, () => new Float64Array(n + 1)), im = Array.from({ length: n }, () => new Float64Array(n + 1));
  const v = (k, a, b) => 4 * (k - 1) + 2 * a + b;
  for (let k = 1; k < M; k++) for (let a = 0; a < 2; a++) for (let b = 0; b < 2; b++) {
    const row = v(k, a, b); re[row][row] += 1; re[row][n] = a === b ? 1 : 0;
    for (const [nb, X] of [[k - 1, P.L], [k + 1, P.R]]) {
      if (nb === 0 || nb === M) continue;
      /* (X*AX)_ab = Σ_cd conj(X_ca)·A_cd·X_db */
      for (let c = 0; c < 2; c++) for (let d = 0; d < 2; d++) {
        const xr = X[ix(c, a)], xi = -X[ix(c, a) + 1], yr = X[ix(d, b)], yi = X[ix(d, b) + 1];
        re[row][v(nb, c, d)] -= xr * yr - xi * yi; im[row][v(nb, c, d)] -= xr * yi + xi * yr;
      }
    }
  }
  /* Gaussian elimination with partial pivoting */
  for (let c = 0; c < n; c++) {
    let p = c; for (let r = c + 1; r < n; r++) if (Math.hypot(re[r][c], im[r][c]) > Math.hypot(re[p][c], im[p][c])) p = r;
    [re[c], re[p]] = [re[p], re[c]]; [im[c], im[p]] = [im[p], im[c]];
    const dr = re[c][c], di = im[c][c], dd = dr * dr + di * di;
    for (let r = 0; r < n; r++) {
      if (r === c) continue;
      const fr0 = (re[r][c] * dr + im[r][c] * di) / dd, fi0 = (im[r][c] * dr - re[r][c] * di) / dd;
      if (fr0 === 0 && fi0 === 0) continue;
      for (let j = c; j <= n; j++) { const a = re[c][j], b = im[c][j]; re[r][j] -= fr0 * a - fi0 * b; im[r][j] -= fr0 * b + fi0 * a; }
    }
  }
  const A = [null];
  for (let k = 1; k < M; k++) {
    const m = Z2();
    for (let a = 0; a < 2; a++) for (let b = 0; b < 2; b++) {
      const r = v(k, a, b), dr = re[r][r], di = im[r][r], dd = dr * dr + di * di;
      m[ix(a, b)] = (re[r][n] * dr + im[r][n] * di) / dd; m[ix(a, b) + 1] = (im[r][n] * dr - re[r][n] * di) / dd;
    }
    A.push(m);
  }
  return A;
}
const trA = (A, rho) => trRe(mul(A, rho));

/* =====================================================================
   4. State and presets
   ===================================================================== */
const S = { pair: 'reset', seed: 7, M: 3, k: 1, th: 90, ph: 90, r: 1, t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { pair: 'reset', seed: 7, M: 3, k: 1, th: 90, ph: 90, r: 1, play: true,
    zh: 'Lean 里的反例：M = 3、从 k = 1 出发，内部态 ρ = ½uu*（Bloch 向量指向 +y）。L 把 u 送到 v，所以第一步就向左走到 0 被吸收——平均吸收时间正好是 1。',
    en: 'Lean’s counterexample: M = 3, start at k = 1, internal state ρ = ½uu* (Bloch vector along +y). L sends u to v, so the walk steps left to 0 at once and is absorbed — the mean absorption time is exactly 1.' },
  conj: { pair: 'reset', seed: 7, M: 3, k: 1, th: 90, ph: 270, r: 1, play: true,
    zh: '同一对矩阵、同一起点，换成 σ = ½vv*（指向 −y）。σ 的 ρ₀₀、ρ₁₁、Re ρ₀₁ 与 ρ 完全一样，只有 Im ρ₀₁ 符号相反。L 消灭 v，R 保持 v，所以它向右走两步才到 M = 3：平均时间 2。猜想的公式给 ρ 和 σ 同一个值，不可能同时等于 1 和 2。',
    en: 'Same pair, same start, now σ = ½vv* (along −y). σ has the same ρ₀₀, ρ₁₁ and Re ρ₀₁ as ρ; only the sign of Im ρ₀₁ differs. L kills v and R keeps it, so the walk needs two steps right to reach M = 3: mean time 2. The conjectured formula gives ρ and σ one value, which cannot be both 1 and 2.' },
  long: { pair: 'reset', seed: 7, M: 8, k: 4, th: 90, ph: 90, r: 1, play: true,
    zh: '更长的走廊：M = 8、k = 4。ρ 先向左一步、变成 v 方向，再一路向右，平均时间 M − k + 2 = 6；σ 一路向右，平均时间 M − k = 4（右下图与读数里的“共轭态”）。本页的论证，未形式化。',
    en: 'A longer corridor: M = 8, k = 4. ρ steps left once, turning into the v direction, then goes right all the way, mean time M − k + 2 = 6; σ goes right all the way, mean time M − k = 4 (the “conjugate state” in the readouts). The page’s argument, not formalized.' },
  fair: { pair: 'fair', seed: 7, M: 6, k: 2, th: 90, ph: 90, r: 1, play: true,
    zh: '经典公平硬币 L = R = I/√2：内部态不起作用，平均时间是经典的 k(M − k) = 8，A_k 是 8 倍单位阵。右下图的三个差全为 0——对这对矩阵，猜想的形式成立。',
    en: 'The classical fair coin L = R = I/√2: the internal state plays no role, the mean time is the classical k(M − k) = 8, and A_k is 8 times the identity. All three gaps in the lower right chart vanish — for this pair the conjectured form holds.' },
  complex: { pair: 'complex', seed: 7, M: 5, k: 2, th: 60, ph: 45, r: 1, play: true,
    zh: '一对带种子的随机复矩阵：几乎必然吸收，但 Im A_k,₀₁ 在每个 k 上都不为 0，所以平均时间真的依赖 Im ρ₀₁（Bloch 球的颜色沿品红轴变化）。页面数值。',
    en: 'A seeded random complex pair: absorption is almost sure, but Im A_k,₀₁ is nonzero at every k, so the mean time really depends on Im ρ₀₁ (the colour of the Bloch ball changes along the magenta axis). Page numbers.' },
  real: { pair: 'real', seed: 11, M: 5, k: 2, th: 60, ph: 45, r: 1, play: true,
    zh: '一对带种子的随机实矩阵：A_k 是实的，Im 项为 0，共轭态的平均时间相同；可反射等式 A_k,₀₀ = A_{M−k},₁₁ 与 Re A_k,₀₁ = −Re A_{M−k},₀₁ 不成立，所以对这对矩阵也找不到 h、j。页面数值，不是定理。',
    en: 'A seeded random real pair: the A_k are real, the Im term vanishes and the conjugate state has the same mean time; but the reflection equations A_k,₀₀ = A_{M−k},₁₁ and Re A_k,₀₁ = −Re A_{M−k},₀₁ fail, so no h, j fit this pair either. Page numbers, not a theorem.' }
};

/* =====================================================================
   5. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
const blochIn = () => { const th = S.th * Math.PI / 180, ph = S.ph * Math.PI / 180; return [S.r * Math.sin(th) * Math.cos(ph), S.r * Math.sin(th) * Math.sin(ph), S.r * Math.cos(th)]; };
function build() {
  S.M = Math.min(MMAX, Math.max(MMIN, Math.round(S.M))); S.k = Math.min(S.M - 1, Math.max(1, Math.round(S.k)));
  const P = pairOf(S.pair, S.seed), M = S.M, k = S.k, bl = blochIn(), rho = rhoOf(bl), conjB = [bl[0], -bl[1], bl[2]];
  const nrm = add(mul(adj(P.L), P.L), mul(adj(P.R), P.R)), normErr = Math.max(Math.abs(nrm[0] - 1), Math.abs(nrm[1]), Math.hypot(nrm[2], nrm[3]), Math.abs(nrm[6] - 1), Math.abs(nrm[7]));
  const W = walk(P, M, k, rho, TV_MAX + 1), Wc = walk(P, M, k, rhoOf(conjB), 0);
  /* the visible stretch: until at least 99.9 % is absorbed */
  let TV = 1, cum = 0; for (let t = 1; t < W.abs0.length; t++) { cum += W.abs0[t] + W.absM[t]; TV = t; if (1 - cum < 1e-3) break; }
  TV = Math.max(2, Math.min(TV_MAX, TV));
  /* absorption can finish before t = 2: pad both series to the visible stretch */
  while (W.abs0.length <= TV) { W.abs0.push(0); W.absM.push(0); }
  const A = hittingOperators(P, M);
  const gaps = { im: [], refl: [], anti: [] };
  for (let q = 1; q < M; q++) { gaps.im.push(A[q][3]); gaps.refl.push(A[q][0] - A[M - q][6]); gaps.anti.push(A[q][2] + A[M - q][2]); }
  const worst = (a) => a.reduce((s, x) => Math.max(s, Math.abs(x)), 0);
  /* the mean time over the Bloch sphere of pure initial states */
  const sphere = []; let eMin = Infinity, eMax = -Infinity;
  for (let i = 1; i < 12; i++) for (let j = 0; j < 24; j++) { const th = Math.PI * i / 12, ph = 2 * Math.PI * j / 24, b = [Math.sin(th) * Math.cos(ph), Math.sin(th) * Math.sin(ph), Math.cos(th)], e = trA(A[k], rhoOf(b)); sphere.push([b, e]); eMin = Math.min(eMin, e); eMax = Math.max(eMax, e); }
  for (const b of [[0, 0, 1], [0, 0, -1]]) { const e = trA(A[k], rhoOf(b)); sphere.push([b, e]); eMin = Math.min(eMin, e); eMax = Math.max(eMax, e); }
  MODEL = { id: ++modelId, P, M, k, bloch: bl, rho, normErr, ...W, meanConj: Wc.mean, conjBloch: conjB, TV, A, gaps,
    gapMax: [worst(gaps.im), worst(gaps.refl), worst(gaps.anti)], eOp: trA(A[k], rho), sphere, eMin, eMax };
}

/* =====================================================================
   6. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');

/* =====================================================================
   7. 3D scene: the walk over sites × time, and the Bloch ball
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 16000, PTS_MAX = 2400;
const CAMS = { iso: [0.6, 1.0, 18], front: [0.0001, 1.35, 18], top: [0.0001, 0.06, 19] };
const cam = { theta: 0.6, phi: 1.0, r: 18, tTheta: 0.6, tPhi: 1.0, tR: 18 };
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
  camera = new THREE.PerspectiveCamera(38, 1, 0.05, 120);
  const g = new THREE.BufferGeometry(); dyn(g, 'position', LINES_MAX, 3); dyn(g, 'color', LINES_MAX, 3);
  lines = new THREE.LineSegments(g, new THREE.LineBasicMaterial({ vertexColors: true, ...additive })); lines.frustumCulled = false; scene3.add(lines);
  const gp = new THREE.BufferGeometry(); dyn(gp, 'position', PTS_MAX, 3); dyn(gp, 'aColor', PTS_MAX, 3); dyn(gp, 'aAlpha', PTS_MAX, 1); dyn(gp, 'aSize', PTS_MAX, 1);
  pts = new THREE.Points(gp, new THREE.ShaderMaterial({ vertexShader: EVT_VS, fragmentShader: DOT_FS, uniforms: { uScale: { value: 60 } }, ...additive }));
  pts.frustumCulled = false; scene3.add(pts);
}
/* layout: site x at X = (x − M/2)·SX, time t at depth Z = 3 − t·DZ; the Bloch ball sits to the right */
function layout(M) {
  const SX = Math.min(1.1, 8.8 / M), DZ = Math.min(0.9, 9 / MODEL.TV), RB = 1.5;
  return { SX, DZ, RB, X: (x) => (x - M / 2) * SX, Zt: (t) => 3 - t * DZ, ball: [M / 2 * SX + 3.2, 1.9, 1.2] };
}
const ramp = (f) => [CYAN3[0] + (AMB3[0] - CYAN3[0]) * f, CYAN3[1] + (AMB3[1] - CYAN3[1]) * f, CYAN3[2] + (AMB3[2] - CYAN3[2]) * f];
const CYAN3 = COL.cyan, AMB3 = COL.amber;
function updateGL() {
  const M = MODEL, G = layout(M.M), tNow = S.t, tInt = Math.floor(tNow + 1e-9), frac = tNow - tInt;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, col, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, al, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const { X, Zt, SX } = G, TV = M.TV;
  /* floor: the sites as lines into the depth, the two absorbing ends brighter */
  for (let x = 0; x <= M.M; x++) seg([X(x), 0, Zt(0)], [X(x), 0, Zt(TV)], x === 0 ? COL.cyan : x === M.M ? COL.amber : GREY, x === 0 || x === M.M ? 0.45 : 0.1);
  for (let t = 0; t <= TV; t++) seg([X(0), 0, Zt(t)], [X(M.M), 0, Zt(t)], GREY, t % 5 === 0 ? 0.12 : 0.04);
  seg([X(0) - 0.3, 0.01, Zt(tNow)], [X(M.M) + 0.3, 0.01, Zt(tNow)], WHITE, 0.55);
  /* the walk: rows t = 0 … ⌊t⌋, the next one fading in */
  const shown = Math.min(TV, tInt);
  for (let t = 0; t <= Math.min(TV, tInt + 1); t++) {
    const row = M.rows[t]; if (!row) continue;
    const fade = t <= shown ? 1 : frac;
    row.forEach((c, x) => {
      if (!c || c.m < 1e-9) return;
      const p = [X(x), 0, Zt(t)], s = Math.sqrt(c.m);
      dot(p, COL.pre, 0.95 * fade, 1.0 + 2.6 * s);
      const b = c.b, col = b[1] > 0.05 ? COL.amber : b[1] < -0.05 ? COL.magenta : GREY, L = 0.8 * Math.min(1, 0.35 + s);
      seg(p, [p[0] + L * b[0], L * b[2] + 0.02, p[2] - L * b[1]], col, 0.95 * fade);
      /* branches into the next step, brightness by probability */
      if (t < TV && t < shown + 1) {
        const k2 = t < shown ? 1 : frac;
        if (c.l > 1e-9) seg(p, [X(x - 1), 0, Zt(t + 1)], COL.cyan, Math.min(1, 0.25 + 0.75 * Math.sqrt(c.l)) * k2);
        if (c.r > 1e-9) seg(p, [X(x + 1), 0, Zt(t + 1)], COL.amber, Math.min(1, 0.25 + 0.75 * Math.sqrt(c.r)) * k2);
      }
    });
  }
  /* absorbed probability at each step: bars at the two ends */
  const HB = 2.6;
  for (let t = 1; t <= Math.min(TV, tInt + 1); t++) {
    const k2 = t <= shown ? 1 : frac;
    if (M.abs0[t] > 1e-9) { seg([X(0), 0, Zt(t)], [X(0), HB * M.abs0[t], Zt(t)], COL.cyan, k2); dot([X(0), HB * M.abs0[t], Zt(t)], COL.cyan, k2, 1.2); }
    if (M.absM[t] > 1e-9) { seg([X(M.M), 0, Zt(t)], [X(M.M), HB * M.absM[t], Zt(t)], COL.amber, k2); dot([X(M.M), HB * M.absM[t], Zt(t)], COL.amber, k2, 1.2); }
  }
  /* the start */
  for (let a = 0; a < 24; a++) { const q0 = 2 * Math.PI * a / 24, q1 = 2 * Math.PI * (a + 1) / 24; seg([X(M.k) + 0.32 * Math.cos(q0), 0, Zt(0) + 0.32 * Math.sin(q0)], [X(M.k) + 0.32 * Math.cos(q1), 0, Zt(0) + 0.32 * Math.sin(q1)], WHITE, 0.6); }
  /* the Bloch ball: Bloch x → scene x, Bloch z → up, Bloch y → towards the viewer */
  const [cx, cy, cz] = G.ball, RB = G.RB, at = (b, r = RB) => [cx + r * b[0], cy + r * b[2], cz + r * b[1]];
  for (let a = 0; a < 48; a++) {
    const q0 = 2 * Math.PI * a / 48, q1 = 2 * Math.PI * (a + 1) / 48;
    seg(at([Math.cos(q0), Math.sin(q0), 0]), at([Math.cos(q1), Math.sin(q1), 0]), GREY, 0.3);
    seg(at([Math.cos(q0), 0, Math.sin(q0)]), at([Math.cos(q1), 0, Math.sin(q1)]), GREY, 0.2);
    seg(at([0, Math.cos(q0), Math.sin(q0)]), at([0, Math.cos(q1), Math.sin(q1)]), GREY, 0.2);
  }
  seg(at([-1.25, 0, 0]), at([1.25, 0, 0]), GREY, 0.45); seg(at([0, 0, -1.25]), at([0, 0, 1.25]), GREY, 0.45);
  seg(at([0, -1.35, 0]), at([0, 1.35, 0]), COL.magenta, 0.9);
  const span = Math.max(1e-9, M.eMax - M.eMin);
  for (const [b, e] of M.sphere) dot(at(b), ramp((e - M.eMin) / span), 0.85, 1.1);
  /* the initial state and its conjugate (same ρ₀₀, ρ₁₁, Re ρ₀₁) */
  seg(at([0, 0, 0]), at(M.bloch), WHITE, 0.9); dot(at(M.bloch), WHITE, 1, 2.2);
  seg(at(M.bloch), at(M.conjBloch), COL.magenta, 0.35); dot(at(M.conjBloch), COL.magenta, 0.9, 1.6);
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const a of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) a.needsUpdate = true;
  pts.material.uniforms.uScale.value = 60 * renderer.getPixelRatio() * (stage.clientHeight / 600);
}

/* =====================================================================
   8. Camera
   ===================================================================== */
function camTarget() { const G = layout(MODEL.M); return [(G.X(0) + G.ball[0] + G.RB) / 2, 1.0, (G.Zt(0) + G.Zt(MODEL.TV)) / 2]; }
function updateCamera(dtSec) {
  const k = reduceMotion ? 1 : 1 - Math.pow(0.001, dtSec);
  cam.theta += (cam.tTheta - cam.theta) * k; cam.phi += (cam.tPhi - cam.phi) * k; cam.r += (cam.tR - cam.r) * k;
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.45 : 1), c = camTarget();
  camera.position.set(c[0] + r * sp * Math.sin(cam.theta), c[1] + r * Math.cos(cam.phi), c[2] + r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(c[0], c[1], c[2]);
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
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()]; drag.pinch = Math.hypot(p.x - q.x, p.y - q.y); }
});
stage.addEventListener('pointermove', (ev) => {
  if (!drag.pts.has(ev.pointerId)) return;
  drag.pts.set(ev.pointerId, { x: ev.clientX, y: ev.clientY });
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(50, Math.max(7, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(50, Math.max(7, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

/* =====================================================================
   9. Tags
   ===================================================================== */
const tagPool = [];
function tagAt(k, cls) { while (tagPool.length <= k) { const el = document.createElement('div'); el.className = 'tag raw'; tagsBox.appendChild(el); tagPool.push(el); } const el = tagPool[k]; el.className = 'tag raw ' + cls; return el; }
function placeTag(el, p) {
  if (!glOK) { el.style.display = 'none'; return; }
  const q = proj3(p); if (q.z > 1 || q.z < -1) { el.style.display = 'none'; return; }
  el.style.display = 'block';
  /* keep tags inside the stage and below the HUD text in its top left corner */
  const w = el.offsetWidth, h = el.offsetHeight, Wd = stage.clientWidth, Hd = stage.clientHeight, hud = document.querySelector('.hud-tl'), top = hud.offsetTop + hud.offsetHeight + 4;
  el.style.left = Math.min(Wd - w / 2 - 6, Math.max(w / 2 + 6, q.x)) + 'px'; el.style.top = Math.min(Hd - h / 2 - 6, Math.max(top + h / 2, q.y)) + 'px';
}
function updateTags() {
  const M = MODEL, G = layout(M.M); let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  put(T('0（吸收）', '0 (absorbing)'), [G.X(0) - 0.2, -0.35, G.Zt(0) + 0.5], 'cy');
  put(T(`M = ${M.M}（吸收）`, `M = ${M.M} (absorbing)`), [G.X(M.M) + 0.2, -0.35, G.Zt(0) + 0.5], 'hot');
  put(`k = ${M.k}`, [G.X(M.k), -0.4, G.Zt(0) + 0.7], 'gr');
  put(T(`时间 t = ${M.TV}`, `time t = ${M.TV}`), [G.X(0) - 0.8, 0, G.Zt(M.TV)], 'gr');
  const [cx, cy, cz] = G.ball, RB = G.RB;
  put(T('初始态的 Bloch 球', 'Bloch ball of initial states'), [cx, cy + RB + 0.55, cz], 'gr');
  put('Im ρ₀₁', [cx, cy, cz + 1.45 * RB], 'mg');
  put(`E = ${fr(M.mean, 3)}`, [cx + RB * M.bloch[0], cy + RB * M.bloch[2] + 0.35, cz + RB * M.bloch[1]], 'hot');
  for (let i = k; i < tagPool.length; i++) tagPool[i].style.display = 'none';
}

/* =====================================================================
   10. 2D panels
   ===================================================================== */
function frame2d(cv, pl0 = 46) {
  const dpr = fitCanvas(cv), ctx = cv.getContext('2d'), Wd = cv.width, Hh = cv.height;
  ctx.clearRect(0, 0, Wd, Hh);
  const pl = pl0 * dpr, pr = 34 * dpr, pt = 12 * dpr, pb = 20 * dpr;
  ctx.font = `${9.5 * dpr}px ${TRV.fonts.data}`;
  return { dpr, ctx, W: Wd, Hh, pl, pt, iw: Wd - pl - pr, ih: Hh - pt - pb };
}
function lab(ctx, txt, x, y, al, bl, col = DIM) { ctx.fillStyle = col; ctx.textAlign = al; ctx.textBaseline = bl; ctx.fillText(txt, x, y); }
/* the distribution of the absorption time: stacked bars (at 0, at M), the cumulative probability and the mean */
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 36); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, TV = M.TV;
  let top = 0; for (let t = 1; t <= TV; t++) top = Math.max(top, M.abs0[t] + M.absM[t]);
  top = Math.max(0.05, top * 1.1);
  const X = (t) => pl + iw * (t - 0.5) / TV, Y = (y) => pt + ih - ih * y / top, Yc = (c) => pt + ih - ih * c, bw = Math.max(1, iw / TV * 0.7);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  for (const y of [0, top / 2, top]) lab(ctx, fr(y, 2), pl - 4 * dpr, Y(y), 'right', 'middle');
  for (const c of [0, 0.5, 1]) lab(ctx, String(c), pl + iw + 4 * dpr, Yc(c), 'left', 'middle', INK);
  const step = Math.max(1, Math.ceil(TV / 10));
  for (let t = 1; t <= TV; t += step) lab(ctx, String(t), X(t), pt + ih + 4 * dpr, 'center', 'top');
  for (let t = 1; t <= TV; t++) {
    const a = M.abs0[t], b = M.absM[t], on = t <= S.t + 1e-9 ? 1 : 0.35;
    ctx.globalAlpha = on; ctx.fillStyle = CY; ctx.fillRect(X(t) - bw / 2, Y(a), bw, Y(0) - Y(a));
    ctx.fillStyle = AM; ctx.fillRect(X(t) - bw / 2, Y(a + b), bw, Y(a) - Y(a + b)); ctx.globalAlpha = 1;
  }
  ctx.strokeStyle = INK; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); let cum = 0;
  for (let t = 1; t <= TV; t++) { cum += M.abs0[t] + M.absM[t]; const x = X(t), y = Yc(cum); if (t === 1) ctx.moveTo(x, y); else ctx.lineTo(x, y); }
  ctx.stroke();
  if (M.mean <= TV + 0.5) { const xm = X(M.mean); ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.strokeStyle = AM; ctx.beginPath(); ctx.moveTo(xm, pt); ctx.lineTo(xm, pt + ih); ctx.stroke(); ctx.setLineDash([]); const right = xm > pl + iw * 0.8; lab(ctx, `E = ${fr(M.mean, 3)}`, xm + (right ? -4 : 4) * dpr, pt + 2 * dpr, right ? 'right' : 'left', 'top', AM); }
  ctx.strokeStyle = 'rgba(255,255,255,0.4)'; ctx.lineWidth = 1; const xc = pl + iw * Math.min(1, S.t / TV); ctx.beginPath(); ctx.moveTo(xc, pt); ctx.lineTo(xc, pt + ih); ctx.stroke();
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('落到 0', 'at 0')}</span><span class="it"><i class="sw" style="--c:${AM}"></i>${T(`落到 M = ${M.M}`, `at M = ${M.M}`)}</span><span class="it"><i class="sw" style="--c:${INK}"></i>${T('累计（右轴）', 'cumulative (right axis)')}</span>`;
}
/* the three equations the conjectured form needs at every k: Im A_k,01 = 0, A_k,00 = A_{M−k},11, Re A_k,01 = −Re A_{M−k},01 */
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 34); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, n = M.M - 1;
  const top = Math.max(0.05, ...M.gaps.im.map(Math.abs), ...M.gaps.refl.map(Math.abs), ...M.gaps.anti.map(Math.abs)) * 1.1;
  const gw = iw / n, Y = (y) => pt + ih / 2 - (ih / 2) * y / top, bw = gw * 0.22;
  ctx.fillStyle = 'rgba(255,200,61,0.08)'; ctx.fillRect(pl + (M.k - 1) * gw, pt, gw, ih);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
  for (const y of [-top, 0, top]) lab(ctx, fr(y, 2), pl - 4 * dpr, Y(y), 'right', 'middle');
  for (let q = 1; q <= n; q++) {
    const x0 = pl + (q - 1) * gw + gw / 2;
    [[M.gaps.im[q - 1], MG], [M.gaps.refl[q - 1], CY], [M.gaps.anti[q - 1], AM]].forEach(([g, col], i) => {
      ctx.fillStyle = col; const y0 = Y(0), y1 = Y(g); ctx.fillRect(x0 + (i - 1.5) * bw, Math.min(y0, y1), bw, Math.max(1, Math.abs(y1 - y0)));
    });
    lab(ctx, `k=${q}`, x0, pt + ih + 4 * dpr, 'center', 'top', q === M.k ? AM : DIM);
  }
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${MG}"></i>Im A₀₁</span><span class="it"><i class="sw" style="--c:${CY}"></i>A₀₀ − A′₁₁</span><span class="it"><i class="sw" style="--c:${AM}"></i>Re A₀₁ + Re A′₀₁</span>`;
}

/* =====================================================================
   11. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const PAIR_NAME = { reset: ['Lean 的复矩阵对', 'Lean’s complex pair'], fair: ['公平硬币', 'fair coin'], complex: ['随机复矩阵对', 'random complex pair'], real: ['随机实矩阵对', 'random real pair'] };
const fits = () => MODEL.gapMax.every((g) => g < 1e-9);
function readouts() {
  const M = MODEL, rho = M.rho, A = M.A[M.k], diff = M.mean - M.meanConj;
  pill('pillA', 'M · k', `${M.M} · ${M.k}`); pill('pillB', 'E(τ)', fr(M.mean, 3)); pill('pillC', T('共轭态', 'CONJUGATE'), fr(M.meanConj, 3)); pill('pillD', 'Im A₀₁', fr(A[3], 3));
  setRo([[T('平均吸收时间 E_k(ρ) · 落到 0 / 落到 M 的概率', 'Mean absorption time E_k(ρ) · probability of ending at 0 / at M'), `${fr(M.mean, 4)} · ${fr(M.p0, 4)} / ${fr(M.pM, 4)}`],
    [T('ρ₀₀ · ρ₁₁ · Re ρ₀₁ · Im ρ₀₁', 'ρ₀₀ · ρ₁₁ · Re ρ₀₁ · Im ρ₀₁'), `${fr(rho[0], 3)} · ${fr(rho[6], 3)} · ${fr(rho[2], 3)} · ${fr(rho[3], 3)}`],
    [T('命中时间算子 A_k：A₀₀ · A₁₁ · Re A₀₁ · Im A₀₁', 'Hitting-time operator A_k: A₀₀ · A₁₁ · Re A₀₁ · Im A₀₁'), `${fr(A[0], 3)} · ${fr(A[6], 3)} · ${fr(A[2], 3)} · ${fr(A[3], 3)}`],
    [T('共轭态 ρ̄（ρ₀₀、ρ₁₁、Re ρ₀₁ 相同）的平均时间 · 差', 'Conjugate state ρ̄ (same ρ₀₀, ρ₁₁, Re ρ₀₁): mean time · difference'), `${fr(M.meanConj, 4)} · ${fr(diff, 4)}`],
    [T('猜想的形式在这对矩阵与 M 上：三个差在各 k 上的最大值', 'The conjectured form for this pair and M: largest of the three gaps over k'), `${fr(M.gapMax[0], 4)} · ${fr(M.gapMax[1], 4)} · ${fr(M.gapMax[2], 4)} · ${fits() ? T('成立', 'holds') : T('不成立', 'fails')}`]]);
  $('roNote').innerHTML = Math.abs(diff) > 1e-9
    ? T(`ρ 与它的共轭 ρ̄ 的 ρ₀₀、ρ₁₁、Re ρ₀₁ 相同，猜想的公式给它们同一个值；游走给出 ${fr(M.mean, 3)} 与 ${fr(M.meanConj, 3)}。`, `ρ and its conjugate ρ̄ share ρ₀₀, ρ₁₁ and Re ρ₀₁, so the conjectured formula gives them one value; the walk gives ${fr(M.mean, 3)} and ${fr(M.meanConj, 3)}.`)
    : fits() ? T('对这对矩阵与 M，三个差全为 0：猜想的形式成立。', 'For this pair and M all three gaps vanish: the conjectured form holds.')
      : T('这里 ρ 与 ρ̄ 的平均时间相同，可反射等式不成立，所以对这对矩阵与 M 找不到 h、j（页面数值）。', 'Here ρ and ρ̄ have the same mean time, but the reflection equations fail, so no h, j fit this pair and M (page numbers).');
}
const stateKey = () => `${S.pair}|${S.seed}|${S.M}|${S.k}|${S.th}|${S.ph}|${S.r}|${Math.floor(S.t + 1e-9)}|${S.preset}|${TRV.lang()}`;
function cplx(re, im) { return `${fr(re, 3)}${im < -5e-13 ? ' − ' : ' + '}${fr(Math.abs(im), 3)}i`; }
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; syncControls(); $('marks').dataset.key = ''; }
  const M = MODEL;
  if (!toasted && S.playing && S.t >= M.TV) { toasted = true; toast(T(`<b>${M.TV} 步后</b>：落到 0 的概率 ${fr(M.p0, 3)}，落到 M 的概率 ${fr(M.pM, 3)}，平均吸收时间 ${fr(M.mean, 3)}；共轭态是 ${fr(M.meanConj, 3)}。`, `<b>After ${M.TV} steps</b>: probability ${fr(M.p0, 3)} of ending at 0 and ${fr(M.pM, 3)} at M, mean absorption time ${fr(M.mean, 3)}; the conjugate state gives ${fr(M.meanConj, 3)}.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  const name = T(...PAIR_NAME[S.pair]), L = M.P.L, R = M.P.R, show = (A) => `[[${cplx(A[0], A[1])}, ${cplx(A[2], A[3])}], [${cplx(A[4], A[5])}, ${cplx(A[6], A[7])}]]`;
  $('pairNote').innerHTML = `${name}${S.pair === 'complex' || S.pair === 'real' ? T(`（种子 ${S.seed}）`, ` (seed ${S.seed})`) : ''}：L = ${show(L)}，R = ${show(R)}；‖L*L + R*R − I‖ ≤ ${M.normErr.toExponential(1)}`.replace(/：/g, T('：', ': ')).replace(/，/g, T('，', ', ')).replace(/；/g, T('；', '; '));
  const r = M.rho;
  $('rhoBox').innerHTML = `ρ = [[${fr(r[0], 3)}, ${cplx(r[2], r[3]).replace(/([+−] [0-9.]+i)/, '<span class="im">$1</span>')}], [${cplx(r[4], r[5]).replace(/([+−] [0-9.]+i)/, '<span class="im">$1</span>')}, ${fr(r[6], 3)}]] · Bloch (${M.bloch.map((v) => fr(v, 2)).join(', ')})`;
  $('litNote').innerHTML = T('平均时间、A_k 与随机矩阵对都由页面算出；冻结的是 Lean 的矩阵对在 M = 3、k = 1 时给 ρ 与 σ 不同的平均时间。', 'The mean times, the A_k and the random pairs are computed on the page; what is frozen is that Lean’s pair gives ρ and σ different mean times at M = 3, k = 1.');
  $('c1Title').textContent = T('吸收时间的分布', 'Distribution of the absorption time');
  $('c2Title').textContent = T('猜想的形式在每个 k 上要求为 0 的三个差（A = A_k，A′ = A_{M−k}）', 'The three gaps the conjectured form needs to vanish at every k (A = A_k, A′ = A_{M−k})');
  $('clock').innerHTML = `t = ${Math.floor(S.t + 1e-9)}`;
  $('hudBig').textContent = `M = ${M.M} · k = ${M.k} · E(τ) = ${fr(M.mean, 3)} · ${T('共轭态', 'conjugate')} ${fr(M.meanConj, 3)}`;
  $('hudSub').textContent = T('左：格点（横）× 时间（纵深）；点 = 该处概率，短箭头 = 内部态的 Bloch 向量（琥珀 Im ρ₀₁ < 0，品红 Im ρ₀₁ > 0），青 / 琥珀连线 = 向左 / 向右的分支，两端的柱 = 每一步被吸收的概率。右：初始态的 Bloch 球，颜色 = 平均时间（青低、琥珀高），白点 = ρ，品红点 = 共轭态 ρ̄，品红轴 = Im ρ₀₁ 方向', 'Left: sites (across) × time (into the depth); dot = probability there, short arrow = Bloch vector of the internal state (amber Im ρ₀₁ < 0, magenta Im ρ₀₁ > 0), cyan / amber links = left / right branches, bars at the ends = probability absorbed at each step. Right: the Bloch ball of initial states, coloured by the mean time (cyan low, amber high), white dot = ρ, magenta dot = the conjugate ρ̄, magenta axis = the Im ρ₀₁ direction');
}
function syncControls() {
  $('mIn').value = S.M; $('mOut').textContent = S.M;
  $('kIn').max = S.M - 1; $('kIn').value = S.k; $('kOut').textContent = S.k;
  $('thIn').value = S.th; $('thOut').textContent = `${S.th}°`; $('phIn').value = S.ph; $('phOut').textContent = `${S.ph}°`; $('rIn').value = S.r; $('rOut').textContent = Number(S.r).toFixed(2);
  document.querySelectorAll('#pairChips [data-pair]').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.pair === S.pair)));
  $('now').value = S.t / MODEL.TV;
}
function syncRail() {
  const M = MODEL, key = `${TRV.lang()}|${M.id}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 't = 0']];
  if (M.mean < M.TV - 0.6 && M.mean > 0.6) marks.push([M.mean / M.TV, `E = ${fr(M.mean, 2)}`]);
  marks.push([1, `t = ${M.TV}`]);
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  Object.assign(S, { pair: p.pair, seed: p.seed, M: p.M, k: p.k, th: p.th, ph: p.ph, r: p.r, t: 0, hold: 0 }); S.preset = name; markPreset(); dirty = true;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); toasted = false;
  build(); dirty = true; setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; S.t = Math.min(S.t, TV_MAX); };
document.querySelectorAll('#pairChips [data-pair]').forEach((b) => b.addEventListener('click', () => { S.pair = b.dataset.pair; custom(); }));
$('redraw').addEventListener('click', () => { if (S.pair !== 'complex' && S.pair !== 'real') S.pair = 'complex'; S.seed = (S.seed * 7 + 13) % 997 + 1; custom(); });
$('mIn').addEventListener('input', () => { S.M = parseInt($('mIn').value, 10); S.k = Math.min(S.k, S.M - 1); custom(); });
$('kIn').addEventListener('input', () => { S.k = parseInt($('kIn').value, 10); custom(); });
$('thIn').addEventListener('input', () => { S.th = parseInt($('thIn').value, 10); custom(); });
$('phIn').addEventListener('input', () => { S.ph = parseInt($('phIn').value, 10); custom(); });
$('rIn').addEventListener('input', () => { S.r = parseFloat($('rIn').value); custom(); });
const setT = (t, user) => { S.t = Math.min(MODEL.TV, Math.max(0, t)); $('now').value = S.t / MODEL.TV; glKey = ''; if (user) { S.preset = null; markPreset(); } };
$('now').addEventListener('input', () => { setT(parseFloat($('now').value) * MODEL.TV, true); S.hold = 0; });
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
const jumpTo = (t) => { S.playing = false; setPlayUI(); setT(t, true); };
document.addEventListener('keydown', (ev) => {
  if (ev.target && (ev.target.tagName === 'INPUT' && ev.target.type !== 'range')) return;
  if (drawer.isOpen()) return;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(Math.floor(S.t + 1e-9) + (ev.key === 'ArrowRight' ? 1 : -1)); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(MODEL.TV);
});

/* =====================================================================
   12. Main loop
   ===================================================================== */
let lastT = performance.now(), frameCount = 0, glKey = '';
function resize() {
  if (!glOK) return;
  const r = stage.getBoundingClientRect();
  renderer.setSize(Math.max(1, r.width), Math.max(1, r.height), false);
  camera.aspect = Math.max(0.2, r.width / Math.max(1, r.height)); camera.updateProjectionMatrix();
}
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    const run = Math.max(5, 0.35 * MODEL.TV);
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : MODEL.TV); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed * MODEL.TV / run);
      if (S.t >= MODEL.TV) S.hold = 2.4;
      if (S.t <= 0 && S.dir < 0) S.hold = 1.2;
    }
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    const gk = `${MODEL.id}|${S.t.toFixed(3)}`;
    if (glKey !== gk) { updateGL(); glKey = gk; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
const arr = (A) => Array.from(A);
window.OQ_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { pair: S.pair, seed: S.seed, M: M.M, k: M.k, L: arr(M.P.L), R: arr(M.P.R), bloch: M.bloch.slice(), rho: arr(M.rho), normErr: M.normErr,
    mean: M.mean, meanConj: M.meanConj, eOp: M.eOp, p0: M.p0, pM: M.pM, rem: M.rem, steps: M.steps, TV: M.TV, abs0: M.abs0.slice(0, M.TV + 1), absM: M.absM.slice(0, M.TV + 1),
    rows: M.rows.length, A: M.A.slice(1).map(arr), gaps: JSON.parse(JSON.stringify(M.gaps)), gapMax: M.gapMax.slice(), fits: fits(), eMin: M.eMin, eMax: M.eMax }; },
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('long'); S.playing = false; setPlayUI(); setT(MODEL.TV); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 17; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
