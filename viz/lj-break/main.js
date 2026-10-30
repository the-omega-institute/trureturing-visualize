/* LJ//BREAK · broken bonds and unstable directions in a Lennard-Jones chain
   m free particles between two fixed walls, joined by m + 1 bonds with φ(r) = r⁻¹² − 2r⁻⁶. Frozen in trureturing
   (LennardJonesChainBreakInstabilityCount.result): at an equilibrium with exactly k ≥ 1 bonds longer than the inflection point
   rᵢ = (13/7)^(1/6), the force Jacobian J has between k − 1 and k positive eigenvalues. The page solves the equilibria (every
   bond carries the same tension τ), computes the spectrum of J, and integrates the motion from each equilibrium.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Constants
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.55, 0.6, 0.68];
const RI = Math.pow(13 / 7, 1 / 6);                                         // the inflection point of φ
const phi = (r) => { const s = Math.pow(r, -6); return s * s - 2 * s; };
const dphi = (r) => 12 * (Math.pow(r, -7) - Math.pow(r, -13));            // the tension φ′(r)
const d2phi = (r) => 12 * (13 - 7 * Math.pow(r, 6)) / Math.pow(r, 14);    // the curvature c = φ″(r)
const TAU_MAX = dphi(RI);
const EPS = 1e-3, DT = 0.002, SAMPLE = 0.05, RUN = 20, STEPS = 200;
const MS = [6, 10, 14], D_MIN = 1.08, D_MAX = 1.6, POS = ['spread', 'block', 'ends'];

/* =====================================================================
   2. Equilibria and the spectrum
   ===================================================================== */
/* φ′ increases on (1, rᵢ) and decreases on (rᵢ, ∞); bisect for φ′(r) = τ on one side */
function invTension(tau, lo, hi) {
  const up = dphi(lo) < dphi(hi);
  for (let i = 0; i < 90; i++) { const mid = 0.5 * (lo + hi); if ((dphi(mid) < tau) === up) lo = mid; else hi = mid; }
  return 0.5 * (lo + hi);
}
const ru = (tau) => invTension(tau, 1, RI);
const rb = (tau) => invTension(tau, RI, Math.max(2 * RI, 2 * Math.pow(12 / tau, 1 / 7)));
/* one shared tension grid, dense near 0 (long broken bonds) and near φ′(rᵢ) (both lengths close to rᵢ) */
const GRID = (() => {
  const ts = [];
  for (let i = 0; i < 160; i++) ts.push(TAU_MAX * Math.pow(10, -11 + 9 * i / 160));
  for (let i = 0; i <= 1400; i++) ts.push(TAU_MAX * (0.01 + 0.99 * (1 - Math.cos(Math.PI * i / 1400)) / 2));
  return { ts, u: ts.map(ru), b: ts.map(rb) };
})();
/* all bonds share τ; k broken ones have length r_b(τ), the others r_u(τ); the walls fix the total length (m + 1)d */
function equilibria(m, k, d) {
  const g = (i) => k * GRID.b[i] + (m + 1 - k) * GRID.u[i] - (m + 1) * d, f = (t) => k * rb(t) + (m + 1 - k) * ru(t) - (m + 1) * d;
  const out = [];
  for (let i = 1; i < GRID.ts.length; i++) {
    const a = g(i - 1), b = g(i);
    if (a === 0) out.push(GRID.ts[i - 1]);
    else if (a * b < 0) { let lo = GRID.ts[i - 1], hi = GRID.ts[i], flo = a; for (let j = 0; j < 70; j++) { const mid = 0.5 * (lo + hi), fm = f(mid); if (flo * fm <= 0) hi = mid; else { lo = mid; flo = fm; } } out.push(0.5 * (lo + hi)); }
  }
  return out;
}
function brokenSet(m, k, pos) {
  const n = m + 1;
  if (pos === 'block') { const s = Math.floor((n - k) / 2); return Array.from({ length: k }, (_, i) => s + i); }
  if (pos === 'ends') { const out = new Set(); for (let i = 0; out.size < k; i++) { out.add(i); if (out.size < k) out.add(n - 1 - i); } return [...out].sort((a, b) => a - b); }
  return Array.from({ length: k }, (_, i) => Math.floor((i + 0.5) * n / k));
}
/* J = −Bᵀ diag(c) B: J_nn = −c_n − c_{n+1}, J_{n,n+1} = c_{n+1} (bond j joins particle j and j + 1; 0 and m + 1 are the walls) */
function jacobian(c) {
  const m = c.length - 1, J = Array.from({ length: m }, () => new Array(m).fill(0));
  for (let n = 0; n < m; n++) { J[n][n] = -c[n] - c[n + 1]; if (n + 1 < m) { J[n][n + 1] = c[n + 1]; J[n + 1][n] = c[n + 1]; } }
  return J;
}
/* cyclic Jacobi rotations; eigenvalues in decreasing order with unit eigenvectors */
function eigSym(A) {
  const n = A.length, M = A.map((r) => r.slice()), V = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => +(i === j)));
  for (let sweep = 0; sweep < 100; sweep++) {
    let off = 0, scale = 0;
    for (let p = 0; p < n; p++) { scale += M[p][p] * M[p][p]; for (let q = p + 1; q < n; q++) off += M[p][q] * M[p][q]; }
    if (off <= 1e-30 * (scale + 1e-300)) break;
    for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
      const apq = M[p][q]; if (apq === 0) continue;
      const th = (M[q][q] - M[p][p]) / (2 * apq), t = (th >= 0 ? 1 : -1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), s = t * c;
      for (let k = 0; k < n; k++) { const kp = M[k][p], kq = M[k][q]; M[k][p] = c * kp - s * kq; M[k][q] = s * kp + c * kq; }
      for (let k = 0; k < n; k++) { const pk = M[p][k], qk = M[q][k]; M[p][k] = c * pk - s * qk; M[q][k] = s * pk + c * qk; }
      for (let k = 0; k < n; k++) { const vp = V[k][p], vq = V[k][q]; V[k][p] = c * vp - s * vq; V[k][q] = s * vp + c * vq; }
    }
  }
  const idx = Array.from({ length: n }, (_, i) => i).sort((a, b) => M[b][b] - M[a][a]);
  return { vals: idx.map((i) => M[i][i]), vecs: idx.map((i) => V.map((row) => row[i])) };
}
function equilibriumAt(m, k, d, tau, broken) {
  const rB = rb(tau), rU = ru(tau), isB = new Set(broken);
  const rs = Array.from({ length: m + 1 }, (_, j) => (isB.has(j) ? rB : rU));
  const u = [0]; for (let j = 0; j < m; j++) u.push(u[j] + rs[j] - d); u.push(0);
  const c = rs.map(d2phi), J = jacobian(c), { vals, vecs } = eigSym(J);
  return { tau, rB, rU, rs, u, c, J, vals, vecs, U: vals.filter((x) => x > 0).length, dLdt: c.reduce((a, x) => a + 1 / x, 0) };
}

/* =====================================================================
   3. The motion from an equilibrium (velocity Verlet)
   ===================================================================== */
function simulate(M) {
  const m = M.m, d = M.d, n = m + 2, eq = M.eq;
  const T1 = eq.vals[0] > 0 ? Math.min(120, Math.max(30, Math.log(400) / Math.sqrt(eq.vals[0]) + 25)) : 30;
  const NF = Math.round(T1 / SAMPLE) + 1, per = Math.round(SAMPLE / DT);
  const x = new Float64Array(n), v = new Float64Array(n), F = new Float64Array(n), x0 = new Float64Array(n);
  const vec = eq.vecs[0], big = vec.reduce((a, b) => (Math.abs(b) > Math.abs(a) ? b : a), 0), dir = vec.map((q) => q / big);
  for (let i = 0; i < n; i++) x0[i] = x[i] = i * d + eq.u[i];
  for (let i = 1; i <= m; i++) x[i] += EPS * dir[i - 1];
  const force = () => { for (let i = 1; i <= m; i++) F[i] = dphi(x[i + 1] - x[i]) - dphi(x[i] - x[i - 1]); };
  const energy = () => { let e = 0; for (let i = 1; i <= m; i++) e += 0.5 * v[i] * v[i]; for (let j = 0; j <= m; j++) e += phi(x[j + 1] - x[j]); return e; };
  const frames = new Float64Array(NF * n), nBroken = new Int16Array(NF), dev = new Float64Array(NF);
  const E0 = energy(); let drift = 0;
  force();
  for (let f = 0; f < NF; f++) {
    if (f) for (let s = 0; s < per; s++) {
      for (let i = 1; i <= m; i++) { v[i] += 0.5 * DT * F[i]; x[i] += DT * v[i]; }
      force();
      for (let i = 1; i <= m; i++) v[i] += 0.5 * DT * F[i];
    }
    frames.set(x, f * n);
    let nb = 0, dv = 0; for (let j = 0; j <= m; j++) if (x[j + 1] - x[j] > RI) nb++;
    for (let i = 1; i <= m; i++) dv = Math.max(dv, Math.abs(x[i] - x0[i]));
    nBroken[f] = nb; dev[f] = dv; drift = Math.max(drift, Math.abs(energy() - E0));
  }
  let fGrow = -1, fChange = -1;
  for (let f = 0; f < NF; f++) { if (fGrow < 0 && dev[f] >= 0.1) fGrow = f; if (fChange < 0 && nBroken[f] !== M.k) fChange = f; }
  return { T: (NF - 1) * SAMPLE, NF, n, frames, nBroken, dev, dir, E0, drift, fGrow, fChange };
}

/* =====================================================================
   4. State and presets
   ===================================================================== */
const S = { m: 10, k: 1, d: 1.3, pos: 'spread', branch: 0, nowFrac: 0, playing: true, dir: 1, speed: 1, hold: 0, preset: 'one' };
const PRESETS = {
  one: { m: 10, k: 1, d: 1.3, pos: 'spread', branch: 0, frac: 0, play: true,
    zh: 'm = 10 个粒子、11 根键，平均间距 d = 1.3。只有一根键被拉断：它长约 4.3，其余 10 根都在拐点以内。定理给出 0 ≤ U ≤ 1，页面算出 U = 0：J 的特征值全为负，平衡是稳定的，扰动只引起微小振动。',
    en: 'm = 10 particles and 11 bonds at mean spacing d = 1.3. Only one bond is broken: it is about 4.3 long and the other 10 stay inside the inflection point. The theorem gives 0 ≤ U ≤ 1; the page computes U = 0: every eigenvalue of J is negative, the equilibrium is stable, and a perturbation only causes tiny vibrations.' },
  two: { m: 10, k: 2, d: 1.3, pos: 'spread', branch: 0, frac: 0, play: true,
    zh: '两根断键分走多出来的长度。定理给出 1 ≤ U ≤ 2，页面算出 U = 1：恰有一个正特征值，但它很小（≈ 0.011），所以扰动长得很慢；到 t ≈ 70 一根断键愈合，只剩一根断键。',
    en: 'Two broken bonds share the extra length. The theorem gives 1 ≤ U ≤ 2; the page computes U = 1: exactly one positive eigenvalue, but a small one (≈ 0.011), so the perturbation grows slowly; by t ≈ 70 one break has healed and a single broken bond is left.' },
  five: { m: 10, k: 5, d: 1.3, pos: 'spread', branch: 0, frac: 0, play: true,
    zh: '五根断键均匀分布。定理给出 4 ≤ U ≤ 5，页面算出 U = 4：四对不稳定特征值，扰动沿最不稳定方向按 e^(√μ₁ t) 增长；之后断键数在 2 到 8 之间起伏，有的键愈合，有的键新断。',
    en: 'Five broken bonds, spread out. The theorem gives 4 ≤ U ≤ 5; the page computes U = 4: four unstable pairs. The perturbation grows like e^(√μ₁ t) along the most unstable direction; afterwards the number of broken bonds fluctuates between 2 and 8 as some bonds heal and others break.' },
  all: { m: 10, k: 11, d: 1.3, pos: 'spread', branch: 0, frac: 0, play: true,
    zh: '把每一根键都拉过拐点：k = m + 1 = 11。此时所有 cⱼ 都是负数，J = −Bᵀ diag(c) B 是正定的，U = m = 10 = k − 1，下端点。均匀拉伸的链最不稳定：t ≈ 1 时扰动就长到 0.1，随后断键数在 2 到 11 之间剧烈起伏。',
    en: 'Every bond is stretched past the inflection point: k = m + 1 = 11. Then every cⱼ is negative, J = −Bᵀ diag(c) B is positive definite, and U = m = 10 = k − 1, the lower end. The uniformly stretched chain is the least stable: the perturbation reaches 0.1 by t ≈ 1, and the number of broken bonds then swings between 2 and 11.' },
  high: { m: 10, k: 3, d: 1.104, pos: 'spread', branch: 1, frac: 0, play: true,
    zh: 'd = 1.104 略小于 rᵢ ≈ 1.1087。三根断键时有两支平衡，这里是张力较高的那一支（τ ≈ 2.68，接近 φ′(rᵢ) ≈ 2.69）：断键长约 1.120，只比 rᵢ 长一点。定理给出 2 ≤ U ≤ 3，页面算出 U = 3 = k，上端点也会出现。',
    en: 'd = 1.104 is slightly below rᵢ ≈ 1.1087. With three breaks there are two branches of equilibria; this is the higher-tension one (τ ≈ 2.68, close to φ′(rᵢ) ≈ 2.69), where the broken bonds, about 1.120 long, are only a little longer than rᵢ. The theorem gives 2 ≤ U ≤ 3; the page computes U = 3 = k, so the upper end occurs too.' },
  twin: { m: 10, k: 3, d: 1.104, pos: 'spread', branch: 0, frac: 0, play: true,
    zh: '同一个 d = 1.104、同样三根断键的另一支平衡：张力 τ ≈ 1.45，断键长约 1.311。右下图里琥珀虚线 y = d 与当前 k 的曲线相交两次：下降段（青）上 U = k − 1 = 2，上升段（品红）上 U = k = 3。用“平衡支”按钮切换。',
    en: 'The other equilibrium at the same d = 1.104 with the same three breaks: tension τ ≈ 1.45 and broken bonds about 1.311 long. In the lower right chart the amber dashed line y = d meets the curve of the current k twice: U = k − 1 = 2 on the decreasing part (cyan) and U = k = 3 on the increasing part (magenta). Switch with the branch buttons.' }
};

/* =====================================================================
   5. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
function build() {
  const m = MS.includes(S.m) ? S.m : 10, k = Math.max(1, Math.min(S.k, m + 1)), d = Math.min(D_MAX, Math.max(D_MIN, S.d));
  S.m = m; S.k = k; S.d = d;
  const taus = equilibria(m, k, d), broken = brokenSet(m, k, S.pos);
  const M = { id: ++modelId, m, k, d, pos: S.pos, broken, taus, none: taus.length === 0 };
  M.branches = taus.map((t) => equilibriumAt(m, k, d, t, broken));
  M.branch = Math.min(S.branch, Math.max(0, taus.length - 1));
  if (!M.none) { M.eq = M.branches[M.branch]; M.sim = simulate(M); }
  /* L(τ)/(m + 1) for every k′ on the shared grid, for the right chart */
  M.family = [];
  for (let kk = 1; kk <= m + 1; kk++) M.family.push(GRID.ts.map((_, i) => (kk * GRID.b[i] + (m + 1 - kk) * GRID.u[i]) / (m + 1)));
  MODEL = M;
}
function progress() {
  const M = MODEL; if (M.none) return { t: 0, f: 0 };
  const f = Math.min(M.sim.NF - 1, Math.round(S.nowFrac * (M.sim.NF - 1)));
  return { f, t: f * SAMPLE };
}
const posAt = (M, f, i) => M.sim.frames[f * M.sim.n + i];

/* =====================================================================
   6. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const fr = (x, d = 4) => (isFinite(x) ? x.toFixed(d) : '—');
const fx = (x, d = 4) => (isFinite(x) ? (x < 0 ? '−' : '') + Math.abs(x).toFixed(d) : '—');

/* =====================================================================
   7. 3D scene
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 40000, PTS_MAX = 400;
const CAMS = { iso: [0.62, 1.08, 17], front: [0.0001, 1.5707, 16], top: [0.0001, 0.0601, 18] };
const cam = { theta: 0.62, phi: 1.08, r: 17, tTheta: 0.62, tPhi: 1.08, tR: 17 };
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
/* chain position X ∈ [0, (m + 1)d] across, the eigenvector up, time t ∈ [0, T] from the back (t = 0) to the front (t = T) */
const WIDTH = 12, DEPTH = 8, BAR = 1.8;
const toScene = (M, X, y, t) => [(X / ((M.m + 1) * M.d) - 0.5) * WIDTH, y, M.none ? 0 : (t / M.sim.T - 0.5) * DEPTH];
function updateGL() {
  const M = MODEL, pr = progress();
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (a, b, col, k) => { if (v + 2 > LINES_MAX) return; for (const p of [a, b]) { Pp[3 * v] = p[0]; Pp[3 * v + 1] = p[1]; Pp[3 * v + 2] = p[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, a, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = a; PT.aSize.array[np] = size; np++; };
  const W = (M.m + 1) * M.d, t = pr.t;
  for (const X of [0, W]) {
    seg(toScene(M, X, -0.5, t), toScene(M, X, 0.5, t), GREY, 0.8);
    if (!M.none) seg(toScene(M, X, 0, 0), toScene(M, X, 0, t), GREY, 0.3);
  }
  if (!M.none) {
    const sim = M.sim, m = M.m, f = pr.f;
    /* the space-time sheet: rungs between neighbouring world-lines, magenta where the bond is broken */
    const step = Math.max(1, Math.round(sim.NF / 90));
    for (let g = 0; g <= f; g += step) for (let j = 0; j <= m; j++) {
      const a = posAt(M, g, j), b = posAt(M, g, j + 1), br = b - a > RI;
      seg(toScene(M, a, 0, g * SAMPLE), toScene(M, b, 0, g * SAMPLE), br ? COL.magenta : COL.cyan, br ? 0.5 : 0.1);
    }
    /* world-lines */
    const ws = Math.max(1, Math.ceil(f / 400));
    for (let i = 1; i <= m; i++) {
      let prev = toScene(M, posAt(M, 0, i), 0, 0);
      for (let g = ws; g <= f + ws - 1; g += ws) { const gg = Math.min(g, f), p = toScene(M, posAt(M, gg, i), 0, gg * SAMPLE); seg(prev, p, COL.cyan, 0.42); prev = p; }
    }
    /* the chain now (two offset copies for weight) */
    for (const dy of [-0.025, 0.025]) for (let j = 0; j <= m; j++) {
      const a = posAt(M, f, j), b = posAt(M, f, j + 1), br = b - a > RI;
      seg(toScene(M, a, dy, t), toScene(M, b, dy, t), br ? COL.magenta : COL.cyan, br ? 1 : 0.75);
    }
    /* the most unstable direction (largest eigenvalue of J), drawn on the equilibrium positions */
    for (let i = 1; i <= m; i++) {
      const X = i * M.d + M.eq.u[i], h = BAR * sim.dir[i - 1];
      seg(toScene(M, X, 0, t), toScene(M, X, h, t), COL.amber, 0.85);
      dot(toScene(M, X, h, t), COL.amber, 0.9, 1.1);
      dot(toScene(M, X, 0, t), GREY, 0.35, 1.2);
    }
    for (let i = 1; i <= m; i++) dot(toScene(M, posAt(M, f, i), 0, t), [0.85, 0.97, 1], 1, 2.4);
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
  const W = (M.m + 1) * M.d;
  put(T('墙', 'wall'), toScene(M, 0, 0.8, pr.t), 'cy'); put(T('墙', 'wall'), toScene(M, W, 0.8, pr.t), 'cy');
  if (M.none) put(T(`d = ${M.d.toFixed(3)} 时没有 k = ${M.k} 的平衡`, `no equilibrium with k = ${M.k} at d = ${M.d.toFixed(3)}`), toScene(M, W / 2, 0.6, 0), 'hot');
  else {
    put(`t = ${pr.t.toFixed(1)}`, toScene(M, W, -0.7, pr.t), 'hot');
    if (pr.f > M.sim.NF * 0.12) put('t = 0', toScene(M, W, -0.5, 0), 'cy');
    const dir = M.sim.dir, iMax = dir.reduce((a, q, i) => (q > dir[a] ? i : a), 0);
    put(`μ₁ = ${fx(M.eq.vals[0], 3)}`, toScene(M, (iMax + 1) * M.d + M.eq.u[iMax + 1], BAR + 0.35, pr.t), 'hot');
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
const SUP = (n) => String(n).replace('-', '⁻').split('').map((c) => ('0123456789'.includes(c) ? '⁰¹²³⁴⁵⁶⁷⁸⁹'[+c] : c)).join('');
/* left: the spectrum of J (asinh scale); right: the largest displacement from equilibrium (log scale) against the linear prediction */
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 34); if (F.iw < 80 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F;
  if (M.none) { lab(ctx, T('没有平衡，故没有谱', 'No equilibrium, so no spectrum'), pl + iw / 2, pt + ih / 2, 'center', 'middle'); $('c1Meta').textContent = ''; return; }
  const pr = progress(), eq = M.eq, sim = M.sim, w1 = iw * 0.38, gap = 34 * dpr, x2 = pl + w1 + gap, w2 = iw - w1 - gap;
  const amax = Math.max(...eq.vals.map(Math.abs)), A = (q) => Math.asinh(q / 0.05) / Math.asinh(amax / 0.05), y0 = pt + ih / 2;
  ctx.strokeStyle = FAINT; ctx.beginPath(); ctx.moveTo(pl, y0); ctx.lineTo(pl + w1, y0); ctx.stroke();
  const bw = w1 / eq.vals.length;
  eq.vals.forEach((q, i) => { ctx.fillStyle = q > 0 ? MG : CY; const h = (ih / 2 - 2 * dpr) * A(q); ctx.fillRect(pl + i * bw + bw * 0.15, Math.min(y0, y0 - h), bw * 0.7, Math.max(1, Math.abs(h))); });
  lab(ctx, '+', pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, '0', pl - 4 * dpr, y0, 'right', 'middle'); lab(ctx, '−', pl - 4 * dpr, pt + ih, 'right', 'bottom');
  lab(ctx, `U = ${eq.U}`, pl + 2 * dpr, pt + ih + 4 * dpr, 'left', 'top', MG); lab(ctx, `k = ${M.k}`, pl + w1, pt + ih + 4 * dpr, 'right', 'top', AM);
  const lo = -3.3, hi = 1, X = (t) => x2 + w2 * t / sim.T, Y = (dv) => pt + ih - ih * (Math.max(lo, Math.min(hi, Math.log10(Math.max(1e-12, dv)))) - lo) / (hi - lo);
  for (const e of [-3, -2, -1, 0, 1]) { ctx.strokeStyle = FAINT; ctx.beginPath(); ctx.moveTo(x2, Y(Math.pow(10, e))); ctx.lineTo(x2 + w2, Y(Math.pow(10, e))); ctx.stroke(); lab(ctx, `10${SUP(e)}`, x2 - 4 * dpr, Y(Math.pow(10, e)), 'right', 'middle'); }
  const mu = eq.vals[0];
  ctx.strokeStyle = mu > 0 ? MG : CY; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.lineWidth = 1.2 * dpr; ctx.beginPath();
  for (let j = 0; j <= 200; j++) { const t = sim.T * j / 200, p = mu > 0 ? EPS * Math.cosh(Math.sqrt(mu) * t) : EPS; if (j) ctx.lineTo(X(t), Y(p)); else ctx.moveTo(X(t), Y(p)); }
  ctx.stroke(); ctx.setLineDash([]);
  for (const [upto, col, wdt] of [[sim.NF - 1, FAINT, 1], [pr.f, INK, 1.5]]) {
    ctx.strokeStyle = col; ctx.lineWidth = wdt * dpr; ctx.beginPath();
    for (let g = 0; g <= upto; g++) { const x = X(g * SAMPLE), y = Y(sim.dev[g]); if (g) ctx.lineTo(x, y); else ctx.moveTo(x, y); }
    ctx.stroke();
  }
  ctx.lineWidth = 1; ctx.strokeStyle = AM; ctx.beginPath(); ctx.moveTo(X(pr.t), pt); ctx.lineTo(X(pr.t), pt + ih); ctx.stroke();
  lab(ctx, 't = 0', x2, pt + ih + 4 * dpr, 'left', 'top'); lab(ctx, `t = ${sim.T.toFixed(0)}`, x2 + w2, pt + ih + 4 * dpr, 'right', 'top');
  $('c1Meta').textContent = T(`左：J 的 ${M.m} 个特征值（从大到小，asinh 纵轴），品红 = 正，青 = 负。右：离平衡的最大位移（对数纵轴），白 = 模拟，虚线 = 线性预言 ${mu > 0 ? '10⁻³ cosh(√μ₁ t)' : '10⁻³'}`,
    `Left: the ${M.m} eigenvalues of J (largest first, asinh scale), magenta = positive, cyan = negative. Right: the largest displacement from equilibrium (log scale), white = simulation, dashes = the linear prediction ${mu > 0 ? '10⁻³ cosh(√μ₁ t)' : '10⁻³'}`);
}
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 34); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F;
  const ytop = Math.max(1.65, M.d + 0.12), ybot = 1.0, X = (t) => pl + iw * t / TAU_MAX, Y = (y) => pt + ih - ih * (Math.min(ytop, y) - ybot) / (ytop - ybot);
  ctx.strokeStyle = FAINT; ctx.beginPath(); ctx.moveTo(pl, Y(RI)); ctx.lineTo(pl + iw, Y(RI)); ctx.stroke();
  M.family.forEach((L, idx) => {
    const kk = idx + 1; if (kk === M.k) return;
    ctx.strokeStyle = 'rgba(140,160,180,0.22)'; ctx.lineWidth = 1; ctx.beginPath(); let started = false;
    GRID.ts.forEach((t, i) => { if (L[i] > ytop + 0.3) { started = false; return; } if (started) ctx.lineTo(X(t), Y(L[i])); else { ctx.moveTo(X(t), Y(L[i])); started = true; } });
    ctx.stroke();
  });
  const L = M.family[M.k - 1];
  ctx.lineWidth = 2 * dpr;
  for (let i = 1; i < GRID.ts.length; i++) {
    if (L[i - 1] > ytop + 0.3 && L[i] > ytop + 0.3) continue;
    ctx.strokeStyle = L[i] > L[i - 1] ? MG : CY; ctx.beginPath(); ctx.moveTo(X(GRID.ts[i - 1]), Y(L[i - 1])); ctx.lineTo(X(GRID.ts[i]), Y(L[i])); ctx.stroke();
  }
  ctx.lineWidth = 1;
  ctx.strokeStyle = AM; ctx.setLineDash([5 * dpr, 4 * dpr]); ctx.beginPath(); ctx.moveTo(pl, Y(M.d)); ctx.lineTo(pl + iw, Y(M.d)); ctx.stroke(); ctx.setLineDash([]);
  M.branches.forEach((e, i) => {
    ctx.fillStyle = e.U === M.k ? MG : CY; ctx.beginPath(); ctx.arc(X(e.tau), Y(M.d), 3.6 * dpr, 0, 2 * Math.PI); ctx.fill();
    if (i === M.branch) { ctx.strokeStyle = AM; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); ctx.arc(X(e.tau), Y(M.d), 6.5 * dpr, 0, 2 * Math.PI); ctx.stroke(); ctx.lineWidth = 1; }
    const right = e.tau > TAU_MAX * 0.8; lab(ctx, `U = ${e.U}`, X(e.tau) + (right ? -8 : 8) * dpr, Y(M.d) + (right ? 6 : -6) * dpr, right ? 'right' : 'left', right ? 'top' : 'bottom', e.U === M.k ? MG : CY);
  });
  lab(ctx, ytop.toFixed(2), pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, 'rᵢ', pl - 4 * dpr, Y(RI), 'right', 'middle'); lab(ctx, '1.00', pl - 4 * dpr, pt + ih, 'right', 'bottom');
  lab(ctx, 'd', pl + iw, Y(M.d) - 3 * dpr, 'right', 'bottom', AM);
  lab(ctx, 'τ = 0', pl, pt + ih + 4 * dpr, 'left', 'top'); lab(ctx, `φ′(rᵢ) = ${TAU_MAX.toFixed(2)}`, pl + iw, pt + ih + 4 * dpr, 'right', 'top');
  $('c2Meta').textContent = T(`平均键长 L/(m + 1) 对张力 τ：灰 = 其他 k；当前 k = ${M.k}：青 = 下降段，品红 = 上升段；琥珀虚线 = d，交点 = 平衡（点色 = 页面算出的 U 是 k − 1 还是 k）`,
    `Mean bond length L/(m + 1) against tension τ: grey = other k; the current k = ${M.k}: cyan = decreasing, magenta = increasing; amber dashes = d, crossings = equilibria (dot colour = whether the computed U is k − 1 or k)`);
}

/* =====================================================================
   11. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const branchName = (M, i) => (M.taus.length < 2 ? T('唯一的一支', 'the only branch') : i === 0 ? T('低张力支', 'low tension') : T('高张力支', 'high tension'));
function readouts() {
  const M = MODEL, pr = progress();
  pill('pillA', 'm', String(M.m)); pill('pillB', 'k', String(M.k)); pill('pillD', 'd', M.d.toFixed(3));
  if (M.none) {
    pill('pillC', 'U', '—');
    setRo([[T('张力 τ · 平衡支', 'Tension τ · branch'), T('无平衡', 'no equilibrium')], [T('断键 k · 断键长 r_b · 其余键长 r_u', 'Breaks k · broken length r_b · other length r_u'), `k = ${M.k} · — · —`],
      [T('正特征值个数 U · 定理区间 [k − 1, k]', 'Positive eigenvalues U · the theorem’s range [k − 1, k]'), `— · [${M.k - 1}, ${M.k}]`], [T('最大特征值 μ₁ · 增长率 √μ₁', 'Largest eigenvalue μ₁ · growth rate √μ₁'), '—'],
      [T('dL/dτ = Σ 1/cⱼ', 'dL/dτ = Σ 1/cⱼ'), '—']]);
    $('roNote').innerHTML = T(`在 d = ${M.d.toFixed(3)} 时，${M.k} 根断键的平均键长 L(τ)/(m + 1) 永远大于 d（右下图里当前曲线整条在琥珀虚线上方），所以不存在恰有 ${M.k} 根断键的平衡。定理只谈存在的平衡；何时存在不在定理之内（OPEN）。`,
      `At d = ${M.d.toFixed(3)} the mean bond length L(τ)/(m + 1) with ${M.k} breaks always exceeds d (in the lower right chart the current curve lies entirely above the amber dashes), so there is no equilibrium with exactly ${M.k} broken bonds. The theorem is about equilibria that exist; when they exist is outside it (OPEN).`);
    return;
  }
  const eq = M.eq, ok = eq.U >= M.k - 1 && eq.U <= M.k, mu = eq.vals[0];
  pill('pillC', 'U', String(eq.U));
  setRo([[T('张力 τ · 平衡支', 'Tension τ · branch'), `${fr(eq.tau, 5)} · ${branchName(M, M.branch)}`],
    [T('断键 k · 断键长 r_b · 其余键长 r_u', 'Breaks k · broken length r_b · other length r_u'), `k = ${M.k} · ${fr(eq.rB)} · ${fr(eq.rU)}`],
    [T('正特征值个数 U · 定理区间 [k − 1, k]', 'Positive eigenvalues U · the theorem’s range [k − 1, k]'), `U = ${eq.U} · [${M.k - 1}, ${M.k}] ${ok ? '✓' : '✗'}`],
    [T('最大特征值 μ₁ · 增长率 √μ₁', 'Largest eigenvalue μ₁ · growth rate √μ₁'), mu > 0 ? `${fx(mu)} · ${fr(Math.sqrt(mu))}` : `${fx(mu)} · ${T('无（振动）', 'none (vibration)')}`],
    [T('dL/dτ = Σ 1/cⱼ · 页面观察到的对应', 'dL/dτ = Σ 1/cⱼ · the correspondence the page observes'), `${fx(eq.dLdt, 3)} ${eq.dLdt < 0 ? T('< 0 ↔ U = k − 1', '< 0 ↔ U = k − 1') : T('> 0 ↔ U = k', '> 0 ↔ U = k')}`]]);
  const sim = M.sim, nb = sim.nBroken[pr.f];
  $('roNote').innerHTML = T(`t = ${pr.t.toFixed(2)} 时有 ${nb} 根键长于 rᵢ（平衡时 ${M.k} 根）。初始扰动 10⁻³ 沿最不稳定的特征向量；能量漂移 ${sim.drift.toExponential(1)}（能量 ${fx(sim.E0, 4)}）。${M.taus.length > 1 ? `这个 d 有 ${M.taus.length} 支平衡。` : ''}`,
    `At t = ${pr.t.toFixed(2)}, ${nb} bonds are longer than rᵢ (${M.k} at equilibrium). The initial perturbation is 10⁻³ along the most unstable eigenvector; energy drift ${sim.drift.toExponential(1)} (energy ${fx(sim.E0, 4)}).${M.taus.length > 1 ? ` This d has ${M.taus.length} branches of equilibria.` : ''}`);
}
function syncControls() {
  const M = MODEL;
  $('kk').max = String(M.m + 1); $('kk').value = String(M.k); $('oK').textContent = String(M.k);
  $('dd').value = String(M.d); $('oD').textContent = M.d.toFixed(3);
  document.querySelectorAll('#mChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.m === M.m)));
  document.querySelectorAll('#posChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.pos === M.pos)));
  document.querySelectorAll('#branchChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.branch === M.branch)));
  $('branchChips').hidden = M.taus.length < 2;
}
const stateKey = () => `${S.m}|${S.k}|${S.d}|${S.pos}|${S.branch}|${S.nowFrac}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; toasted = false; syncControls(); $('marks').dataset.key = ''; }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  const M = MODEL, pr = progress();
  readouts();
  $('formula').innerHTML = 'J = −B<sup>T</sup> diag(c) B, &nbsp; c<sub>j</sub> = φ″(r<sub>j</sub>), &nbsp; k − 1 ≤ #{μ &gt; 0} ≤ k';
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('modeNote').innerHTML = M.none ? T('没有平衡，故没有运动可以模拟。', 'No equilibrium, so there is no motion to simulate.')
    : T(`时间轴 = 时间 t，从 0 到 ${M.sim.T.toFixed(0)}；运动方程 ü = F(u)，质量为 1，速度 Verlet 步长 ${DT}。${M.k === M.m + 1 ? '全部断开时断键位置无从选择。' : '断键位置只改变谱的数值，不改变键长。'}`,
      `The time axis is t, from 0 to ${M.sim.T.toFixed(0)}; the equation of motion is ü = F(u) with unit masses, integrated by velocity Verlet with step ${DT}. ${M.k === M.m + 1 ? 'With every bond broken there is no choice of positions.' : 'The positions of the breaks change the values of the spectrum, not the bond lengths.'}`);
  $('litNote').innerHTML = T('平衡、谱与运动都由页面按定义算出；冻结的是计数不等式 k − 1 ≤ U ≤ k。', 'The equilibria, the spectrum and the motion are computed on the page from the definitions; what is frozen is the counting inequality k − 1 ≤ U ≤ k.');
  $('c1Title').textContent = T('J 的谱与扰动的增长', 'The spectrum of J and the growth of the perturbation');
  $('c2Title').textContent = T('平均键长对张力', 'Mean bond length against tension');
  $('clock').innerHTML = M.none ? 't —' : `t ${pr.t.toFixed(1)}`;
  $('hudBig').textContent = M.none ? T(`k = ${M.k} · 无平衡`, `k = ${M.k} · no equilibrium`) : `U = ${M.eq.U} · k = ${M.k} · ${M.k - 1} ≤ U ≤ ${M.k}`;
  $('hudSub').textContent = T('青 = 未断的键，品红 = 断键（r > rᵢ），白点 = 粒子，灰点 = 平衡位置，琥珀 = 最不稳定方向的特征向量；向后延伸的线 = 粒子的世界线（t = 0 在最后面），俯视即时空图',
    'cyan = unbroken bonds, magenta = broken bonds (r > rᵢ), white dots = particles, grey dots = equilibrium positions, amber = the eigenvector of the most unstable direction; the lines running back are the world-lines of the particles (t = 0 at the back); seen from the top they form the space-time diagram');
  if (!toasted && S.playing && S.nowFrac >= 1 && !M.none) {
    toasted = true;
    const sim = M.sim, mu = M.eq.vals[0], tg = sim.fGrow >= 0 ? sim.fGrow * SAMPLE : NaN, tp = mu > 0 ? Math.acosh(100) / Math.sqrt(mu) : NaN, nb = sim.nBroken[sim.NF - 1];
    toast(mu > 0 ? T(`<b>t = ${sim.T.toFixed(0)}</b>：位移在 t = ${fr(tg, 2)} 达到 0.1（线性预言 ${fr(tp, 2)}）；断键数从 ${M.k} 变成 ${nb}。`, `<b>t = ${sim.T.toFixed(0)}</b>: the displacement reached 0.1 at t = ${fr(tg, 2)} (linear prediction ${fr(tp, 2)}); the number of broken bonds went from ${M.k} to ${nb}.`)
      : T(`<b>t = ${sim.T.toFixed(0)}</b>：最大位移始终 ≤ ${Math.max(...sim.dev).toExponential(1)}，断键数保持 ${nb}——稳定。`, `<b>t = ${sim.T.toFixed(0)}</b>: the largest displacement stayed ≤ ${Math.max(...sim.dev).toExponential(1)} and the number of broken bonds stayed ${nb} — stable.`));
  }
}
function syncRail() {
  const M = MODEL, key = `${M.id}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  if (M.none) { $('marks').innerHTML = ''; return; }
  const marks = [[0, 't = 0']];
  if (M.sim.fGrow > 0 && M.sim.fGrow < M.sim.NF * 0.85) marks.push([M.sim.fGrow / (M.sim.NF - 1), T('位移 0.1', 'displacement 0.1')]);
  marks.push([1, `t = ${M.sim.T.toFixed(0)}`]);
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
function custom() { S.preset = null; markPreset(); dirty = true; S.nowFrac = 0; $('now').value = 0; }
document.querySelectorAll('#mChips .chip').forEach((b) => b.addEventListener('click', () => { const m = +b.dataset.m; if (!MS.includes(m) || m === S.m) return; S.m = m; S.k = Math.min(S.k, m + 1); custom(); }));
document.querySelectorAll('#posChips .chip').forEach((b) => b.addEventListener('click', () => { S.pos = POS.includes(b.dataset.pos) ? b.dataset.pos : 'spread'; custom(); }));
document.querySelectorAll('#branchChips .chip').forEach((b) => b.addEventListener('click', () => { S.branch = +b.dataset.branch === 1 ? 1 : 0; custom(); }));
$('kk').addEventListener('input', () => { S.k = parseInt($('kk').value, 10); $('oK').textContent = String(S.k); custom(); });
$('dd').addEventListener('input', () => { S.d = parseFloat($('dd').value); $('oD').textContent = S.d.toFixed(3); custom(); });
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.m = p.m; S.k = p.k; S.d = p.d; S.pos = p.pos; S.branch = p.branch;
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
document.addEventListener('keydown', (ev) => {
  if (ev.target && (ev.target.tagName === 'INPUT' && ev.target.type !== 'range')) return;
  if (drawer.isOpen()) return;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(S.nowFrac + (ev.key === 'ArrowRight' ? 1 : -1) / STEPS); }
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
  if (S.playing && !scrubbing && !MODEL.none) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { S.nowFrac = S.dir > 0 ? 0 : 1; toasted = false; } }
    else {
      S.nowFrac += S.dir * dtSec * S.speed / RUN;
      if (S.nowFrac >= 1) { S.nowFrac = 1; S.hold = 2.4; }
      if (S.nowFrac <= 0) { S.nowFrac = 0; S.hold = 1.2; }
    }
    $('now').value = S.nowFrac;
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    const k = `${MODEL.id}|${progress().f}`;
    if (k !== glKey) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.LJ_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => {
    const M = MODEL, pr = progress();
    const base = { m: M.m, k: M.k, d: M.d, pos: M.pos, broken: M.broken, taus: M.taus, none: M.none, branch: M.branch, ri: RI, tauMax: TAU_MAX,
      branches: M.branches.map((e) => ({ tau: e.tau, rB: e.rB, rU: e.rU, U: e.U, dLdt: e.dLdt, vals: e.vals })) };
    if (M.none) return base;
    const eq = M.eq, sim = M.sim;
    return { ...base, tau: eq.tau, rs: eq.rs, u: eq.u, c: eq.c, J: eq.J, vals: eq.vals, vec: eq.vecs[0], U: eq.U, dLdt: eq.dLdt,
      T: sim.T, NF: sim.NF, dt: DT, sample: SAMPLE, eps: EPS, dir: sim.dir, E0: sim.E0, drift: sim.drift, fGrow: sim.fGrow, fChange: sim.fChange,
      f: pr.f, t: pr.t, nBroken: Array.from(sim.nBroken), dev: Array.from(sim.dev) };
  },
  frameAt: (g) => { const M = MODEL; return M.none ? null : Array.from(M.sim.frames.subarray(g * M.sim.n, (g + 1) * M.sim.n)); },
  setFrac: (f) => { S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; }
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('five'); S.playing = false; setPlayUI(); S.nowFrac = 0.62; $('now').value = S.nowFrac; setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 15; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
applyPreset('one');
setPlayUI();
requestAnimationFrame(frame);
})();
