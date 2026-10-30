/* QAOA//SUPPORT · the support of the level-one QAOA state on three qubits
   ψ = e^(−iβB) e^(−iγC)|+⟩⊗³ with B = Σ Xⱼ and C = diag(e). Frozen in trureturing (LevelOneQAOAGenuineSuperposition.result):
   the unrestricted claim of Streif and Leib that no support size strictly between 2 and 2ⁿ occurs is false, because for the
   energy π/2 on x₀ ≠ x₁ and 2π otherwise, β = π/8 and γ = 1, exactly the 4 states with x₀ ≠ x₁ survive. The page draws the
   smallest amplitude over the (β, γ) plane, locates the zeros of every amplitude by Newton's method, and compares energies.
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
const GREY = [0.55, 0.6, 0.68], VIOLET = [0.62, 0.55, 1];
const VI = '#9d8cff';
const NQ = 3, NS = 8, RUN = 20, STEPS = 400, TOL = 1e-9;
const NB = 160, NG = 320, G_MAX = 2 * Math.PI;           // the (β, γ) grid: β ∈ [0, π), γ ∈ [0, 2π]
const bit = (x, j) => (x >> j) & 1;
const label = (x) => `${bit(x, 0)}${bit(x, 1)}${bit(x, 2)}`;
const popcount = (x) => { let c = 0; while (x) { c += x & 1; x >>= 1; } return c; };
const ENERGIES = {
  lean: { zh: 'Lean 的能量', en: 'Lean’s energy', e: Array.from({ length: NS }, (_, x) => (bit(x, 0) !== bit(x, 1) ? Math.PI / 2 : 2 * Math.PI)) },
  tri: { zh: '三角形 MaxCut', en: 'Triangle MaxCut', e: Array.from({ length: NS }, (_, x) => (bit(x, 0) ^ bit(x, 1)) + (bit(x, 1) ^ bit(x, 2)) + (bit(x, 0) ^ bit(x, 2))) },
  asym: { zh: '无对称', en: 'No symmetry', e: [0, 1, 3, 2, 5, 7, 4, 6].map((v) => 0.37 * v) }
};

/* =====================================================================
   2. Amplitudes and their zeros
   ===================================================================== */
/* ψ(x) = 2^(−3/2) Σ_y cos^(3−d) β (−i sin β)^d e^(−iγ e(y)), d = the number of bits where x and y differ */
const IPOW = [[1, 0], [0, -1], [-1, 0], [0, 1]];          // (−i)^d
function amplitude(e, x, beta, gamma) {
  const c = Math.cos(beta), s = Math.sin(beta); let re = 0, im = 0;
  for (let y = 0; y < NS; y++) {
    const d = popcount(x ^ y), m = Math.pow(c, NQ - d) * Math.pow(s, d), p = IPOW[d & 3], ar = m * p[0], ai = m * p[1];
    const th = -gamma * e[y], er = Math.cos(th), ei = Math.sin(th);
    re += ar * er - ai * ei; im += ar * ei + ai * er;
  }
  return [re / Math.sqrt(8), im / Math.sqrt(8)];
}
const amplitudes = (e, beta, gamma) => Array.from({ length: NS }, (_, x) => amplitude(e, x, beta, gamma));
/* Newton's method on the complex amplitude as a map (β, γ) ↦ (Re, Im), with a forward-difference Jacobian */
function newtonZero(e, x, b, g) {
  for (let it = 0; it < 60; it++) {
    const f = amplitude(e, x, b, g); if (Math.hypot(f[0], f[1]) < 1e-15) break;
    const h = 1e-7, fb = amplitude(e, x, b + h, g), fg = amplitude(e, x, b, g + h);
    const j11 = (fb[0] - f[0]) / h, j12 = (fg[0] - f[0]) / h, j21 = (fb[1] - f[1]) / h, j22 = (fg[1] - f[1]) / h, det = j11 * j22 - j12 * j21;
    if (Math.abs(det) < 1e-14) return null;
    b -= (j22 * f[0] - j12 * f[1]) / det; g -= (-j21 * f[0] + j11 * f[1]) / det;
  }
  const f = amplitude(e, x, b, g);
  return Math.hypot(f[0], f[1]) < 1e-12 ? [b, g] : null;
}
function analyse(key) {
  const e = ENERGIES[key].e, grid = Array.from({ length: NS }, () => new Float64Array(NB * (NG + 1))), minGrid = new Float64Array(NB * (NG + 1));
  /* the same sum as amplitude(), with the phases e^(−iγ e(y)) tabulated per γ and the coefficients per β */
  const phR = new Float64Array((NG + 1) * NS), phI = new Float64Array((NG + 1) * NS);
  for (let j = 0; j <= NG; j++) for (let y = 0; y < NS; y++) { const th = -G_MAX * j / NG * e[y]; phR[j * NS + y] = Math.cos(th); phI[j * NS + y] = Math.sin(th); }
  const cR = new Float64Array(NQ + 1), cI = new Float64Array(NQ + 1);
  for (let i = 0; i < NB; i++) {
    const b = Math.PI * i / NB, c = Math.cos(b), s = Math.sin(b);
    for (let d = 0; d <= NQ; d++) { const m = Math.pow(c, NQ - d) * Math.pow(s, d); cR[d] = m * IPOW[d & 3][0]; cI[d] = m * IPOW[d & 3][1]; }
    for (let j = 0; j <= NG; j++) {
      let mn = Infinity;
      for (let x = 0; x < NS; x++) {
        let re = 0, im = 0;
        for (let y = 0; y < NS; y++) { const d = popcount(x ^ y), pr = phR[j * NS + y], pi = phI[j * NS + y]; re += cR[d] * pr - cI[d] * pi; im += cR[d] * pi + cI[d] * pr; }
        const v = Math.hypot(re, im) / Math.sqrt(8); grid[x][i * (NG + 1) + j] = v; mn = Math.min(mn, v);
      }
      minGrid[i * (NG + 1) + j] = mn;
    }
  }
  const raw = [];
  for (let x = 0; x < NS; x++) for (let i = 0; i < NB; i++) for (let j = 0; j <= NG; j++) {
    const v = grid[x][i * (NG + 1) + j]; if (v > 0.08) continue;
    let low = true;
    for (const [di, dj] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) { const ii = (i + di + NB) % NB, jj = j + dj; if (jj < 0 || jj > NG) continue; if (grid[x][ii * (NG + 1) + jj] < v) low = false; }
    if (!low) continue;
    const z = newtonZero(e, x, Math.PI * i / NB, G_MAX * j / NG); if (!z) continue;
    const b = ((z[0] % Math.PI) + Math.PI) % Math.PI, g = z[1];
    if (g < 0 || g > G_MAX || amplitude(e, x, b, g).some((q) => Math.abs(q) > 1e-12)) continue;
    if (!raw.some((r) => r.x === x && Math.abs(r.b - b) < 1e-7 && Math.abs(r.g - g) < 1e-7)) raw.push({ x, b, g });
  }
  const zeros = [];
  for (const r of raw) { let z = zeros.find((q) => Math.abs(q.b - r.b) < 1e-6 && Math.abs(q.g - r.g) < 1e-6); if (!z) { z = { b: r.b, g: r.g, xs: [] }; zeros.push(z); } z.xs.push(r.x); }
  for (const z of zeros) { z.xs.sort((p, q) => p - q); z.support = NS - amplitudes(e, z.b, z.g).filter(([re, im]) => Math.hypot(re, im) <= TOL).length; }
  zeros.sort((p, q) => p.b - q.b || p.g - q.g);
  return { key, e, minGrid, zeros };
}

/* =====================================================================
   3. State and presets
   ===================================================================== */
const S = { e: 'lean', g: 1, nowFrac: 1 / 8, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { e: 'lean', g: 1, frac: 1 / 8, play: false, cam: 'iso',
    zh: 'Lean 冻结的反例：能量在前两位不同的基态上为 π/2、其余为 2π，γ = 1，β = π/8。前两位相同的 000、001、110、111 振幅恰为 0，010、011、100、101 的振幅都是 −(1 + i)e^(iπ/8)/√8，概率各 1/4。支撑大小 4，介于 2 与 8 之间。',
    en: 'The counterexample frozen in Lean: energy π/2 on the basis states whose first two bits differ and 2π on the others, γ = 1, β = π/8. The states with equal first two bits, 000, 001, 110, 111, have amplitude exactly 0; 010, 011, 100, 101 all have amplitude −(1 + i)e^(iπ/8)/√8, probability 1/4 each. The support has size 4, between 2 and 8.' },
  sweep: { e: 'lean', g: 1, frac: 0, play: true, cam: 'iso',
    zh: '固定 γ = 1，让 β 从 0 走到 π。左下图里四条青线（前两位相同的基态）在 β = π/8 与 5π/8 同时碰到零，四条品红线在 3π/8 与 7π/8 同时碰到零——每次都留下恰好 4 个基态。',
    en: 'Fix γ = 1 and let β run from 0 to π. In the lower left chart the four cyan curves (equal first two bits) touch zero together at β = π/8 and 5π/8, and the four magenta curves at 3π/8 and 7π/8 — each time leaving exactly 4 basis states.' },
  miss: { e: 'lean', g: 0.9, frac: 1 / 8, play: false, cam: 'iso',
    zh: '把 γ 从 1 挪到 0.9，β 仍是 π/8：被消去的四个振幅回到约 0.117，支撑又是全部 8 个基态。零点是 (β, γ) 平面上的孤立点——两个实方程要同时成立。',
    en: 'Move γ from 1 to 0.9 and keep β = π/8: the four cancelled amplitudes come back to about 0.117 and the support is all 8 basis states again. Zeros are isolated points of the (β, γ) plane — two real equations must hold at once.' },
  tri: { e: 'tri', snap: [0.3077, 0.6155], play: false, cam: 'iso',
    zh: '三角形 MaxCut（e = 切边数）。牛顿法在 (β, γ) ≈ (0.3077, 0.6155) 找到零点：|000⟩ 与 |111⟩ 的振幅同时为零，其余 6 个不为零，支撑大小 6（页面数值，不是定理）。同一能量在 β = π/4、γ = π/2 只剩 |000⟩、|111⟩，那是论文允许的两态情形。',
    en: 'Triangle MaxCut (e = the number of cut edges). Newton’s method finds a zero at (β, γ) ≈ (0.3077, 0.6155): the amplitudes of |000⟩ and |111⟩ vanish together and the other 6 do not, a support of size 6 (page numbers, not a theorem). The same energy keeps only |000⟩ and |111⟩ at β = π/4, γ = π/2, the two-state case the paper allows.' },
  asym: { e: 'asym', snap: [0.4833, 1.0765], play: false, cam: 'iso',
    zh: '没有对称性的能量（0.37 乘一个置换）。振幅只能一个一个地在孤立点为零；这里 |000⟩ 的振幅为零，其余 7 个不为零，支撑大小 7（页面数值，不是定理）。',
    en: 'An energy without symmetry (0.37 times a permutation). Amplitudes can only vanish one at a time at isolated points; here |000⟩ has amplitude zero and the other 7 do not, a support of size 7 (page numbers, not a theorem).' },
  map: { e: 'lean', g: 1, frac: 1 / 8, play: false, cam: 'top',
    zh: '俯视 (β, γ) 平面：Lean 的能量的零点排成格子，β ∈ {π/8, 3π/8, 5π/8, 7π/8}，γ 每隔 2/3 一个；每个零点同时消去 4 个振幅。品红点上标的是那里的支撑大小。',
    en: 'The (β, γ) plane from above: the zeros of Lean’s energy form a lattice, β ∈ {π/8, 3π/8, 5π/8, 7π/8} and γ every 2/3; each zero removes 4 amplitudes at once. The magenta points carry the support size there.' }
};

/* =====================================================================
   4. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
const cache = new Map();
function build() {
  if (!ENERGIES[S.e]) S.e = 'lean';
  S.g = Math.min(G_MAX, Math.max(0, isFinite(S.g) ? S.g : 1));
  if (!cache.has(S.e)) cache.set(S.e, analyse(S.e));
  const A = cache.get(S.e), M = { id: ++modelId, key: S.e, e: A.e, g: S.g, minGrid: A.minGrid, zeros: A.zeros };
  M.curves = Array.from({ length: NS }, () => new Float64Array(STEPS + 1));
  for (let k = 0; k <= STEPS; k++) amplitudes(M.e, Math.PI * k / STEPS, M.g).forEach(([re, im], x) => { M.curves[x][k] = re * re + im * im; });
  M.onLine = M.zeros.filter((z) => Math.abs(z.g - M.g) < 1e-6);
  MODEL = M;
}
function progress() {
  const M = MODEL, beta = Math.PI * S.nowFrac, amps = amplitudes(M.e, beta, M.g), mags = amps.map(([re, im]) => Math.hypot(re, im));
  const support = mags.filter((v) => v > TOL).length;
  let near = null, dn = Infinity; for (const z of M.zeros) { const d = Math.hypot(z.b - beta, z.g - M.g); if (d < dn) { dn = d; near = z; } }
  return { beta, amps, mags, support, near, dn, minX: mags.indexOf(Math.min(...mags)) };
}
/* colour groups: the cancelling pairs of each energy */
function groupOf(key, x) {
  if (key === 'lean') return bit(x, 0) === bit(x, 1) ? 0 : 1;
  if (key === 'tri') return x === 0 || x === 7 ? 2 : 0;
  return 3;
}
const HUES = ['#19f0ff', '#ff2fd0', '#ffc83d', '#7dff9a', '#9d8cff', '#ff8a3d', '#46b4ff', '#f5f5f5'];
const colOf = (key, x) => (key === 'asym' ? HUES[x] : [CY, MG, AM][groupOf(key, x)]);

/* =====================================================================
   5. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const fr = (x, d = 4) => (isFinite(x) ? x.toFixed(d) : '—');
const ex = (x) => (x === 0 ? '0' : x.toExponential(1).replace('e-', 'e−'));
const piFrac = (b) => { const q = b / Math.PI; for (const den of [1, 2, 4, 8]) { const num = Math.round(q * den); if (Math.abs(q * den - num) < 1e-9) return num === 0 ? '0' : `${num === 1 ? '' : num}π${den === 1 ? '' : '/' + den}`; } return `${q.toFixed(4)}π`; };

/* =====================================================================
   6. 3D scene
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 60000, PTS_MAX = 400;
const CAMS = { iso: [0.55, 1.0, 19], front: [0.0001, 1.5707, 18], top: [0.0001, 0.0601, 19] };
const cam = { theta: 0.55, phi: 1.0, r: 19, tTheta: 0.55, tPhi: 1.0, tR: 19 };
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
/* the landscape: β across (x ∈ [−8, 3]), γ in depth (z ∈ [−5, 5]), height = log₁₀ of the smallest |ψ(x)|, floored at 10⁻³ */
const HL = 3;
const hOf = (m) => HL * (Math.log10(Math.max(1e-3, m)) + 3) / 3;
const land = (b, g, y) => [-8 + 11 * b / Math.PI, y, -5 + 10 * g / G_MAX];
const CUBE = [6.2, 0.4, 0], CS = 1.5;
const cubeAt = (x) => [CUBE[0] + (bit(x, 0) - 0.5) * 2 * CS, CUBE[1] + (bit(x, 2) - 0.5) * 2 * CS + CS, CUBE[2] + (bit(x, 1) - 0.5) * 2 * CS];
function heightCol(y) { const t = y / HL; return [COL.magenta[0] * (1 - t) + COL.cyan[0] * t, COL.magenta[1] * (1 - t) + COL.cyan[1] * t, COL.magenta[2] * (1 - t) + COL.cyan[2] * t]; }
function updateGL() {
  const M = MODEL, pr = progress();
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (a, b, col, k) => { if (v + 2 > LINES_MAX) return; for (const p of [a, b]) { Pp[3 * v] = p[0]; Pp[3 * v + 1] = p[1]; Pp[3 * v + 2] = p[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, a, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = a; PT.aSize.array[np] = size; np++; };
  const at = (i, j) => M.minGrid[i * (NG + 1) + j];
  const P = (i, j) => { const y = hOf(at(i % NB, j)); return land(Math.PI * i / NB, G_MAX * j / NG, y); };
  for (let j = 0; j <= NG; j += 8) for (let i = 0; i < NB; i++) { const a = P(i, j), b = P(i + 1 === NB ? NB : i + 1, j); seg(a, b, heightCol(Math.min(a[1], b[1])), 0.42); }
  for (let i = 0; i <= NB; i += 8) for (let j = 0; j < NG; j++) { const a = P(i, j), b = P(i, j + 1); seg(a, b, heightCol(Math.min(a[1], b[1])), 0.32); }
  for (const z of M.zeros) { const p = land(z.b, z.g, 0); dot(p, COL.magenta, 1, 1.6); seg(p, land(z.b, z.g, 0.5), COL.magenta, 0.8); }
  /* the current γ across β, and the current point */
  let prev = null;
  for (let k = 0; k <= 200; k++) { const b = Math.PI * k / 200, m = Math.min(...amplitudes(M.e, b, M.g).map(([re, im]) => Math.hypot(re, im))), p = land(b, M.g, hOf(m) + 0.02); if (prev) seg(prev, p, COL.amber, 0.9); prev = p; }
  const minNow = Math.min(...pr.mags), cur = land(pr.beta, M.g, hOf(minNow));
  seg(land(pr.beta, M.g, 0), land(pr.beta, M.g, HL + 0.3), COL.amber, 0.7); dot(cur, COL.amber, 1, 2.4);
  /* the cube of basis states: bar height = probability */
  for (let x = 0; x < NS; x++) for (const f of [1, 2, 4]) if (!(x & f)) seg(cubeAt(x), cubeAt(x | f), GREY, 0.35);
  for (let x = 0; x < NS; x++) {
    const p = cubeAt(x), prob = pr.mags[x] * pr.mags[x], top = [p[0], p[1] + 2.6 * prob, p[2]], zero = pr.mags[x] <= TOL;
    const c = zero ? COL.magenta : (groupOf(M.key, x) === 0 ? COL.cyan : groupOf(M.key, x) === 1 ? COL.magenta : COL.amber);
    if (!zero) seg(p, top, c, 1);
    dot(p, zero ? COL.magenta : [1, 1, 1], zero ? 0.5 : 0.9, zero ? 1.4 : 1.8);
    if (!zero) dot(top, c, 1, 1.4);
  }
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const a of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) a.needsUpdate = true;
  pts.material.uniforms.uScale.value = 60 * renderer.getPixelRatio() * (stage.clientHeight / 600);
}

/* =====================================================================
   7. Camera
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
  if (drag.pts.size === 2) { const [a, b] = [...drag.pts.values()], d = Math.hypot(a.x - b.x, a.y - b.y); if (drag.pinch > 0) cam.tR = Math.min(36, Math.max(7, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(36, Math.max(7, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

/* =====================================================================
   8. Tags
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
  put('β = 0', land(0, 0, -0.4), 'cy'); put('β = π', land(Math.PI, 0, -0.4), 'cy'); put('γ = 2π', land(0, G_MAX, -0.4), 'cy');
  for (let x = 0; x < NS; x++) { const p = cubeAt(x); put(label(x), [p[0], p[1] - 0.35, p[2]], pr.mags[x] <= TOL ? 'mg' : 'cy'); }
  if (pr.near && pr.dn < 0.6) put(`|S| = ${pr.near.support}`, land(pr.near.b, pr.near.g, 0.85), 'mg');
  put(`(${fr(pr.beta, 3)}, ${fr(M.g, 3)})`, land(pr.beta, M.g, HL + 0.55), 'hot');
  for (let i = k; i < tagPool.length; i++) tagPool[i].style.display = 'none';
}

/* =====================================================================
   9. 2D panels
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
  const M = MODEL, F = frame2d(cv1, 34); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress();
  const top = Math.max(0.3, ...M.curves.map((c) => Math.max(...c))) * 1.08, X = (b) => pl + iw * b / Math.PI, Y = (p) => pt + ih - ih * p / top;
  for (const b of [Math.PI / 4, 3 * Math.PI / 4]) vline(ctx, X(b), pt, ih, VI, true, dpr);
  for (const z of M.onLine) vline(ctx, X(z.b), pt, ih, MG, true, dpr);
  for (let x = 0; x < NS; x++) {
    ctx.strokeStyle = colOf(M.key, x); ctx.lineWidth = 1.4 * dpr; ctx.globalAlpha = 0.85; ctx.beginPath();
    M.curves[x].forEach((p, k) => { const xx = X(Math.PI * k / STEPS), y = Y(p); if (k) ctx.lineTo(xx, y); else ctx.moveTo(xx, y); });
    ctx.stroke();
  }
  ctx.globalAlpha = 1; ctx.lineWidth = 1;
  vline(ctx, X(pr.beta), pt, ih, INK, false, dpr);
  lab(ctx, top.toFixed(2), pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, '0', pl - 4 * dpr, pt + ih, 'right', 'bottom');
  lab(ctx, 'β = 0', pl, pt + ih + 4 * dpr, 'left', 'top'); lab(ctx, 'π/4', X(Math.PI / 4), pt + ih + 4 * dpr, 'center', 'top', VI); lab(ctx, '3π/4', X(3 * Math.PI / 4), pt + ih + 4 * dpr, 'center', 'top', VI); lab(ctx, 'π', pl + iw, pt + ih + 4 * dpr, 'right', 'top');
  $('c1Meta').textContent = M.key === 'asym' ? T(`γ = ${fr(M.g)} 时 8 个基态的概率 |ψ(x)|² 随 β 变化，每个基态一种颜色；紫虚线 = 论文的 π/4、3π/4；品红虚线 = 这条 γ 线上的零点；白 = 当前 β`, `the probabilities |ψ(x)|² of the 8 basis states against β at γ = ${fr(M.g)}, one colour per state; violet dashes = the paper’s π/4, 3π/4; magenta dashes = zeros on this γ line; white = the current β`)
    : T(`γ = ${fr(M.g)} 时 8 个基态的概率 |ψ(x)|² 随 β 变化；${M.key === 'lean' ? '青 = 前两位相同，品红 = 前两位不同' : '琥珀 = |000⟩、|111⟩，青 = 其余'}；紫虚线 = 论文的 π/4、3π/4；品红虚线 = 这条 γ 线上的零点；白 = 当前 β`,
      `the probabilities |ψ(x)|² of the 8 basis states against β at γ = ${fr(M.g)}; ${M.key === 'lean' ? 'cyan = equal first two bits, magenta = different' : 'amber = |000⟩, |111⟩, cyan = the others'}; violet dashes = the paper’s π/4, 3π/4; magenta dashes = zeros on this γ line; white = the current β`);
}
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 12); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress();
  const cx = pl + iw / 2, cy = pt + ih / 2, R = Math.min(iw, ih) / 2 - 4 * dpr, sc = R / Math.max(0.55, ...pr.mags);
  ctx.strokeStyle = FAINT; ctx.beginPath(); ctx.moveTo(cx - R, cy); ctx.lineTo(cx + R, cy); ctx.moveTo(cx, cy - R); ctx.lineTo(cx, cy + R); ctx.stroke();
  ctx.setLineDash([3 * dpr, 3 * dpr]); ctx.beginPath(); ctx.arc(cx, cy, sc / Math.sqrt(8), 0, 2 * Math.PI); ctx.stroke(); ctx.beginPath(); ctx.arc(cx, cy, sc * 0.5, 0, 2 * Math.PI); ctx.stroke(); ctx.setLineDash([]);
  pr.amps.forEach(([re, im], x) => {
    const px = cx + sc * re, py = cy - sc * im, zero = pr.mags[x] <= TOL;
    ctx.strokeStyle = colOf(M.key, x); ctx.fillStyle = colOf(M.key, x); ctx.lineWidth = 1.6 * dpr;
    ctx.beginPath(); ctx.moveTo(cx, cy); ctx.lineTo(px, py); ctx.stroke(); ctx.lineWidth = 1;
    ctx.beginPath(); ctx.arc(px, py, (zero ? 4.5 : 2.6) * dpr, 0, 2 * Math.PI); if (zero) { ctx.strokeStyle = MG; ctx.stroke(); } else ctx.fill();
    lab(ctx, label(x), px + 5 * dpr, py - 3 * dpr - (x % 2) * 9 * dpr, 'left', 'bottom', zero ? MG : DIM);
  });
  lab(ctx, '1/√8', cx + sc / Math.sqrt(8) + 2 * dpr, cy + 2 * dpr, 'left', 'top'); lab(ctx, '1/2', cx + sc * 0.5 + 2 * dpr, cy + 2 * dpr, 'left', 'top');
  $('c2Meta').textContent = T('8 个复振幅 ψ(x)；虚线圆 = 1/√8（均匀叠加）与 1/2；品红圈 = 振幅为零', 'the 8 complex amplitudes ψ(x); dashed circles = 1/√8 (the uniform superposition) and 1/2; magenta rings = zero amplitude');
}

/* =====================================================================
   10. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function readouts() {
  const M = MODEL, pr = progress(), en = ENERGIES[M.key], sup = pr.mags.map((v, x) => (v > TOL ? label(x) : null)).filter(Boolean);
  const mid = pr.support > 2 && pr.support < NS;
  setRo([[T('能量 · 相位角 γ', 'Energy · phase angle γ'), `${T(en.zh, en.en)} · γ = ${fr(M.g, 5)}`],
    [T('混合角 β', 'Mixing angle β'), `${fr(pr.beta, 6)} = ${piFrac(pr.beta)}`],
    [T('支撑大小（|ψ(x)| > 10⁻⁹）', 'Support size (|ψ(x)| > 10⁻⁹)'), `${pr.support}${mid ? ` · 2 < ${pr.support} < 8` : ''}${pr.support < NS ? ` · {${sup.join(', ')}}` : ''}`],
    [T('最小振幅 |ψ(x)| · 基态', 'Smallest amplitude |ψ(x)| · basis state'), `${ex(pr.mags[pr.minX])} · ${label(pr.minX)}`],
    [T('Σ|ψ|² · 最近的零点 (β, γ) · 那里的支撑', 'Σ|ψ|² · nearest zero (β, γ) · support there'), `${fr(pr.mags.reduce((s, v) => s + v * v, 0), 9)} · ${pr.near ? `(${fr(pr.near.b)}, ${fr(pr.near.g)}) · ${pr.near.support}` : '—'}`]]);
  pill('pillA', 'β', fr(pr.beta, 4)); pill('pillB', 'γ', fr(M.g, 4)); pill('pillC', T('支撑', 'SUPPORT'), String(pr.support)); pill('pillD', T('零点', 'ZEROS'), String(M.zeros.length));
  const counts = {}; M.zeros.forEach((z) => { counts[z.support] = (counts[z.support] || 0) + 1; });
  $('roNote').innerHTML = T(`这个能量在 β ∈ [0, π)、γ ∈ [0, 2π] 内有 ${M.zeros.length} 个零点（牛顿法收敛到 |ψ| < 10⁻¹²），按支撑大小分：${Object.entries(counts).map(([s, c]) => `${s} → ${c} 个`).join('，')}。`,
    `This energy has ${M.zeros.length} zeros in β ∈ [0, π), γ ∈ [0, 2π] (Newton's method converged to |ψ| < 10⁻¹²); by support size: ${Object.entries(counts).map(([s, c]) => `${s} → ${c}`).join(', ')}.`);
}
function syncControls() {
  const M = MODEL;
  document.querySelectorAll('#eChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.e === M.key)));
  $('gg').value = String(M.g); $('oG').textContent = M.g.toFixed(4);
}
const stateKey = () => `${S.e}|${S.g}|${S.nowFrac}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; toasted = false; syncControls(); $('marks').dataset.key = ''; }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  const M = MODEL, pr = progress();
  readouts();
  $('formula').innerHTML = 'ψ(x) = 2<sup>−3/2</sup> Σ<sub>y</sub> cos<sup>3−d</sup>β (−i sin β)<sup>d</sup> e<sup>−iγ e(y)</sup>, &nbsp; d = |x ⊕ y|';
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('modeNote').innerHTML = T(`时间轴 = 混合角 β，从 0 到 π；γ 用滑块设定。能量：${M.e.map((v, x) => `${label(x)}: ${piFrac(v) !== `${(v / Math.PI).toFixed(4)}π` ? piFrac(v) : fr(v, 2)}`).join('，')}。`,
    `The time axis is the mixing angle β, from 0 to π; γ is set with the slider. Energy: ${M.e.map((v, x) => `${label(x)}: ${piFrac(v) !== `${(v / Math.PI).toFixed(4)}π` ? piFrac(v) : fr(v, 2)}`).join(', ')}.`);
  $('litNote').innerHTML = T('振幅、零点与地形都由页面按定义算出；冻结的是 β = π/8、γ = 1 处支撑恰为 4 的反例。', 'The amplitudes, zeros and landscape are computed on the page from the definitions; what is frozen is the counterexample with support exactly 4 at β = π/8, γ = 1.');
  $('c1Title').textContent = T('各基态的概率随 β', 'Probability of each basis state against β');
  $('c2Title').textContent = T('振幅相量', 'Amplitude phasors');
  $('clock').innerHTML = `β ${piFrac(pr.beta)}`;
  $('hudBig').textContent = `|S| = ${pr.support} · β = ${fr(pr.beta, 4)} · γ = ${fr(M.g, 4)}`;
  $('hudSub').textContent = T('地面 = (β, γ) 平面，高度 = 8 个振幅中最小者的 log₁₀（下限 10⁻³）；品红点 = 牛顿法找到的零点；琥珀线 = 当前 γ，琥珀点 = 当前 (β, γ)；右侧立方体 = 8 个基态，柱高 = 概率，品红 = 振幅为零',
    'floor = the (β, γ) plane, height = log₁₀ of the smallest of the 8 amplitudes (floored at 10⁻³); magenta points = zeros found by Newton’s method; amber line = the current γ, amber point = the current (β, γ); cube on the right = the 8 basis states, bar height = probability, magenta = zero amplitude');
  if (!toasted && S.playing && S.nowFrac >= 1) {
    toasted = true;
    toast(M.onLine.length ? T(`<b>β 扫完</b>：这条 γ 线上有 ${M.onLine.length} 个零点，β = ${M.onLine.map((z) => piFrac(z.b)).join('、')}，支撑大小 ${M.onLine.map((z) => z.support).join('、')}。`, `<b>β swept</b>: this γ line has ${M.onLine.length} zeros, at β = ${M.onLine.map((z) => piFrac(z.b)).join(', ')}, with support sizes ${M.onLine.map((z) => z.support).join(', ')}.`)
      : T('<b>β 扫完</b>：这条 γ 线上没有零点，支撑始终是 8。', '<b>β swept</b>: this γ line has no zeros; the support stays 8.'));
  }
}
function syncRail() {
  const M = MODEL, key = `${M.id}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, '0'], [0.25, 'π/4'], [0.5, 'π/2'], [0.75, '3π/4'], [1, 'π']];
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
function custom() { S.preset = null; markPreset(); dirty = true; }
document.querySelectorAll('#eChips .chip').forEach((b) => b.addEventListener('click', () => { S.e = ENERGIES[b.dataset.e] ? b.dataset.e : 'lean'; custom(); }));
$('gg').addEventListener('input', () => { S.g = parseFloat($('gg').value); $('oG').textContent = S.g.toFixed(4); custom(); });
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.e = p.e;
  if (p.snap) { if (!cache.has(p.e)) cache.set(p.e, analyse(p.e)); const zs = cache.get(p.e).zeros; let best = zs[0]; for (const z of zs) if (Math.hypot(z.b - p.snap[0], z.g - p.snap[1]) < Math.hypot(best.b - p.snap[0], best.g - p.snap[1])) best = z; S.g = best.g; S.nowFrac = best.b / Math.PI; }
  else { S.g = p.g; S.nowFrac = p.frac; }
  S.preset = name; markPreset(); dirty = true;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.nowFrac;
  setCamPreset(p.cam);
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
   11. Main loop
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
      S.nowFrac += S.dir * dtSec * S.speed / RUN;
      if (S.nowFrac >= 1) { S.nowFrac = 1; S.hold = 2.4; }
      if (S.nowFrac <= 0) { S.nowFrac = 0; S.hold = 1.2; }
    }
    $('now').value = S.nowFrac;
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    const k = `${MODEL.id}|${S.nowFrac}`;
    if (k !== glKey) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.QS_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => {
    const M = MODEL, pr = progress();
    return { e: M.key, energy: M.e, g: M.g, beta: pr.beta, amps: pr.amps, mags: pr.mags, support: pr.support, zeros: M.zeros, onLine: M.onLine, near: pr.near, tol: TOL, curves: M.curves.map((c) => Array.from(c.filter((_, k) => k % 10 === 0))), steps: STEPS };
  },
  setFrac: (f) => { S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; }
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 17; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
applyPreset('lean');
setPlayUI();
requestAnimationFrame(frame);
})();
