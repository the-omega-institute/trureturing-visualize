/* LG//SIX · six-time Leggett–Garg inequalities are not sufficient
   Halliwell and Mawby (2019) conjectured that compatible pair tables p_ij(a, b) of n dichotomic variables have a joint
   law as soon as the full n-gon inequalities and all three-time LG inequalities hold. Frozen in trureturing
   (LeggettGargSixTimeSufficiencyRefutation.result): false at n = 6, for the star correlations C_i6 = 1/2 (i ≤ 4),
   C_56 = −1/2, all others 0. With b = (1, 1, 1, 1, −1, −2) every sign vector has W(x)² = (Σ bᵢxᵢ)² ≥ 1, while any
   matching law would give Σ μ W² = bᵀ(I + C)b = −1. The page scales the correlations by t, shows where each condition
   holds, and gives an explicit joint law for t ≤ 0.8.
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
const GREY = [0.5, 0.58, 0.68], VIOLET = '#9d8cff';
const TMAX = 1.2, RUN = 22, B = [1, 1, 1, 1, -1, -2], T_JOINT = 0.8, T_PSD = 2 / Math.sqrt(5);
const fr = (x, d = 4) => (isFinite(x) ? (Math.abs(x) < 5e-13 ? 0 : x).toFixed(d) : '—');
/* the 64 sign vectors x ∈ {±1}⁶; index bit i set ↔ xᵢ = −1 */
const ATOMS = Array.from({ length: 64 }, (_, k) => [0, 1, 2, 3, 4, 5].map((i) => ((k >> i) & 1 ? -1 : 1)));
const W = (x) => x.reduce((s, v, i) => s + B[i] * v, 0);
/* an exact joint law at t = 0.8, found offline by linear programming; the page checks it below. Entries: sign vector, weight */
const MU08 = [
  ['+++−−+', 1 / 10], ['++−+++', 1 / 20], ['++−−+−', 1 / 20], ['++−−−+', 1 / 20], ['+−++++', 1 / 20], ['+−++−+', 1 / 10],
  ['+−−++−', 1 / 20], ['+−−−+−', 1 / 20], ['−+++++', 1 / 20], ['−+++−+', 1 / 20], ['−++−+−', 1 / 20], ['−+−++−', 1 / 20],
  ['−+−+−+', 1 / 20], ['−−+−+−', 1 / 10], ['−−−+−−', 1 / 20], ['−−−−−−', 1 / 10]
].map(([s, w]) => [s.replace(/ /g, '').split('').map((c) => (c === '+' ? 1 : -1)), w]);
const atomIndex = (x) => x.reduce((k, v, i) => k + (v < 0 ? 1 << i : 0), 0);

/* =====================================================================
   2. The model at scale t
   ===================================================================== */
/* C(t): t times the star correlations */
function corrMatrix(t) {
  const C = Array.from({ length: 6 }, () => new Array(6).fill(0));
  for (let i = 0; i < 4; i++) C[i][5] = C[5][i] = t / 2;
  C[4][5] = C[5][4] = -t / 2;
  return C;
}
const pairTable = (C, i, j, a, b) => (1 + a * b * C[i][j]) / 4;
/* the full 6-gon inequalities: 6 + 2 Σ_{i<j} sᵢsⱼCᵢⱼ ≥ 0 (n even) for every s; the minimum over the 64 sign vectors */
function ngonMin(C, idx = [0, 1, 2, 3, 4, 5]) {
  const n = idx.length; let best = Infinity;
  for (let m = 0; m < 2 ** n; m++) { const s = idx.map((_, k) => ((m >> k) & 1 ? -1 : 1)); let v = n; for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) v += 2 * s[p] * s[q] * C[idx[p]][idx[q]]; best = Math.min(best, v - (n % 2)); }
  return best;
}
/* every polygon inequality on a subset of at least three times */
function subsetPolygonMin(C) { let best = Infinity; for (let m = 0; m < 64; m++) { const idx = [0, 1, 2, 3, 4, 5].filter((i) => (m >> i) & 1); if (idx.length >= 3) best = Math.min(best, ngonMin(C, idx)); } return best; }
/* all three-time LG inequalities 1 + abCᵢⱼ + acCᵢₖ + bcCⱼₖ ≥ 0 */
function lgMin(C) {
  let best = Infinity;
  for (let i = 0; i < 6; i++) for (let j = i + 1; j < 6; j++) for (let k = j + 1; k < 6; k++) for (let m = 0; m < 8; m++) {
    const a = m & 1 ? -1 : 1, b = m & 2 ? -1 : 1, c = m & 4 ? -1 : 1;
    best = Math.min(best, 1 + a * b * C[i][j] + a * c * C[i][k] + b * c * C[j][k]);
  }
  return best;
}
/* eigenvalues of the symmetric matrix I + C by Jacobi rotations */
function jacobiEig(Ain) {
  const n = Ain.length, A = Ain.map((r) => r.slice());
  for (let sweep = 0; sweep < 60; sweep++) {
    let off = 0; for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) off += A[p][q] ** 2; if (off < 1e-24) break;
    for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
      if (Math.abs(A[p][q]) < 1e-300) continue;
      const th = (A[q][q] - A[p][p]) / (2 * A[p][q]), tt = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(tt * tt + 1), s = tt * c;
      for (let k = 0; k < n; k++) { const akp = A[k][p], akq = A[k][q]; A[k][p] = c * akp - s * akq; A[k][q] = s * akp + c * akq; }
      for (let k = 0; k < n; k++) { const apk = A[p][k], aqk = A[q][k]; A[p][k] = c * apk - s * aqk; A[q][k] = s * apk + c * aqk; }
    }
  }
  return A.map((r, i) => r[i]).sort((x, y) => x - y);
}
/* the explicit joint law for t ≤ 0.8: (1 − t/0.8)·uniform + (t/0.8)·MU08; null beyond */
function jointLaw(t) {
  if (t > T_JOINT + 1e-12) return null;
  const s = t / T_JOINT, mu = new Array(64).fill((1 - s) / 64);
  for (const [x, w] of MU08) mu[atomIndex(x)] += s * w;
  return mu;
}
/* the largest deviation of the law's pair marginals from the tables */
function marginalError(mu, C) {
  let err = 0;
  for (let i = 0; i < 6; i++) for (let j = i + 1; j < 6; j++) for (const a of [1, -1]) for (const b of [1, -1]) {
    let s = 0; ATOMS.forEach((x, k) => { if (x[i] === a && x[j] === b) s += mu[k]; }); err = Math.max(err, Math.abs(s - pairTable(C, i, j, a, b)));
  }
  return err;
}

/* =====================================================================
   3. State and presets
   ===================================================================== */
const S = { t: 1, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { t: 1, play: false,
    zh: 'Lean 里的例子（t = 1）：时刻 6 与时刻 1–4 的关联都是 1/2，与时刻 5 是 −1/2，其余为 0。完整的 6 边形不等式与全部三时刻 LG 不等式都成立（最小值 1 和 0），可没有联合分布：64 根青柱是 W(x)² = (x₁ + x₂ + x₃ + x₄ − x₅ − 2x₆)²，全都 ≥ 1；任何联合分布对它们的加权平均却必须等于 bᵀ(I + C)b = −1——琥珀平面落到了地板以下。',
    en: 'The example in Lean (t = 1): time 6 is correlated 1/2 with times 1–4 and −1/2 with time 5, all other correlations are 0. The full 6-gon inequality and every three-time LG inequality hold (minima 1 and 0), yet there is no joint law: the 64 cyan bars are W(x)² = (x₁ + x₂ + x₃ + x₄ − x₅ − 2x₆)², all ≥ 1, while any joint law would have to average them to bᵀ(I + C)b = −1 — the amber plane sinks below the floor.' },
  sweep: { t: 0, play: true,
    zh: '把关联整体乘以 t，从 0 扫到 1.2。左下图是各条件的余量：联合分布在 t = 0.8 消失（W 的平均 9 − 10t 跌破 1），二阶矩矩阵在 t = 2/√5 ≈ 0.894 不再半正定，三时刻 LG 在 t = 1 用尽，6 边形在 t = 1.2 用尽。',
    en: 'Scale all correlations by t and sweep from 0 to 1.2. The lower left chart shows the slack of each condition: the joint law disappears at t = 0.8 (the average of W², 9 − 10t, drops below 1), the second-moment matrix stops being positive semidefinite at t = 2/√5 ≈ 0.894, the three-time LG inequalities run out at t = 1 and the 6-gon at t = 1.2.' },
  edge: { t: 0.8, play: false,
    zh: 't = 0.8：联合分布仍然存在，而且页面给出一个精确的：16 个符号向量，权重 1/10 或 1/20（离线线性规划找到，页面逐项核对 60 个边缘表）。琥珀柱是这个分布，加权平均恰好是 9 − 8 = 1，正好贴着地板。',
    en: 't = 0.8: a joint law still exists, and the page shows an exact one: 16 sign vectors with weights 1/10 or 1/20 (found offline by linear programming; the page checks all 60 marginal tables). The amber bars are this law, and its average of W² is exactly 9 − 8 = 1, touching the floor.' },
  psd: { t: 0.85, play: false,
    zh: 't = 0.85：二阶矩矩阵 I + C 仍半正定（最小特征值约 0.05），6 边形、全部子集多边形与三时刻 LG 都成立，可 W 的平均 9 − 8.5 = 0.5 < 1，所以没有联合分布。卷宗把“再加上半正定条件够不够”列为未决；这里是本页按同一论证给出的反例，未形式化、未经评审。',
    en: 't = 0.85: the second-moment matrix I + C is still positive semidefinite (smallest eigenvalue about 0.05), the 6-gon, every subset polygon and every three-time LG inequality hold, yet the average of W² would be 9 − 8.5 = 0.5 < 1, so there is no joint law. The dossier lists “does adding positive semidefiniteness suffice?” as open; this is the page’s counterexample by the same argument, not formalized and not reviewed.' },
  half: { t: 0.5, play: false,
    zh: 't = 0.5：一切都好——条件成立，联合分布也存在：均匀分布与 t = 0.8 那个分布按 3 : 5 混合。琥珀柱是这个分布，它对 W² 的平均是 9 − 5 = 4，高出地板 W² = 1 很多。',
    en: 't = 0.5: everything is fine — the conditions hold and a joint law exists: the uniform law and the t = 0.8 law mixed 3 : 5. The amber bars are this law; its average of W² is 9 − 5 = 4, well above the floor W² = 1.' },
  beyond: { t: 1.1, play: false,
    zh: 't = 1.1：三时刻 LG 不等式本身已经失败（最小值 1 − t = −0.1），6 边形的余量 6 − 5t = 0.5 却仍为正。猜想的前提不成立，所以这里不再是反例；联合分布当然也不存在。',
    en: 't = 1.1: the three-time LG inequalities themselves fail (minimum 1 − t = −0.1), although the 6-gon still has slack 6 − 5t = 0.5. The conjecture’s hypothesis fails, so this is no longer a counterexample; there is of course no joint law either.' }
};

/* =====================================================================
   4. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
function build() {
  if (!isFinite(S.t)) S.t = 1; S.t = Math.min(TMAX, Math.max(0, S.t));
  const t = S.t, C = corrMatrix(t), R = C.map((r, i) => r.map((v, j) => v + (i === j ? 1 : 0)));
  const eig = jacobiEig(R), mu = jointLaw(t);
  const avgW2 = B.reduce((s, bi, i) => s + B.reduce((u, bj, j) => u + bi * bj * R[i][j], 0), 0);
  MODEL = { id: ++modelId, t, C, eig, ngon: ngonMin(C), sub: subsetPolygonMin(C), lg: lgMin(C), mu, muErr: mu ? marginalError(mu, C) : null, avgW2,
    pairFamily: C.every((r) => r.every((v) => Math.abs(v) <= 1 + 1e-12)) };
}

/* =====================================================================
   5. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');

/* =====================================================================
   6. 3D scene: the 64 sign vectors on an 8 × 8 floor
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 4000, PTS_MAX = 400;
const CAMS = { iso: [0.7, 1.0, 20], front: [0.0001, 1.45, 18], top: [0.0001, 0.06, 18] };
const cam = { theta: 0.7, phi: 1.0, r: 20, tTheta: 0.7, tPhi: 1.0, tR: 20 };
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
/* atom k: x₁x₂x₃ pick the row, x₄x₅x₆ the column; height of a W² bar = W²/8, of a law bar = 40·μ */
const CELL = 1.05, HW = 1 / 8, HMU = 40;
const cellOf = (k) => [((k & 7) - 3.5) * CELL, ((k >> 3) - 3.5) * CELL];
function updateGL() {
  const M = MODEL;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, col, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, al, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const E = 4 * CELL;
  for (let c = 0; c <= 8; c++) { const u = (c - 4) * CELL; seg([u, 0, -E], [u, 0, E], GREY, 0.18); seg([-E, 0, u], [E, 0, u], GREY, 0.18); }
  /* the floor W² = 1 and the plane the average of W² must reach */
  const rect = (h, col, k) => { seg([-E, h, -E], [E, h, -E], col, k); seg([E, h, -E], [E, h, E], col, k); seg([E, h, E], [-E, h, E], col, k); seg([-E, h, E], [-E, h, -E], col, k); };
  rect(HW, COL.cyan, 0.5);
  const hp = M.avgW2 * HW, bad = M.avgW2 < 1 - 1e-12;
  rect(hp, bad ? COL.magenta : COL.amber, 1);
  for (let c = 1; c < 8; c++) { const u = (c - 4) * CELL; seg([u, hp, -E], [u, hp, E], bad ? COL.magenta : COL.amber, 0.22); }
  ATOMS.forEach((x, k) => {
    const [px, pz] = cellOf(k), w2 = W(x) ** 2;
    seg([px - 0.12, 0, pz], [px - 0.12, w2 * HW, pz], COL.cyan, 0.55); dot([px - 0.12, w2 * HW, pz], COL.cyan, 0.8, 0.9);
    if (M.mu && M.mu[k] > 1e-12) { const h = M.mu[k] * HMU; seg([px + 0.15, 0, pz], [px + 0.15, h, pz], COL.amber, 1); dot([px + 0.15, h, pz], COL.amber, 1, 1.3); }
  });
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const at of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) at.needsUpdate = true;
  pts.material.uniforms.uScale.value = 60 * renderer.getPixelRatio() * (stage.clientHeight / 600);
}

/* =====================================================================
   7. Camera
   ===================================================================== */
function updateCamera(dtSec) {
  const k = reduceMotion ? 1 : 1 - Math.pow(0.001, dtSec);
  cam.theta += (cam.tTheta - cam.theta) * k; cam.phi += (cam.tPhi - cam.phi) * k; cam.r += (cam.tR - cam.r) * k;
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.45 : 1);
  camera.position.set(r * sp * Math.sin(cam.theta), r * Math.cos(cam.phi), r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(0, 1.8, 0);
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
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(45, Math.max(7, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(45, Math.max(7, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

/* =====================================================================
   8. Tags
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
  const M = MODEL, E = 4 * CELL; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  put(T('地板 W² = 1', 'floor W² = 1'), [E + 0.4, HW, E], 'cy');
  put(`${T('联合分布要求的平均', 'average a joint law needs')} 9 − 10t = ${fr(M.avgW2, 2)}`, [-E - 0.4, M.avgW2 * HW + 0.3, -E], M.avgW2 < 1 - 1e-12 ? 'mg' : 'hot');
  const big = ATOMS.findIndex((x) => W(x) === 7); const [px, pz] = cellOf(big);
  put('W = 7: (+ + + + − −)', [px, 0.7 * 49 * HW, pz], 'cy');
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
/* the slack of every condition against t */
const CURVES = [
  ['ngon', (t) => 6 - 5 * t, CY, '6-gon'], ['lg', (t) => 1 - t, OK, 'LG₃'], ['psd', (t) => 1 - t * Math.sqrt(5) / 2, VIOLET, 'λmin'], ['joint', (t) => 8 - 10 * t, AM, '9 − 10t − 1']
];
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 36); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, lo = -4, hi = 8, X = (t) => pl + iw * t / TMAX, Y = (y) => pt + ih - ih * (y - lo) / (hi - lo);
  ctx.fillStyle = 'rgba(255,47,208,0.08)'; ctx.fillRect(X(T_JOINT), pt, X(1) - X(T_JOINT), ih);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
  for (const y of [-4, 0, 4, 8]) lab(ctx, String(y), pl - 4 * dpr, Y(y), 'right', 'middle');
  for (const t of [0, 0.4, 0.8, 1, 1.2]) lab(ctx, String(t), X(t), pt + ih + 4 * dpr, 'center', 'top', t === 0.8 || t === 1 ? AM : DIM);
  for (const [, f, col] of CURVES) { ctx.strokeStyle = col; ctx.lineWidth = 2 * dpr; ctx.beginPath(); ctx.moveTo(X(0), Y(f(0))); ctx.lineTo(X(TMAX), Y(f(TMAX))); ctx.stroke(); }
  ctx.strokeStyle = 'rgba(255,255,255,0.4)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(X(M.t), pt); ctx.lineTo(X(M.t), pt + ih); ctx.stroke();
  /* the band is narrow, so its label sits to its left, shrunk if the chart is narrow */
  const bandTxt = T('品红区：条件都成立，却没有联合分布 →', 'magenta: all hold, no joint law →'), room = X(T_JOINT) - 4 * dpr - (X(0.05) + 2 * dpr);
  const fs = Math.max(7 * dpr, Math.min(9.5 * dpr, 9.5 * dpr * room / ctx.measureText(bandTxt).width));
  ctx.font = `${fs}px ${TRV.fonts.data}`; lab(ctx, bandTxt, X(T_JOINT) - 4 * dpr, pt + 2 * dpr, 'right', 'top', MG);
  $('c1Meta').innerHTML = CURVES.map(([, , col, name]) => `<span class="it"><i class="sw" style="--c:${col}"></i>${name}</span>`).join('') + `<span class="it">${T('（≥ 0 才成立）', '(holds when ≥ 0)')}</span>`;
}
/* the correlation matrix t·C as a heatmap, with the star graph beside it */
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 10); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, cell = Math.min(ih / 6, iw * 0.55 / 6), x0 = pl + iw - 6 * cell - 4 * dpr, y0 = pt;
  ctx.font = `${Math.min(10.5 * dpr, cell * 0.32)}px ${TRV.fonts.data}`;
  for (let i = 0; i < 6; i++) for (let j = 0; j < 6; j++) {
    const v = i === j ? 1 : M.C[i][j], a = Math.min(1, Math.abs(v));
    ctx.fillStyle = v > 0 ? `rgba(25,240,255,${0.12 + 0.6 * a})` : v < 0 ? `rgba(255,47,208,${0.12 + 0.6 * a})` : 'rgba(110,140,170,0.08)';
    ctx.fillRect(x0 + j * cell + 1, y0 + i * cell + 1, cell - 2, cell - 2);
    lab(ctx, i === j ? '1' : v === 0 ? '0' : fr(v, 2), x0 + (j + 0.5) * cell, y0 + (i + 0.5) * cell, 'center', 'middle', INK);
  }
  /* star graph: centre 6, leaves 1–5 */
  const cx = pl + (x0 - pl) / 2, cy = pt + ih / 2, R = Math.min((x0 - pl) / 2 - 14 * dpr, ih / 2 - 10 * dpr);
  const pos = [0, 1, 2, 3, 4].map((k) => [cx + R * Math.cos(-Math.PI / 2 + 2 * Math.PI * k / 5), cy + R * Math.sin(-Math.PI / 2 + 2 * Math.PI * k / 5)]);
  pos.forEach(([x, y], k) => { ctx.strokeStyle = k === 4 ? MG : CY; ctx.lineWidth = 2 * dpr; ctx.beginPath(); ctx.moveTo(cx, cy); ctx.lineTo(x, y); ctx.stroke(); });
  ctx.font = `${10 * dpr}px ${TRV.fonts.data}`;
  [...pos, [cx, cy]].forEach(([x, y], k) => { ctx.fillStyle = '#02040a'; ctx.beginPath(); ctx.arc(x, y, 9 * dpr, 0, 2 * Math.PI); ctx.fill(); ctx.strokeStyle = k === 5 ? AM : INK; ctx.lineWidth = 1.2 * dpr; ctx.stroke(); lab(ctx, String(k + 1), x, y, 'center', 'middle', k === 5 ? AM : INK); });
  $('c2Meta').textContent = T(`t = ${fr(M.t, 2)}：时刻 6 与 1–4 的关联 t/2（青），与 5 的关联 −t/2（品红），其余为 0`, `t = ${fr(M.t, 2)}: time 6 correlates t/2 with 1–4 (cyan) and −t/2 with 5 (magenta), the rest 0`);
}

/* =====================================================================
   10. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const okTxt = (b) => (b ? T('成立', 'holds') : T('失败', 'fails'));
function readouts() {
  const M = MODEL, conds = M.ngon >= -1e-12 && M.lg >= -1e-12;
  pill('pillA', 't', fr(M.t, 3)); pill('pillB', T('条件', 'CONDITIONS'), okTxt(conds)); pill('pillC', T('联合分布', 'JOINT LAW'), M.mu ? T('存在', 'exists') : T('不存在', 'none')); pill('pillD', 'λmin', fr(M.eig[0], 3));
  setRo([[T('6 边形不等式的最小值 · 所有子集多边形的最小余量', 'Minimum of the 6-gon inequality · smallest slack over all subset polygons'), `${fr(M.ngon, 4)} · ${fr(M.sub, 4)} · ${okTxt(M.ngon >= -1e-12 && M.sub >= -1e-12)}`],
    [T('三时刻 LG 的最小值（20 组 × 8 种符号）', 'Minimum of the three-time LG inequalities (20 triples × 8 signs)'), `${fr(M.lg, 4)} · ${okTxt(M.lg >= -1e-12)}`],
    [T('二阶矩矩阵 I + C 的特征值', 'Eigenvalues of the second-moment matrix I + C'), M.eig.map((v) => fr(v, 3)).join(', ')],
    [T('W = Σ bᵢxᵢ：联合分布要求的平均 bᵀ(I + C)b，而每个 W² ≥ 1', 'W = Σ bᵢxᵢ: the average bᵀ(I + C)b a joint law would need, while every W² ≥ 1'), `${fr(M.avgW2, 4)}${M.avgW2 < 1 - 1e-12 ? T('  < 1，矛盾', '  < 1, contradiction') : ''}`],
    [T('联合分布', 'Joint law'), M.mu ? T(`存在：均匀分布与 t = 0.8 的分布按 ${fr(1 - M.t / T_JOINT, 3)} : ${fr(M.t / T_JOINT, 3)} 混合，60 个边缘表的最大误差 ${M.muErr.toExponential(1)}`, `exists: the uniform law and the t = 0.8 law mixed ${fr(1 - M.t / T_JOINT, 3)} : ${fr(M.t / T_JOINT, 3)}, largest error over the 60 marginal tables ${M.muErr.toExponential(1)}`) : T('不存在（上一行的论证）', 'none (the argument in the row above)')]]);
  const verdict = !M.pairFamily ? T('关联超出 [−1, 1]，不再是概率表。', 'Correlations leave [−1, 1]; these are no longer probability tables.')
    : conds && !M.mu ? T(`条件全部成立，却没有联合分布——${M.eig[0] >= -1e-12 ? '而且二阶矩矩阵仍半正定（本页的论证）' : '二阶矩矩阵已不再半正定'}。`, `Every condition holds, yet there is no joint law — ${M.eig[0] >= -1e-12 ? 'and the second-moment matrix is still positive semidefinite (the page’s argument)' : 'the second-moment matrix is no longer positive semidefinite'}.`)
    : conds ? T('条件成立，联合分布也存在。', 'The conditions hold and a joint law exists.') : T('猜想的条件本身已失败，这里不是反例。', 'The conjecture’s conditions themselves fail; this is not a counterexample.');
  $('roNote').innerHTML = verdict;
}
const stateKey = () => `${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; }
  if (!toasted && S.playing && S.t >= TMAX) { toasted = true; toast(T('<b>t 从 0 到 1.2</b>：联合分布在 0.8 消失，可猜想的条件一直撑到 1——这一段全是反例。', '<b>t from 0 to 1.2</b>: the joint law disappears at 0.8, but the conjecture’s conditions last until 1 — that whole stretch consists of counterexamples.')); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  const M = MODEL;
  readouts();
  $('formula').innerHTML = `p<sub>ij</sub>(a, b) = (1 + ab·C<sub>ij</sub>)/4, &nbsp; C<sub>i6</sub> = t/2 (i ≤ 4), C<sub>56</sub> = −t/2`;
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('tNote').innerHTML = T('时间轴 = t，从 0 到 1.2；t = 1 是 Lean 里的例子。所有单时刻边缘都是 1/2。', 'The time axis is t, from 0 to 1.2; t = 1 is the example in Lean. Every one-time marginal is 1/2.');
  $('litNote').innerHTML = T('条件、特征值与联合分布都由页面算出；冻结的是 t = 1 时条件成立而联合分布不存在。', 'The conditions, the eigenvalues and the joint law are computed on the page; what is frozen is that at t = 1 the conditions hold and no joint law exists.');
  $('c1Title').textContent = T('各条件的余量随 t 变化（≥ 0 才成立）', 'Slack of each condition against t (holds when ≥ 0)');
  $('c2Title').textContent = T('关联矩阵 t·C 与它的星形图', 'The correlation matrix t·C and its star graph');
  $('clock').innerHTML = `t = ${fr(M.t, 3)}`;
  $('hudBig').textContent = `t = ${fr(M.t, 3)} · ${T('平均 W²', 'mean W²')} = 9 − 10t = ${fr(M.avgW2, 3)} · ${M.mu ? T('联合分布存在', 'joint law exists') : T('无联合分布', 'no joint law')}`;
  $('hudSub').textContent = T('8 × 8 地板 = 64 个符号向量 (x₁, …, x₆)；青柱 = W(x)²/8（W = x₁ + x₂ + x₃ + x₄ − x₅ − 2x₆，全都 ≥ 1），青框 = W² = 1 的地板；琥珀框 = 任何联合分布必须达到的平均 9 − 10t（跌破地板时变品红）；琥珀柱 = t ≤ 0.8 时页面给出的联合分布 μ(x)', '8 × 8 floor = the 64 sign vectors (x₁, …, x₆); cyan bars = W(x)²/8 (W = x₁ + x₂ + x₃ + x₄ − x₅ − 2x₆, all ≥ 1), cyan frame = the floor W² = 1; amber frame = the average 9 − 10t any joint law must reach (magenta once it drops below the floor); amber bars = the joint law μ(x) the page gives for t ≤ 0.8');
}
function syncRail() {
  const key = TRV.lang(); if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 't = 0'], [T_JOINT / TMAX, '0.8'], [T_PSD / TMAX, '2/√5'], [1 / TMAX, T('1（Lean）', '1 (Lean)')], [1, '1.2']];
  /* 0.8, 2/√5, 1 and 1.2 crowd the right end; on narrow screens 2/√5 and 1.2 drop to a second line (style.css) */
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last low' : i === 2 ? 'low' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.t = p.t; S.preset = name; markPreset(); dirty = true;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.t / TMAX;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const setT = (t, user) => { S.t = Math.min(TMAX, Math.max(0, t)); $('now').value = S.t / TMAX; dirty = true; if (user) { S.preset = null; markPreset(); } };
$('now').addEventListener('input', () => { setT(parseFloat($('now').value) * TMAX, true); S.hold = 0; });
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(Math.round(S.t * 20 + (ev.key === 'ArrowRight' ? 1 : -1)) / 20); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(TMAX);
});

/* =====================================================================
   11. Main loop
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
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : TMAX); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed * TMAX / RUN);
      if (S.t >= TMAX) S.hold = 2.4;
      if (S.t <= 0 && S.dir < 0) S.hold = 1.2;
    }
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    if (glKey !== String(MODEL.id)) { updateGL(); glKey = String(MODEL.id); }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.LG_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { t: M.t, C: M.C, eig: M.eig, ngon: M.ngon, sub: M.sub, lg: M.lg, avgW2: M.avgW2, mu: M.mu, muErr: M.muErr, pairFamily: M.pairFamily, b: B.slice() }; },
  mu08: () => MU08.map(([x, w]) => [x, w]),
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 15; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
