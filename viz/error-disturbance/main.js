/* ERROR//DISTURB · an intermediate measurement beats both endpoints
   Zhou, Wu and Chau (2016, Conjecture 3, second inequality): Δ(A, A′, B) ≥ f(A, B) = min{ε_rel(A, B), η(A, B)}, where Δ is the
   worst error of A′ measuring A plus the disturbance A′ causes to B, on one common state. Frozen in trureturing
   (ErrorDisturbanceEndpointRefutation.result): false in dimension three with A = I, A′ = U, B = V (rational orthogonal
   matrices), Δ ≤ 71/250 < 57/200 < f. The page moves A′ from A to B along a path through U and evaluates Δ, ε and η with the
   dossier's spectral formulas.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Constants and 3 × 3 matrices
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.5, 0.58, 0.68], WHITE = [0.92, 0.95, 1];
const RUN = 14, SAMPLES = 201, S_CERT = 71 / 250, R_LOW = 57 / 200;
const fr = (x, d = 6) => (isFinite(x) ? (Math.abs(x) < 5e-13 ? 0 : x).toFixed(d) : '—');
const U = [[312, -25, 0], [25, 312, 0], [0, 0, 313]].map((r) => r.map((v) => v / 313));
const V = [[32976, -3757, -1020], [3893, 31824, 8640], [0, -8700, 32045]].map((r) => r.map((v) => v / 33205));
const I3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
const mm = (A, B) => A.map((r, i) => B[0].map((_, j) => r.reduce((s, _, k) => s + A[i][k] * B[k][j], 0)));
const tr = (A) => A[0].map((_, j) => A.map((r) => r[j]));
const add = (A, B, s = 1) => A.map((r, i) => r.map((v, j) => v + s * B[i][j]));
const scal = (A, s) => A.map((r) => r.map((v) => v * s));
const col = (M, i) => [M[0][i], M[1][i], M[2][i]];
const outer = (x) => x.map((a) => x.map((b) => a * b));
const proj = (M) => [0, 1, 2].map((i) => outer(col(M, i)));
/* rotations: log by axis–angle, exp by Rodrigues */
function rotLog(R) {
  const c = Math.min(1, Math.max(-1, (R[0][0] + R[1][1] + R[2][2] - 1) / 2)), th = Math.acos(c), v = [R[2][1] - R[1][2], R[0][2] - R[2][0], R[1][0] - R[0][1]];
  const k = th < 1e-9 ? 0.5 : th / (2 * Math.sin(th)); return v.map((x) => x * k);
}
function rotExp(w) {
  const th = Math.hypot(...w); if (th < 1e-15) return I3.map((r) => r.slice());
  const [x, y, z] = w.map((v) => v / th), K = [[0, -z, y], [z, 0, -x], [-y, x, 0]], K2 = mm(K, K);
  return add(add(I3, scal(K, Math.sin(th))), scal(K2, 1 - Math.cos(th)));
}
const LOG_U = rotLog(U), LOG_VU = rotLog(mm(V, tr(U))), LOG_V = rotLog(V);
function pathAt(path, t) {
  if (path === 'direct') return rotExp(LOG_V.map((v) => v * t));
  return t <= 0.5 ? rotExp(LOG_U.map((v) => v * 2 * t)) : mm(rotExp(LOG_VU.map((v) => v * (2 * t - 1))), U);
}
/* eigen-decomposition of a symmetric 3 × 3 matrix by Jacobi rotations: values ascending, vectors as columns */
function eig(Ain) {
  const A = Ain.map((r) => r.slice()), Vv = I3.map((r) => r.slice());
  for (let sweep = 0; sweep < 50; sweep++) {
    let off = 0; for (let p = 0; p < 3; p++) for (let q = p + 1; q < 3; q++) off += A[p][q] ** 2; if (off < 1e-30) break;
    for (let p = 0; p < 3; p++) for (let q = p + 1; q < 3; q++) {
      if (Math.abs(A[p][q]) < 1e-300) continue;
      const th = (A[q][q] - A[p][p]) / (2 * A[p][q]), t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), s = t * c;
      for (let k = 0; k < 3; k++) { const akp = A[k][p], akq = A[k][q]; A[k][p] = c * akp - s * akq; A[k][q] = s * akp + c * akq; }
      for (let k = 0; k < 3; k++) { const apk = A[p][k], aqk = A[q][k]; A[p][k] = c * apk - s * aqk; A[q][k] = s * apk + c * aqk; }
      for (let k = 0; k < 3; k++) { const vkp = Vv[k][p], vkq = Vv[k][q]; Vv[k][p] = c * vkp - s * vkq; Vv[k][q] = s * vkp + c * vkq; }
    }
  }
  return [0, 1, 2].map((i) => [A[i][i], col(Vv, i)]).sort((a, b) => a[0] - b[0]);
}
const opNorm = (H) => { const e = eig(H); return Math.max(Math.abs(e[0][0]), Math.abs(e[2][0])); };
/* E_i = P_i − Q_i (error) and D_j = R_j − Σ_k Q_k R_j Q_k (disturbance) for A = I, A′ = M, B = V */
const P_A = proj(I3), R_B = proj(V);
function parts(M) {
  const Q = proj(M);
  return { E: P_A.map((P, i) => add(P, Q[i], -1)), D: R_B.map((R) => add(R, Q.reduce((s, Qk) => add(s, mm(mm(Qk, R), Qk)), [[0, 0, 0], [0, 0, 0], [0, 0, 0]]), -1)) };
}
/* Δ = max_{i,j,±} ‖E_i ± D_j‖ with the state attaining it; ε = max ‖E_i‖; η = max ‖D_j‖ (the dossier's spectral formulas) */
function evaluate(M) {
  const { E, D } = parts(M); let best = { val: -1 };
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) for (const s of [1, -1]) {
    const H = add(E[i], D[j], s), e = eig(H), top = Math.abs(e[2][0]) >= Math.abs(e[0][0]) ? e[2] : e[0];
    if (Math.abs(top[0]) > best.val) best = { val: Math.abs(top[0]), i, j, s, x: top[1] };
  }
  const cert = [];
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) for (const a of [1, -1]) for (const b of [1, -1]) cert.push(eig(add(scal(I3, S_CERT), add(scal(E[i], a), scal(D[j], b)), -1))[0][0]);
  return { Delta: best.val, best, eps: Math.max(...E.map(opNorm)), eta: Math.max(...D.map(opNorm)), cert, E, D };
}
/* the endpoint costs: η(A, B) and ε_rel(A, B) = min over relabelings π of max_i ‖P_i − R_π(i)‖ */
const PERMS = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
const ETA_AB = evaluate(I3).eta, EPS_LABEL = PERMS.map((p) => Math.max(...p.map((k, i) => opNorm(add(P_A[i], R_B[k], -1))))), EPS_REL = Math.min(...EPS_LABEL), F = Math.min(ETA_AB, EPS_REL);
/* the two witness states of the Lean proof */
const unit = (x) => { const n = Math.hypot(...x); return x.map((v) => v / n); };
const W_DIST = unit([-5, 11, -10]), W_ERR = unit([-5, -16, -11]);
const quad = (H, x) => x.reduce((s, xi, a) => s + xi * H[a].reduce((u, h, b) => u + h * x[b], 0), 0);

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { path: 'viaU', t: 0.5, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean', witness: false };
const PRESETS = {
  lean: { path: 'viaU', t: 0.5, play: false, witness: false,
    zh: 'Lean 里的反例：A′ = U，绕第三根轴转了 arctan(25/312) ≈ 4.6°。按谱公式 Δ(I, U, V) ≈ 0.283676，Lean 用 36 个半正定证书证明 Δ ≤ 71/250 = 0.284；两个端点的代价 η(I, V) ≈ 0.285229、ε_rel(I, V) ≈ 0.285395 都超过 57/200 = 0.285。中间的测量严格更便宜。',
    en: 'The counterexample in Lean: A′ = U, a turn by arctan(25/312) ≈ 4.6° about the third axis. By the spectral formula Δ(I, U, V) ≈ 0.283676, and Lean proves Δ ≤ 71/250 = 0.284 with 36 semidefinite certificates; both endpoint costs, η(I, V) ≈ 0.285229 and ε_rel(I, V) ≈ 0.285395, exceed 57/200 = 0.285. The intermediate measurement is strictly cheaper.' },
  sweep: { path: 'viaU', t: 0, play: true, witness: false,
    zh: 'A′ 从 A 出发，先转到 U、再转到 B（SO(3) 上的分段测地线）。A′ 一离开 A，Δ 就低于平线 f，并一路下降，在 U 稍前（t ≈ 0.48）最低，约比 f 低 0.00156；过了 U 迅速回升，t ≈ 0.54 处回到 f 以上，最后在 A′ = B 处等于 ε(A, B)。页面数值；Lean 证明的是 U 这一点。',
    en: 'A′ starts at A, turns to U and then to B (a piecewise geodesic on SO(3)). As soon as A′ leaves A, Δ drops below the flat line f and keeps falling, lowest just before U (t ≈ 0.48), about 0.00156 below f; past U it climbs quickly, is back above f at t ≈ 0.54, and ends at ε(A, B) when A′ = B. Page numbers; Lean proves the point U.' },
  endA: { path: 'viaU', t: 0, play: false, witness: false,
    zh: '端点 A′ = A：不会出错（ε = 0），代价全是对 B 的扰动，Δ = η(A, B) ≈ 0.285229。这是 f 取到的那个值。',
    en: 'Endpoint A′ = A: no error (ε = 0); the whole cost is the disturbance of B, Δ = η(A, B) ≈ 0.285229. This is the value f takes.' },
  endB: { path: 'viaU', t: 1, play: false, witness: false,
    zh: '端点 A′ = B：不扰动 B（η = 0），代价全是测 A 的误差，Δ = ε(A, B) ≈ 0.285395。B 的其余 5 种结果编号给出的误差在 0.966 到 1 之间。',
    en: 'Endpoint A′ = B: no disturbance of B (η = 0); the whole cost is the error in measuring A, Δ = ε(A, B) ≈ 0.285395. The other 5 relabelings of B’s outcomes give errors between 0.966 and 1.' },
  direct: { path: 'direct', t: 0, play: true, witness: false,
    zh: '直接的测地线 A → B：沿途 Δ 处处不低于 f——随手连一条路并找不到更便宜的中间测量，要专门走到 U 附近。页面数值。',
    en: 'The direct geodesic A → B: along it Δ never drops below f — a naive path finds no cheaper intermediate measurement; one has to go near U. Page numbers.' },
  witness: { path: 'viaU', t: 0, play: false, witness: true,
    zh: 'Lean 用来证明 η(I, V) > 57/200 的见证态：纯态 x = (−5, 11, −10)/√246。在 A′ = A 处它的扰动是 0.285112，已超过 0.285；另一个见证态 (−5, −16, −11)/√402 在 A′ = B 处给出误差 0.285337。',
    en: 'The witness Lean uses to prove η(I, V) > 57/200: the pure state x = (−5, 11, −10)/√246. At A′ = A its disturbance is 0.285112, already above 0.285; the other witness (−5, −16, −11)/√402 gives error 0.285337 at A′ = B.' }
};
let MODEL = null, dirty = true, modelId = 0;
const CURVES = {};
function curve(path) { if (!CURVES[path]) CURVES[path] = Array.from({ length: SAMPLES }, (_, k) => { const t = k / (SAMPLES - 1), r = evaluate(pathAt(path, t)); return [t, r.Delta, r.eps, r.eta]; }); return CURVES[path]; }
function build() {
  S.t = Math.min(1, Math.max(0, S.t));
  const M = pathAt(S.path, S.t), r = evaluate(M), cv = curve(S.path);
  const below = cv.filter(([, d]) => d < F - 1e-12).map(([t]) => t), minPt = cv.reduce((m, p) => (p[1] < m[1] ? p : m), cv[0]);
  const state = S.witness ? W_DIST : r.best.x;
  const wDist = Math.max(...r.D.map((Dj) => Math.abs(quad(Dj, W_DIST)))), wErr = Math.max(...evaluate(V).E.map((Ei) => Math.abs(quad(Ei, W_ERR))));
  MODEL = { id: ++modelId, t: S.t, path: S.path, Ap: M, ...r, state, worst: r.best.x, gap: F - r.Delta, below: below.length ? [below[0], below[below.length - 1]] : null, minPt, wDist, wErr, certMin: Math.min(...r.cert) };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');

/* =====================================================================
   4. 3D scene: the bases A (grey), A′ (cyan), B (amber) and the worst state (magenta)
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 4000, PTS_MAX = 200;
const CAMS = { iso: [0.75, 1.0, 9.5], front: [0.0001, 1.45, 9], top: [0.0001, 0.06, 9.5] };
const cam = { theta: 0.75, phi: 1.0, r: 9.5, tTheta: 0.75, tPhi: 1.0, tR: 9.5 };
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
/* vector (x, y, z) → scene (x, z, −y), radius RS */
const RS = 2.2, sc = (v, r = RS) => [r * v[0], r * v[2], -r * v[1]];
function updateGL() {
  const M = MODEL;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = c[0]; PT.aColor.array[3 * np + 1] = c[1]; PT.aColor.array[3 * np + 2] = c[2]; PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  /* unit sphere */
  for (let a = 0; a < 64; a++) {
    const q0 = 2 * Math.PI * a / 64, q1 = 2 * Math.PI * (a + 1) / 64;
    seg(sc([Math.cos(q0), Math.sin(q0), 0]), sc([Math.cos(q1), Math.sin(q1), 0]), GREY, 0.18);
    seg(sc([Math.cos(q0), 0, Math.sin(q0)]), sc([Math.cos(q1), 0, Math.sin(q1)]), GREY, 0.12);
    seg(sc([0, Math.cos(q0), Math.sin(q0)]), sc([0, Math.cos(q1), Math.sin(q1)]), GREY, 0.12);
  }
  /* the trails of A′'s columns along the whole path */
  const steps = 60;
  for (let i = 0; i < 3; i++) for (let k = 0; k < steps; k++) { const a = col(pathAt(M.path, k / steps), i), b = col(pathAt(M.path, (k + 1) / steps), i); seg(sc(a), sc(b), COL.cyan, 0.25); }
  /* the three bases as arrows from the origin */
  const triad = (Mx, c, k, size) => { for (let i = 0; i < 3; i++) { const e = col(Mx, i); seg([0, 0, 0], sc(e), c, k); dot(sc(e), c, k, size); } };
  triad(I3, GREY, 0.75, 1.4); triad(V, COL.amber, 1, 1.8); triad(M.Ap, COL.cyan, 1, 1.8);
  /* the worst state is a ray: draw it through the origin */
  const x = M.state; seg(sc(x, -RS * 1.15), sc(x, RS * 1.15), COL.magenta, 1); dot(sc(x, RS * 1.15), COL.magenta, 1, 2.2); dot(sc(x, -RS * 1.15), COL.magenta, 0.6, 1.6);
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
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
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.45 : 1);
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
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()]; drag.pinch = Math.hypot(p.x - q.x, p.y - q.y); }
});
stage.addEventListener('pointermove', (ev) => {
  if (!drag.pts.has(ev.pointerId)) return;
  drag.pts.set(ev.pointerId, { x: ev.clientX, y: ev.clientY });
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(30, Math.max(4, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
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
function placeTag(el, p) {
  if (!glOK) { el.style.display = 'none'; return; }
  const q = proj3(p); if (q.z > 1 || q.z < -1) { el.style.display = 'none'; return; }
  el.style.display = 'block';
  const w = el.offsetWidth, h = el.offsetHeight, Wd = stage.clientWidth, Hd = stage.clientHeight, hud = document.querySelector('.hud-tl'), top = hud.offsetTop + hud.offsetHeight + 4;
  el.style.left = Math.min(Wd - w / 2 - 6, Math.max(w / 2 + 6, q.x)) + 'px'; el.style.top = Math.min(Hd - h / 2 - 6, Math.max(top + h / 2, q.y)) + 'px';
}
function updateTags() {
  const M = MODEL; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  for (let i = 0; i < 3; i++) { put(`a${'₁₂₃'[i]}`, sc(col(I3, i), RS * 1.12), 'gr'); put(`b${'₁₂₃'[i]}`, sc(col(V, i), RS * 1.12), 'hot'); put(`a′${'₁₂₃'[i]}`, sc(col(M.Ap, i), RS * 1.22), 'cy'); }
  put(S.witness ? T('见证态 x', 'witness x') : T('最坏的态', 'worst state'), sc(M.state, RS * 1.3), 'mg');
  for (let i = k; i < tagPool.length; i++) tagPool[i].style.display = 'none';
}

/* =====================================================================
   7. 2D panels
   ===================================================================== */
function frame2d(cv, pl0 = 46) {
  const dpr = fitCanvas(cv), ctx = cv.getContext('2d'), Wd = cv.width, Hh = cv.height;
  ctx.clearRect(0, 0, Wd, Hh);
  const pl = pl0 * dpr, pr = 12 * dpr, pt = 12 * dpr, pb = 20 * dpr;
  ctx.font = `${9.5 * dpr}px ${TRV.fonts.data}`;
  return { dpr, ctx, W: Wd, Hh, pl, pt, iw: Wd - pl - pr, ih: Hh - pt - pb };
}
function lab(ctx, txt, x, y, al, bl, c = DIM) { ctx.fillStyle = c; ctx.textAlign = al; ctx.textBaseline = bl; ctx.fillText(txt, x, y); }
/* Δ along the path against f, with the stretch where Δ < f shaded */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 52); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, cv = curve(M.path);
  const lo = Math.min(F, S_CERT, ...cv.map((p) => p[1])) - 0.0004, hi = Math.max(...cv.map((p) => p[1])) + 0.0004;
  const X = (t) => pl + iw * t, Y = (y) => pt + ih - ih * (y - lo) / (hi - lo);
  if (M.below) { ctx.fillStyle = 'rgba(255,47,208,0.10)'; ctx.fillRect(X(M.below[0]), pt, X(M.below[1]) - X(M.below[0]), ih); }
  ctx.strokeStyle = AM; ctx.lineWidth = 1.2 * dpr; ctx.setLineDash([5 * dpr, 4 * dpr]); ctx.beginPath(); ctx.moveTo(pl, Y(F)); ctx.lineTo(pl + iw, Y(F)); ctx.stroke(); ctx.setLineDash([]);
  ctx.strokeStyle = 'rgba(255,47,208,0.6)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(S_CERT)); ctx.lineTo(pl + iw, Y(S_CERT)); ctx.stroke();
  for (const [y, c] of [[F, AM], [S_CERT, MG], [lo, DIM], [hi, DIM]]) if (c !== DIM || Math.min(Math.abs(Y(y) - Y(F)), Math.abs(Y(y) - Y(S_CERT))) > 12 * dpr) lab(ctx, y.toFixed(4), pl - 4 * dpr, Y(y), 'right', 'middle', c);
  ctx.strokeStyle = CY; ctx.lineWidth = 2 * dpr; ctx.beginPath(); cv.forEach(([t, d], i) => { if (i === 0) ctx.moveTo(X(t), Y(d)); else ctx.lineTo(X(t), Y(d)); }); ctx.stroke();
  ctx.strokeStyle = 'rgba(255,255,255,0.45)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(X(M.t), pt); ctx.lineTo(X(M.t), pt + ih); ctx.stroke();
  ctx.fillStyle = INK; ctx.beginPath(); ctx.arc(X(M.t), Y(M.Delta), 3.5 * dpr, 0, 2 * Math.PI); ctx.fill();
  for (const [t, l] of [[0, 'A′ = A'], [M.path === 'viaU' ? 0.5 : null, 'U'], [1, 'A′ = B']]) if (t !== null) lab(ctx, l, X(t), pt + ih + 4 * dpr, t === 0 ? 'left' : t === 1 ? 'right' : 'center', 'top', t === 0.5 ? MG : DIM);
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>Δ(A, A′, B)</span><span class="it"><i class="sw" style="--c:${AM}"></i>f = min{ε_rel, η}</span><span class="it"><i class="sw" style="--c:${MG}"></i>s = 71/250</span>`;
}
/* the 36 smallest eigenvalues of sI − (±E_i ± D_j) at s = 71/250: all ≥ 0 exactly when Δ ≤ s. Only the sign matters, so the
   axis is ±CERT_RANGE and larger bars are clipped (a cap marks the clip). */
const CERT_RANGE = 0.004;
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 50); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, n = M.cert.length, bw = iw / n;
  const Y = (y) => pt + ih / 2 - (ih / 2) * Math.max(-1, Math.min(1, y / CERT_RANGE));
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
  for (const y of [-CERT_RANGE, 0, CERT_RANGE]) lab(ctx, y.toFixed(3), pl - 4 * dpr, Y(y), 'right', 'middle');
  const kMin = M.cert.indexOf(M.certMin);
  M.cert.forEach((v, k) => {
    ctx.fillStyle = v >= -1e-12 ? CY : MG; const y0 = Y(0), y1 = Y(v), x = pl + k * bw + bw * 0.15, w = bw * 0.7;
    ctx.fillRect(x, Math.min(y0, y1), w, Math.max(1, Math.abs(y1 - y0)));
    if (Math.abs(v) > CERT_RANGE) { ctx.fillStyle = INK; ctx.fillRect(x, v > 0 ? y1 : y1 - 2 * dpr, w, 2 * dpr); }
    if (k === kMin) { ctx.strokeStyle = INK; ctx.lineWidth = 1.2 * dpr; ctx.strokeRect(x - 1.5 * dpr, Math.min(y0, y1) - 1.5 * dpr, w + 3 * dpr, Math.max(1, Math.abs(y1 - y0)) + 3 * dpr); }
  });
  for (let i = 0; i < 9; i++) lab(ctx, `${Math.floor(i / 3) + 1}${(i % 3) + 1}`, pl + (i * 4 + 2) * bw, pt + ih + 4 * dpr, 'center', 'top');
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>≥ 0</span><span class="it"><i class="sw" style="--c:${MG}"></i>&lt; 0</span><span class="it">min <b>${fr(M.certMin)}</b></span><span class="it note">${T('（每组 ij 4 种符号；纵轴截在 ±0.004）', '(4 signs per ij; axis clipped at ±0.004)')}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function readouts() {
  const M = MODEL, x = M.worst.map((v) => fr(v, 3)).join(', ');
  pill('pillA', 't', fr(M.t, 3)); pill('pillB', 'Δ', fr(M.Delta, 5)); pill('pillC', 'f − Δ', fr(M.gap, 5)); pill('pillD', T('证书', 'CERT'), M.certMin >= -1e-12 ? '✓' : '✗');
  setRo([[T('Δ(A, A′, B)：误差加扰动的最坏值 · 最坏的态 x', 'Δ(A, A′, B): worst error plus disturbance · the worst state x'), `${fr(M.Delta)} · (${x})`],
    [T('ε(A, A′) · η(A′, B) · 两者之和（第一个不等式的左边）', 'ε(A, A′) · η(A′, B) · their sum (left side of the first inequality)'), `${fr(M.eps)} · ${fr(M.eta)} · ${fr(M.eps + M.eta)}`],
    [T('f(A, B) = min{ε_rel(A, B), η(A, B)}', 'f(A, B) = min{ε_rel(A, B), η(A, B)}'), `min{${fr(EPS_REL)}, ${fr(ETA_AB)}} = ${fr(F)}`],
    [T('f − Δ（为正即第二个不等式不成立）', 'f − Δ (positive means the second inequality fails)'), `${fr(M.gap)}`],
    S.witness ? [T('见证态：A′ = A 处 (−5, 11, −10)/√246 的扰动 · A′ = B 处 (−5, −16, −11)/√402 的误差', 'Witnesses: disturbance of (−5, 11, −10)/√246 at A′ = A · error of (−5, −16, −11)/√402 at A′ = B'), `${fr(M.wDist)} · ${fr(M.wErr)} > 57/200`]
      : [T('证书：sI − (±Eᵢ ± Dⱼ) 在 s = 71/250 时的最小特征值', 'Certificate: smallest eigenvalue of sI − (±Eᵢ ± Dⱼ) at s = 71/250'), `${fr(M.certMin)} ${M.certMin >= -1e-12 ? T('≥ 0，所以 Δ ≤ 0.284', '≥ 0, so Δ ≤ 0.284') : T('< 0', '< 0')}`]]);
  $('roNote').innerHTML = M.gap > 1e-12 ? T(`这里 Δ 比两个端点中便宜的那个还低 ${fr(M.gap, 5)}：猜想的第二个不等式不成立${Math.abs(M.t - 0.5) < 1e-9 && M.path === 'viaU' ? '（Lean 定理在 A′ = U 处证明了这一点）' : '（页面数值）'}。`, `Here Δ is ${fr(M.gap, 5)} below the cheaper endpoint: the conjecture’s second inequality fails${Math.abs(M.t - 0.5) < 1e-9 && M.path === 'viaU' ? ' (the Lean theorem proves this at A′ = U)' : ' (page numbers)'}.`)
    : T('这里 Δ 不低于 f，与猜想一致。', 'Here Δ is not below f, consistent with the conjecture.');
}
const stateKey = () => `${S.path}|${S.t}|${S.preset}|${S.witness}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; }
  const M = MODEL;
  if (!toasted && S.playing && S.t >= 1) { toasted = true; const b0 = M.below && (M.below[0] <= 1.5 / (SAMPLES - 1) ? '0' : fr(M.below[0], 2)); toast(M.below ? T(`<b>A → U → B</b>：Δ 在 t ≈ ${b0} 到 ${fr(M.below[1], 2)} 之间低于 f，最低 ${fr(M.minPt[1])} 在 t ≈ ${fr(M.minPt[0], 2)}（U 在 t = 0.5）。`, `<b>A → U → B</b>: Δ is below f for t ≈ ${b0} to ${fr(M.below[1], 2)}, lowest ${fr(M.minPt[1])} at t ≈ ${fr(M.minPt[0], 2)} (U is at t = 0.5).`) : T('<b>A → B</b>：沿这条路 Δ 处处不低于 f。', '<b>A → B</b>: along this path Δ never drops below f.')); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  document.querySelectorAll('#pathChips [data-path]').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.path === S.path)));
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('pathNote').innerHTML = M.path === 'viaU' ? T('t ∈ [0, ½]：A′ = exp(2t·log U)；t ∈ [½, 1]：A′ = exp((2t − 1)·log(VUᵀ))·U。t = ½ 时 A′ = U。', 't ∈ [0, ½]: A′ = exp(2t·log U); t ∈ [½, 1]: A′ = exp((2t − 1)·log(VUᵀ))·U. At t = ½, A′ = U.') : T('A′ = exp(t·log V)：SO(3) 上从 A = I 到 B = V 的测地线。', 'A′ = exp(t·log V): the geodesic on SO(3) from A = I to B = V.');
  $('litNote').innerHTML = T('沿路径的数值用卷宗的谱公式算出；冻结的是 A′ = U 时 Δ ≤ 71/250 &lt; 57/200 &lt; f。', 'The values along the path use the dossier’s spectral formulas; what is frozen is that at A′ = U, Δ ≤ 71/250 &lt; 57/200 &lt; f.');
  $('c1Title').textContent = T('沿路径的 Δ（青）与平线 f（琥珀虚线）', 'Δ along the path (cyan) against the flat line f (amber, dashed)');
  $('c2Title').textContent = T('半正定证书：sI − (±Eᵢ ± Dⱼ) 的最小特征值，s = 71/250', 'Semidefinite certificate: smallest eigenvalues of sI − (±Eᵢ ± Dⱼ), s = 71/250');
  $('clock').innerHTML = `t = ${fr(M.t, 3)}`;
  $('hudBig').textContent = `t = ${fr(M.t, 3)} · Δ = ${fr(M.Delta, 5)} · f = ${fr(F, 5)} · ${M.gap > 1e-12 ? T('Δ < f：猜想不成立', 'Δ < f: the conjecture fails') : T('Δ ≥ f', 'Δ ≥ f')}`;
  $('hudSub').textContent = T('三组箭头是三组测量基（矩阵的列）：灰 = A（坐标轴），青 = A′，琥珀 = B；青色细线是 A′ 沿整条路径扫过的轨迹；品红射线是让误差加扰动最大的那个态', 'The three triads are the three measurement bases (the columns of the matrices): grey = A (the axes), cyan = A′, amber = B; thin cyan curves trace A′ along the whole path; the magenta ray is the state that maximizes error plus disturbance');
}
function syncRail() {
  const key = `${S.path}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 'A′ = A']]; if (S.path === 'viaU') marks.push([0.5, T('U（Lean）', 'U (Lean)')]); marks.push([1, 'A′ = B']);
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  Object.assign(S, { path: p.path, t: p.t, witness: p.witness, hold: 0 }); S.preset = name; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
document.querySelectorAll('#pathChips [data-path]').forEach((b) => b.addEventListener('click', () => { S.path = b.dataset.path; S.preset = null; S.witness = false; markPreset(); dirty = true; }));
const setT = (t, user) => { S.t = Math.min(1, Math.max(0, t)); $('now').value = S.t; dirty = true; if (user) { S.preset = null; S.witness = false; markPreset(); } };
$('now').addEventListener('input', () => { setT(parseFloat($('now').value), true); S.hold = 0; });
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
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : 1); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed / RUN);
      if (S.t >= 1) S.hold = 2.4;
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
window.ED_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { t: M.t, path: M.path, Ap: M.Ap, Delta: M.Delta, eps: M.eps, eta: M.eta, f: F, epsRel: EPS_REL, epsLabel: EPS_LABEL.slice(), etaAB: ETA_AB, gap: M.gap, state: M.state.slice(), worst: M.worst.slice(), best: { i: M.best.i, j: M.best.j, s: M.best.s }, cert: M.cert.slice(), certMin: M.certMin, below: M.below, minPt: M.minPt.slice(), wDist: M.wDist, wErr: M.wErr }; },
  curve: (p) => curve(p).map((r) => r.slice()),
  U: () => U.map((r) => r.slice()), V: () => V.map((r) => r.slice()),
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 8; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
