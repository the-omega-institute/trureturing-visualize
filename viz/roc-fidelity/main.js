/* ROC//FIDELITY · the Fuchs–Caves fidelity measurement need not give optimal ROC points
   Bodor and Koniorczyk (2017) asked whether the d + 1 cumulative points (Q_k, P_k) of the fidelity measurement
   M = ρ^{−1/2} (ρ^{1/2} σ ρ^{1/2})^{1/2} ρ^{−1/2} lie on the optimal receiver operating characteristic. Refuted in
   trureturing (FidelityMeasurementROCRefutation.result): for ρ = (1/20)[[2,1,1],[1,10,1],[1,1,8]], σ = DρD,
   D = diag(2, 1, 1/2), the effect F = vv†/1382 with v = (37, 2, −3) has false-positive rate 1/10 = Q₁ and true-positive
   rate 5539/13820 > 2/5 = P₁. The page varies the off-diagonal coupling ε and the diagonal D, finds the optimal curve by
   the supporting-line dual y*(x) = min_t [λ₊(σ − tρ) + t x], and draws the effects on the sphere of directions.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Linear algebra for 3 × 3 real symmetric matrices
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const WHITE = [0.92, 0.95, 1], GREY = [0.42, 0.5, 0.6], GOLD = [1, 0.84, 0.3];
const GOLDC = '#ffd34d';
const R3 = [0, 1, 2];
const mm = (A, B) => R3.map((i) => R3.map((j) => A[i][0] * B[0][j] + A[i][1] * B[1][j] + A[i][2] * B[2][j]));
const mv = (A, v) => R3.map((i) => A[i][0] * v[0] + A[i][1] * v[1] + A[i][2] * v[2]);
const dot = (u, v) => u[0] * v[0] + u[1] * v[1] + u[2] * v[2];
const quad = (A, v) => dot(v, mv(A, v));
const lin = (A, a, B, b) => R3.map((i) => R3.map((j) => a * A[i][j] + b * B[i][j]));
const tr = (A) => A[0][0] + A[1][1] + A[2][2];
const unit = (v) => { const n = Math.hypot(...v); return v.map((x) => x / n); };
/* Jacobi rotations: eigenvalues ascending, with unit eigenvectors */
function eig(Ain) {
  const A = Ain.map((r) => r.slice()), V = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
  for (let sweep = 0; sweep < 50; sweep++) {
    const off = A[0][1] ** 2 + A[0][2] ** 2 + A[1][2] ** 2; if (off < 1e-34) break;
    for (let p = 0; p < 3; p++) for (let q = p + 1; q < 3; q++) {
      if (Math.abs(A[p][q]) < 1e-300) continue;
      const th = (A[q][q] - A[p][p]) / (2 * A[p][q]), t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), s = t * c;
      for (let k = 0; k < 3; k++) { const akp = A[k][p], akq = A[k][q]; A[k][p] = c * akp - s * akq; A[k][q] = s * akp + c * akq; }
      for (let k = 0; k < 3; k++) { const apk = A[p][k], aqk = A[q][k]; A[p][k] = c * apk - s * aqk; A[q][k] = s * apk + c * aqk; }
      for (let k = 0; k < 3; k++) { const vkp = V[k][p], vkq = V[k][q]; V[k][p] = c * vkp - s * vkq; V[k][q] = s * vkp + c * vkq; }
    }
  }
  const idx = R3.slice().sort((i, j) => A[i][i] - A[j][j]);
  /* sign: the largest component of each eigenvector is positive */
  const vecs = idx.map((i) => { const v = R3.map((k) => V[k][i]); const m = v.reduce((b, x, k) => (Math.abs(x) > Math.abs(v[b]) ? k : b), 0); return v[m] < 0 ? v.map((x) => -x) : v; });
  return { w: idx.map((i) => A[i][i]), V: vecs };
}
const fn = (A, f) => { const { w, V } = eig(A); return R3.map((i) => R3.map((j) => w.reduce((s, l, k) => s + f(l) * V[k][i] * V[k][j], 0))); };
const sym = (A) => R3.map((i) => R3.map((j) => (A[i][j] + A[j][i]) / 2));
const lamPlus = (H) => eig(H).w.reduce((s, l) => s + Math.max(0, l), 0);

/* =====================================================================
   2. The pair, the fidelity measurement and the optimal ROC
   ===================================================================== */
/* ρ = (diag(2, 10, 8) + ε (J − I)) / 20 and σ = DρD / tr(DρD), D = diag(d₀, 1, d₂); ε = 1, D = diag(2, 1, ½) is Lean's witness */
function pair(eps, d0, d2) {
  const rho = R3.map((i) => R3.map((j) => (i === j ? [2, 10, 8][i] : eps) / 20));
  const d = [d0, 1, d2], s0 = R3.map((i) => R3.map((j) => d[i] * rho[i][j] * d[j])), c2 = tr(s0);
  return { rho, sigma: s0.map((r) => r.map((v) => v / c2)), c: Math.sqrt(c2), d };
}
/* the supporting-line dual: y*(x) = min over t ≥ 0 of λ₊(σ − tρ) + t x, by golden section (the objective is convex in t) */
function dual(P, x) {
  if (x <= 0) return { y: 0, t: P.tmax };
  if (x >= 1) return { y: 1, t: 0 };
  const phi = (t) => lamPlus(lin(P.sigma, 1, P.rho, -t)) + t * x;
  let a = 0, b = P.tmax, g = (Math.sqrt(5) - 1) / 2, c = b - g * (b - a), e = a + g * (b - a), fc = phi(c), fe = phi(e);
  for (let it = 0; it < 90; it++) { if (fc <= fe) { b = e; e = c; fe = fc; c = b - g * (b - a); fc = phi(c); } else { a = c; c = e; fc = fe; e = a + g * (b - a); fe = phi(e); } }
  const t = (a + b) / 2; return { y: Math.min(phi(t), fc, fe), t };
}
const GRID = 200;
const CURVES = new Map();
function curveOf(P, key) {
  if (CURVES.has(key)) return CURVES.get(key);
  const xs = [], ys = []; for (let i = 0; i <= GRID; i++) { const x = i / GRID; xs.push(x); ys.push(dual(P, x).y); }
  const c = { xs, ys }; CURVES.set(key, c); if (CURVES.size > 40) CURVES.delete(CURVES.keys().next().value); return c;
}
const polyAt = (Q, Pc, x) => { for (let k = 1; k < Q.length; k++) if (x <= Q[k] + 1e-15) { const w = Q[k] - Q[k - 1]; return w <= 0 ? Pc[k] : Pc[k - 1] + (Pc[k] - Pc[k - 1]) * (x - Q[k - 1]) / w; } return 1; };
/* unit vectors u with uᵀρu = c, as one closed loop (empty when c is outside the spectrum of ρ) */
function ringOf(rho, c, n = 360) {
  const { w, V } = eig(rho), [l1, l2, l3] = w, pts = [];
  if (c < l1 - 1e-15 || c > l3 + 1e-15) return pts;
  for (let s = 0; s < n; s++) {
    const a = 2 * Math.PI * s / n, ca = Math.cos(a), sa = Math.sin(a);
    if (c <= l2) { const la = l2 * ca * ca + l3 * sa * sa, r2 = Math.min(1, Math.max(0, (c - l1) / (la - l1))), r = Math.sqrt(r2), h = Math.sqrt(1 - r2); pts.push(R3.map((k) => h * V[0][k] + r * ca * V[1][k] + r * sa * V[2][k])); }
    else { const la = l1 * ca * ca + l2 * sa * sa, r2 = Math.min(1, Math.max(0, (l3 - c) / (l3 - la))), r = Math.sqrt(r2), h = Math.sqrt(1 - r2); pts.push(R3.map((k) => h * V[2][k] + r * ca * V[0][k] + r * sa * V[1][k])); }
  }
  return pts;
}
const angleDeg = (u, v) => 180 / Math.PI * Math.acos(Math.min(1, Math.abs(dot(unit(u), unit(v)))));

/* =====================================================================
   3. State, presets and the model
   ===================================================================== */
const S = { eps: 1, lg0: 1, lg2: -1, t: 0.1, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { eps: 1, lg0: 1, lg2: -1, k: 1,
    zh: 'Lean 的反例：ρ = (1/20)[[2,1,1],[1,10,1],[1,1,8]]，σ = DρD，D = diag(2, 1, ½)。保真度观测量正是 D，有序本征基是坐标基，第一个累积点 (Q₁, P₁) = (1/10, 2/5)。Lean 给出效应 F = vv†/1382，v = (37, 2, −3)：假阳性同为 1/10，真阳性 5539/13820 > 2/5。页面算出这一假阳性下的最优真阳性约为 0.402031，比 2/5 高约 0.00203（页面数值）。',
    en: 'Lean’s counterexample: ρ = (1/20)[[2,1,1],[1,10,1],[1,1,8]], σ = DρD, D = diag(2, 1, ½). The fidelity observable is D itself, the ordered eigenbasis is the coordinate basis, and the first cumulative point is (Q₁, P₁) = (1/10, 2/5). Lean exhibits the effect F = vv†/1382 with v = (37, 2, −3): the same false-positive rate 1/10 and true-positive rate 5539/13820 > 2/5. The page finds the optimal true-positive rate at this false-positive rate to be about 0.402031, about 0.00203 above 2/5 (page numbers).' },
  second: { eps: 1, lg0: 1, lg2: -1, k: 2,
    zh: '同一对态的第二个累积点 (Q₂, P₂) = (3/5, 9/10)：页面算出的最优真阳性约为 0.900880，也高出约 0.00088。最优效应是秩 2 的投影 I − ww†，w 偏离 a₂ 约 2.9°。Lean 只用到第一个点；这一点是页面数值。',
    en: 'The second cumulative point of the same pair, (Q₂, P₂) = (3/5, 9/10): the page’s optimal true-positive rate is about 0.900880, again higher, by about 0.00088. The optimal effect is the rank-2 projector I − ww†, with w about 2.9° away from a₂. Lean uses only the first point; this one is a page number.' },
  commute: { eps: 0, lg0: 1, lg2: -1, k: 1,
    zh: 'ε = 0：ρ 与 σ 都是对角的，两者对易。最优 ROC 曲线就是保真度折线，每个累积点都在曲线上（档案里的阈值论证，未形式化；页面算出的差距为 0）。x 环缩成一点 a₀：假阳性为 1/10 的秩 1 投影只有它一个。',
    en: 'ε = 0: ρ and σ are both diagonal and commute. The optimal ROC curve is the fidelity polyline and every cumulative point lies on it (the dossier’s threshold argument, not formalized; the page’s gap is 0). The x-ring shrinks to the single point a₀: it is the only rank-1 projector with false-positive rate 1/10.' },
  small: { eps: 0.25, lg0: 1, lg2: -1, k: 1,
    zh: 'ε = 1/4：非对易性很弱，Q₁ 处的差距只有约 1.2 × 10⁻⁴，约为 ε = 1/2 时（约 4.9 × 10⁻⁴）的四分之一——在这一族里，小 ε 时差距大致按 ε² 增长（页面数值，没有证明）。',
    en: 'ε = 1/4: the pair barely fails to commute, and the gap at Q₁ is only about 1.2 × 10⁻⁴, about a quarter of its value at ε = 1/2 (about 4.9 × 10⁻⁴) — in this family the gap grows roughly like ε² for small ε (page numbers, not proved).' },
  strong: { eps: 3, lg0: 1, lg2: -1, k: 1,
    zh: 'ε = 3（ρ 仍正定，最小本征值约 0.021）：Q₁ 处的差距增大到约 0.0214，在 ROC 图上也看得出；最优方向偏离 a₀ 约 11°。页面数值。',
    en: 'ε = 3 (ρ is still positive definite, with smallest eigenvalue about 0.021): the gap at Q₁ grows to about 0.0214, visible even in the ROC plane, and the optimal direction is about 11° away from a₀. Page numbers.' },
  reversed: { eps: 1, lg0: -1, lg2: 1, k: 1,
    zh: 'D = diag(½, 1, 2)：σ 需要重新归一，保真度观测量是 D/√2.125，似然比的顺序反过来：a₀ = e₂，a₁ = e₁，a₂ = e₀。第一个累积点是 (2/5, 64/85)，最优真阳性高出约 5.1 × 10⁻⁴（页面数值）。',
    en: 'D = diag(½, 1, 2): σ has to be renormalized, the fidelity observable is D/√2.125, and the likelihood-ratio order is reversed: a₀ = e₂, a₁ = e₁, a₂ = e₀. The first cumulative point is (2/5, 64/85), and the optimal true-positive rate is about 5.1 × 10⁻⁴ higher (page numbers).' }
};
const LEANV = [37, 2, -3];
const isLean = () => S.eps === 1 && S.lg0 === 1 && S.lg2 === -1;
let MODEL = null, dirty = true, modelId = 0;
function build() {
  const d0 = 2 ** S.lg0, d2 = 2 ** S.lg2, P = pair(S.eps, d0, d2), { rho, sigma } = P;
  /* the fidelity observable, computed from its definition */
  const Rh = fn(rho, Math.sqrt), Ri = fn(rho, (l) => 1 / Math.sqrt(l)), M = sym(mm(mm(Ri, fn(sym(mm(mm(Rh, sigma), Rh)), Math.sqrt)), Ri));
  const EM = eig(M), m = EM.w;
  const degenerate = Math.min(m[1] - m[0], m[2] - m[1]) < 1e-7;
  /* outcomes ordered by non-increasing likelihood ratio p/q (cross-multiplied, as in Lean); ties keep the eigen order */
  const basis = EM.V.map((a, i) => ({ a, m: m[i], q: quad(rho, a), p: quad(sigma, a) }));
  const ord = basis.map((_, i) => i).sort((i, j) => { const A = basis[i], B = basis[j], dlt = B.p * A.q - A.p * B.q; return Math.abs(dlt) < 1e-14 ? i - j : dlt; });
  const B = ord.map((i) => basis[i]), Q = [0], Pc = [0];
  B.forEach((b) => { Q.push(Q[Q.length - 1] + b.q); Pc.push(Pc[Pc.length - 1] + b.p); });
  Q[3] = 1; Pc[3] = 1;
  /* t beyond the largest generalized eigenvalue of (σ, ρ) gives σ − tρ < 0 */
  const G = eig(sym(mm(mm(Ri, sigma), Ri))).w;
  P.tmax = G[2] * 1.02 + 0.01;
  const key = `${S.eps}|${S.lg0}|${S.lg2}`, curve = curveOf(P, key);
  const x = S.t, L = polyAt(Q, Pc, x), D = dual(P, x), H = lin(sigma, 1, rho, -D.t), EH = eig(H);
  const rank = EH.w.filter((l) => l > 1e-10).length;
  const mode = x <= 0.5 ? 'one' : 'two', level = mode === 'one' ? x : 1 - x;
  const ring = ringOf(rho, level).map((u) => ({ u, y: mode === 'one' ? quad(sigma, u) : 1 - quad(sigma, u) }));
  let best = null; ring.forEach((r) => { if (!best || r.y > best.y) best = r; });
  const better = ring.filter((r) => r.y > L + 1e-12).length;
  /* at a vertex k the fidelity effect is the projector on a₍₀₎ … a₍ₖ₋₁₎; the direction drawn on the ring is a₍₀₎ (k = 1) or a₍₂₎ (k = 2) */
  const vertex = [1, 2].find((k) => Math.abs(x - Q[k]) < 1e-9) || 0;
  const fidDir = vertex === 1 && mode === 'one' ? B[0].a : vertex === 2 && mode === 'two' ? B[2].a : null;
  const optDir = rank === 1 ? EH.V[2] : rank === 2 ? EH.V[0] : null;
  const tilt = vertex && optDir && ((vertex === 1 && rank === 1) || (vertex === 2 && rank === 2)) ? angleDeg(vertex === 1 ? B[0].a : B[2].a, optDir) : null;
  const gaps = [1, 2].map((k) => dual(P, Q[k]).y - Pc[k]);
  const comp = isLean() ? { v: LEANV, n: dot(LEANV, LEANV), x: quad(rho, LEANV) / dot(LEANV, LEANV), y: quad(sigma, LEANV) / dot(LEANV, LEANV) } : null;
  MODEL = { id: ++modelId, eps: S.eps, d: P.d, c: P.c, rho, sigma, M, m, degenerate, B, ord, Q, Pc, x, L, ystar: D.y, tstar: D.t, gap: D.y - L, H, EH, rank, mode, ring, best, arcFrac: ring.length ? better / ring.length : 0,
    vertex, fidDir, optDir, tilt, gaps, comp, curve, rhoEig: eig(rho).w, lean: isLean(), tmax: P.tmax };
}

/* =====================================================================
   4. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const SUB = '₀₁₂';
const fx = (v, d = 6) => (Math.abs(v) < 0.5 * 10 ** -d ? 0 : v).toFixed(d);
const f3 = (v) => String(+v.toFixed(3));
const ci = (a) => a.reduce((b, x, k) => (Math.abs(x) > Math.abs(a[b]) ? k : b), 0);
const sci = (v) => (Math.abs(v) < 1e-12 ? '0' : Math.abs(v) >= 1e-3 ? v.toFixed(5) : `${(v / 10 ** Math.floor(Math.log10(Math.abs(v)))).toFixed(2)} × 10${String(Math.floor(Math.log10(Math.abs(v)))).replace('-', '⁻').replace(/\d/g, (c) => '⁰¹²³⁴⁵⁶⁷⁸⁹'[c])}`);

/* =====================================================================
   5. 3D scene: the sphere of directions coloured by the supporting-line score uᵀ(σ − t*ρ)u
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, dotsMesh, marks, inner;
const RS = 2.4, NDOT = 6000, LINES_MAX = 4000, MK_MAX = 16;
const CAMS = { iso: [0.55, 1.12, 8.4], top: [0.0001, 0.08, 8.4] };
const cam = { theta: 0.55, phi: 1.12, r: 8.4, tTheta: 0.55, tPhi: 1.12, tR: 8.4 };
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
  float r = length(gl_PointCoord - 0.5) * 2.0;
  float a = smoothstep(1.0, 0.55, r) * vA;
  if (a < 0.02) discard;
  gl_FragColor = vec4(vCol, a);
}`;
/* math coordinates (u₀, u₁, u₂) ↦ scene (u₁, u₂, u₀), so that a₀ faces the default camera */
const toScene = (u, r = RS) => [u[1] * r, u[2] * r, u[0] * r];
function dyn(g, nm, n, size) { const a = new THREE.BufferAttribute(new Float32Array(n * size), size); a.setUsage(THREE.DynamicDrawUsage); g.setAttribute(nm, a); return a; }
const FIB = Array.from({ length: NDOT }, (_, i) => { const y = 1 - 2 * (i + 0.5) / NDOT, r = Math.sqrt(1 - y * y), a = i * Math.PI * (3 - Math.sqrt(5)); return [r * Math.cos(a), y, r * Math.sin(a)]; });
function pointsMesh(n) {
  const g = new THREE.BufferGeometry(); dyn(g, 'position', n, 3); dyn(g, 'aColor', n, 3); dyn(g, 'aAlpha', n, 1); dyn(g, 'aSize', n, 1);
  const p = new THREE.Points(g, new THREE.ShaderMaterial({ vertexShader: VS, fragmentShader: FS, uniforms: { uScale: { value: 60 } }, transparent: true, depthWrite: false, depthTest: true }));
  p.frustumCulled = false; return p;
}
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
  inner = new THREE.Mesh(new THREE.SphereGeometry(RS * 0.985, 64, 48), new THREE.MeshBasicMaterial({ color: 0x050b14 }));
  scene3.add(inner);
  const g = new THREE.BufferGeometry(); dyn(g, 'position', LINES_MAX, 3); dyn(g, 'color', LINES_MAX, 3);
  lines = new THREE.LineSegments(g, new THREE.LineBasicMaterial({ vertexColors: true, transparent: true, depthTest: true })); lines.frustumCulled = false; scene3.add(lines);
  dotsMesh = pointsMesh(NDOT); scene3.add(dotsMesh);
  marks = pointsMesh(MK_MAX); marks.material.depthTest = false; marks.renderOrder = 2; scene3.add(marks);
}
function updateGL() {
  const M = MODEL, Hn = Math.max(...M.EH.w.map(Math.abs)) || 1;
  /* the sphere: cyan where uᵀHu > 0 (the optimal effect takes these directions), magenta where it is negative */
  const D = dotsMesh.geometry.attributes;
  FIB.forEach((u, i) => {
    const s = quad(M.H, u) / Hn, p = toScene(u), c = s > 0 ? COL.cyan : COL.magenta, k = 0.1 + 0.7 * Math.min(1, Math.abs(s) * 1.6);
    for (let j = 0; j < 3; j++) { D.position.array[3 * i + j] = p[j]; D.aColor.array[3 * i + j] = c[j] * k; }
    D.aAlpha.array[i] = 0.9; D.aSize.array[i] = 0.72;
  });
  for (const a of [D.position, D.aColor, D.aAlpha, D.aSize]) a.needsUpdate = true;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  /* the ordered fidelity basis (white) and the eigenvectors of H (amber, bright where the eigenvalue is positive) */
  M.B.forEach((b) => seg(toScene(b.a, -1.32 * RS), toScene(b.a, 1.32 * RS), WHITE, 0.75));
  M.EH.V.forEach((h, i) => seg(toScene(h, -1.22 * RS), toScene(h, 1.22 * RS), COL.amber, M.EH.w[i] > 1e-10 ? 0.95 : 0.3));
  /* the x-ring and its antipodal copy: amber where the effect beats the fidelity polyline at this x */
  const n = M.ring.length;
  for (let s = 0; s < n; s++) {
    const a = M.ring[s], b = M.ring[(s + 1) % n], good = a.y > M.L + 1e-12 && b.y > M.L + 1e-12, c = good ? COL.amber : GREY;
    seg(toScene(a.u, RS * 1.006), toScene(b.u, RS * 1.006), c, good ? 1 : 0.8);
    seg(toScene(a.u, -RS * 1.006), toScene(b.u, -RS * 1.006), c, good ? 0.55 : 0.45);
  }
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  const K = marks.geometry.attributes; let np = 0;
  const mk = (u, c, size) => { const p = toScene(u, RS * 1.01); for (let j = 0; j < 3; j++) { K.position.array[3 * np + j] = p[j]; K.aColor.array[3 * np + j] = c[j]; } K.aAlpha.array[np] = 1; K.aSize.array[np] = size; np++; };
  if (M.best) mk(M.best.u, COL.cyan, 1.05);
  if (M.fidDir) mk(M.fidDir, WHITE, 0.95);
  if (M.comp && Math.abs(M.x - M.comp.x) < 1e-9 && M.mode === 'one') mk(unit(M.comp.v), GOLD, 0.95);
  for (let i = np; i < MK_MAX; i++) K.aAlpha.array[i] = 0;
  for (const a of [K.position, K.aColor, K.aAlpha, K.aSize]) a.needsUpdate = true;
  const sc = renderer.getPixelRatio() * (stage.clientHeight / 600);
  dotsMesh.material.uniforms.uScale.value = 60 * sc; marks.material.uniforms.uScale.value = 60 * sc;
}

/* =====================================================================
   6. Camera
   ===================================================================== */
function updateCamera(dtSec) {
  const k = reduceMotion ? 1 : 1 - Math.pow(0.001, dtSec);
  cam.theta += (cam.tTheta - cam.theta) * k; cam.phi += (cam.tPhi - cam.phi) * k; cam.r += (cam.tR - cam.r) * k;
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.4 : 1);
  camera.position.set(r * sp * Math.sin(cam.theta), r * Math.cos(cam.phi), r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(0, 0, 0);
}
/* "focus" looks straight at the centre of the x-ring from close by */
function camTarget(nm) {
  if (nm !== 'focus') return CAMS[nm];
  const M = MODEL, c = M.ring.length ? unit(M.ring.reduce((s, r) => s.map((x, i) => x + r.u[i] * Math.sign(dot(r.u, M.ring[0].u) || 1)), [0, 0, 0])) : M.B[0].a;
  const p = toScene(c, 1);
  return [Math.atan2(p[0], p[2]), Math.acos(Math.max(-1, Math.min(1, p[1]))), 4.3];
}
let camName = 'iso';
function setCamPreset(nm) {
  const p = camTarget(nm); if (!p) return; camName = nm;
  let d = (p[0] - cam.theta) % (Math.PI * 2);
  if (d > Math.PI) d -= Math.PI * 2; if (d < -Math.PI) d += Math.PI * 2;
  cam.tTheta = cam.theta + d; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, p[1])); cam.tR = p[2];
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
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(24, Math.max(3.2, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi; camName = '';
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(24, Math.max(3.2, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

/* =====================================================================
   7. Tags
   ===================================================================== */
const tagPool = [];
function tagAt(k, cls) { while (tagPool.length <= k) { const el = document.createElement('div'); el.className = 'tag raw'; tagsBox.appendChild(el); tagPool.push(el); } const el = tagPool[k]; el.className = 'tag raw ' + cls; return el; }
function placeTag(el, p) {
  if (!glOK) { el.style.display = 'none'; return; }
  const q = proj3(p); if (q.z > 1 || q.z < -1) { el.style.display = 'none'; return; }
  /* hide labels on the far side of the sphere */
  const c = camera.position, toCam = [c.x - p[0], c.y - p[1], c.z - p[2]], nrm = Math.hypot(...p);
  if (nrm > 0 && nrm < RS * 1.2 && dot(p, toCam) < 0) { el.style.display = 'none'; return; }
  el.style.display = 'block';
  const w = el.offsetWidth, h = el.offsetHeight, Wd = stage.clientWidth, Hd = stage.clientHeight, hud = document.querySelector('.hud-tl'), top = hud.offsetTop + hud.offsetHeight + 4;
  el.style.left = Math.min(Wd - w / 2 - 6, Math.max(w / 2 + 6, q.x)) + 'px'; el.style.top = Math.min(Hd - h / 2 - 6, Math.max(top + h / 2, q.y)) + 'px';
}
function updateTags() {
  const M = MODEL; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  M.B.forEach((b, i) => put(`a${SUB[i]} · p/q = ${f3(b.p / b.q)}`, toScene(b.a, 1.42 * RS), 'w'));
  if (M.best) put(T(M.mode === 'one' ? '最优 v' : '最优 w', M.mode === 'one' ? 'best v' : 'best w'), toScene(M.best.u, RS * 1.1), 'cy');
  if (M.comp && Math.abs(M.x - M.comp.x) < 1e-9 && M.mode === 'one') put('Lean F', toScene(unit(M.comp.v), RS * 1.1).map((x, i) => (i === 1 ? x - 0.22 : x)), 'gd');
  for (let i = k; i < tagPool.length; i++) tagPool[i].style.display = 'none';
}

/* =====================================================================
   8. 2D panels
   ===================================================================== */
function frame2d(cv, pl0 = 46) {
  const dpr = fitCanvas(cv), ctx = cv.getContext('2d'), Wd = cv.width, Hh = cv.height;
  ctx.clearRect(0, 0, Wd, Hh);
  const pl = pl0 * dpr, pr = 14 * dpr, pt = 12 * dpr, pb = 22 * dpr;
  ctx.font = `${9.5 * dpr}px ${TRV.fonts.data}`;
  return { dpr, ctx, W: Wd, Hh, pl, pt, iw: Wd - pl - pr, ih: Hh - pt - pb };
}
function lab(ctx, txt, x, y, al, bl, c = DIM) { ctx.fillStyle = c; ctx.textAlign = al; ctx.textBaseline = bl; ctx.fillText(txt, x, y); }
const disc = (ctx, x, y, r, c) => { ctx.fillStyle = c; ctx.beginPath(); ctx.arc(x, y, r, 0, 2 * Math.PI); ctx.fill(); };
/* the ROC plane: optimal curve, fidelity polyline, the current false-positive rate */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 40); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, X = (x) => pl + iw * x, Y = (y) => pt + ih * (1 - y);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.strokeRect(X(0), Y(1), iw, ih);
  ctx.setLineDash([3 * dpr, 4 * dpr]); ctx.beginPath(); ctx.moveTo(X(0), Y(0)); ctx.lineTo(X(1), Y(1)); ctx.stroke(); ctx.setLineDash([]);
  ctx.strokeStyle = CY; ctx.lineWidth = 2 * dpr; ctx.beginPath(); M.curve.xs.forEach((x, i) => (i ? ctx.lineTo(X(x), Y(M.curve.ys[i])) : ctx.moveTo(X(x), Y(M.curve.ys[i])))); ctx.stroke();
  ctx.strokeStyle = INK; ctx.lineWidth = 1.2 * dpr; ctx.beginPath(); M.Q.forEach((x, k) => (k ? ctx.lineTo(X(x), Y(M.Pc[k])) : ctx.moveTo(X(x), Y(M.Pc[k])))); ctx.stroke();
  M.Q.forEach((x, k) => { disc(ctx, X(x), Y(M.Pc[k]), 3 * dpr, INK); if (k === 1 || k === 2) lab(ctx, `(Q${SUB[k]}, P${SUB[k]})`, X(x) + 6 * dpr, Y(M.Pc[k]) + 4 * dpr, 'left', 'top', INK); });
  ctx.strokeStyle = AM; ctx.lineWidth = 1 * dpr; ctx.beginPath(); ctx.moveTo(X(M.x), Y(0)); ctx.lineTo(X(M.x), Y(1)); ctx.stroke();
  disc(ctx, X(M.x), Y(M.ystar), 3.5 * dpr, CY);
  if (M.comp) disc(ctx, X(M.comp.x), Y(M.comp.y), 3 * dpr, GOLDC);
  lab(ctx, T('假阳性 x = tr Fρ', 'false positive x = tr Fρ'), X(0.5), pt + ih + 5 * dpr, 'center', 'top');
  lab(ctx, '1', X(1), pt + ih + 5 * dpr, 'right', 'top'); lab(ctx, '0', X(0) - 4 * dpr, Y(0), 'right', 'middle'); lab(ctx, '1', X(0) - 4 * dpr, Y(1), 'right', 'middle');
  ctx.save(); ctx.translate(pl - 26 * dpr, Y(0.5)); ctx.rotate(-Math.PI / 2); lab(ctx, T('真阳性 tr Fσ', 'true positive tr Fσ'), 0, 0, 'center', 'middle'); ctx.restore();
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('最优 ROC', 'optimal ROC')}</span><span class="it"><i class="sw" style="--c:${INK}"></i>${T('保真度测量的折线', 'fidelity polyline')}</span>${M.comp ? `<span class="it"><i class="sw" style="--c:${GOLDC}"></i>${T('Lean 的 F', 'Lean’s F')}</span>` : ''}`;
}
/* the gap y*(x) − L(x) between the optimal curve and the fidelity polyline, magnified */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 52); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, g = M.curve.xs.map((x, i) => M.curve.ys[i] - polyAt(M.Q, M.Pc, x));
  /* square-root scale, so that the gaps at the cumulative points stay visible next to the larger gaps on the segments */
  const vmax = Math.max(...M.gaps, M.comp ? M.comp.y - M.Pc[1] : 0), gmax = Math.max(...g, vmax);
  const top = gmax > 1e-9 ? gmax * 1.12 : 1e-3;
  const X = (x) => pl + iw * x, Y = (v) => pt + ih * (1 - Math.sqrt(Math.max(0, v) / top));
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(X(0), Y(0)); ctx.lineTo(X(1), Y(0)); ctx.stroke();
  (gmax > 1e-9 ? [gmax, ...(vmax < gmax * 0.6 ? [vmax] : [])] : []).forEach((v) => { ctx.setLineDash([2 * dpr, 4 * dpr]); ctx.beginPath(); ctx.moveTo(X(0), Y(v)); ctx.lineTo(X(1), Y(v)); ctx.stroke(); ctx.setLineDash([]); lab(ctx, sci(v), pl - 4 * dpr, Y(v), 'right', 'middle'); });
  lab(ctx, '0', pl - 4 * dpr, Y(0), 'right', 'middle');
  ctx.fillStyle = 'rgba(25,240,255,0.22)'; ctx.strokeStyle = CY; ctx.lineWidth = 1.6 * dpr; ctx.beginPath(); ctx.moveTo(X(0), Y(0));
  g.forEach((v, i) => ctx.lineTo(X(M.curve.xs[i]), Y(v))); ctx.lineTo(X(1), Y(0)); ctx.closePath(); ctx.fill();
  ctx.beginPath(); g.forEach((v, i) => (i ? ctx.lineTo(X(M.curve.xs[i]), Y(v)) : ctx.moveTo(X(M.curve.xs[i]), Y(v)))); ctx.stroke();
  [1, 2].forEach((k) => { ctx.strokeStyle = INK; ctx.globalAlpha = 0.5; ctx.setLineDash([3 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(X(M.Q[k]), Y(0)); ctx.lineTo(X(M.Q[k]), Y(top)); ctx.stroke(); ctx.setLineDash([]); ctx.globalAlpha = 1; disc(ctx, X(M.Q[k]), Y(M.gaps[k - 1]), 3 * dpr, INK); lab(ctx, `Q${SUB[k]}`, X(M.Q[k]) + 4 * dpr, pt + 2 * dpr, 'left', 'top', INK); lab(ctx, sci(M.gaps[k - 1]), X(M.Q[k]) + 6 * dpr, Y(M.gaps[k - 1]) - 3 * dpr, 'left', 'bottom', INK); });
  if (M.comp) disc(ctx, X(M.comp.x), Y(M.comp.y - M.Pc[1]), 3.2 * dpr, GOLDC);
  ctx.strokeStyle = AM; ctx.lineWidth = 1 * dpr; ctx.beginPath(); ctx.moveTo(X(M.x), Y(0)); ctx.lineTo(X(M.x), Y(top)); ctx.stroke();
  disc(ctx, X(M.x), Y(M.gap), 3.5 * dpr, CY);
  lab(ctx, 'x', X(1), pt + ih + 5 * dpr, 'right', 'top');
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>y*(x) − L(x)${T('（√ 刻度）', ' (√ scale)')}</span>${M.comp ? `<span class="it"><i class="sw" style="--c:${GOLDC}"></i>${T('Lean 的 F：11/13820', 'Lean’s F: 11/13820')}</span>` : ''}<span class="it">· ${gmax > 1e-9 ? T(`累积点处最大 ${sci(Math.max(...M.gaps))}`, `max at Qₖ ${sci(Math.max(...M.gaps))}`) : T('处处为 0', '0 everywhere')}</span>`;
}

/* =====================================================================
   9. Readouts and controls
   ===================================================================== */
let syncedKey = '';
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const mat = (A, s) => A.map((r) => r.map((v) => f3(v * s)).join(' ')).join(' / ');
function readouts() {
  const M = MODEL, dv = M.d.map(f3).join(', ');
  pill('pillA', 'x', fx(M.x, 3)); pill('pillB', 'y*', fx(M.ystar, 5)); pill('pillC', T('差距', 'gap'), sci(M.gap)); pill('pillD', T('秩', 'rank'), String(M.rank));
  setRo([
    [T(`ε = ${f3(M.eps)} · D = diag(${dv}) · 20ρ · 20σ`, `ε = ${f3(M.eps)} · D = diag(${dv}) · 20ρ · 20σ`), `${mat(M.rho, 20)}  ·  ${mat(M.sigma, 20)}`],
    [T('有序本征基 a₀ a₁ a₂（按似然比排序）· 保真度观测量的本征值 · 似然比 p/q', 'Ordered eigenbasis a₀ a₁ a₂ (by likelihood ratio) · eigenvalues of the fidelity observable · likelihood ratios p/q'), `${M.B.map((b, i) => `a${SUB[i]} = e${SUB[ci(b.a)]}`).join(', ')} · ${M.B.map((b) => f3(b.m)).join(', ')} · ${M.B.map((b) => f3(b.p / b.q)).join(', ')}${M.degenerate ? T(' · 本征值重合，基不唯一', ' · degenerate, basis not unique') : ''}`],
    [T('累积点 (Q_k, P_k)', 'Cumulative points (Q_k, P_k)'), M.Q.map((q, k) => `(${f3(q)}, ${f3(M.Pc[k])})`).join(' · ')],
    [T('x 处：折线 L · 最优 y* · 差距 · 对偶 t* · 最优效应的秩', 'At x: polyline L · optimum y* · gap · dual t* · rank of the optimal effect'), `x = ${fx(M.x, 4)} · L = ${fx(M.L)} · y* = ${fx(M.ystar)} · ${sci(M.gap)} · t* = ${M.tstar.toFixed(4)} · ${M.rank}${M.tilt !== null ? T(` · 偏离 a 轴 ${M.tilt.toFixed(2)}°`, ` · ${M.tilt.toFixed(2)}° off the a-axis`) : ''}`],
    M.comp ? [T('Lean 的效应 F = vv†/1382，v = (37, 2, −3)', 'Lean’s effect F = vv†/1382, v = (37, 2, −3)'), `(1/10, 5539/13820) = (${fx(M.comp.x)}, ${fx(M.comp.y)}) · ${T('比 P₁ = 2/5 高', 'beats P₁ = 2/5 by')} 11/13820 ≈ ${sci(M.comp.y - 0.4)}`]
      : [T(M.mode === 'one' ? 'x 环上最好的秩 1 投影 vv† · 环上胜过折线的比例' : 'x 环上最好的秩 2 投影 I − ww† · 环上胜过折线的比例', M.mode === 'one' ? 'Best rank-1 projector vv† on the x-ring · share of the ring that beats the polyline' : 'Best rank-2 projector I − ww† on the x-ring · share of the ring that beats the polyline'), M.best ? `(${M.best.u.map((v) => v.toFixed(3)).join(', ')}) · ${fx(M.best.y)} · ${(100 * M.arcFrac).toFixed(1)}%` : T('环为空：没有这样的投影', 'empty ring: no such projector')]]);
  $('roNote').innerHTML = M.gaps[0] > 1e-9 || M.gaps[1] > 1e-9
    ? T(`Q₁ 与 Q₂ 处，最优曲线分别高出折线 ${sci(M.gaps[0])} 与 ${sci(M.gaps[1])}：保真度测量的累积点不在最优 ROC 上。`, `At Q₁ and Q₂ the optimal curve lies ${sci(M.gaps[0])} and ${sci(M.gaps[1])} above the polyline: the cumulative points of the fidelity measurement are not on the optimal ROC.`)
    : T('这里 ρ 与 σ 对易：折线与最优曲线重合，累积点都在最优 ROC 上。', 'Here ρ and σ commute: the polyline coincides with the optimal curve and the cumulative points lie on the optimal ROC.');
}
const stateKey = () => `${S.eps}|${S.lg0}|${S.lg2}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; }
  const M = MODEL, key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('epsIn').value = String(S.eps); $('epsOut').textContent = f3(S.eps);
  $('d0In').value = String(S.lg0); $('d0Out').textContent = f3(2 ** S.lg0);
  $('d2In').value = String(S.lg2); $('d2Out').textContent = f3(2 ** S.lg2);
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T(`ρ 的最小本征值 ${M.rhoEig[0].toFixed(4)}（必须为正）。σ = DρD / tr(DρD)，所以保真度观测量是 D/√tr(DρD)，它的本征基总是坐标基。`, `Smallest eigenvalue of ρ: ${M.rhoEig[0].toFixed(4)} (must be positive). σ = DρD / tr(DρD), so the fidelity observable is D/√tr(DρD) and its eigenbasis is always the coordinate basis.`);
  $('litNote').innerHTML = T('Lean 证明的是一个反例（ε = 1，D = diag(2, 1, ½)，第一个累积点）；最优值、差距与这一族的其他成员是页面数值。', 'Lean proves one counterexample (ε = 1, D = diag(2, 1, ½), the first cumulative point); the optimal values, the gaps and the rest of this family are page numbers.');
  $('c1Title').textContent = T('ROC 平面', 'The ROC plane');
  $('c2Title').textContent = T('最优曲线高出折线多少（放大）', 'How far the optimum lies above the polyline (magnified)');
  $('clock').innerHTML = `x = ${fx(M.x, 3)}`;
  $('hudBig').textContent = `x = ${fx(M.x, 3)} · y* − L = ${sci(M.gap)}`;
  $('hudSub').textContent = M.mode === 'one'
    ? T('球面上每个点是一个方向 v；青色处 vᵀ(σ − t*ρ)v > 0，品红处为负。白轴是保真度测量的有序本征基，琥珀轴是 σ − t*ρ 的本征向量。x 环：vᵀρv = x 的秩 1 投影 vv†，琥珀段胜过折线', 'Each point of the sphere is a direction v; cyan where vᵀ(σ − t*ρ)v > 0, magenta where it is negative. White axes: the ordered eigenbasis of the fidelity measurement; amber axes: eigenvectors of σ − t*ρ. The x-ring: rank-1 projectors vv† with vᵀρv = x, amber where they beat the polyline')
    : T('球面上每个点是一个方向 w；青色处 wᵀ(σ − t*ρ)w > 0，品红处为负。白轴是保真度测量的有序本征基，琥珀轴是 σ − t*ρ 的本征向量。x 环：wᵀρw = 1 − x 的秩 2 投影 I − ww†，琥珀段胜过折线', 'Each point of the sphere is a direction w; cyan where wᵀ(σ − t*ρ)w > 0, magenta where it is negative. White axes: the ordered eigenbasis of the fidelity measurement; amber axes: eigenvectors of σ − t*ρ. The x-ring: rank-2 projectors I − ww† with wᵀρw = 1 − x, amber where they beat the polyline');
}
function syncRail() {
  const M = MODEL, key = `${M.Q[1]}|${M.Q[2]}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 'x = 0'], [M.Q[1], `Q₁ = ${f3(M.Q[1])}`], [M.Q[2], `Q₂ = ${f3(M.Q[2])}`], [1, 'x = 1']];
  const low = marks.map(([f], i) => i > 0 && i < marks.length - 1 && (f - marks[i - 1][0] < 0.15 || marks[i + 1][0] - f < 0.15));
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}${low[i] ? ' low' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
const setT = (t, user) => { S.t = Math.min(1, Math.max(0, t)); $('now').value = S.t; dirty = true; if (user) { S.preset = null; markPreset(); } };
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { eps: p.eps, lg0: p.lg0, lg2: p.lg2, hold: 0 }); S.preset = nm; markPreset(); dirty = true;
  build(); setT(MODEL.Q[p.k]); build(); dirty = true;
  S.playing = false; S.dir = 1; setPlayUI();
  setCamPreset(camName === 'focus' ? 'focus' : 'iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; };
$('epsIn').addEventListener('input', () => { S.eps = parseFloat($('epsIn').value); custom(); });
$('d0In').addEventListener('input', () => { S.lg0 = parseFloat($('d0In').value); custom(); });
$('d2In').addEventListener('input', () => { S.lg2 = parseFloat($('d2In').value); custom(); });
document.querySelectorAll('#jumpChips [data-k]').forEach((b) => b.addEventListener('click', () => { if (dirty) build(); S.playing = false; setPlayUI(); setT(MODEL.Q[Number(b.dataset.k)], true); }));
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
const STEPX = 0.005;
document.addEventListener('keydown', (ev) => {
  if (ev.target && (ev.target.tagName === 'INPUT' && ev.target.type !== 'range')) return;
  if (drawer.isOpen()) return;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(Math.round((S.t + (ev.key === 'ArrowRight' ? STEPX : -STEPX)) * 1e6) / 1e6); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(1);
});

/* =====================================================================
   10. Main loop
   ===================================================================== */
let lastT = performance.now(), frameCount = 0, glKey = '';
function resize() {
  if (!glOK) return;
  const r = stage.getBoundingClientRect();
  renderer.setSize(Math.max(1, r.width), Math.max(1, r.height), false);
  camera.aspect = Math.max(0.2, r.width / Math.max(1, r.height)); camera.updateProjectionMatrix();
}
/* a full sweep of the false-positive axis takes SWEEP seconds at 1× */
const SWEEP = 16;
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) setT(S.dir > 0 ? 0 : 1); }
    else {
      const before = S.t;
      setT(S.t + S.dir * dtSec * S.speed / SWEEP);
      const M = MODEL;
      for (const k of [1, 2]) if ((before - M.Q[k]) * (S.t - M.Q[k]) <= 0 && before !== S.t) {
        const gp = M.gaps[k - 1];
        toast(gp > 1e-9 ? T(`<b>x = Q${SUB[k]} = ${f3(M.Q[k])}</b>：保真度测量的点比最优低 ${sci(gp)}。`, `<b>x = Q${SUB[k]} = ${f3(M.Q[k])}</b>: the fidelity point lies ${sci(gp)} below the optimum.`)
          : T(`<b>x = Q${SUB[k]} = ${f3(M.Q[k])}</b>：保真度测量的点在最优曲线上。`, `<b>x = Q${SUB[k]} = ${f3(M.Q[k])}</b>: the fidelity point is on the optimal curve.`));
      }
      if (S.t >= 1) S.hold = 2.4;
      if (S.t <= 0 && S.dir < 0) S.hold = 1.2;
    }
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    if (glKey !== String(MODEL.id)) { updateGL(); glKey = String(MODEL.id); if (camName === 'focus') setCamPreset('focus'); }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.ROC_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return JSON.parse(JSON.stringify({ eps: M.eps, d: M.d, rho: M.rho, sigma: M.sigma, M: M.M, m: M.m, degenerate: M.degenerate, ord: M.ord, basis: M.B.map((b) => ({ a: b.a, q: b.q, p: b.p })), Q: M.Q, P: M.Pc,
    x: M.x, L: M.L, ystar: M.ystar, tstar: M.tstar, gap: M.gap, rank: M.rank, Hw: M.EH.w, HV: M.EH.V, mode: M.mode, ring: M.ring.filter((_, i) => i % 6 === 0).map((r) => r.u), best: M.best, arcFrac: M.arcFrac,
    tilt: M.tilt, gaps: M.gaps, comp: M.comp, lean: M.lean, rhoEig: M.rhoEig, curve: M.curve.xs.filter((_, i) => i % 8 === 0).map((x, j) => [x, M.curve.ys[j * 8]]) })); },
  setT: (t) => setT(t),
  cam: () => camName
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('strong'); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 7.6; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
