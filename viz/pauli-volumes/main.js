/* PAULI//VOLUMES · volume ratios of generalized Pauli channels
   In ℝ^m with m = d + 1 and s = Σλᵢ: the box P (−1/(d−1) ≤ λᵢ ≤ 1), the completely positive region C (−1/(d−1) ≤ s ≤ 1 + dλⱼ for
   every j), G = C ∩ {λ ≥ 0} and E = G ∩ {s ≤ 1}. Frozen in trureturing: V_C/V_P = d/(d+1)!, V_G/V_C = ((d²−1)/d²)((d−1)/d)^d,
   V_E/V_G = 1/(d+1) for every d ≥ 2, through C = T_L(S), G = S ∪ T₁(S), E = S. The page draws the d = 2 solids, the d = 3
   slices λ₄ = t, and random-point estimates in higher d. Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Constants
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG, ok: OK } = TRV.palette;
const VIOLET = [0.62, 0.55, 1], GREY = [0.55, 0.6, 0.68];
const VI = '#9d8cff';
const MODES = ['solid', 'slice', 'sample'];
const RUN = { solid: 24, slice: 22, sample: 24 };
const NS = 30000, SHOW = 2600, TS = 150, D_MAX = 16;
const REGION_COL = { C: COL.cyan, G: COL.magenta, E: VIOLET };

/* =====================================================================
   2. The regions and their exact volumes
   ===================================================================== */
const fact = (n) => { let f = 1; for (let i = 2; i <= n; i++) f *= i; return f; };
const lowOf = (d) => -1 / (d - 1);
const Lof = (d) => d / (d - 1);
function exact(d) {
  const m = d + 1, L = Lof(d);
  return { r1: d / fact(d + 1), r2: ((d * d - 1) / (d * d)) * Math.pow((d - 1) / d, d), r3: 1 / (d + 1),
    P: Math.pow(L, m), C: d * Math.pow(L, m) / fact(m), G: (d + 1) / fact(m), E: 1 / fact(m) };
}
const sum = (x) => x.reduce((a, b) => a + b, 0);
const inP = (x, d) => x.every((v) => v >= lowOf(d) - 1e-12 && v <= 1 + 1e-12);
const inC = (x, d) => { const s = sum(x), mn = Math.min(...x); return s >= lowOf(d) - 1e-12 && s <= 1 + d * mn + 1e-12; };
const inG = (x, d) => inC(x, d) && x.every((v) => v >= -1e-12);
const inE = (x, d) => inG(x, d) && sum(x) <= 1 + 1e-12;
const unit = (m, i) => Array.from({ length: m }, (_, j) => (j === i ? 1 : 0));
const Tc = (t, c) => { const s = sum(t); return t.map((v) => 1 + c * (v - s)); };            // T_c(t) = u + c(t − (Σt)u)
function simplexVerts(d) {   // the three simplices behind the regions: S, T₁(S) and C = T_L(S)
  const m = d + 1, Sv = [Array(m).fill(0), ...Array.from({ length: m }, (_, i) => unit(m, i))];
  return { S: Sv, T1: Sv.map((t) => Tc(t, 1)), C: Sv.map((t) => Tc(t, Lof(d))) };
}

/* random points in three steps: the box (for V_C/V_P), C itself (for V_G/V_C), and the G-points among them (for V_E/V_G) */
function sampleAll(d) {
  const m = d + 1, lo = lowOf(d), L = Lof(d), rng = TRV.mulberry32(2020 + 97 * d);
  const cumA = new Int32Array(NS + 1), cumG = new Int32Array(NS + 1), cumE = new Int32Array(NS + 1), showA = [], showB = [];
  for (let i = 0; i < NS; i++) {
    const x = Array.from({ length: m }, () => lo + (1 - lo) * rng()), c = inC(x, d);
    cumA[i + 1] = cumA[i] + (c ? 1 : 0);
    if (i < SHOW) showA.push([x, !c ? 0 : !inG(x, d) ? 1 : !inE(x, d) ? 2 : 3]);
    const e = Array.from({ length: m + 1 }, () => -Math.log(1 - rng())), es = sum(e), t = e.slice(0, m).map((v) => v / es), y = Tc(t, L);
    const g = y.every((v) => v >= 0), ee = g && sum(y) <= 1;
    cumG[i + 1] = cumG[i] + (g ? 1 : 0); cumE[i + 1] = cumE[i] + (ee ? 1 : 0);
    if (i < SHOW) showB.push([y, !g ? 1 : !ee ? 2 : 3]);
  }
  return { cumA, cumG, cumE, showA, showB };
}

/* d = 3: sections of the simplices by λ₄ = t (one segment per triangular face that the hyperplane crosses) */
function section(verts, t) {
  const segs = [], tt = t + 1e-9, n = verts.length;
  const cut = (a, b) => { const s = (tt - a[3]) / (b[3] - a[3]); return [0, 1, 2].map((k) => a[k] + s * (b[k] - a[k])); };
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) for (let k = j + 1; k < n; k++) {
    const tri = [verts[i], verts[j], verts[k]], pts = [];
    for (const [a, b] of [[0, 1], [1, 2], [0, 2]]) { const p = tri[a], q = tri[b]; if ((p[3] - tt) * (q[3] - tt) < 0) pts.push(cut(p, q)); }
    if (pts.length === 2) segs.push(pts);
  }
  return segs;
}
/* the exact volume of a simplex section: its facets (4 of the 5 vertices) cut the hyperplane in polygons; ordering each polygon
   around its centre and fanning to the centre of the whole section splits the convex section into tetrahedra */
function sectionVolume(verts, t) {
  const tt = t + 1e-9, n = verts.length, cut = (a, b) => { const s = (tt - a[3]) / (b[3] - a[3]); return [0, 1, 2].map((k) => a[k] + s * (b[k] - a[k])); };
  const all = [];
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if ((verts[i][3] - tt) * (verts[j][3] - tt) < 0) all.push(cut(verts[i], verts[j]));
  if (all.length < 4) return 0;
  const c = [0, 1, 2].map((k) => all.reduce((a, p) => a + p[k], 0) / all.length);
  const sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]], cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]], dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  let vol = 0;
  for (let omit = 0; omit < n; omit++) {
    const f = verts.filter((_, i) => i !== omit), poly = [];
    for (let i = 0; i < f.length; i++) for (let j = i + 1; j < f.length; j++) if ((f[i][3] - tt) * (f[j][3] - tt) < 0) poly.push(cut(f[i], f[j]));
    if (poly.length < 3) continue;
    const pc = [0, 1, 2].map((k) => poly.reduce((a, p) => a + p[k], 0) / poly.length), nrm = cross(sub(poly[1], poly[0]), sub(poly[2], poly[0]));
    const e1 = sub(poly[0], pc), e2 = cross(nrm, e1);
    poly.sort((a, b) => Math.atan2(dot(sub(a, pc), e2), dot(sub(a, pc), e1)) - Math.atan2(dot(sub(b, pc), e2), dot(sub(b, pc), e1)));
    for (let i = 1; i + 1 < poly.length; i++) vol += Math.abs(dot(sub(poly[0], c), cross(sub(poly[i], c), sub(poly[i + 1], c)))) / 6;
  }
  return vol;
}
let SLICE = null;
function sliceVolumes() {   // λ₄ = t on TS + 1 values; exact section volumes, integrated over t by the midpoint rule
  if (SLICE) return SLICE;
  const d = 3, lo = lowOf(d), V = simplexVerts(d), ts = [], vC = [], vG = [], vE = [];
  for (let k = 0; k <= TS; k++) {
    const t = lo + (1 - lo) * k / TS, e = sectionVolume(V.S, t);
    ts.push(t); vC.push(sectionVolume(V.C, t)); vG.push(e + sectionVolume(V.T1, t)); vE.push(e);
  }
  // the section volumes jump where a facet lies in λ₄ = t (S has the facet λ₄ = 0), so the integral uses the midpoint rule
  const NI = 1200, h = (1 - lo) / NI; let iC = 0, iG = 0, iE = 0;
  for (let k = 0; k < NI; k++) { const t = lo + (k + 0.5) * h, e = sectionVolume(V.S, t); iC += h * sectionVolume(V.C, t); iG += h * (e + sectionVolume(V.T1, t)); iE += h * e; }
  SLICE = { ts, vC, vG, vE, iC, iG, iE };
  return SLICE;
}

/* =====================================================================
   3. State and presets
   ===================================================================== */
const S = { mode: 'solid', d: 5, focus: 'C', nowFrac: 0, playing: true, dir: 1, speed: 1, hold: 0, preset: 'tetra' };
const PRESETS = {
  tetra: { mode: 'solid', focus: 'C', frac: 0, play: true,
    zh: 'd = 2：三个特征值 (λ₁, λ₂, λ₃)。盒子 P 是立方体 [−1, 1]³；完全正区域 C 是顶点为 (1, 1, 1)、(1, −1, −1)、(−1, 1, −1)、(−1, −1, 1) 的四面体，体积 8/3，恰是盒子的 1/3 = d/(d + 1)!。时间轴往盒子里撒点，落进 C 的比例收敛到 1/3。',
    en: 'd = 2: three eigenvalues (λ₁, λ₂, λ₃). The box P is the cube [−1, 1]³; the completely positive region C is the tetrahedron with vertices (1, 1, 1), (1, −1, −1), (−1, 1, −1), (−1, −1, 1), of volume 8/3, exactly 1/3 = d/(d + 1)! of the box. The timeline scatters points in the box, and the share landing in C converges to 1/3.' },
  bipyramid: { mode: 'solid', focus: 'G', frac: 1, play: false,
    zh: 'G = C 中特征值都非负的部分。它由两块四面体拼成：标准单纯形 S 与 T₁(S)，共用由三个单位向量张成的那个面（冻结引理 generator_eq_union）。体积 1/6 + 1/3 = 1/2，占 C 的 3/16 = (3/4)(1/2)²。',
    en: 'G is the part of C where every eigenvalue is nonnegative. It is made of two tetrahedra, the standard simplex S and T₁(S), sharing the face spanned by the three unit vectors (the frozen lemma generator_eq_union). Its volume is 1/6 + 1/3 = 1/2, which is 3/16 = (3/4)(1/2)² of C.' },
  simplex: { mode: 'solid', focus: 'E', frac: 1, play: false,
    zh: 'E = G 中 s = λ₁ + λ₂ + λ₃ ≤ 1 的部分，恰好就是标准单纯形 S（冻结引理 eb_eq_standard），体积 1/6，占 G 的 1/3 = 1/(d + 1)。',
    en: 'E is the part of G with s = λ₁ + λ₂ + λ₃ ≤ 1, and it is exactly the standard simplex S (the frozen lemma eb_eq_standard), of volume 1/6, which is 1/3 = 1/(d + 1) of G.' },
  slice: { mode: 'slice', focus: 'C', frac: 0, play: true,
    zh: 'd = 3：区域在四维里。固定第四个特征值 λ₄ = t，从 −1/2 扫到 1，画出每个区域与这个超平面的截面：青 = C，品红 = G 中的 T₁(S) 部分，紫 = E = S。左下图是截面体积，对 t 积分就是四维体积。',
    en: 'd = 3: the regions live in four dimensions. Fix the fourth eigenvalue λ₄ = t, sweep it from −1/2 to 1, and draw each region’s section by that hyperplane: cyan = C, magenta = the T₁(S) part of G, violet = E = S. The lower left chart shows the section volumes, whose integral over t is the four-dimensional volume.' },
  sample5: { mode: 'sample', d: 5, focus: 'G', frac: 0, play: true,
    zh: 'd = 5：六个特征值。三维里画的是 C 中随机点的前三个坐标（品红 = 落进 G，紫 = 落进 E）。左下图是三个比值的随机估计除以冻结公式的值，随点数增加收敛到 1。',
    en: 'd = 5: six eigenvalues. The 3D view shows the first three coordinates of random points in C (magenta = in G, violet = in E). The lower left chart divides the three random estimates by the frozen formulas; they converge to 1 as points accumulate.' },
  limit: { mode: 'sample', d: 6, focus: 'G', frac: 1, play: false,
    zh: '右下图是三个公式对 d = 2 … 16。第一个比值 d/(d + 1)! 迅速变小，第三个按 1/(d + 1) 变小；第二个随 d 增加，从下方逼近 1/e ≈ 0.3679（卷宗里的论证，未形式化）。',
    en: 'The lower right chart plots the three formulas for d = 2 … 16. The first ratio d/(d + 1)! shrinks fast and the third shrinks like 1/(d + 1); the second increases with d and approaches 1/e ≈ 0.3679 from below (argued in the dossier, not formalized).' }
};

/* =====================================================================
   4. The model
   ===================================================================== */
let MODEL = null, dirty = true;
const sampleCache = new Map();
function build() {
  const d = S.mode === 'solid' ? 2 : S.mode === 'slice' ? 3 : S.d;
  if (!sampleCache.has(d)) sampleCache.set(d, sampleAll(d));
  const M = { mode: S.mode, d, focus: S.focus, ex: exact(d), smp: sampleCache.get(d), verts: simplexVerts(d) };
  if (S.mode === 'slice') M.slice = sliceVolumes();
  MODEL = M;
}
function progress() {
  const M = MODEL;
  if (M.mode === 'slice') {
    const k = Math.round(S.nowFrac * TS), sl = M.slice, t = sl.ts[k];
    return { t, k, vC: sl.vC[k], vG: sl.vG[k], vE: sl.vE[k], segC: section(M.verts.C, t), segS: section(M.verts.S, t), segT: section(M.verts.T1, t) };
  }
  const n = Math.max(1, Math.round(S.nowFrac * NS)), sm = M.smp;
  const eA = sm.cumA[n] / n, eB = sm.cumG[n] / n, eC = sm.cumG[n] ? sm.cumE[n] / sm.cumG[n] : NaN;
  return { n, eA, eB, eC, hitsC: sm.cumA[n], hitsG: sm.cumG[n], hitsE: sm.cumE[n] };
}

/* =====================================================================
   5. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const fmtN = (n) => n.toLocaleString('en-US');
const fr = (x, d = 6) => (isFinite(x) ? x.toFixed(d) : '—');

/* =====================================================================
   6. 3D scene
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 20000, PTS_MAX = 6000;
const CAMS = { iso: [0.75, 1.12, 15], front: [0.0001, 1.5707, 15], diag: [0.7854, 0.9553, 15] };
const cam = { theta: 0.75, phi: 1.12, r: 15, tTheta: 0.75, tPhi: 1.12, tR: 15 };
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
/* λ = (λ₁, λ₂, λ₃) ↦ scene: λ₁ across, λ₃ up, λ₂ towards the viewer; the box [lo, 1]³ is centred and scaled to side 7 */
const toScene = (x, d) => { const lo = lowOf(d), c = (1 + lo) / 2, k = 7 / (1 - lo); return [(x[0] - c) * k, (x[2] - c) * k, (x[1] - c) * k]; };
function cubeEdges(d) { const lo = lowOf(d), v = [lo, 1], out = []; for (const a of v) for (const b of v) { out.push([[lo, a, b], [1, a, b]], [[a, lo, b], [a, 1, b]], [[a, b, lo], [a, b, 1]]); } return out; }
const pairs = (vs, skip = []) => { const out = []; for (let i = 0; i < vs.length; i++) for (let j = i + 1; j < vs.length; j++) if (!skip.some(([a, b]) => (a === i && b === j))) out.push([vs[i], vs[j]]); return out; };
function updateGL() {
  const M = MODEL, pr = progress(), d = M.d;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (a, b, col, k) => { if (v + 2 > LINES_MAX) return; for (const p of [a, b]) { Pp[3 * v] = p[0]; Pp[3 * v + 1] = p[1]; Pp[3 * v + 2] = p[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, a, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = a; PT.aSize.array[np] = size; np++; };
  const kFor = (r) => (M.focus === r ? 1 : 0.35);
  for (const [a, b] of cubeEdges(d)) seg(toScene(a, d), toScene(b, d), GREY, 0.35);
  if (M.mode === 'solid') {
    const V = M.verts, cv = V.C.map((x) => toScene(x, d)), sv = V.S.map((x) => toScene(x, d)), tv = V.T1.map((x) => toScene(x, d));
    for (const [a, b] of pairs(cv)) seg(a, b, REGION_COL.C, kFor('C'));
    for (const [a, b] of pairs(tv)) seg(a, b, REGION_COL.G, kFor('G'));
    for (const [a, b] of pairs(sv)) seg(a, b, M.focus === 'G' ? REGION_COL.G : REGION_COL.E, M.focus === 'G' ? 1 : kFor('E'));
    const cls = [GREY, COL.cyan, COL.magenta, VIOLET];
    M.smp.showA.forEach(([x, c], i) => { if (i < pr.n) dot(toScene(x, d), cls[c], c ? 0.85 : 0.25, c ? 0.9 : 0.6); });
    for (const p of cv) dot(p, REGION_COL.C, 1, 2.2);
    dot(toScene([1, 1, 1], d), COL.amber, 1, 2.6);
  } else if (M.mode === 'slice') {
    const sc = (p) => toScene(p, 3);
    for (const [a, b] of pr.segC) seg(sc(a), sc(b), REGION_COL.C, kFor('C'));
    for (const [a, b] of pr.segT) seg(sc(a), sc(b), REGION_COL.G, kFor('G'));
    for (const [a, b] of pr.segS) seg(sc(a), sc(b), M.focus === 'G' ? REGION_COL.G : REGION_COL.E, M.focus === 'G' ? 1 : kFor('E'));
    for (const [a, b] of [...pr.segC, ...pr.segS, ...pr.segT]) { dot(sc(a), COL.amber, 0.7, 1); dot(sc(b), COL.amber, 0.7, 1); }
  } else {
    const cls = [GREY, COL.cyan, COL.magenta, VIOLET];
    M.smp.showB.forEach(([x, c], i) => { if (i < pr.n) dot(toScene(x, d), cls[c], c === 1 ? 0.35 : 0.9, c === 1 ? 0.6 : 0.95); });
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
  if (drag.pts.size === 2) { const [a, b] = [...drag.pts.values()], d = Math.hypot(a.x - b.x, a.y - b.y); if (drag.pinch > 0) cam.tR = Math.min(30, Math.max(6, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(30, Math.max(6, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

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
  const M = MODEL, pr = progress(), d = M.d; let k = 0;
  const put = (text, x, cls, lift = 0.35) => { const el = tagAt(k++, cls); el.textContent = text; const p = toScene(x, d); p[1] += lift; placeTag(el, p); };
  const lo = lowOf(d);
  put('λ₁', [1.15, lo, lo], 'cy', 0); put('λ₂', [lo, 1.15, lo], 'cy', 0); put('λ₃', [lo, lo, 1.12], 'cy', 0);
  if (M.mode === 'solid') {
    put('(1, 1, 1)', [1, 1, 1], 'hot'); put('(1, −1, −1)', [1, -1, -1], 'cy'); put('(−1, 1, −1)', [-1, 1, -1], 'cy'); put('(−1, −1, 1)', [-1, -1, 1], 'cy');
    put('0', [0, 0, 0], 'vi', -0.4);
  } else if (M.mode === 'slice') {
    put(`λ₄ = ${pr.t.toFixed(3)}`, [1, lo, 1], 'hot', 0.6);
  } else {
    put(T(`C 中的随机点，d = ${d}`, `random points in C, d = ${d}`), [1, lo, 1], 'cy', 0.6);
  }
  for (let i = k; i < tagPool.length; i++) tagPool[i].style.display = 'none';
}

/* =====================================================================
   9. 2D panels
   ===================================================================== */
function frame2d(cv, pl0 = 46) {
  const dpr = fitCanvas(cv), ctx = cv.getContext('2d'), Wd = cv.width, Hh = cv.height;
  ctx.clearRect(0, 0, Wd, Hh);
  const pl = pl0 * dpr, pr = 12 * dpr, pt = 10 * dpr, pb = 20 * dpr;
  ctx.font = `${9.5 * dpr}px ${TRV.fonts.data}`;
  return { dpr, ctx, W: Wd, Hh, pl, pt, iw: Wd - pl - pr, ih: Hh - pt - pb };
}
function lab(ctx, txt, x, y, al, bl) { ctx.fillStyle = DIM; ctx.textAlign = al; ctx.textBaseline = bl; ctx.fillText(txt, x, y); }
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 40); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress();
  if (M.mode === 'slice') {
    const sl = M.slice, top = Math.max(...sl.vC) * 1.1, lo = lowOf(3), X = (t) => pl + iw * (t - lo) / (1 - lo), Y = (v) => pt + ih - ih * v / top;
    for (const [arr, col] of [[sl.vC, CY], [sl.vG, MG], [sl.vE, VI]]) { ctx.strokeStyle = col; ctx.lineWidth = 1.6 * dpr; ctx.beginPath(); arr.forEach((v, k) => { const x = X(sl.ts[k]), y = Y(v); if (k) ctx.lineTo(x, y); else ctx.moveTo(x, y); }); ctx.stroke(); }
    ctx.lineWidth = 1; ctx.strokeStyle = AM; ctx.beginPath(); ctx.moveTo(X(pr.t), pt); ctx.lineTo(X(pr.t), pt + ih); ctx.stroke();
    lab(ctx, 't = −1/2', X(lo), pt + ih + 4 * dpr, 'left', 'top'); lab(ctx, '0', X(0), pt + ih + 4 * dpr, 'center', 'top'); lab(ctx, 't = 1', X(1), pt + ih + 4 * dpr, 'right', 'top');
    lab(ctx, top.toFixed(2), pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, '0', pl - 4 * dpr, pt + ih, 'right', 'middle');
    $('c1Meta').textContent = T('截面体积：青 = C，品红 = G，紫 = E；琥珀 = 当前的 t', 'section volumes: cyan = C, magenta = G, violet = E; amber = the current t');
  } else {
    const n = pr.n, x0 = Math.log10(10), Xl = (k) => pl + iw * (Math.log10(Math.max(10, k)) - x0) / (Math.log10(NS) - x0), Y = (q) => pt + ih / 2 - (ih / 2) * Math.max(-1, Math.min(1, (q - 1) / 0.3));
    ctx.strokeStyle = OK; ctx.lineWidth = 1.2 * dpr; ctx.beginPath(); ctx.moveTo(pl, Y(1)); ctx.lineTo(pl + iw, Y(1)); ctx.stroke(); ctx.lineWidth = 1;
    const sm = M.smp, ex = M.ex;
    const curve = (fn, col) => { ctx.strokeStyle = col; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); let first = true; for (let j = 0; j <= 220; j++) { const k = Math.round(Math.pow(10, x0 + (Math.log10(n) - x0) * j / 220)); if (k < 10) continue; const q = fn(k); if (!isFinite(q)) continue; const x = Xl(k), y = Y(q); if (first) { ctx.moveTo(x, y); first = false; } else ctx.lineTo(x, y); } ctx.stroke(); ctx.lineWidth = 1; };
    curve((k) => sm.cumA[k] / k / ex.r1, CY); curve((k) => sm.cumG[k] / k / ex.r2, MG); curve((k) => (sm.cumG[k] ? sm.cumE[k] / sm.cumG[k] : NaN) / ex.r3, VI);
    ctx.strokeStyle = AM; ctx.beginPath(); ctx.moveTo(Xl(n), pt); ctx.lineTo(Xl(n), pt + ih); ctx.stroke();
    lab(ctx, '1.3', pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, '1', pl - 4 * dpr, Y(1), 'right', 'middle'); lab(ctx, '0.7', pl - 4 * dpr, pt + ih, 'right', 'bottom');
    lab(ctx, 'n=10', Xl(10), pt + ih + 4 * dpr, 'left', 'top'); lab(ctx, 'n=1000', Xl(1000), pt + ih + 4 * dpr, 'center', 'top'); lab(ctx, `n=${fmtN(NS)}`, Xl(NS), pt + ih + 4 * dpr, 'right', 'top');
    $('c1Meta').textContent = T('随机估计 ÷ 冻结公式：青 = V_C/V_P，品红 = V_G/V_C，紫 = V_E/V_G；绿 = 1', 'random estimate ÷ frozen formula: cyan = V_C/V_P, magenta = V_G/V_C, violet = V_E/V_G; green = 1');
  }
}
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 34); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F;
  const lmin = -14, X = (d) => pl + iw * (d - 2) / (D_MAX - 2), Y = (r) => pt + ih - ih * (Math.log10(r) - lmin) / (0 - lmin);
  for (const e of [0, -4, -8, -12]) { ctx.strokeStyle = FAINT; ctx.beginPath(); ctx.moveTo(pl, Y(Math.pow(10, e))); ctx.lineTo(pl + iw, Y(Math.pow(10, e))); ctx.stroke(); lab(ctx, `10${e ? '⁻' + String(-e).split('').map((c) => '⁰¹²³⁴⁵⁶⁷⁸⁹'[+c]).join('') : '⁰'}`, pl - 4 * dpr, Y(Math.pow(10, e)), 'right', 'middle'); }
  ctx.strokeStyle = VI; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(pl, Y(1 / Math.E)); ctx.lineTo(pl + iw, Y(1 / Math.E)); ctx.stroke(); ctx.setLineDash([]);
  for (const [key, col] of [['r1', CY], ['r2', MG], ['r3', VI]]) {
    ctx.strokeStyle = col; ctx.lineWidth = 1.5 * dpr; ctx.beginPath();
    for (let d = 2; d <= D_MAX; d++) { const x = X(d), y = Y(exact(d)[key]); if (d === 2) ctx.moveTo(x, y); else ctx.lineTo(x, y); }
    ctx.stroke(); ctx.lineWidth = 1;
    for (let d = 2; d <= D_MAX; d++) { ctx.fillStyle = d === M.d ? AM : col; ctx.beginPath(); ctx.arc(X(d), Y(exact(d)[key]), (d === M.d ? 3.4 : 1.8) * dpr, 0, 2 * Math.PI); ctx.fill(); }
  }
  for (const d of [2, 6, 10, 16]) lab(ctx, `d=${d}`, X(d), pt + ih + 4 * dpr, d === 2 ? 'left' : d === D_MAX ? 'right' : 'center', 'top');
  $('c2Meta').textContent = T('冻结公式（对数纵轴）：青 = d/(d + 1)!，品红 = ((d² − 1)/d²)((d − 1)/d)^d，紫 = 1/(d + 1)；紫虚线 = 1/e；琥珀 = 当前的 d', 'frozen formulas (log scale): cyan = d/(d + 1)!, magenta = ((d² − 1)/d²)((d − 1)/d)^d, violet = 1/(d + 1); violet dashes = 1/e; amber = the current d');
}

/* =====================================================================
   10. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const fracStr = { 2: ['1/3', '3/16', '1/3'], 3: ['1/8', '64/243', '1/4'], 4: ['1/30', '1215/4096', '1/5'], 5: ['1/144', '24576/78125', '1/6'], 6: ['1/840', '546875/1679616', '1/7'] };
function readouts() {
  const M = MODEL, pr = progress(), ex = M.ex, d = M.d, fs = fracStr[d] || ['', '', ''];
  if (M.mode === 'slice') {
    const sl = M.slice;
    setRo([[T('维数 d · 坐标数 m', 'Dimension d · coordinates m'), `d = 3 · m = 4`], [T('切片位置 λ₄ = t', 'Slice position λ₄ = t'), pr.t.toFixed(4)],
      [T('截面体积 C · G · E', 'Section volumes C · G · E'), `${pr.vC.toFixed(4)} · ${pr.vG.toFixed(4)} · ${pr.vE.toFixed(4)}`],
      [T('∫ 截面 dt 与四维体积（C）', '∫ section dt against the 4D volume (C)'), `${sl.iC.toFixed(4)} · ${ex.C.toFixed(4)}`],
      [T('∫ 截面 dt 与四维体积（G · E）', '∫ section dt against the 4D volume (G · E)'), `${sl.iG.toFixed(4)} · ${ex.G.toFixed(4)} | ${sl.iE.toFixed(4)} · ${ex.E.toFixed(4)}`]]);
    pill('pillA', 'd', '3'); pill('pillB', 'λ₄', pr.t.toFixed(3)); pill('pillC', 'V_G/V_C', fs[1]); pill('pillD', T('截面线段', 'SEGMENTS'), String(pr.segC.length + pr.segS.length + pr.segT.length));
    $('roNote').innerHTML = T(`四维体积来自冻结的公式：Leb(C) = dLᵐ/m! = ${ex.C.toFixed(4)}，Leb(G) = (d + 1)/m! = 1/6，Leb(E) = 1/m! = 1/24；截面体积由截面多面体的顶点精确算出，对 t 用中点法积分。`, `The 4D volumes come from the frozen formulas: Leb(C) = dLᵐ/m! = ${ex.C.toFixed(4)}, Leb(G) = (d + 1)/m! = 1/6, Leb(E) = 1/m! = 1/24; the section volumes are computed exactly from the vertices of the sections and integrated over t by the midpoint rule.`);
  } else {
    setRo([[T('维数 d · 坐标数 m · 取点数', 'Dimension d · coordinates m · points'), `d = ${d} · m = ${d + 1} · n = ${fmtN(pr.n)}`],
      [T('V_C/V_P：公式 · 随机估计', 'V_C/V_P: formula · random estimate'), `${fs[0]} = ${fr(ex.r1)} · ${fr(pr.eA)}`],
      [T('V_G/V_C：公式 · 随机估计', 'V_G/V_C: formula · random estimate'), `${fs[1]} = ${fr(ex.r2)} · ${fr(pr.eB)}`],
      [T('V_E/V_G：公式 · 随机估计', 'V_E/V_G: formula · random estimate'), `${fs[2]} = ${fr(ex.r3)} · ${fr(pr.eC)}`],
      [T('体积 Leb(P) · Leb(C) · Leb(G) · Leb(E)', 'Volumes Leb(P) · Leb(C) · Leb(G) · Leb(E)'), `${ex.P.toFixed(4)} · ${ex.C.toFixed(4)} · ${ex.G.toFixed(5)} · ${ex.E.toFixed(6)}`]]);
    pill('pillA', 'd', String(d)); pill('pillB', 'n', fmtN(pr.n)); pill('pillC', 'V_C/V_P', fs[0]); pill('pillD', 'V_E/V_G', fs[2]);
    $('roNote').innerHTML = T(`落进 C 的盒子点 ${fmtN(pr.hitsC)} 个；C 中的点落进 G ${fmtN(pr.hitsG)} 个，其中落进 E ${fmtN(pr.hitsE)} 个。公式是冻结定理，估计是页面的随机数。`, `${fmtN(pr.hitsC)} box points land in C; of the points in C, ${fmtN(pr.hitsG)} land in G and ${fmtN(pr.hitsE)} of those in E. The formulas are the frozen theorem; the estimates are the page’s random numbers.`);
  }
}
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; toasted = false; }
  const M = MODEL, key = `${S.mode}|${S.nowFrac}|${S.focus}|${TRV.lang()}`;
  if (key === syncedKey) return; syncedKey = key;
  const pr = progress();
  readouts();
  document.querySelectorAll('#modeChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.mode === S.mode)));
  document.querySelectorAll('#focusChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.focus === S.focus)));
  document.querySelectorAll('#dChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.d === M.d)));
  $('dChips').hidden = S.mode !== 'sample';
  $('formula').innerHTML = M.mode === 'slice' ? 'C ∩ {λ₄ = t}, &nbsp; G ∩ {λ₄ = t}, &nbsp; E ∩ {λ₄ = t}' : `V<sub>C</sub>/V<sub>P</sub> = d/(d+1)!, &nbsp; V<sub>G</sub>/V<sub>C</sub> = ((d²−1)/d²)((d−1)/d)<sup>d</sup>, &nbsp; V<sub>E</sub>/V<sub>G</sub> = 1/(d+1)`;
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('modeNote').innerHTML = M.mode === 'slice' ? T('时间轴 = λ₄，从 −1/2 到 1。', 'The time axis is λ₄, from −1/2 to 1.') : T(`时间轴 = 取点数，从 0 到 ${fmtN(NS)}（每一步三种点各一个）。`, `The time axis is the number of points, from 0 to ${fmtN(NS)} (one point of each of the three kinds per step).`);
  $('litNote').innerHTML = T('多面体、切片与随机点都由页面按定义算出；冻结的是三个比值公式和它的结构引理。', 'The polytopes, slices and random points are computed on the page from the definitions; what is frozen are the three ratio formulas and their structural lemmas.');
  $('c1Title').textContent = M.mode === 'slice' ? T('截面体积对 λ₄', 'Section volumes against λ₄') : T('随机估计的收敛', 'Convergence of the random estimates');
  $('c2Title').textContent = T('三个冻结公式对 d', 'The three frozen formulas against d');
  $('clock').innerHTML = M.mode === 'slice' ? `λ₄ ${pr.t.toFixed(3)}` : `n ${fmtN(pr.n)}`;
  $('hudBig').textContent = M.mode === 'solid' ? `d = 2 · P ⊃ C ⊃ G ⊃ E · n = ${fmtN(pr.n)}` : M.mode === 'slice' ? `d = 3 · λ₄ = ${pr.t.toFixed(3)}` : `d = ${M.d} · n = ${fmtN(pr.n)}`;
  $('hudSub').textContent = M.mode === 'solid' ? T('灰框 = 盒子 P，青 = 四面体 C，品红 = T₁(S)（与 S 合成 G），紫 = S = E；点 = 盒子里的随机点（颜色 = 所在的最小区域）', 'grey frame = the box P, cyan = the tetrahedron C, magenta = T₁(S) (with S it makes G), violet = S = E; dots = random points in the box (colour = the smallest region containing them)')
    : M.mode === 'slice' ? T('灰框 = 盒子 P 的截面，青 = C 的截面，品红 = T₁(S) 的截面，紫 = S = E 的截面；琥珀点 = 截面的顶点', 'grey frame = the section of the box P, cyan = the section of C, magenta = of T₁(S), violet = of S = E; amber dots = vertices of the sections')
    : T('C 中随机点的前三个坐标：灰青 = 不在 G，品红 = 在 G 不在 E，紫 = 在 E', 'the first three coordinates of random points in C: grey-cyan = not in G, magenta = in G but not E, violet = in E');
  if (!toasted && S.playing && S.nowFrac >= 1) {
    toasted = true;
    toast(M.mode === 'slice' ? T(`<b>λ₄ 扫完</b>：∫ 截面 dt = ${M.slice.iC.toFixed(4)}（C）、${M.slice.iG.toFixed(4)}（G）、${M.slice.iE.toFixed(4)}（E），四维体积是 ${M.ex.C.toFixed(4)}、${M.ex.G.toFixed(4)}、${M.ex.E.toFixed(4)}。`, `<b>λ₄ swept</b>: ∫ section dt = ${M.slice.iC.toFixed(4)} (C), ${M.slice.iG.toFixed(4)} (G), ${M.slice.iE.toFixed(4)} (E); the 4D volumes are ${M.ex.C.toFixed(4)}, ${M.ex.G.toFixed(4)}, ${M.ex.E.toFixed(4)}.`)
      : T(`<b>n = ${fmtN(pr.n)}</b>：估计 ${fr(pr.eA, 4)}、${fr(pr.eB, 4)}、${fr(pr.eC, 4)}，公式 ${fr(M.ex.r1, 4)}、${fr(M.ex.r2, 4)}、${fr(M.ex.r3, 4)}。`, `<b>n = ${fmtN(pr.n)}</b>: estimates ${fr(pr.eA, 4)}, ${fr(pr.eB, 4)}, ${fr(pr.eC, 4)}; formulas ${fr(M.ex.r1, 4)}, ${fr(M.ex.r2, 4)}, ${fr(M.ex.r3, 4)}.`));
  }
}
function syncRail() {
  const M = MODEL, key = `${M.mode}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = M.mode === 'slice' ? [[0, 'λ₄ = −1/2'], [1 / 3, '0'], [1, '1']] : [[0, 'n = 0'], [0.5, fmtN(NS / 2)], [1, fmtN(NS)]];
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
function custom() { S.preset = null; markPreset(); dirty = true; }
document.querySelectorAll('#modeChips .chip').forEach((b) => b.addEventListener('click', () => { const m = MODES.includes(b.dataset.mode) ? b.dataset.mode : 'solid'; if (S.mode === m) return; S.mode = m; custom(); }));
document.querySelectorAll('#focusChips .chip').forEach((b) => b.addEventListener('click', () => { S.focus = ['C', 'G', 'E'].includes(b.dataset.focus) ? b.dataset.focus : 'C'; custom(); }));
document.querySelectorAll('#dChips .chip').forEach((b) => b.addEventListener('click', () => { const d = +b.dataset.d; S.d = d >= 2 && d <= 6 ? d : 4; custom(); }));
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.mode = p.mode; S.focus = p.focus; if (p.d) S.d = p.d;
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(S.nowFrac + (ev.key === 'ArrowRight' ? 1 : -1) / TS); }
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
      S.nowFrac += S.dir * dtSec * S.speed / RUN[MODEL.mode];
      if (S.nowFrac >= 1) { S.nowFrac = 1; S.hold = 2.4; }
      if (S.nowFrac <= 0) { S.nowFrac = 0; S.hold = 1.2; }
    }
    $('now').value = S.nowFrac;
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    const k = `${S.mode}|${MODEL.d}|${S.focus}|${S.mode === 'slice' ? Math.round(S.nowFrac * TS) : Math.min(SHOW, Math.round(S.nowFrac * NS))}`;
    if (k !== glKey) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.PV_DEBUG = {
  pending: () => dirty || syncedKey !== `${S.mode}|${S.nowFrac}|${S.focus}|${TRV.lang()}`,
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => {
    const M = MODEL, pr = progress();
    const base = { mode: M.mode, d: M.d, focus: M.focus, exact: M.ex, verts: M.verts };
    if (M.mode === 'slice') return { ...base, t: pr.t, k: pr.k, vC: pr.vC, vG: pr.vG, vE: pr.vE, segC: pr.segC, segS: pr.segS, segT: pr.segT, iC: M.slice.iC, iG: M.slice.iG, iE: M.slice.iE };
    return { ...base, n: pr.n, eA: pr.eA, eB: pr.eB, eC: pr.eC, hitsC: pr.hitsC, hitsG: pr.hitsG, hitsE: pr.hitsE, shown: M.smp.showA.slice(0, 400).map(([x, c]) => [x, c]), shownB: M.smp.showB.slice(0, 400) };
  },
  setFrac: (f) => { S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; }
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('bipyramid'); S.playing = false; setPlayUI(); S.nowFrac = 0.06; $('now').value = S.nowFrac; setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 13; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
applyPreset('tetra');
setPlayUI();
requestAnimationFrame(frame);
})();
