/* MPEMBA//FOUR · every triplet fails the test, yet four levels show the Mpemba effect
   Avitan, Factor and Gelbwaser-Klimovsky (2026) conjectured that an N-level system whose every triplet violates their
   three-level condition (3) shows no Markovian Mpemba effect. Refuted in trureturing (MarkovMpembaTripletRefutation.result)
   by four levels with energies (0, 1, 2, 64)·ln 16 and bath β_b = 1: every triplet violates (3), −1 is the simple slow
   mode with left eigenvector f = g − μ, and the hotter start x = 1023/1024 has a smaller f·Π than x = 127/128. The page
   uses the same rate table for any top level n, relaxes a hot and a warm start, and draws the hump of f·Π(β).
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. The model: rates, generator, eigenvalues, relaxation
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.5, 0.58, 0.68], WHITE = [0.92, 0.95, 1];
const LN16 = Math.log(16), TMAX = 12, NT = 241, LMIN = -6, LMAX = -0.05;
const Gv = [0, 1, 2 / 3, 8 / 15];
const LEAN_B1 = Math.log(1024 / 1023) / LN16, LEAN_B2 = Math.log(128 / 127) / LN16;
const TRIPLETS = [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]];
const fr = (x, d = 6) => (isFinite(x) ? (Math.abs(x) < 5e-13 ? 0 : x).toFixed(d) : '—');
const sci = (x, d = 3) => { if (!isFinite(x)) return '—'; if (x === 0) return '0'; const e = Math.floor(Math.log10(Math.abs(x))), m = x / 10 ** e; return `${m.toFixed(d - 1)}e${e}`; };
/* the rate table of the Lean witness with r = 16^−n: a[i][j] is the rate from level j to level i */
function rates(n) {
  const r = Math.pow(16, -n), mu = 2 * (125 + 1024 * r) / (15 * (273 + 256 * r));
  const A = 47 / 48 - mu - 112 * r / 25, B = 3 / 2 - 3 * mu / 2 - 128 * r / 25, C = 31 / 20 - 15 * mu / 8;
  return { r, mu, a: [[0, A, B, C], [A / 16, 0, 1, 3 / 5], [B / 256, 1 / 16, 0, 1 / 10], [C * r, 48 * r / 5, 128 * r / 5, 0]] };
}
const levels = (n) => [0, 1, 2, n];
function gibbs(n, beta) { const x = Math.pow(16, -beta), w = levels(n).map((l) => Math.pow(x, l)), s = w.reduce((a, b) => a + b, 0); return w.map((v) => v / s); }
const matmul = (A, B) => A.map((row, i) => B[0].map((_, j) => row.reduce((s, _, k) => s + A[i][k] * B[k][j], 0)));
/* exp(M t) by scaling and squaring with a Taylor series */
function expm(M, t) {
  const norm = Math.max(...M.map((row) => row.reduce((s, v) => s + Math.abs(v), 0))) * t;
  const sq = Math.max(0, Math.ceil(Math.log2(Math.max(norm, 1e-300))) + 1), h = t / 2 ** sq;
  const A = M.map((row) => row.map((v) => v * h));
  let E = A.map((row, i) => row.map((_, j) => (i === j ? 1 : 0))), term = E.map((row) => row.slice());
  for (let k = 1; k <= 18; k++) { term = matmul(term, A).map((row) => row.map((v) => v / k)); E = E.map((row, i) => row.map((v, j) => v + term[i][j])); }
  for (let s = 0; s < sq; s++) E = matmul(E, E);
  return E;
}
/* eigenvalues of a symmetric matrix by Jacobi rotations, ascending */
function eigSym(Ain) {
  const A = Ain.map((r) => r.slice()), N = A.length;
  for (let sweep = 0; sweep < 60; sweep++) {
    let off = 0; for (let p = 0; p < N; p++) for (let q = p + 1; q < N; q++) off += A[p][q] ** 2; if (off < 1e-30) break;
    for (let p = 0; p < N; p++) for (let q = p + 1; q < N; q++) {
      if (Math.abs(A[p][q]) < 1e-300) continue;
      const th = (A[q][q] - A[p][p]) / (2 * A[p][q]), tt = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(tt * tt + 1), s = tt * c;
      for (let k = 0; k < N; k++) { const akp = A[k][p], akq = A[k][q]; A[k][p] = c * akp - s * akq; A[k][q] = s * akp + c * akq; }
      for (let k = 0; k < N; k++) { const apk = A[p][k], aqk = A[q][k]; A[p][k] = c * apk - s * aqk; A[q][k] = s * apk + c * aqk; }
    }
  }
  return A.map((r, i) => r[i]).sort((x, y) => x - y);
}
function model(n) {
  const { r, mu, a } = rates(n);
  const M = a.map((row, i) => row.map((v, j) => (i === j ? -a.reduce((s, rr, k) => s + (k === j ? 0 : rr[j]), 0) : v)));
  /* detailed balance makes D^{−1/2} M D^{1/2} symmetric with off-diagonal entries √(a_ij a_ji) */
  const Sm = M.map((row, i) => row.map((v, j) => (i === j ? v : Math.sqrt(a[i][j] * a[j][i]))));
  const eig = eigSym(Sm).reverse(), pi = gibbs(n, 1), f = Gv.map((g) => g - mu);
  const fM = [0, 1, 2, 3].map((j) => f.reduce((s, fi, i) => s + fi * M[i][j], 0)), resid = Math.max(...fM.map((v, j) => Math.abs(v + f[j])));
  const b2 = (beta) => gibbs(n, beta).reduce((s, p, i) => s + f[i] * p, 0);
  const lv = levels(n), margins = TRIPLETS.map(([i, j, k]) => {
    const x = Math.pow(16, -(lv[j] - lv[i])), y = Math.pow(16, -(lv[k] - lv[j])), kap = (a[i][k] + a[j][k]) / (a[i][j] * (1 + x));
    return { t: [i, j, k], kappa: kap, m1: a[i][k] * (1 + x * y / 2) - a[j][k] * (1 + y / 2) - a[i][j] * (1 - x), m2: a[i][k] * x - a[j][k] };
  });
  /* the hump: scan log β, then refine the maximum by golden section */
  const scan = []; for (let k = 0; k <= 600; k++) { const L = -7 + 7 * k / 600; scan.push([L, b2(10 ** L)]); }
  let kmax = 0; scan.forEach((p, k) => { if (p[1] > scan[kmax][1]) kmax = k; });
  let lo = scan[Math.max(0, kmax - 1)][0], hi = scan[Math.min(600, kmax + 1)][0];
  for (let it = 0; it < 80; it++) { const m1 = lo + (hi - lo) * 0.382, m2 = lo + (hi - lo) * 0.618; if (b2(10 ** m1) < b2(10 ** m2)) lo = m1; else hi = m2; }
  const Lstar = (lo + hi) / 2, interior = kmax > 0 && b2(10 ** Lstar) > b2(1e-12) + 1e-13;
  return { n, r, mu, a, M, eig, pi, f, resid, b2, margins, scan, betaStar: interior ? 10 ** Lstar : null, b2Star: interior ? b2(10 ** Lstar) : b2(1e-12), b2Zero: b2(1e-12), slope0: LN16 * (n - 41) / 240 };
}
const dist = (p, pi) => p.reduce((s, v, i) => s + Math.abs(v - pi[i]), 0);

/* =====================================================================
   2. State, presets and the derived quantities
   ===================================================================== */
const S = { n: 64, L1: Math.log10(LEAN_B1), L2: Math.log10(LEAN_B2), t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { n: 64, L1: Math.log10(LEAN_B1), L2: Math.log10(LEAN_B2), t: 0, play: false,
    zh: 'Lean 里的反例：顶层 n = 64，两个初态取 x = 16^(−β) = 1023/1024（热，β₁ ≈ 3.5·10⁻⁴）与 127/128（温，β₂ ≈ 2.8·10⁻³）。慢模系数分别约为 0.4890371 与 0.4892979：更热的那个更小。四个三能级子系统的两条不等式余量全是负的。',
    en: 'The counterexample in Lean: top level n = 64 and the two starts x = 16^(−β) = 1023/1024 (hot, β₁ ≈ 3.5·10⁻⁴) and 127/128 (warm, β₂ ≈ 2.8·10⁻³). Their slow-mode coefficients are about 0.4890371 and 0.4892979: the hotter one is smaller. In all four triplets both margins are negative.' },
  race: { n: 64, L1: Math.log10(LEAN_B1), L2: Math.log10(LEAN_B2), t: 0, play: true,
    zh: '两个初态同时弛豫。开始时热的那个离平衡更远（距离之比 − 1 约 +3.8%），t ≈ 4.28 时两条距离曲线交叉，之后热的那个一直更近，比值趋向 0.4890371/0.4892979 − 1 ≈ −0.053%。差别很小，但符号翻转了。页面数值。',
    en: 'Both starts relax together. At first the hot one is farther from equilibrium (the ratio minus one is about +3.8%); the two distance curves cross at t ≈ 4.28, and afterwards the hot one stays closer, the ratio tending to 0.4890371/0.4892979 − 1 ≈ −0.053%. The difference is small, but its sign flips. Page numbers.' },
  hump: { n: 64, L1: -6, L2: 'star', t: 0, play: true,
    zh: '把温的初态放在驼峰顶点 β*（n = 64 时约 2.7·10⁻³），热的初态放到 β₁ = 10⁻⁶，差别最大：慢模系数相差约 3.5·10⁻⁴，即 0.07%。',
    en: 'Put the warm start at the top of the hump β* (about 2.7·10⁻³ for n = 64) and the hot start at β₁ = 10⁻⁶: this is the largest contrast, a difference in slow-mode coefficient of about 3.5·10⁻⁴, or 0.07%.' },
  n41: { n: 41, L1: Math.log10(LEAN_B1), L2: Math.log10(LEAN_B2), t: 0, play: false,
    zh: 'n = 41：同一张速率表，三能级检验同样全都不过，但慢模系数随温度单调，没有驼峰——更热的初态始终离平衡更远，没有姆潘巴效应。β = 0 处的斜率 ln 16·(n − 41)/240 恰好为 0。页面数值与本页的论证。',
    en: 'n = 41: the same rate table, every triplet still fails, but the slow-mode coefficient is monotone in temperature with no hump — the hotter start always stays farther, and there is no Mpemba effect. The slope at β = 0, ln 16·(n − 41)/240, is exactly 0. Page numbers and the page’s argument.' },
  n42: { n: 42, L1: -6, L2: 'star', t: 0, play: false,
    zh: 'n = 42：驼峰刚出现，最大点 β* 约 2.1·10⁻⁴，比无穷高温只高约 1.2·10⁻⁶。Lean 的两个温度此时都在驼峰右侧，所以这里换成 β₁ = 10⁻⁶ 与 β₂ = β*。页面数值。',
    en: 'n = 42: the hump has just appeared, with its maximum β* near 2.1·10⁻⁴, only about 1.2·10⁻⁶ above infinite temperature. Lean’s two temperatures both lie to the right of the hump here, so this preset uses β₁ = 10⁻⁶ and β₂ = β*. Page numbers.' },
  n100: { n: 100, L1: -6, L2: 'star', t: 0, play: true,
    zh: 'n = 100：顶层更高，要更高的温度才能填上，驼峰更明显（最大点约 3.5·10⁻³，比无穷高温高约 1.1·10⁻³），两条距离曲线也交叉得更早。页面数值。',
    en: 'n = 100: the top level is higher and needs an even higher temperature to fill, so the hump is larger (maximum near 3.5·10⁻³, about 1.1·10⁻³ above infinite temperature) and the distance curves cross earlier. Page numbers.' }
};
let MODEL = null, CURVES = null, dirty = true, modelId = 0;
const MODELS = {};
const getModel = (n) => MODELS[n] || (MODELS[n] = model(n));
function curves(m, L1, L2) {
  const p1 = gibbs(m.n, 10 ** L1), p2 = gibbs(m.n, 10 ** L2), ts = [], d1 = [], d2 = [], pops1 = [], pops2 = [];
  for (let k = 0; k < NT; k++) { const t = TMAX * k / (NT - 1), E = expm(m.M, t), q1 = E.map((row) => row.reduce((s, v, j) => s + v * p1[j], 0)), q2 = E.map((row) => row.reduce((s, v, j) => s + v * p2[j], 0)); ts.push(t); d1.push(dist(q1, m.pi)); d2.push(dist(q2, m.pi)); pops1.push(q1); pops2.push(q2); }
  const R = d1.map((v, k) => v / d2[k] - 1);
  let cross = null; for (let k = 0; k + 1 < NT; k++) if ((R[k] > 0 && R[k + 1] <= 0) || (R[k] < 0 && R[k + 1] >= 0)) { cross = ts[k] + (ts[k + 1] - ts[k]) * R[k] / (R[k] - R[k + 1]); break; }
  return { ts, d1, d2, R, cross, pops1, pops2 };
}
function build() {
  const m = getModel(S.n);
  const key = `${S.n}|${S.L1}|${S.L2}`;
  if (!CURVES || CURVES.key !== key) CURVES = { key, ...curves(m, S.L1, S.L2) };
  const t = S.t * TMAX, k = Math.min(NT - 1, Math.round(t / TMAX * (NT - 1)));
  const E = expm(m.M, t), p1 = gibbs(m.n, 10 ** S.L1), p2 = gibbs(m.n, 10 ** S.L2);
  const q1 = E.map((row) => row.reduce((s, v, j) => s + v * p1[j], 0)), q2 = E.map((row) => row.reduce((s, v, j) => s + v * p2[j], 0));
  const hot = S.L1 <= S.L2, bA = m.b2(10 ** S.L1), bB = m.b2(10 ** S.L2), bHot = hot ? bA : bB, bWarm = hot ? bB : bA;
  MODEL = { id: ++modelId, ...m, L1: S.L1, L2: S.L2, beta1: 10 ** S.L1, beta2: 10 ** S.L2, b2a: bA, b2b: bB, effect: Math.abs(bHot) < Math.abs(bWarm), t, k, q1, q2, D1: dist(q1, m.pi), D2: dist(q2, m.pi), C: CURVES };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');

/* =====================================================================
   4. 3D scene: two columns of four levels, particles in proportion to the occupations
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 2400, PTS_MAX = 900;
const CAMS = { iso: [0.55, 1.25, 10], front: [0.0001, 1.5708, 9.5], top: [0.0001, 0.06, 10] };
const cam = { theta: 0.55, phi: 1.25, r: 10, tTheta: 0.55, tPhi: 1.25, tR: 10 };
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
  pts = new THREE.Points(gp, new THREE.ShaderMaterial({ vertexShader: EVT_VS, fragmentShader: DOT_FS, uniforms: { uScale: { value: 60 } }, ...additive }));
  pts.frustumCulled = false; scene3.add(pts);
}
const NP = 320, XS = [-1.75, 1.75], YS = [-1.9, -0.95, 0, 2.0], RD = 1;
/* a fixed density of particles: the j-th particle of a level sits on a golden-angle spiral */
const spiral = (j) => { const a = j * 2.399963, rr = 0.95 * RD * Math.sqrt((j + 0.5) / NP); return [rr * Math.cos(a), rr * Math.sin(a)]; };
function counts(p) {
  const raw = p.map((v) => v * NP), c = raw.map(Math.floor); let left = NP - c.reduce((a, b) => a + b, 0);
  raw.map((v, i) => [v - c[i], i]).sort((x, y) => y[0] - x[0]).forEach(([, i]) => { if (left > 0) { c[i]++; left--; } });
  return c;
}
function updateGL() {
  const M = MODEL;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = c[0]; PT.aColor.array[3 * np + 1] = c[1]; PT.aColor.array[3 * np + 2] = c[2]; PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  [M.q1, M.q2].forEach((q, col) => {
    const x0 = XS[col], c = col === 0 ? COL.magenta : COL.amber, cnt = counts(q);
    for (let i = 0; i < 4; i++) {
      for (let s = 0; s < 48; s++) { const a0 = 2 * Math.PI * s / 48, a1 = 2 * Math.PI * (s + 1) / 48; seg([x0 + RD * Math.cos(a0), YS[i], RD * Math.sin(a0)], [x0 + RD * Math.cos(a1), YS[i], RD * Math.sin(a1)], c, 0.45); }
      for (let j = 0; j < cnt[i]; j++) { const [dx, dz] = spiral(j); dot([x0 + dx, YS[i] + 0.02, dz], c, 0.95, 1.05); }
    }
    /* the energy axis, broken between the third level and the top level */
    const ax = x0 - RD - 0.25, mid = (YS[2] + YS[3]) / 2;
    seg([ax, YS[0], 0], [ax, mid - 0.18, 0], GREY, 0.6); seg([ax, mid + 0.18, 0], [ax, YS[3] + 0.3, 0], GREY, 0.6);
    seg([ax - 0.12, mid - 0.24, 0], [ax + 0.12, mid - 0.12, 0], GREY, 0.8); seg([ax - 0.12, mid + 0.12, 0], [ax + 0.12, mid + 0.24, 0], GREY, 0.8);
    for (let i = 0; i < 4; i++) seg([ax - 0.06, YS[i], 0], [ax + 0.06, YS[i], 0], GREY, 0.8);
  });
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
const pct = (x) => (x >= 0.001 ? `${(100 * x).toFixed(1)}%` : x > 0 ? `${sci(100 * x, 2)}%` : '0%');
function updateTags() {
  const M = MODEL; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  const hot = M.L1 <= M.L2;
  put(T(`${hot ? '热' : '温'} β₁ = ${sci(M.beta1, 2)}`, `${hot ? 'hot' : 'warm'} β₁ = ${sci(M.beta1, 2)}`), [XS[0], YS[3] + 0.75, 0], 'col hot');
  put(T(`${hot ? '温' : '热'} β₂ = ${sci(M.beta2, 2)}`, `${hot ? 'warm' : 'hot'} β₂ = ${sci(M.beta2, 2)}`), [XS[1], YS[3] + 0.75, 0], 'col warm');
  const lab = ['E = 0', 'ln 16', '2 ln 16', `${M.n} ln 16`];
  for (let i = 0; i < 4; i++) put(lab[i], [XS[0] - RD - 0.6, YS[i], 0], 'lv');
  for (let i = 0; i < 4; i++) { put(pct(M.q1[i]), [XS[0] + RD + 0.2, YS[i] + 0.12, 0], 'hot'); put(pct(M.q2[i]), [XS[1] + RD + 0.2, YS[i] + 0.12, 0], 'warm'); }
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
/* the slow-mode coefficient b₂(β) = f·Π(β) on a log β axis, zoomed to the hump */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 62); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, X = (L) => pl + iw * (L - LMIN) / (0 - LMIN);
  const h = Math.max(M.b2Star - M.b2Zero, Math.abs(M.b2a - M.b2b), 2e-6), lo = M.b2Zero - 2.2 * h, hi = Math.max(M.b2Star, M.b2a, M.b2b) + 0.7 * h;
  const Y = (y) => pt + ih - ih * (y - lo) / (hi - lo);
  ctx.save(); ctx.beginPath(); ctx.rect(pl, pt, iw, ih); ctx.clip();
  ctx.strokeStyle = FAINT; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(pl, Y(M.b2Zero)); ctx.lineTo(pl + iw, Y(M.b2Zero)); ctx.stroke(); ctx.setLineDash([]);
  ctx.strokeStyle = CY; ctx.lineWidth = 2 * dpr; ctx.beginPath(); let first = true;
  for (let k = 0; k <= 400; k++) { const L = LMIN + (0 - LMIN) * k / 400, y = M.b2(10 ** L); if (first) { ctx.moveTo(X(L), Y(y)); first = false; } else ctx.lineTo(X(L), Y(y)); }
  ctx.stroke();
  const mark = (L, y, c, r) => { ctx.fillStyle = c; ctx.beginPath(); ctx.arc(X(L), Y(y), r * dpr, 0, 2 * Math.PI); ctx.fill(); };
  if (M.betaStar) mark(Math.log10(M.betaStar), M.b2Star, INK, 3.2);
  mark(M.L1, M.b2a, MG, 4); mark(M.L2, M.b2b, AM, 4);
  ctx.restore();
  for (const y of [M.b2Zero, hi]) lab(ctx, y.toFixed(6), pl - 4 * dpr, Y(y), 'right', 'middle', y === M.b2Zero ? INK : DIM);
  for (const L of [-6, -4, -2, 0]) lab(ctx, `10^${L}`, X(L), pt + ih + 4 * dpr, L === 0 ? 'right' : 'center', 'top');
  lab(ctx, T('β_b = 1 处 b₂ = 0（在图下方）', 'b₂ = 0 at β_b = 1 (below the frame)'), pl + iw - 4 * dpr, pt + ih - 4 * dpr, 'right', 'bottom');
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>b₂(β)</span><span class="it"><i class="sw" style="--c:${MG}"></i>β₁</span><span class="it"><i class="sw" style="--c:${AM}"></i>β₂</span><span class="it"><i class="sw" style="--c:#8a9bb0"></i>${T('无穷高温', 'infinite temperature')}</span>`;
}
/* the ratio D₁(t)/D₂(t) − 1 of the two L1 distances, on an asinh scale */
function drawSide() {
  const M = MODEL, C = M.C, F2 = frame2d(cv2, 50); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, eps = 1e-4, top = Math.asinh(0.2 / eps);
  const X = (t) => pl + iw * t / TMAX, Y = (r) => pt + ih / 2 - (ih / 2) * Math.asinh(r / eps) / top;
  for (const r of [-1e-2, -1e-3, -1e-4, 0, 1e-4, 1e-3, 1e-2, 1e-1]) { ctx.strokeStyle = r === 0 ? 'rgba(200,215,230,0.45)' : 'rgba(120,140,160,0.15)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(r)); ctx.lineTo(pl + iw, Y(r)); ctx.stroke(); if (Math.abs(r) !== 1e-4) lab(ctx, r === 0 ? '0' : `${r > 0 ? '+' : '−'}${Math.abs(r) * 100}%`, pl - 4 * dpr, Y(r), 'right', 'middle'); }
  ctx.strokeStyle = CY; ctx.lineWidth = 2 * dpr; ctx.beginPath(); C.R.forEach((r, k) => { if (k === 0) ctx.moveTo(X(C.ts[k]), Y(r)); else ctx.lineTo(X(C.ts[k]), Y(r)); }); ctx.stroke();
  if (C.cross !== null) { ctx.fillStyle = INK; ctx.beginPath(); ctx.arc(X(C.cross), Y(0), 3.5 * dpr, 0, 2 * Math.PI); ctx.fill(); lab(ctx, `t ≈ ${C.cross.toFixed(2)}`, X(C.cross), Y(0) - 6 * dpr, 'center', 'bottom', INK); }
  ctx.strokeStyle = 'rgba(255,255,255,0.45)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(X(M.t), pt); ctx.lineTo(X(M.t), pt + ih); ctx.stroke();
  for (const t of [0, 4, 8, 12]) lab(ctx, `t = ${t}`, X(t), pt + ih + 4 * dpr, t === 0 ? 'left' : t === 12 ? 'right' : 'center', 'top');
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>D₁/D₂ − 1</span><span class="it">${T('（正：β₁ 那列更远）', '(positive: the β₁ column is farther)')}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function readouts() {
  const M = MODEL, C = M.C, hotFirst = M.L1 <= M.L2;
  pill('pillA', 'n', String(M.n)); pill('pillB', 'λ₂', fr(M.eig[1], 4));
  pill('pillC', 'MPEMBA', M.effect ? '✓' : '✗'); pill('pillD', T('交叉', 'CROSS'), C.cross !== null ? `t ≈ ${C.cross.toFixed(2)}` : '—');
  setRo([
    [T('生成元的本征值（对称化后 Jacobi）· fᵀM + fᵀ 的残差', 'Eigenvalues of the generator (symmetrized, Jacobi) · residual of fᵀM + fᵀ'), `${M.eig.map((e) => fr(e, 4)).join(', ')} · ${sci(M.resid, 2)}`],
    [T('慢模系数 b₂ = f·Π(β)：β₁ · β₂', 'Slow-mode coefficient b₂ = f·Π(β): β₁ · β₂'), `${fr(M.b2a, 7)} · ${fr(M.b2b, 7)}`],
    [T('驼峰：最大点 β* · b₂(β*) · β = 0 处的斜率 ln 16·(n − 41)/240', 'Hump: maximum β* · b₂(β*) · slope at β = 0, ln 16·(n − 41)/240'), `${M.betaStar ? sci(M.betaStar, 3) : T('无（在 β → 0）', 'none (at β → 0)')} · ${fr(M.b2Star, 7)} · ${M.slope0 >= 0 ? '+' : ''}${fr(M.slope0, 4)}`],
    [T(`t = ${M.t.toFixed(2)} 时到平衡的 L1 距离：β₁ · β₂ · 之比 − 1`, `L1 distance to equilibrium at t = ${M.t.toFixed(2)}: β₁ · β₂ · ratio − 1`), `${sci(M.D1, 4)} · ${sci(M.D2, 4)} · ${((M.D1 / M.D2 - 1) * 100).toFixed(3)}%`],
    [T('四个三元组 (i, j, k) 的两条不等式余量（都 ≤ 0 即不满足 (3)）', 'The two margins for each triplet (i, j, k) (both ≤ 0 means (3) fails)'), M.margins.map((m) => `(${m.t.map((x) => x + 1).join('')}) ${fr(m.m1, 3)}/${fr(m.m2, 3)}`).join(' · ')]]);
  const fail = M.margins.every((m) => m.m1 <= 0 && m.m2 <= 0);
  $('roNote').innerHTML = (fail ? T('四个三元组都不满足 (3)。', 'Every triplet violates (3). ') : T('有三元组满足 (3)。', 'Some triplet satisfies (3). '))
    + (M.effect ? T(`更热的初态（β = ${sci(Math.min(M.beta1, M.beta2), 2)}）的 |b₂| 更小：姆潘巴效应${M.n === 64 && Math.abs(M.L1 - Math.log10(LEAN_B1)) < 1e-9 && Math.abs(M.L2 - Math.log10(LEAN_B2)) < 1e-9 ? '（Lean 定理）' : '（页面数值）'}。`, `The hotter start (β = ${sci(Math.min(M.beta1, M.beta2), 2)}) has the smaller |b₂|: a Mpemba effect${M.n === 64 && Math.abs(M.L1 - Math.log10(LEAN_B1)) < 1e-9 && Math.abs(M.L2 - Math.log10(LEAN_B2)) < 1e-9 ? ' (the Lean theorem)' : ' (page numbers)'}.`)
      : T('更热的初态的 |b₂| 不更小：这两个温度之间没有姆潘巴效应。', 'The hotter start does not have the smaller |b₂|: no Mpemba effect between these two temperatures.'));
}
const stateKey = () => `${S.n}|${S.L1}|${S.L2}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; }
  const M = MODEL, C = M.C;
  if (!toasted && S.playing && C.cross !== null && M.t >= C.cross) { toasted = true; toast(T(`<b>t ≈ ${C.cross.toFixed(2)}</b>：两条距离曲线交叉，${M.effect ? '更热的初态从此离平衡更近' : '从此 β₂ 那列离平衡更近'}。`, `<b>t ≈ ${C.cross.toFixed(2)}</b>: the two distance curves cross; ${M.effect ? 'from now on the hotter start is closer to equilibrium' : 'from now on the β₂ column is closer to equilibrium'}.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('nIn').value = S.n; $('nOut').textContent = String(S.n); $('b1In').value = S.L1; $('b1Out').textContent = sci(10 ** S.L1, 2); $('b2In').value = S.L2; $('b2Out').textContent = sci(10 ** S.L2, 2);
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T(`能量 (0, 1, 2, ${M.n})·ln 16，r = 16^(−${M.n}) ≈ ${sci(M.r, 2)}，μ = ${fr(M.mu, 7)}。x = 16^(−β)：β₁ 对应 x = ${fr(16 ** (-M.beta1), 6)}，β₂ 对应 x = ${fr(16 ** (-M.beta2), 6)}。`, `Energies (0, 1, 2, ${M.n})·ln 16, r = 16^(−${M.n}) ≈ ${sci(M.r, 2)}, μ = ${fr(M.mu, 7)}. With x = 16^(−β): β₁ gives x = ${fr(16 ** (-M.beta1), 6)} and β₂ gives x = ${fr(16 ** (-M.beta2), 6)}.`);
  $('litNote').innerHTML = T('Lean 证明的是 n = 64 与两个固定温度；其他 n、温度、本征值与距离曲线都是页面数值。', 'Lean proves the case n = 64 at two fixed temperatures; other values of n, other temperatures, the eigenvalues and the distance curves are page numbers.');
  $('c1Title').textContent = T('慢模系数 b₂ 随初始温度：驼峰', 'Slow-mode coefficient b₂ against the initial temperature: the hump');
  $('c2Title').textContent = T('两列到平衡的距离之比 − 1（过零即交叉）', 'Ratio of the two distances minus one (zero is the crossing)');
  $('clock').innerHTML = `t = ${M.t.toFixed(2)}`;
  $('hudBig').textContent = `n = ${M.n} · t = ${M.t.toFixed(2)} · ${M.effect ? T('热的 |b₂| 更小：姆潘巴效应', 'hot |b₂| smaller: Mpemba effect') : T('没有姆潘巴效应', 'no Mpemba effect')}`;
  $('hudSub').textContent = T('左列从 β₁ 的平衡态出发（品红），右列从 β₂ 出发（琥珀），一起向浴温 β_b = 1 弛豫；每个圆盘是一个能级，粒子数正比于占据概率，顶层画在折断的能量轴上方', 'The left column starts in equilibrium at β₁ (magenta) and the right one at β₂ (amber), both relaxing to the bath β_b = 1; each disc is an energy level with particles in proportion to its occupation, and the top level sits above a broken energy axis');
}
function syncRail() {
  const C = MODEL.C, key = `${C.key}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 't = 0']]; if (C.cross !== null) marks.push([C.cross / TMAX, T(`交叉 ${C.cross.toFixed(2)}`, `cross ${C.cross.toFixed(2)}`)]); marks.push([1, `t = ${TMAX}`]);
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  const m = getModel(p.n);
  Object.assign(S, { n: p.n, L1: p.L1, L2: p.L2 === 'star' ? Math.log10(m.betaStar) : p.L2, t: p.t, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('nIn').addEventListener('input', () => { S.n = parseInt($('nIn').value, 10); custom(); });
$('b1In').addEventListener('input', () => { S.L1 = parseFloat($('b1In').value); custom(); });
$('b2In').addEventListener('input', () => { S.L2 = parseFloat($('b2In').value); custom(); });
const setT = (t, user) => { S.t = Math.min(1, Math.max(0, t)); $('now').value = S.t; dirty = true; if (user) { S.preset = null; markPreset(); } };
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(Math.round(S.t * TMAX * 2 + (ev.key === 'ArrowRight' ? 1 : -1)) / (2 * TMAX)); }
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
const RUN = 16;
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
window.MF_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { n: M.n, r: M.r, mu: M.mu, a: M.a.map((r) => r.slice()), eig: M.eig.slice(), resid: M.resid, f: M.f.slice(), beta1: M.beta1, beta2: M.beta2, b2a: M.b2a, b2b: M.b2b, effect: M.effect, betaStar: M.betaStar, b2Star: M.b2Star, b2Zero: M.b2Zero, slope0: M.slope0,
    margins: M.margins.map((m) => ({ t: m.t.slice(), kappa: m.kappa, m1: m.m1, m2: m.m2 })), t: M.t, q1: M.q1.slice(), q2: M.q2.slice(), D1: M.D1, D2: M.D2, cross: M.C.cross, pi: M.pi.slice() }; },
  ratio: () => MODEL.C.R.slice(),
  b2: (n, beta) => getModel(n).b2(beta),
  hump: (n) => { const m = getModel(n); return { betaStar: m.betaStar, b2Star: m.b2Star, b2Zero: m.b2Zero }; },
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setT(0.25); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 9; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
