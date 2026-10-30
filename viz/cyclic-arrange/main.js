/* CYCLIC//ARRANGE · Javaheri's cyclic arrangement inequality
   For a, b ≥ 0 and c = (a + b + 1)/2 the cyclic inequality (Σ xᵢ)(Σ xᵢᵃ xᵢ₊₁ᵇ) ≤ (Σ xᵢᶜ)² either holds for every
   nonnegative n-tuple or not; Javaheri's Conjecture 1.3 says the largest valid n equals
   N*(a, b) = max{n : n = 1 or (a + b − 1)² ≤ 8ab sin²(π/n)}. Frozen in trureturing (JavaheriArrangementDimensionRefutation
   .result): false at (a, b) = (6, 1), where N* = 3 but (6, 5, 5) violates n = 3 by exactly 364. The page draws the ratio of
   the two sides over the triangle of 3-tuples, the threshold behind N*, and a numerical search in every dimension up to 7.
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
const GREY = [0.5, 0.58, 0.68];
const NS = [2, 3, 4, 5, 6, 7], TRI = 48, RUN = 14, EPS = 1e-9, CAP = { 3: 12, 4: 10 };
const fr = (x, d = 4) => (isFinite(x) ? x.toFixed(d) : '—');
const gs = (g) => (Number.isInteger(g) ? String(g) : g.toFixed(1));

/* =====================================================================
   2. The inequality
   ===================================================================== */
const cOf = (a, b) => (a + b + 1) / 2;
/* both sides for a nonnegative tuple; the successor is cyclic */
function sides(a, b, x) {
  const n = x.length, c = cOf(a, b); let s = 0, t = 0, u = 0;
  for (let i = 0; i < n; i++) { s += x[i]; t += x[i] ** a * x[(i + 1) % n] ** b; u += x[i] ** c; }
  return { lhs: s * t, rhs: u * u };
}
const ratio = (a, b, x) => { const { lhs, rhs } = sides(a, b, x); return rhs > 0 ? lhs / rhs : 0; };
/* exact left minus right for integer tuples when a, b and c are integers */
const exactOK = (a, b) => Number.isInteger(a) && Number.isInteger(b) && Number.isInteger(cOf(a, b));
function exactDiff(a, b, x) {
  const n = x.length, c = BigInt(cOf(a, b)), A = BigInt(a), B = BigInt(b), X = x.map(BigInt); let s = 0n, t = 0n, u = 0n;
  for (let i = 0; i < n; i++) { s += X[i]; t += X[i] ** A * X[(i + 1) % n] ** B; u += X[i] ** c; }
  return { lhs: s * t, rhs: u * u, diff: s * t - u * u };
}
/* the threshold dimensions; equality is decided with a relative tolerance (48·sin²(π/3) is 35.999… in floating point) */
const thrRight = (a, b, n) => 8 * a * b * Math.sin(Math.PI / n) ** 2;
const isThreshold = (a, b, n) => n === 1 || (a + b - 1) ** 2 <= thrRight(a, b, n) * (1 + EPS) + EPS;
function nStar(a, b) { let best = 1; for (let n = 2; n <= 2000; n++) if (isThreshold(a, b, n)) best = n; return best; }

/* numerical maximum of the ratio over nonnegative n-tuples: x₁ = 1 by homogeneity, the rest squares, Nelder–Mead from
   seeded random starts */
function nelderMead(f, x0, iters) {
  const d = x0.length; let S = [x0.slice()]; for (let i = 0; i < d; i++) { const v = x0.slice(); v[i] += 0.3; S.push(v); }
  let F = S.map(f);
  for (let it = 0; it < iters; it++) {
    const idx = F.map((_, i) => i).sort((i, j) => F[i] - F[j]); S = idx.map((i) => S[i]); F = idx.map((i) => F[i]);
    const c = new Array(d).fill(0); for (let i = 0; i < d; i++) for (let j = 0; j < d; j++) c[j] += S[i][j] / d;
    const xr = c.map((v, j) => v + (v - S[d][j])), fr2 = f(xr);
    if (fr2 < F[0]) { const xe = c.map((v, j) => v + 2 * (v - S[d][j])), fe = f(xe); if (fe < fr2) { S[d] = xe; F[d] = fe; } else { S[d] = xr; F[d] = fr2; } }
    else if (fr2 < F[d - 1]) { S[d] = xr; F[d] = fr2; }
    else { const xc = c.map((v, j) => v + 0.5 * (S[d][j] - v)), fc = f(xc); if (fc < F[d]) { S[d] = xc; F[d] = fc; } else { for (let i = 1; i <= d; i++) { S[i] = S[i].map((v, j) => S[0][j] + 0.5 * (v - S[0][j])); F[i] = f(S[i]); } } }
  }
  let k = 0; for (let i = 1; i <= d; i++) if (F[i] < F[k]) k = i; return { x: S[k], f: F[k] };
}
function maxRatio(a, b, n) {
  const rnd = TRV.mulberry32(7919 * n + 17), f = (y) => -ratio(a, b, [1, ...y.map((v) => v * v)]);
  let best = { f: 0, x: new Array(n - 1).fill(1) };
  for (let k = 0; k < 12; k++) { const r1 = nelderMead(f, Array.from({ length: n - 1 }, () => rnd() * 1.4), 300 * n), r2 = nelderMead(f, r1.x, 300 * n); if (r2.f < best.f) best = r2; }
  const x = [1, ...best.x.map((v) => v * v)], m = Math.max(...x);
  return { ratio: -best.f, x: x.map((v) => v / m) };
}
/* the integer tuple with the smallest largest entry (≤ CAP[n]) that violates the inequality, by exhaustive search */
function smallestWitness(a, b, n) {
  if (!exactOK(a, b) || !CAP[n]) return null;
  for (let M = 1; M <= CAP[n]; M++) {
    let found = null; const pre = [];
    (function rec() { if (found) return; if (pre.length === n) { if (Math.max(...pre) === M && exactDiff(a, b, pre).diff > 0n) found = pre.slice(); return; } for (let v = 0; v <= M; v++) { pre.push(v); rec(); pre.pop(); } })();
    if (found) return found;
  }
  return null;
}

/* =====================================================================
   3. State and presets
   ===================================================================== */
const S = { a: 6, b: 1, nowFrac: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { a: 6, b: 1, frac: 0, play: true, focus: 'lean',
    zh: '(a, b) = (6, 1)，c = 4。门槛 36 ≤ 48 sin²(π/n) 在 n = 3 恰好取等号，n ≥ 4 不成立，所以猜想说 N(6, 1) = 3。可三元组 (6, 5, 5) 让左边 6482480 比右边 6482116 大 364——三维里的琥珀点在 0 平面之上。Lean 用这一点证明了猜想不成立。',
    en: '(a, b) = (6, 1), c = 4. The threshold 36 ≤ 48 sin²(π/n) holds with equality at n = 3 and fails for n ≥ 4, so the conjecture says N(6, 1) = 3. But the triple (6, 5, 5) makes the left side 6482480 exceed the right side 6482116 by 364 — the amber point in 3D sits above the zero plane. Lean uses this point to refute the conjecture.' },
  small: { a: 6, b: 1, frac: 0.5, play: false, focus: 'small',
    zh: '更小的反例：页面在最大分量 ≤ 12 的整数三元组里穷举，最大分量最小的是 (2, 4, 3)，左边减右边 = 1409。这是页面的精确整数计算，不是 Lean 定理；冻结的反例是 (6, 5, 5)。',
    en: 'A smaller counterexample: the page searches every integer triple with largest entry ≤ 12, and the one with the smallest largest entry is (2, 4, 3), with left minus right = 1409. This is exact integer arithmetic on the page, not a Lean theorem; the frozen counterexample is (6, 5, 5).' },
  max: { a: 6, b: 1, frac: 1, play: false, focus: 'max',
    zh: '数值搜索给出 n = 3 时比值 LHS/RHS 的最大值约 1.0177，在 (1, 0.779, 0.592) 附近（按最大分量归一；循环轮换给出同一个值）——比 (6, 5, 5) 的 1.000056 大得多。三维的高度是带符号的 √|LHS/RHS − 1|，品红区域就是不等式失败的地方。',
    en: 'A numerical search gives a maximum ratio LHS/RHS of about 1.0177 at n = 3, near (1, 0.779, 0.592) (scaled to largest entry 1; cyclic rotations give the same value) — far larger than the 1.000056 of (6, 5, 5). The height in 3D is the signed √|LHS/RHS − 1|, and the magenta region is where the inequality fails.' },
  four: { a: 4, b: 1, frac: 0.5, play: false, focus: 'small',
    zh: '(a, b) = (4, 1)：门槛 16 ≤ 32 sin²(π/n) 在 n = 4 取等号，N* = 4；n = 3 时三维曲面处处 ≤ 0（不等式成立）。可页面在 n = 4 找到整数四元组 (7, 7, 10, 9)，左边减右边 = 327 > 0——又一处等号情形失败。这是页面的精确整数计算，不是 Lean 定理。',
    en: '(a, b) = (4, 1): the threshold 16 ≤ 32 sin²(π/n) holds with equality at n = 4, so N* = 4; at n = 3 the 3D surface stays ≤ 0 everywhere (the inequality holds). But at n = 4 the page finds the integer quadruple (7, 7, 10, 9) with left minus right = 327 > 0 — another failure at the equality case. This is exact integer arithmetic on the page, not a Lean theorem.' },
  holds: { a: 3, b: 0.5, frac: 0, play: true, focus: 'max',
    zh: '(a, b) = (3, 0.5)：门槛在 n = 3 严格成立（6.25 < 9），在 n = 4 不成立，N* = 3。数值搜索在 n = 2、3 找不到反例（最大比值就是全相等时的 1），n = 4 起失败——这里猜想与数值一致。页面数值，不是证明。',
    en: '(a, b) = (3, 0.5): the threshold holds strictly at n = 3 (6.25 < 9) and fails at n = 4, so N* = 3. The numerical search finds no counterexample at n = 2 or 3 (the largest ratio is the 1 of equal entries) and failures from n = 4 on — here the conjecture and the numbers agree. Page numbers, not a proof.' },
  one: { a: 1, b: 1, frac: 0, play: true, focus: 'max',
    zh: '(a, b) = (1, 1)：门槛 1 ≤ 8 sin²(π/n) 给出 N* = 8。原文第 8 节把 (1, 1) 列为等号成立的情形之一；页面的数值搜索到 n = 7 都只得到全相等时的比值 1。卷宗把这些情形的独立验证列为未决。',
    en: '(a, b) = (1, 1): the threshold 1 ≤ 8 sin²(π/n) gives N* = 8. Section 8 of the source lists (1, 1) among the cases where equality holds; the page’s numerical search up to n = 7 only finds the ratio 1 of equal entries. The dossier lists independent verification of these cases as open.' }
};

/* =====================================================================
   4. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
const searchCache = new Map();
function build() {
  if (!isFinite(S.a) || S.a < 0) S.a = 6; if (!isFinite(S.b) || S.b < 0) S.b = 1;
  const a = S.a, b = S.b, M = { id: ++modelId, a, b, c: cOf(a, b), excluded: Math.abs(a + b - 1) < 1e-12 };
  M.nstar = M.excluded ? null : nStar(a, b);
  /* the ratio on the triangle of 3-tuples x = (i, j, k)/TRI */
  M.tri = []; let best = { r: -1 };
  for (let i = 0; i <= TRI; i++) for (let j = 0; i + j <= TRI; j++) { const x = [i / TRI, j / TRI, (TRI - i - j) / TRI], r = ratio(a, b, x); M.tri.push({ i, j, r }); if (r > best.r) best = { r, x }; }
  M.triMax = best;
  const key = `${a}|${b}`;
  if (!searchCache.has(key)) searchCache.set(key, new Map());
  M.search = searchCache.get(key);
  M.witness = null;
  MODEL = M;
}
/* one dimension of the numerical search per frame, so the page stays responsive */
function stepSearch() {
  const M = MODEL; if (M.excluded) return false;
  for (const n of NS) if (!M.search.has(n)) { M.search.set(n, maxRatio(M.a, M.b, n)); syncedKey = ''; return true; }
  if (!M.witnessDone) {
    M.witnessDone = true;
    const fail = NS.find((n) => M.search.get(n).ratio > 1 + EPS);
    M.witness = fail ? { n: fail, x: smallestWitness(M.a, M.b, fail) } : null;
    syncedKey = ''; return true;
  }
  return false;
}
const searchDone = () => MODEL.excluded || (NS.every((n) => MODEL.search.has(n)) && MODEL.witnessDone);
function numericN(M) { let last = 1; for (const n of NS) { const s = M.search.get(n); if (!s) return null; if (s.ratio > 1 + EPS) return last; last = n; } return last; }
/* the point shown in 3D and the readouts: the frozen triple, the smallest witness, or the numerical maximum */
function focusPoint(M) {
  const f = S.preset ? PRESETS[S.preset].focus : 'max';
  if (f === 'lean' && M.a === 6 && M.b === 1) return { label: '(6, 5, 5)', x: [6, 5, 5] };
  if (f === 'small' && M.witness && M.witness.x && M.witness.n === 3) return { label: `(${M.witness.x.join(', ')})`, x: M.witness.x };
  const s3 = M.search.get(3);
  return s3 ? { label: T('n = 3 的数值最大值', 'numerical maximum at n = 3'), x: s3.x } : { label: T('n = 3 的网格最大值', 'grid maximum at n = 3'), x: M.triMax.x };
}

/* =====================================================================
   5. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');

/* =====================================================================
   6. 3D scene: the triangle of 3-tuples, height = signed √|ratio − 1|
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 20000, PTS_MAX = 2400;
const CAMS = { iso: [0.55, 1.0, 12.5], front: [0.0001, 1.5, 12], top: [0.0001, 0.06, 12.5] };
const cam = { theta: 0.55, phi: 1.0, r: 12.5, tTheta: 0.55, tPhi: 1.0, tR: 12.5 };
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
/* barycentric (x₁, x₂, x₃) with Σ = 1 → the plane; the vertices sit at 120° */
const R3 = 4.2, VERT = [0, 1, 2].map((k) => [R3 * Math.sin(2 * Math.PI * k / 3), R3 * Math.cos(2 * Math.PI * k / 3)]);
const HS = 2.6, height = (r) => { const d = r - 1; return HS * Math.sign(d) * Math.sqrt(Math.abs(d)); };
function posOf(x, h = 0) { const s = x[0] + x[1] + x[2] || 1, p = [0, 0]; for (let k = 0; k < 3; k++) { p[0] += VERT[k][0] * x[k] / s; p[1] += VERT[k][1] * x[k] / s; } return [p[0], h, p[1]]; }
function updateGL() {
  const M = MODEL, a = M.a, b = M.b;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, col, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, al, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  /* the zero plane (ratio = 1) and the triangle's edges */
  for (let k = 0; k < 3; k++) seg([VERT[k][0], 0, VERT[k][1]], [VERT[(k + 1) % 3][0], 0, VERT[(k + 1) % 3][1]], COL.amber, 0.6);
  for (let t = 1; t < 8; t++) { const f = t / 8; for (let k = 0; k < 3; k++) { const e = [0, 0, 0]; e[k] = f; e[(k + 1) % 3] = 1 - f; const e2 = [0, 0, 0]; e2[k] = f; e2[(k + 2) % 3] = 1 - f; seg(posOf(e), posOf(e2), COL.amber, 0.12); } }
  /* the surface as a triangular mesh of lines, magenta where the inequality fails */
  const H = (i, j) => { const x = [i / TRI, j / TRI, (TRI - i - j) / TRI]; const r = ratio(a, b, x); return { p: posOf(x, height(r)), bad: r > 1 + EPS }; };
  const cache = new Map(), get = (i, j) => { const k = i * 1000 + j; if (!cache.has(k)) cache.set(k, H(i, j)); return cache.get(k); };
  for (let i = 0; i <= TRI; i++) for (let j = 0; i + j <= TRI; j++) {
    const p = get(i, j);
    for (const [di, dj] of [[1, 0], [0, 1], [-1, 1]]) { const i2 = i + di, j2 = j + dj; if (i2 < 0 || j2 < 0 || i2 + j2 > TRI) continue; const q = get(i2, j2), bad = p.bad && q.bad; seg(p.p, q.p, bad ? COL.magenta : COL.cyan, bad ? 0.9 : 0.32); }
  }
  /* equal entries: ratio exactly 1 */
  dot(posOf([1, 1, 1], 0), COL.sigma, 1, 1.6);
  const F = focusPoint(M), rf = ratio(a, b, F.x);
  seg(posOf(F.x, 0), posOf(F.x, height(rf)), COL.amber, 1); dot(posOf(F.x, height(rf)), COL.amber, 1, 2.6);
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
  camera.up.set(0, 1, 0); camera.lookAt(0, -0.4, 0);
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
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(40, Math.max(6, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(40, Math.max(6, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

/* =====================================================================
   8. Tags
   ===================================================================== */
const tagPool = [];
function tagAt(k, cls) { while (tagPool.length <= k) { const el = document.createElement('div'); el.className = 'tag raw'; tagsBox.appendChild(el); tagPool.push(el); } const el = tagPool[k]; el.className = 'tag raw ' + cls; return el; }
function placeTag(el, p) {
  if (!glOK) { el.style.display = 'none'; return; }
  const q = proj3(p); if (q.z > 1 || q.z < -1) { el.style.display = 'none'; return; }
  el.style.display = 'block';
  const w = el.offsetWidth, Wd = stage.clientWidth, x = Math.min(Wd - w / 2 - 6, Math.max(w / 2 + 6, q.x));
  el.style.left = x + 'px'; el.style.top = q.y + 'px';
}
function updateTags() {
  const M = MODEL; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  ['x₁', 'x₂', 'x₃'].forEach((t, j) => { const e = [0, 0, 0]; e[j] = 1; const p = posOf(e, 0); put(t, [p[0] * 1.12, 0, p[2] * 1.12], 'cy'); });
  put(T('全相等：比值 1', 'equal entries: ratio 1'), posOf([1, 1, 1], -0.45), 'gr');
  const F = focusPoint(M), r = ratio(M.a, M.b, F.x);
  put(`${F.label} · ${fr(r, 5)}`, posOf(F.x, height(r) + 0.45), 'hot');
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
/* the threshold: 8ab sin²(π/n) against (a + b − 1)² for n = 1 … 12 */
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 40); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, NMAXC = 12, lhs = (M.a + M.b - 1) ** 2;
  const top = Math.max(lhs, 8 * M.a * M.b, 1) * 1.12, X = (n) => pl + iw * (n - 1) / (NMAXC - 1), Y = (y) => pt + ih - ih * y / top;
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  ctx.strokeStyle = MG; ctx.lineWidth = 1.6 * dpr; ctx.setLineDash([6 * dpr, 4 * dpr]); ctx.beginPath(); ctx.moveTo(pl, Y(lhs)); ctx.lineTo(pl + iw, Y(lhs)); ctx.stroke(); ctx.setLineDash([]);
  lab(ctx, `(a + b − 1)² = ${gs(lhs)}`, pl + iw, Y(lhs) - 3 * dpr, 'right', 'bottom', MG);
  for (let n = 1; n <= NMAXC; n++) {
    const v = n === 1 ? null : thrRight(M.a, M.b, n), ok = !M.excluded && isThreshold(M.a, M.b, n);
    if (v !== null) { ctx.fillStyle = ok ? CY : 'rgba(110,140,170,0.5)'; ctx.beginPath(); ctx.arc(X(n), Y(v), 3.4 * dpr, 0, 2 * Math.PI); ctx.fill(); }
    lab(ctx, String(n), X(n), pt + ih + 4 * dpr, 'center', 'top', M.nstar === n ? AM : DIM);
  }
  if (M.nstar && M.nstar <= NMAXC) { ctx.strokeStyle = AM; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(X(M.nstar), pt); ctx.lineTo(X(M.nstar), pt + ih); ctx.stroke(); ctx.setLineDash([]); lab(ctx, `N* = ${M.nstar}`, X(M.nstar) + 4 * dpr, pt + 2 * dpr, 'left', 'top', AM); }
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>8ab sin²(π/n) ${T('（门槛成立）', '(threshold holds)')}</span><span class="it"><i class="sw" style="--c:${MG}"></i>(a + b − 1)²</span><span class="it"><i class="sw" style="--c:${AM}"></i>N*</span>`;
}
/* the numerical search: the largest ratio found in each dimension */
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 40); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F;
  const vals = NS.map((n) => (M.search.get(n) ? M.search.get(n).ratio : null)), top = Math.max(0.05, ...vals.filter((v) => v !== null).map((v) => Math.sqrt(Math.max(0, v - 1)))) * 1.15;
  const X = (k) => pl + iw * (k + 0.5) / NS.length, Y = (h) => pt + ih - ih * h / top, w = iw / NS.length * 0.55;
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
  NS.forEach((n, k) => {
    const v = vals[k];
    lab(ctx, `n = ${n}`, X(k), pt + ih + 4 * dpr, 'center', 'top', M.nstar === n ? AM : DIM);
    if (v === null) { lab(ctx, '…', X(k), Y(0) - 4 * dpr, 'center', 'bottom'); return; }
    if (v > 1 + EPS) { const h = Math.sqrt(v - 1); ctx.fillStyle = MG; ctx.fillRect(X(k) - w / 2, Y(h), w, Y(0) - Y(h)); lab(ctx, fr(v, v < 1.001 ? 6 : 4), X(k), Y(h) - 3 * dpr, 'center', 'bottom', INK); }
    else { ctx.fillStyle = CY; ctx.fillRect(X(k) - w / 2, Y(0) - 3 * dpr, w, 3 * dpr); lab(ctx, '1', X(k), Y(0) - 6 * dpr, 'center', 'bottom', CY); }
  });
  if (M.nstar) { const k = NS.indexOf(M.nstar); if (k >= 0) { ctx.strokeStyle = AM; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(X(k) + iw / NS.length / 2, pt); ctx.lineTo(X(k) + iw / NS.length / 2, pt + ih); ctx.stroke(); ctx.setLineDash([]); lab(ctx, T('N* 右侧：猜想预期失败', 'right of N*: the conjecture expects failure'), X(k) + iw / NS.length / 2 + 4 * dpr, pt + 2 * dpr, 'left', 'top', AM); } }
  $('c2Meta').textContent = T('每个 n 找到的最大比值 LHS/RHS；高度 = √(比值 − 1)，青 = 只找到全相等时的 1', 'the largest ratio LHS/RHS found for each n; height = √(ratio − 1), cyan = only the 1 of equal entries was found');
}

/* =====================================================================
   10. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function witnessText(M) {
  const F = focusPoint(M);
  if (exactOK(M.a, M.b) && F.x.every(Number.isInteger)) { const e = exactDiff(M.a, M.b, F.x); return `${F.label}: ${e.lhs} − ${e.rhs} = ${e.diff}`; }
  const s = sides(M.a, M.b, F.x); return `${F.label}: ${T('比值', 'ratio')} ${fr(s.lhs / s.rhs, 6)}`;
}
function readouts() {
  const M = MODEL, nn = numericN(M);
  pill('pillA', 'a', gs(M.a)); pill('pillB', 'b', gs(M.b)); pill('pillC', 'N*', M.nstar === null ? '—' : String(M.nstar)); pill('pillD', T('数值', 'NUM'), nn === null ? '…' : (nn === 7 ? '≥ 7' : String(nn)));
  const w = M.witness;
  setRo([[T('(a, b) · c = (a + b + 1)/2', '(a, b) · c = (a + b + 1)/2'), `(${gs(M.a)}, ${gs(M.b)}) · ${M.c % 1 ? M.c.toFixed(2) : M.c}`],
    [T('猜想的 N*(a, b)', 'Conjectured N*(a, b)'), M.excluded ? T('a + b = 1 被排除', 'a + b = 1 is excluded') : String(M.nstar)],
    [T('数值上成立的最大维数（只查到 n = 7）', 'Largest dimension that holds numerically (checked up to n = 7)'), nn === null ? T('搜索中…', 'searching…') : (nn === 7 ? '≥ 7' : String(nn))],
    [T('琥珀点：两边之差', 'Amber point: the two sides'), witnessText(M)],
    [T('最先失败的维数的最小整数反例（最大分量 ≤ 上限）', 'Smallest integer counterexample in the first failing dimension (largest entry ≤ cap)'), !searchDone() ? T('搜索中…', 'searching…') : !w ? T('n ≤ 7 内没有失败', 'no failure for n ≤ 7') : w.x ? `n = ${w.n}: (${w.x.join(', ')}) · ${exactDiff(M.a, M.b, w.x).diff}` : T(`n = ${w.n}：${exactOK(M.a, M.b) && CAP[w.n] ? `最大分量 ≤ ${CAP[w.n]} 内没有` : '只在 a、b、c 为整数且 n ≤ 4 时穷举'}`, `n = ${w.n}: ${exactOK(M.a, M.b) && CAP[w.n] ? `none with largest entry ≤ ${CAP[w.n]}` : 'searched only for integer a, b, c and n ≤ 4'}`)]]);
  const mx = M.triMax;
  $('roNote').innerHTML = T(`n = 3 的三角形上（${TRI} 等分网格）比值最大 ${fr(mx.r, 5)}，在 (${mx.x.map((v) => fr(v / Math.max(...mx.x), 3)).join(', ')})（按最大分量归一）。`, `On the triangle of 3-tuples (a grid of ${TRI} steps) the largest ratio is ${fr(mx.r, 5)}, at (${mx.x.map((v) => fr(v / Math.max(...mx.x), 3)).join(', ')}) (scaled to largest entry 1).`);
}
function syncControls() {
  const M = MODEL;
  $('aSlider').value = M.a; $('aVal').textContent = gs(M.a); $('bSlider').value = M.b; $('bVal').textContent = gs(M.b);
}
const stateKey = () => `${S.a}|${S.b}|${S.preset}|${Math.round(S.nowFrac * 100)}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; toasted = false; syncControls(); glKey = ''; }
  if (!toasted && S.playing && S.nowFrac >= 1 && searchDone()) {
    toasted = true; const M = MODEL, nn = numericN(M);
    toast(M.nstar !== null && nn !== null && nn < M.nstar ? T(`<b>猜想说 N* = ${M.nstar}</b>，数值上 n = ${nn + 1} 已经失败。`, `<b>The conjecture says N* = ${M.nstar}</b>, but numerically n = ${nn + 1} already fails.`) : T(`<b>N* = ${M.nstar}</b>：n ≤ 7 内数值与猜想一致。`, `<b>N* = ${M.nstar}</b>: for n ≤ 7 the numbers agree with the conjecture.`));
  }
  const key = stateKey() + `|${MODEL.search.size}|${MODEL.witnessDone ? 1 : 0}`; if (key === syncedKey) return; syncedKey = key;
  const M = MODEL;
  readouts();
  $('formula').innerHTML = `(Σ x<sub>i</sub>)(Σ x<sub>i</sub><sup>a</sup> x<sub>i+1</sub><sup>b</sup>) ≤ (Σ x<sub>i</sub><sup>c</sup>)², &nbsp; c = (a + b + 1)/2`;
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('paramNote').innerHTML = T('N*(a, b) = max{n : n = 1 或 (a + b − 1)² ≤ 8ab sin²(π/n)}。等号用 10⁻⁹ 的相对容差判定，因为 48·sin²(π/3) 在浮点下是 35.999…。', 'N*(a, b) = max{n : n = 1 or (a + b − 1)² ≤ 8ab sin²(π/n)}. Equality is decided with a relative tolerance of 10⁻⁹, because 48·sin²(π/3) is 35.999… in floating point.');
  $('litNote').innerHTML = T('比值、门槛、数值搜索与整数反例都由页面算出；冻结的是 (a, b) = (6, 1) 时猜想不成立。', 'The ratios, the threshold, the numerical search and the integer counterexamples are computed on the page; what is frozen is that the conjecture fails at (a, b) = (6, 1).');
  $('c1Title').textContent = T('猜想的门槛：哪些 n 满足 (a + b − 1)² ≤ 8ab sin²(π/n)', 'The conjecture’s threshold: which n satisfy (a + b − 1)² ≤ 8ab sin²(π/n)');
  $('c2Title').textContent = T('数值搜索：每个维数 n 找到的最大比值', 'Numerical search: the largest ratio found in each dimension n');
  $('clock').innerHTML = `${Math.round(S.nowFrac * 360)}°`;
  $('hudBig').textContent = `n = 3 · (a, b) = (${gs(M.a)}, ${gs(M.b)}) · ${T('最大比值', 'max ratio')} ${fr(M.triMax.r, 5)}`;
  $('hudSub').textContent = T('三角形 = 所有非负三元组（按和归一）；高度 = 带符号的 √|LHS/RHS − 1|，零平面以上（品红）不等式失败，青色网格不等式成立；白点 = 全相等，琥珀点 = 当前标出的三元组', 'The triangle holds every nonnegative triple (scaled to sum 1); height = signed √|LHS/RHS − 1|, above the zero plane (magenta) the inequality fails, the cyan mesh is where it holds; white point = equal entries, amber point = the marked triple');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
function custom() { S.preset = null; markPreset(); dirty = true; }
$('aSlider').addEventListener('input', () => { S.a = Math.round(parseFloat($('aSlider').value) * 2) / 2; custom(); });
$('bSlider').addEventListener('input', () => { S.b = Math.round(parseFloat($('bSlider').value) * 2) / 2; custom(); });
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.a = p.a; S.b = p.b; S.preset = name; markPreset(); dirty = true;
  S.nowFrac = p.frac; S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.nowFrac;
  build(); setCamPreset('iso');
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(Math.round(S.nowFrac * 24 + (ev.key === 'ArrowRight' ? 1 : -1)) / 24); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(1);
});

/* =====================================================================
   11. Main loop: the time axis turns the camera once around the triangle
   ===================================================================== */
let lastT = performance.now(), frameCount = 0, glKey = '';
function resize() {
  if (!glOK) return;
  const r = stage.getBoundingClientRect();
  renderer.setSize(Math.max(1, r.width), Math.max(1, r.height), false);
  camera.aspect = Math.max(0.2, r.width / Math.max(1, r.height)); camera.updateProjectionMatrix();
}
let railTheta = null;
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  stepSearch();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { S.nowFrac = S.dir > 0 ? 0 : 1; toasted = false; } }
    else {
      S.nowFrac += S.dir * dtSec * S.speed / RUN;
      if (S.nowFrac >= 1) { S.nowFrac = 1; S.hold = 2.4; }
      if (S.nowFrac <= 0) { S.nowFrac = 0; S.hold = 1.2; }
    }
    $('now').value = S.nowFrac;
  }
  /* the rail sets the viewing angle around the triangle */
  if (railTheta !== S.nowFrac) { railTheta = S.nowFrac; cam.tTheta = CAMS.iso[0] + 2 * Math.PI * S.nowFrac; if (!S.playing) cam.theta = cam.tTheta; }
  syncOutputs();
  if (glOK) {
    updateCamera(dtSec);
    const k = `${MODEL.id}|${S.preset}|${MODEL.search.has(3) ? 1 : 0}|${MODEL.witnessDone ? 1 : 0}`;
    if (k !== glKey) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); });

/* read-only probe for automated browser tests */
window.CA_DEBUG = {
  pending: () => dirty || !searchDone() || syncedKey !== stateKey() + `|${MODEL.search.size}|${MODEL.witnessDone ? 1 : 0}`,
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => {
    const M = MODEL, F = focusPoint(M);
    return { a: M.a, b: M.b, c: M.c, nstar: M.nstar, excluded: M.excluded, numericN: numericN(M),
      search: NS.map((n) => (M.search.get(n) ? { n, ratio: M.search.get(n).ratio, x: M.search.get(n).x } : null)),
      witness: M.witness ? { n: M.witness.n, x: M.witness.x, diff: M.witness.x ? String(exactDiff(M.a, M.b, M.witness.x).diff) : null } : null,
      focus: { label: F.label, x: F.x, ratio: ratio(M.a, M.b, F.x) }, triMax: { r: M.triMax.r, x: M.triMax.x }, tri: TRI };
  },
  setFrac: (f) => { S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; }
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('max'); S.playing = false; setPlayUI(); S.nowFrac = 0; $('now').value = 0; setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 11; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
