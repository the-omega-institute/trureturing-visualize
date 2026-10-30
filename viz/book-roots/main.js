/* BOOK//ROOTS · the book-graph domination root conjecture fails at the square
   Rather (2026, Conjecture 5.4) conjectured that D(B_n, x), the domination polynomial of the book B_n (n four-cycles sharing
   an edge), has exactly four real roots counting multiplicity: 0 twice, then one root below −2 and one in (−1/2, 0) for even
   n, two roots in (−1/2, 0) for odd n. Frozen in trureturing (RatherBookRootRefutation.result): false for the full range
   n ≥ 1, because B₁ = C₄ and D(C₄, x) = x²((x + 2)² + 2). The page enumerates dominating sets for n ≤ 8, uses the closed form
   x²(1 + x)^{2n} + (2x + 1)(x² + 2x)^n − 2x^n otherwise, and finds the real and complex roots for n ≤ 20.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Constants and the polynomial
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.5, 0.58, 0.68], WHITE = [0.92, 0.95, 1];
const NMIN = 1, NMAX = 20, NENUM = 8, RUN = 16;
const fr = (x, d = 4) => (isFinite(x) ? (Math.abs(x) < 5e-13 ? 0 : x).toFixed(d) : '—');
const binom = (n, k) => { let r = 1; for (let i = 1; i <= k; i++) r = r * (n - k + i) / i; return Math.round(r); };
/* coefficients of x²(1 + x)^{2n} + (2x + 1)·x^n·(x + 2)^n − 2x^n, constant term first */
function closedForm(n) {
  const c = new Array(2 * n + 3).fill(0);
  for (let k = 0; k <= 2 * n; k++) c[k + 2] += binom(2 * n, k);
  for (let k = 0; k <= n; k++) { const v = binom(n, k) * 2 ** (n - k); c[n + k] += v; c[n + k + 1] += 2 * v; }
  c[n] -= 2;
  while (c.length > 1 && c[c.length - 1] === 0) c.pop();
  return c;
}
/* vertices 0, 1 (the spine edge) and, for page i, 2i + 2 (next to 1) and 2i + 3 (next to 0) */
function neighbours(n) {
  const N = 2 * n + 2, adj = Array.from({ length: N }, () => new Set());
  const e = (u, v) => { adj[u].add(v); adj[v].add(u); };
  e(0, 1); for (let i = 0; i < n; i++) { e(1, 2 * i + 2); e(2 * i + 2, 2 * i + 3); e(2 * i + 3, 0); }
  return adj;
}
/* every subset by bitmask: dom[m] = closed neighbourhood of m, built from m without its lowest bit */
const ENUM = new Map();
function enumerate(n) {
  if (ENUM.has(n)) return ENUM.get(n);
  const adj = neighbours(n), N = adj.length, full = (1 << N) - 1, cn = adj.map((s, v) => [...s].reduce((m, u) => m | (1 << u), 1 << v));
  const dom = new Int32Array(1 << N), coeffs = new Array(N + 1).fill(0), sets = [];
  for (let m = 1; m <= full; m++) { const low = m & -m; dom[m] = dom[m ^ low] | cn[31 - Math.clz32(low)]; }
  for (let m = 0; m <= full; m++) if (dom[m] === full) { let k = 0; for (let x = m; x; x &= x - 1) k++; coeffs[k]++; sets.push(m); }
  while (coeffs.length > 1 && coeffs[coeffs.length - 1] === 0) coeffs.pop();
  const res = { coeffs, sets }; ENUM.set(n, res); return res;
}
/* D(B_n, x)/x² from the closed form, stable for x away from 0: (1 + x)^{2n} + (2x + 1)·x^{n−2}·(x + 2)^n − 2x^{n−2} */
const pReal = (n, x) => (1 + x) ** (2 * n) + (2 * x + 1) * x ** (n - 2) * (x + 2) ** n - 2 * x ** (n - 2);
const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]], cadd = (a, b) => [a[0] + b[0], a[1] + b[1]];
const cpow = (z, k) => { let r = [1, 0], b = z; if (k < 0) { const d = z[0] * z[0] + z[1] * z[1]; b = [z[0] / d, -z[1] / d]; k = -k; } while (k) { if (k & 1) r = cmul(r, b); b = cmul(b, b); k >>= 1; } return r; };
const pCx = (n, z) => cadd(cadd(cpow([1 + z[0], z[1]], 2 * n), cmul(cmul([2 * z[0] + 1, 2 * z[1]], cpow(z, n - 2)), cpow([z[0] + 2, z[1]], n))), cmul([-2, 0], cpow(z, n - 2)));
/* real roots of D/x²: sign changes on a fine grid of [−10, 0), refined by bisection */
function realRoots(n) {
  const out = [], G = 60000, lo = -10, hi = -1e-6; let xp = lo, yp = pReal(n, lo);
  for (let i = 1; i <= G; i++) {
    const x = lo + (hi - lo) * i / G, y = pReal(n, x);
    if (yp === 0) out.push(xp);
    else if (Math.sign(y) !== Math.sign(yp)) { let a = xp, b = x, fa = yp; for (let it = 0; it < 80; it++) { const m = (a + b) / 2, fm = pReal(n, m); if (Math.sign(fm) === Math.sign(fa)) { a = m; fa = fm; } else b = m; } out.push((a + b) / 2); }
    xp = x; yp = y;
  }
  return out;
}
/* all 2n roots of the monic D/x² by Durand–Kerner */
function complexRoots(n) {
  const d = 2 * n; let z = Array.from({ length: d }, (_, k) => { const a = 2 * Math.PI * (k + 0.25) / d; return [-1 + 1.4 * Math.cos(a), 1.4 * Math.sin(a)]; });
  for (let it = 0; it < 800; it++) {
    let move = 0;
    z = z.map((zi, i) => {
      let den = [1, 0]; z.forEach((zj, j) => { if (j !== i) den = cmul(den, [zi[0] - zj[0], zi[1] - zj[1]]); });
      const num = pCx(n, zi), dd = den[0] * den[0] + den[1] * den[1], q = [(num[0] * den[0] + num[1] * den[1]) / dd, (num[1] * den[0] - num[0] * den[1]) / dd];
      move = Math.max(move, Math.hypot(q[0], q[1])); return [zi[0] - q[0], zi[1] - q[1]];
    });
    if (move < 1e-14) break;
  }
  return z.map(([a, b]) => [a, Math.abs(b) < 1e-9 ? 0 : b]);
}
/* the conjecture's prediction for n, and whether the roots found satisfy it */
function verdict(n, rr) {
  if (n % 2 === 0) return { kind: 'even', holds: rr.length === 2 && rr[0] < -2 && rr[1] > -0.5 && rr[1] < 0 };
  return { kind: 'odd', holds: rr.length === 2 && rr.every((r) => r > -0.5 && r < 0) };
}

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { n: 1, t: 1, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean', cycle: false, setIdx: 0, cycleClock: 0 };
const PRESETS = {
  lean: { n: 1, play: false, cycle: false,
    zh: 'Lean 里的反例：n = 1 时书图只有一页，就是四边形 C₄。它的支配集是 6 个两点集、4 个三点集与全集，D = 6x² + 4x³ + x⁴ = x²((x + 2)² + 2)。括号恒正，所以除了 0 没有实根——右边复平面上的两个根是 −2 ± i√2，都不在实轴上。',
    en: 'The counterexample in Lean: at n = 1 the book has a single page, the four-cycle C₄. Its dominating sets are the 6 pairs, the 4 triples and the whole set, D = 6x² + 4x³ + x⁴ = x²((x + 2)² + 2). The bracket is always positive, so there is no real root besides 0 — the two roots in the complex plane on the right are −2 ± i√2, off the real axis.' },
  sweep: { n: 1, play: true, cycle: false,
    zh: '从 n = 1 翻到 20：复根云逐渐围成一圈，实轴上从 n = 2 起每次恰好出现猜想说的两个根——偶数时一个在 −2 左边、一个在 (−1/2, 0)，奇数时两个都在 (−1/2, 0)。只有 n = 1 不合。n ≥ 2 的规律是页面数值，不是定理。',
    en: 'Leaf from n = 1 to 20: the cloud of complex roots closes into a ring, and from n = 2 on the real axis shows exactly the two roots the conjecture predicts — one below −2 and one in (−1/2, 0) for even n, two in (−1/2, 0) for odd n. Only n = 1 breaks the pattern. The pattern for n ≥ 2 is page numbers, not a theorem.' },
  two: { n: 2, play: false, cycle: false,
    zh: 'n = 2：D = 3x² + 16x³ + 15x⁴ + 6x⁵ + x⁶（页面枚举了 2⁶ = 64 个子集），非零实根约 −2.2113 与 −0.2343——符合偶数情形的预测。',
    en: 'n = 2: D = 3x² + 16x³ + 15x⁴ + 6x⁵ + x⁶ (the page enumerated all 2⁶ = 64 subsets), nonzero real roots about −2.2113 and −0.2343 — as predicted for even n.' },
  three: { n: 3, play: false, cycle: false,
    zh: 'n = 3：D = x² + 12x³ + 43x⁴ + 50x⁵ + 28x⁶ + 8x⁷ + x⁸，非零实根约 −0.2451 与 −0.1563，两个都在 (−1/2, 0) 里——符合奇数情形的预测。',
    en: 'n = 3: D = x² + 12x³ + 43x⁴ + 50x⁵ + 28x⁶ + 8x⁷ + x⁸, nonzero real roots about −0.2451 and −0.1563, both in (−1/2, 0) — as predicted for odd n.' },
  edge: { n: 16, play: false, cycle: false,
    zh: 'n = 16：偶数情形里 (−1/2, 0) 中的那个根约 −0.4985，已经很贴近 −1/2；另一个约 −2.5352。区间是否还能收紧，卷宗列为未决。页面数值。',
    en: 'n = 16: in the even case the root in (−1/2, 0) is about −0.4985, very close to −1/2; the other is about −2.5352. Whether the intervals can be sharpened is open in the dossier. Page numbers.' },
  sets: { n: 4, play: false, cycle: true,
    zh: 'n = 4：书有 10 个顶点，2¹⁰ = 1024 个子集里有一部分是支配集，页面逐个点亮（每个点要么亮、要么挨着亮点）。{0, 1} 这条书脊本身就支配整本书，所以 n ≥ 1 时最小支配集的大小是 2。',
    en: 'n = 4: the book has 10 vertices, and some of the 2¹⁰ = 1024 subsets dominate; the page lights them up one by one (every vertex is lit or next to a lit one). The spine {0, 1} alone dominates the whole book, so the smallest dominating set has size 2 for every n ≥ 1.' }
};
let MODEL = null, dirty = true, modelId = 0;
function build() {
  S.n = Math.min(NMAX, Math.max(NMIN, Math.round(S.n)));
  const n = S.n, coeffs = closedForm(n), en = n <= NENUM ? enumerate(n) : null, rr = realRoots(n), cr = complexRoots(n);
  const domSet = en ? en.sets[S.setIdx % en.sets.length] : 3;   /* beyond the enumeration, the spine {0, 1} */
  MODEL = { id: ++modelId, n, coeffs, enumCoeffs: en ? en.coeffs : null, domCount: coeffs.reduce((s, v) => s + v, 0), realRoots: rr, complexRoots: cr, verdict: verdict(n, rr), domSet, setsTotal: en ? en.sets.length : null };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');

/* =====================================================================
   4. 3D scene: the book on the left, the complex plane on the right
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 4000, PTS_MAX = 400;
const CAMS = { iso: [0.5, 1.05, 17], front: [0.0001, 1.4, 16], top: [0.0001, 0.06, 18] };
const cam = { theta: 0.5, phi: 1.05, r: 17, tTheta: 0.5, tPhi: 1.05, tR: 17 };
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
/* the book: spine from vertex 0 (bottom) to vertex 1 (top) at BX; page i fanned at angle φ_i; vertex 2i + 2 top outer, 2i + 3 bottom outer */
const BX = -4.2, HB = 2.4, RB = 2.3;
const pageAngle = (i, n) => (n === 1 ? 0 : -0.8 * Math.PI + 1.6 * Math.PI * i / (n - 1));
function vpos(v, n) {
  if (v === 0) return [BX, 0, 0]; if (v === 1) return [BX, HB, 0];
  const i = (v - 2) >> 1, a = pageAngle(i, n), top = v % 2 === 0;
  return [BX + RB * Math.cos(a), top ? HB : 0, RB * Math.sin(a)];
}
/* the complex plane: Re → x, Im → −z around (CX, 0, 0), scale SC */
const CX = 3.4, SC = 1.25, cz = (z) => [CX + SC * (z[0] + 1), 0, -SC * z[1]];
function updateGL() {
  const M = MODEL, n = M.n;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, col, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, al, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  /* the book and its dominating set: members amber, dominated vertices cyan */
  const inSet = (u) => ((M.domSet >> u) & 1) === 1, N = 2 * n + 2;
  seg(vpos(0, n), vpos(1, n), COL.amber, 1);
  for (let i = 0; i < n; i++) {
    const a = 2 * i + 2, b = 2 * i + 3;
    seg(vpos(1, n), vpos(a, n), GREY, 0.7); seg(vpos(a, n), vpos(b, n), GREY, 0.7); seg(vpos(b, n), vpos(0, n), GREY, 0.7);
    for (let s = 1; s < 4; s++) { const f = s / 4; seg([BX, HB * f, 0], [vpos(a, n)[0], HB * f, vpos(a, n)[2]], GREY, 0.08); }
  }
  for (let u = 0; u < N; u++) dot(vpos(u, n), inSet(u) ? COL.amber : COL.cyan, inSet(u) ? 1 : 0.55, inSet(u) ? 2.4 : 1.4);
  /* the complex plane: grid, real axis, the conjectured intervals and the roots */
  for (let re = -3; re <= 1; re++) seg(cz([re, -2.2]), cz([re, 2.2]), GREY, re === 0 ? 0.35 : 0.12);
  for (let im = -2; im <= 2; im++) seg(cz([-3.3, im]), cz([1, im]), GREY, im === 0 ? 0.5 : 0.12);
  seg([cz([-3.3, 0])[0], 0.02, 0], [cz([-2, 0])[0], 0.02, 0], COL.cyan, 1);
  seg([cz([-0.5, 0])[0], 0.02, 0], [cz([0, 0])[0], 0.02, 0], COL.amber, 1);
  dot(cz([0, 0]), WHITE, 1, 2.2);
  for (const z of M.complexRoots) {
    const real = z[1] === 0, p = cz(z);
    dot(p, real ? COL.magenta : COL.cyan, 1, real ? 2.4 : 1.5);
    if (real) seg(p, [p[0], 0.9, p[2]], COL.magenta, 0.9);
  }
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
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.45 : 1), c = [0, 0.9, 0];
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
  put(T(`书图 B_${M.n}（${2 * M.n + 2} 个顶点）`, `book B_${M.n} (${2 * M.n + 2} vertices)`), [BX, HB + 0.7, 0], 'gr');
  put('0', [BX - 0.35, -0.2, 0], 'hot'); put('1', [BX - 0.35, HB + 0.2, 0], 'hot');
  put('(−∞, −2)', [cz([-2.7, 0])[0], 0.35, 0.45], 'cy'); put('(−½, 0)', [cz([-0.25, 0])[0], 0.35, 0.45], 'hot');
  put(T('复平面：D/x² 的根', 'complex plane: roots of D/x²'), [cz([-1, 2.4])[0], 0.3, cz([-1, 2.4])[2]], 'gr');
  if (!M.realRoots.length) put(T('实轴上没有根', 'no root on the real axis'), [cz([-1.2, 0])[0], 1.0, 0], 'mg');
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
function lab(ctx, txt, x, y, al, bl, col = DIM) { ctx.fillStyle = col; ctx.textAlign = al; ctx.textBaseline = bl; ctx.fillText(txt, x, y); }
const slog = (y) => Math.sign(y) * Math.log10(1 + Math.abs(y));
/* D/x² on [−3, 0.3], on a signed log scale, with the conjectured intervals shaded */
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 40); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, lo = -3, hi = 0.3, X = (x) => pl + iw * (x - lo) / (hi - lo);
  const N = 600, ys = []; let top = 0.5;
  for (let i = 0; i <= N; i++) { const x = lo + (hi - lo) * i / N, y = Math.abs(x) < 1e-9 ? M.coeffs[2] : slog(pReal(M.n, x)); ys.push([x, y]); top = Math.max(top, Math.abs(y)); }
  const Y = (y) => pt + ih / 2 - (ih / 2) * y / top;
  ctx.fillStyle = 'rgba(25,240,255,0.08)'; ctx.fillRect(X(lo), pt, X(-2) - X(lo), ih);
  ctx.fillStyle = 'rgba(255,200,61,0.10)'; ctx.fillRect(X(-0.5), pt, X(0) - X(-0.5), ih);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
  for (const x of [-3, -2, -1, -0.5, 0]) lab(ctx, String(x), X(x), pt + ih + 4 * dpr, 'center', 'top', x === -2 || x === -0.5 ? AM : DIM);
  for (const y of [-top, 0, top]) lab(ctx, y === 0 ? '0' : `${y < 0 ? '−' : ''}10^${Math.abs(y).toFixed(0)}`, pl - 4 * dpr, Y(y), 'right', 'middle');
  ctx.strokeStyle = INK; ctx.lineWidth = 1.6 * dpr; ctx.beginPath(); ys.forEach(([x, y], i) => { if (i === 0) ctx.moveTo(X(x), Y(y)); else ctx.lineTo(X(x), Y(y)); }); ctx.stroke();
  for (const r of M.realRoots) if (r >= lo) { ctx.fillStyle = MG; ctx.beginPath(); ctx.arc(X(r), Y(0), 4 * dpr, 0, 2 * Math.PI); ctx.fill(); }
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${INK}"></i>sgn·log₁₀(1 + |D/x²|)</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('根', 'roots')}</span>`;
}
/* the nonzero real roots for every n, against the conjectured bands */
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 34); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, lo = -2.8, hi = 0, bw = iw / NMAX, X = (n) => pl + bw * (n - 0.5), Y = (y) => pt + ih * (hi - y) / (hi - lo);
  ctx.fillStyle = 'rgba(25,240,255,0.08)'; ctx.fillRect(pl, Y(-2), iw, Y(lo) - Y(-2));
  ctx.fillStyle = 'rgba(255,200,61,0.10)'; ctx.fillRect(pl, Y(0), iw, Y(-0.5) - Y(0));
  ctx.fillStyle = 'rgba(255,255,255,0.06)'; ctx.fillRect(X(M.n) - bw / 2, pt, bw, ih);
  for (const y of [0, -0.5, -2]) lab(ctx, String(y), pl - 4 * dpr, Y(y), 'right', 'middle', y === 0 ? DIM : AM);
  for (let n = NMIN; n <= NMAX; n++) {
    const rr = ALL[n - 1]; if (!rr) continue;
    if (!rr.length) lab(ctx, '∅', X(n), Y(-1.2), 'center', 'middle', MG);
    for (const r of rr) { ctx.fillStyle = verdict(n, rr).holds ? (n % 2 ? AM : CY) : MG; ctx.beginPath(); ctx.arc(X(n), Y(Math.max(lo, r)), 3 * dpr, 0, 2 * Math.PI); ctx.fill(); }
    if (n === 1 || n % 5 === 0 || n === M.n) lab(ctx, String(n), X(n), pt + ih + 4 * dpr, 'center', 'top', n === M.n ? AM : DIM);
  }
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('偶数 n', 'even n')}</span><span class="it"><i class="sw" style="--c:${AM}"></i>${T('奇数 n', 'odd n')}</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('与猜想不符', 'against the conjecture')}</span>`;
}
const ALL = Array.from({ length: NMAX }, (_, i) => realRoots(i + 1));

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const SUP = '⁰¹²³⁴⁵⁶⁷⁸⁹', sup = (k) => String(k).split('').map((d) => SUP[+d]).join('');
function polyTxt(c, maxTerms = 7) {
  const terms = []; c.forEach((v, k) => { if (v) terms.push(`${v === 1 && k ? '' : v}${k ? 'x' + (k > 1 ? sup(k) : '') : ''}`); });
  return terms.length <= maxTerms ? terms.join(' + ') : `${terms.slice(0, 3).join(' + ')} + … + ${terms.slice(-2).join(' + ')}`;
}
function readouts() {
  const M = MODEL, V = M.verdict, low = M.coeffs.findIndex((v) => v > 0);
  pill('pillA', 'n', M.n); pill('pillB', T('顶点', 'VERTICES'), 2 * M.n + 2); pill('pillC', T('猜想', 'CONJECTURE'), V.holds ? T('符合', 'fits') : T('不符', 'fails')); pill('pillD', T('非零实根', 'REAL ROOTS'), M.realRoots.length);
  setRo([[T('支配集个数 D(B_n, 1) · 最小支配集的大小', 'Dominating sets D(B_n, 1) · smallest dominating set'), `${M.domCount} · ${low}`],
    [T('D(B_n, x)', 'D(B_n, x)'), polyTxt(M.coeffs)],
    [T('非零实根（0 是二重根）', 'Nonzero real roots (0 is a double root)'), M.realRoots.length ? M.realRoots.map((r) => fr(r, 6)).join(', ') : T('没有', 'none')],
    [T('猜想的预测', 'What the conjecture predicts'), V.kind === 'even' ? T('偶数：一个 < −2，一个在 (−1/2, 0)', 'even: one < −2, one in (−1/2, 0)') : T('奇数：两个在 (−1/2, 0)', 'odd: two in (−1/2, 0)')],
    [T('系数的来源', 'Where the coefficients come from'), M.enumCoeffs ? T(`枚举 2^${2 * M.n + 2} 个子集，与闭式${M.enumCoeffs.join() === M.coeffs.join() ? '逐项一致' : '不一致'}`, `enumerating 2^${2 * M.n + 2} subsets, ${M.enumCoeffs.join() === M.coeffs.join() ? 'equal to the closed form term by term' : 'different from the closed form'}`) : T('闭式（n > 8 不再枚举）', 'the closed form (no enumeration for n > 8)')]]);
  $('roNote').innerHTML = M.n === 1 ? T('D = x²((x + 2)² + 2)：括号恒正，除 0 外没有实根——奇数分支要的两个根不存在，猜想在 n = 1 不成立（Lean 定理）。', 'D = x²((x + 2)² + 2): the bracket is always positive, so there is no real root besides 0 — the two roots the odd branch needs do not exist, and the conjecture fails at n = 1 (Lean theorem).')
    : V.holds ? T('找到的实根符合猜想的模式（页面数值，不是证明）。', 'The real roots found follow the conjectured pattern (page numbers, not a proof).') : T('找到的实根不符合猜想的模式。', 'The real roots found do not follow the conjectured pattern.');
}
const stateKey = () => `${S.n}|${S.preset}|${S.setIdx}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; $('nIn').value = S.n; $('nOut').textContent = S.n; }
  const M = MODEL;
  if (!toasted && S.playing && S.t >= NMAX) { toasted = true; const bad = ALL.map((rr, i) => (verdict(i + 1, rr).holds ? null : i + 1)).filter((x) => x); toast(T(`<b>n = 1 … ${NMAX}</b>：与猜想不符的只有 n = ${bad.join('、')}——n = 1 是 Lean 定理，其余 n 的规律是页面数值。`, `<b>n = 1 … ${NMAX}</b>: only n = ${bad.join(', ')} breaks the pattern — n = 1 is a Lean theorem, the pattern for the other n is page numbers.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('polyNote').innerHTML = T(`顶点 0、1 是书脊；第 i 页加上 2i + 2（连 1）与 2i + 3（连 0）。${M.setsTotal ? `共有 ${M.setsTotal} 个支配集，三维视图点亮其中第 ${S.setIdx % M.setsTotal + 1} 个。` : '三维视图点亮书脊 {0, 1}，它支配整本书。'}`, `Vertices 0 and 1 form the spine; page i adds 2i + 2 (joined to 1) and 2i + 3 (joined to 0). ${M.setsTotal ? `There are ${M.setsTotal} dominating sets; the 3D view lights number ${S.setIdx % M.setsTotal + 1}.` : 'The 3D view lights the spine {0, 1}, which dominates the whole book.'}`);
  $('litNote').innerHTML = T('多项式与根都由页面算出；冻结的是 n = 1 时猜想不成立。', 'The polynomials and roots are computed on the page; what is frozen is that the conjecture fails at n = 1.');
  $('c1Title').textContent = T(`实轴上的 D(B_${M.n}, x)/x²（青、琥珀：猜想放根的区间）`, `D(B_${M.n}, x)/x² on the real axis (cyan, amber: where the conjecture puts roots)`);
  $('c2Title').textContent = T('n = 1 … 20 的非零实根', 'Nonzero real roots for n = 1 … 20');
  $('clock').innerHTML = `n = ${M.n}`;
  $('hudBig').textContent = `B_${M.n} · ${M.realRoots.length ? T(`非零实根 ${M.realRoots.map((r) => fr(r, 3)).join(', ')}`, `nonzero real roots ${M.realRoots.map((r) => fr(r, 3)).join(', ')}`) : T('除 0 外没有实根', 'no real root besides 0')} · ${M.verdict.holds ? T('符合猜想', 'fits the conjecture') : T('与猜想不符', 'against the conjecture')}`;
  $('hudSub').textContent = T('左：书图，琥珀的书脊是公共边 0–1，每页一个四边形；琥珀点 = 一个支配集，青点 = 被它支配的顶点。右：复平面，品红 = 实根（竖线），青 = 复根，白点 = 0（二重根），实轴上青段 (−∞, −2)、琥珀段 (−1/2, 0) 是猜想放根的区间', 'Left: the book, the amber spine is the shared edge 0–1 and every page a four-cycle; amber dots = a dominating set, cyan dots = vertices it dominates. Right: the complex plane, magenta = real roots (with stems), cyan = complex roots, white = 0 (a double root); on the real axis the cyan stretch (−∞, −2) and the amber stretch (−1/2, 0) are where the conjecture puts roots');
}
function syncRail() {
  const key = TRV.lang(); if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, T('n = 1（Lean）', 'n = 1 (Lean)')], [(10 - 1) / (NMAX - 1), 'n = 10'], [1, `n = ${NMAX}`]];
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.n = p.n; S.t = p.n; S.preset = name; S.cycle = p.cycle; S.setIdx = 0; S.cycleClock = 0; S.hold = 0; toasted = false; markPreset(); dirty = true;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = (S.t - NMIN) / (NMAX - NMIN);
  build(); dirty = true; setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const setN = (t, user) => { S.t = Math.min(NMAX, Math.max(NMIN, t)); $('now').value = (S.t - NMIN) / (NMAX - NMIN); const k = Math.round(S.t); if (k !== S.n) { S.n = k; S.setIdx = 0; dirty = true; } if (user) { S.preset = null; markPreset(); dirty = true; } };
$('now').addEventListener('input', () => { setN(NMIN + parseFloat($('now').value) * (NMAX - NMIN), true); S.hold = 0; });
$('nIn').addEventListener('input', () => { setN(parseInt($('nIn').value, 10), true); });
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
const jumpTo = (t) => { S.playing = false; setPlayUI(); setN(t, true); };
document.addEventListener('keydown', (ev) => {
  if (ev.target && (ev.target.tagName === 'INPUT' && ev.target.type !== 'range')) return;
  if (drawer.isOpen()) return;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(S.n + (ev.key === 'ArrowRight' ? 1 : -1)); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(NMAX);
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
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setN(S.dir > 0 ? NMIN : NMAX); toasted = false; } }
    else {
      setN(S.t + S.dir * dtSec * S.speed * (NMAX - NMIN) / RUN);
      if (S.t >= NMAX) S.hold = 2.4;
      if (S.t <= NMIN && S.dir < 0) S.hold = 1.2;
    }
  }
  if (S.cycle && !reduceMotion && MODEL && MODEL.setsTotal) { S.cycleClock += dtSec; if (S.cycleClock > 1.2) { S.cycleClock = 0; S.setIdx++; dirty = true; } }
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
window.BK_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { n: M.n, coeffs: M.coeffs.slice(), enumCoeffs: M.enumCoeffs && M.enumCoeffs.slice(), domCount: M.domCount, realRoots: M.realRoots.slice(), complexRoots: M.complexRoots.map((z) => z.slice()), verdict: { ...M.verdict }, domSet: M.domSet, setsTotal: M.setsTotal }; },
  allReal: () => ALL.map((r) => r.slice()),
  setN: (n) => setN(n)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('two'); S.playing = false; setPlayUI(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 15; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
