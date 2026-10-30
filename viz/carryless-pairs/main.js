/* CARRYLESS//PAIRS · ordinary against carryless multiplication
   C(u, k) is binary polynomial multiplication (OEIS A048720): bit t of C(u, k) is the parity of Σᵢ bitᵢ(u) bit_{t−i}(k).
   Four OEIS entries by Karttunen ask whether two equations m·k = C(u, k) pick the same k, or one set inside the other.
   Frozen in trureturing (four modules in D5/S1/Digit/Admissibility): 9k = C(25, k) ⇔ 15k = C(19, k), 7k = C(11, k) ⇔
   5k = C(13, k), 13k = C(29, k) ⇒ 11k = C(31, k) and 17k = C(49, k) ⇒ 9k = C(25, k), for every k ≥ 0. Each proof runs
   both equations as automata on the bits of k, lowest first, and closes a finite relation between their states. The page
   builds that product automaton, walks k through it, and compares the two sets.
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
const GREY = [0.46, 0.54, 0.64], VIOLET = [0.62, 0.55, 1.0];
const LENS = [8, 10, 12], RUN = 40;
/* first equation m₁k = C(u₁, k), second m₂k = C(u₂, k); kind: 'iff' or 'imp' (first ⇒ second) */
const MODS = {
  A115801: { e1: [9, 25], e2: [15, 19], kind: 'iff', oeis: ['A115801'], lean: 'CarrylessMultiplierEquivalence', related: 29, issue: 23220 },
  A115770: { e1: [7, 11], e2: [5, 13], kind: 'iff', oeis: ['A115770'], lean: 'CarrylessSevenFiveEquivalence', related: 15, issue: 23261 },
  A115803: { e1: [13, 29], e2: [11, 31], kind: 'imp', oeis: ['A115805', 'A115803'], lean: 'CarrylessThirteenElevenContainment', related: 50, issue: 23302 },
  A115809: { e1: [17, 49], e2: [9, 25], kind: 'imp', oeis: ['A115809', 'A115801'], lean: 'CarrylessSeventeenNineContainment', related: 101, issue: 23260 }
};
const fmtRel = (Md) => `${Md.e1[0]}k = C(${Md.e1[1]}, k) ${Md.kind === 'iff' ? '⇔' : '⇒'} ${Md.e2[0]}k = C(${Md.e2[1]}, k)`;

/* =====================================================================
   2. Carryless products and the digit automaton
   ===================================================================== */
/* binary polynomial product, by shifting and exclusive or (BigInt, so no width limit) */
function clmul(u, k) { let r = 0n, U = BigInt(u), K = BigInt(k), s = 0n; while (K > 0n) { if (K & 1n) r ^= U << s; K >>= 1n; s++; } return r; }
const holdsEq = ([m, u], k) => BigInt(m) * BigInt(k) === clmul(u, k);
/* state (c, d) means m·k + c = P(u, k) xor d still has to hold for the unread part; null = rejected. Reading bit b:
   e = (b ? u : 0) xor d, v = m·b + c; the low bits must agree, then (c, d) → (v div 2, e div 2) */
function step([m, u], s, b) {
  if (!s) return null;
  const [c, d] = s, e = (b ? u : 0) ^ d, v = m * b + c;
  return (v & 1) === (e & 1) ? [v >> 1, e >> 1] : null;
}
const accepts = (s) => !!s && s[0] === s[1];
const skey = (s) => (s ? `(${s[0]}, ${s[1]})` : '∅');
const pkey = (p) => `${skey(p[0])}|${skey(p[1])}`;
function productAutomaton(Md) {
  const start = [[0, 0], [0, 0]], nodes = [start], index = new Map([[pkey(start), 0]]), edges = [], depth = [0];
  for (let i = 0; i < nodes.length; i++) for (const b of [0, 1]) {
    const n = [step(Md.e1, nodes[i][0], b), step(Md.e2, nodes[i][1], b)], k = pkey(n);
    if (!index.has(k)) { index.set(k, nodes.length); nodes.push(n); depth.push(depth[i] + 1); }
    edges.push({ from: i, to: index.get(k), b });
  }
  const cls = nodes.map(([a, b]) => (accepts(a) && accepts(b) ? 'both' : accepts(a) ? 'first' : accepts(b) ? 'second' : !a && !b ? 'dead' : 'alive'));
  return { nodes, index, edges, depth, cls };
}
/* the path of k through the automaton, lowest bit first */
function walk(A, k) {
  const path = [0]; let i = 0, K = k;
  while (K > 0) { const b = K & 1; i = A.edges.find((e) => e.from === i && e.b === b).to; path.push(i); K = Math.floor(K / 2); }
  return path;
}
/* deterministic 3D spring layout seeded by breadth-first depth */
function layout(A) {
  const n = A.nodes.length, rnd = TRV.mulberry32(97 + n), P = A.depth.map((d, i) => [d * 0.9 - 3, (rnd() - 0.5) * 3, (rnd() - 0.5) * 3]);
  const adj = new Set(A.edges.filter((e) => e.from !== e.to).map((e) => `${Math.min(e.from, e.to)},${Math.max(e.from, e.to)}`));
  for (let it = 0; it < 260; it++) {
    const F = P.map(() => [0, 0, 0]), t = 0.06 * (1 - it / 300);
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
      const d = [P[j][0] - P[i][0], P[j][1] - P[i][1], P[j][2] - P[i][2]], r = Math.max(0.05, Math.hypot(...d)), rep = 1.4 / (r * r), att = adj.has(`${i},${j}`) ? (r - 1.3) * 0.6 : 0, f = att - rep;
      for (let q = 0; q < 3; q++) { F[i][q] += f * d[q] / r; F[j][q] -= f * d[q] / r; }
    }
    for (let i = 0; i < n; i++) for (let q = 0; q < 3; q++) P[i][q] += Math.max(-0.4, Math.min(0.4, F[i][q] * t));
  }
  const c = [0, 1, 2].map((q) => P.reduce((s, p) => s + p[q], 0) / n), R = Math.max(...P.map((p) => Math.hypot(p[0] - c[0], p[1] - c[1], p[2] - c[2]))) || 1;
  return P.map((p) => p.map((v, q) => (v - c[q]) * 4.0 / R));
}

/* =====================================================================
   3. State and presets
   ===================================================================== */
const S = { mod: 'A115801', len: 10, nowFrac: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'nine' };
const PRESETS = {
  nine: { mod: 'A115801', len: 10, k: 0, play: true,
    zh: 'A115801：9k = C(25, k) 的 k 与 15k = C(19, k) 的 k 是否同一批？OEIS 查到 2²⁵ 并猜想相同；本库在 Lean 里对全部 k ≥ 0 证明了。三维是两条方程同时读 k 的二进制位（低位先）的乘积自动机：29 个状态，全部状态上两条方程“此刻结束是否成立”都一致。',
    en: 'A115801: do 9k = C(25, k) and 15k = C(19, k) pick the same k? OEIS checked up to 2²⁵ and conjectured so; this library proves it in Lean for every k ≥ 0. The 3D view is the product automaton that reads the bits of k, lowest first, for both equations at once: 29 states, and in every one the two equations agree on whether they would hold if the input ended there.' },
  seven: { mod: 'A115770', len: 10, k: 0, play: true,
    zh: 'A115770：7k = C(11, k) ⇔ 5k = C(13, k)。乘积自动机只有 15 个状态。下方条码上下两行逐位相同——两个集合相等。',
    en: 'A115770: 7k = C(11, k) ⇔ 5k = C(13, k). The product automaton has only 15 states. The two rows of the barcode below agree position by position — the two sets are equal.' },
  member: { mod: 'A115801', len: 10, k: 15, play: false,
    zh: 'k = 15 = 1111₂：9·15 = 135，C(25, 15) = 11001₂ 与 1111₂ 的无进位乘积也是 135；15·15 = 225 = C(19, 15)。路径从 (0, 0) 出发，读完四个 1 停在一个两条方程都成立的状态（琥珀）。',
    en: 'k = 15 = 1111₂: 9·15 = 135, and the carryless product of 11001₂ and 1111₂ is also 135; 15·15 = 225 = C(19, 15). The path starts at (0, 0), reads four 1s and stops in a state where both equations hold (amber).' },
  contain: { mod: 'A115803', len: 12, k: 0, play: true,
    zh: 'A115805 ⊆ A115803：13k = C(29, k) ⇒ 11k = C(31, k)。反方向不成立——例如 k = 15 满足第二条而不满足第一条。50 个状态里有些只有第二条方程成立（紫），但没有一个状态只有第一条成立。',
    en: 'A115805 ⊆ A115803: 13k = C(29, k) ⇒ 11k = C(31, k). The converse fails — k = 15, for example, satisfies the second equation but not the first. Of the 50 states some accept only the second equation (violet), but none accepts only the first.' },
  seventeen: { mod: 'A115809', len: 12, k: 0, play: true,
    zh: 'A115809 ⊆ A115801：17k = C(49, k) ⇒ 9k = C(25, k)。A115809 自 2006 年起写着“Subset of A115801 ?”。乘积自动机最大，101 个状态。',
    en: 'A115809 ⊆ A115801: 17k = C(49, k) ⇒ 9k = C(25, k). A115809 has carried “Subset of A115801 ?” since 2006. Its product automaton is the largest, 101 states.' },
  converse: { mod: 'A115803', len: 10, k: 15, play: false,
    zh: 'k = 15 只走到一个“只有第二条成立”的状态：11·15 = 165 = C(31, 15)，而 13·15 = 195 ≠ C(29, 15) = 187。所以包含关系只是单向的。',
    en: 'k = 15 ends in a state where only the second equation holds: 11·15 = 165 = C(31, 15), while 13·15 = 195 ≠ C(29, 15) = 187. So the containment goes one way only.' }
};

/* =====================================================================
   4. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
const cache = new Map();
function build() {
  if (!MODS[S.mod]) S.mod = 'A115801';
  if (!LENS.includes(S.len)) S.len = 10;
  if (!cache.has(S.mod)) { const Md = MODS[S.mod], A = productAutomaton(Md); cache.set(S.mod, { A, P: layout(A) }); }
  const Md = MODS[S.mod], { A, P } = cache.get(S.mod), K = 2 ** S.len;
  const m1 = new Uint8Array(K), m2 = new Uint8Array(K); let c1 = 0, c2 = 0, bad = 0;
  for (let k = 0; k < K; k++) { m1[k] = holdsEq(Md.e1, k) ? 1 : 0; m2[k] = holdsEq(Md.e2, k) ? 1 : 0; c1 += m1[k]; c2 += m2[k]; if (Md.kind === 'iff' ? m1[k] !== m2[k] : m1[k] && !m2[k]) bad++; }
  MODEL = { id: ++modelId, mod: S.mod, Md, A, P, len: S.len, K, m1, m2, c1, c2, bad };
}
const kNow = () => Math.round(S.nowFrac * (MODEL.K - 1));

/* =====================================================================
   5. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const bin = (x) => (typeof x === 'bigint' ? x : BigInt(x)).toString(2);

/* =====================================================================
   6. 3D scene: the product automaton
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 2000, PTS_MAX = 400;
const CAMS = { iso: [0.6, 1.1, 15], front: [0.0001, 1.5, 14], top: [0.0001, 0.06, 15] };
const cam = { theta: 0.6, phi: 1.1, r: 15, tTheta: 0.6, tPhi: 1.1, tR: 15 };
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
const CLS_COL = { both: COL.amber, first: COL.magenta, second: VIOLET, alive: COL.cyan, dead: GREY };
function updateGL() {
  const M = MODEL, { A, P } = M, path = walk(A, kNow()), onPath = new Set(path), pathEdges = new Set();
  for (let i = 1; i < path.length; i++) pathEdges.add(`${path[i - 1]}>${path[i]}`);
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, col, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, al, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  /* edges: bit 0 grey-blue, bit 1 brighter; a self-loop is drawn as a short tick; the current path in amber */
  for (const e of A.edges) {
    const a = P[e.from], b = P[e.to], hot = pathEdges.has(`${e.from}>${e.to}`);
    if (e.from === e.to) { seg(a, [a[0], a[1] + 0.35, a[2]], hot ? COL.amber : (e.b ? COL.cyan : GREY), hot ? 1 : 0.35); continue; }
    /* shift the two directions of a pair slightly apart */
    const off = e.b ? 0.05 : -0.05, toDead = A.cls[e.to] === 'dead';
    seg([a[0], a[1] + off, a[2]], [b[0], b[1] + off, b[2]], hot ? COL.amber : (e.b ? COL.cyan : GREY), hot ? 1 : toDead ? 0.07 : (e.b ? 0.36 : 0.24));
  }
  A.nodes.forEach((_, i) => dot(P[i], CLS_COL[A.cls[i]], onPath.has(i) ? 1 : 0.7, i === 0 ? 2.4 : (onPath.has(i) ? 1.9 : 1.3)));
  const end = path[path.length - 1]; dot(P[end], COL.sigma, 1, 3.0);
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
  const M = MODEL, { A, P } = M, path = walk(A, kNow()), end = path[path.length - 1]; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  put(T('起点 (0, 0)|(0, 0)', 'start (0, 0)|(0, 0)'), [P[0][0], P[0][1] + 0.6, P[0][2]], 'hot');
  if (end !== 0) put(`${T('终点', 'end')} ${pkey(A.nodes[end])}`, [P[end][0], P[end][1] - 0.6, P[end][2]], A.cls[end] === 'both' ? 'hot' : A.cls[end] === 'second' ? 'vi' : 'cy');
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
/* membership barcode: one row per equation over 0 ≤ k < 2^L */
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 74); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, k0 = kNow(), X = (k) => pl + iw * (k + 0.5) / M.K, rowH = ih * 0.32;
  const rows = [[M.m1, `${M.Md.e1[0]}k = C(${M.Md.e1[1]}, k)`, CY, pt + ih * 0.08], [M.m2, `${M.Md.e2[0]}k = C(${M.Md.e2[1]}, k)`, '#9d8cff', pt + ih * 0.56]];
  for (const [mem, name, col, y] of rows) {
    ctx.fillStyle = 'rgba(110,140,170,0.08)'; ctx.fillRect(pl, y, iw, rowH);
    ctx.fillStyle = col; for (let k = 0; k < M.K; k++) if (mem[k]) ctx.fillRect(X(k) - Math.max(0.6, iw / M.K / 2) , y, Math.max(1.2 * dpr, iw / M.K), rowH);
    lab(ctx, name, pl - 6 * dpr, y + rowH / 2, 'right', 'middle', col);
  }
  for (let k = 0; k < M.K; k++) if (M.Md.kind === 'iff' ? M.m1[k] !== M.m2[k] : M.m1[k] && !M.m2[k]) { ctx.fillStyle = MG; ctx.fillRect(X(k) - 1.5 * dpr, pt, 3 * dpr, ih); }
  ctx.strokeStyle = AM; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); ctx.moveTo(X(k0), pt); ctx.lineTo(X(k0), pt + ih); ctx.stroke();
  for (const k of [0, M.K / 2, M.K - 1]) lab(ctx, String(k), X(k), pt + ih + 4 * dpr, k === 0 ? 'left' : k === M.K - 1 ? 'right' : 'center', 'top');
  $('c1Meta').textContent = T(`0 ≤ k < 2^${M.len}：第一条方程 ${M.c1} 个，第二条 ${M.c2} 个，${M.Md.kind === 'iff' ? '不一致' : '只满足第一条'}的 ${M.bad} 个（品红）；琥珀线 = 当前 k`, `0 ≤ k < 2^${M.len}: ${M.c1} for the first equation, ${M.c2} for the second, ${M.bad} ${M.Md.kind === 'iff' ? 'disagreements' : 'satisfying only the first'} (magenta); amber line = current k`);
}
/* the two products of the current k, bit by bit */
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 96); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, k = kNow(), Md = M.Md;
  const rows = [['k', BigInt(k), INK], [`${Md.e1[0]}·k`, BigInt(Md.e1[0]) * BigInt(k), CY], [`C(${Md.e1[1]}, k)`, clmul(Md.e1[1], k), CY], [`${Md.e2[0]}·k`, BigInt(Md.e2[0]) * BigInt(k), '#9d8cff'], [`C(${Md.e2[1]}, k)`, clmul(Md.e2[1], k), '#9d8cff']];
  const width = Math.max(...rows.map((r) => bin(r[1]).length), 4), cw = Math.min(16 * dpr, iw / width), rh = ih / rows.length;
  ctx.font = `${Math.min(13 * dpr, cw * 0.9)}px ${TRV.fonts.data}`;
  rows.forEach(([name, val, col], r) => {
    const s = bin(val).padStart(width, ' '), y = pt + rh * (r + 0.5), pair = r === 1 || r === 2 ? [rows[1][1], rows[2][1]] : r >= 3 ? [rows[3][1], rows[4][1]] : null;
    lab(ctx, name, pl - 8 * dpr, y, 'right', 'middle', col);
    for (let j = 0; j < width; j++) {
      if (s[j] === ' ') continue;
      const bit = width - 1 - j, differ = pair && (((pair[0] >> BigInt(bit)) & 1n) !== ((pair[1] >> BigInt(bit)) & 1n));
      lab(ctx, s[j], pl + iw - (width - j - 0.5) * cw, y, 'center', 'middle', differ ? MG : col);
    }
  });
  $('c2Meta').textContent = T('二进制，低位在右；品红 = 普通乘积与无进位乘积在这一位不同', 'binary, lowest bit on the right; magenta = the ordinary and the carryless product differ in that bit');
}

/* =====================================================================
   10. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const yes = (b) => (b ? T('成立', 'holds') : T('不成立', 'fails'));
function readouts() {
  const M = MODEL, Md = M.Md, k = kNow(), path = walk(M.A, k), end = path[path.length - 1];
  const h1 = holdsEq(Md.e1, k), h2 = holdsEq(Md.e2, k);
  pill('pillA', 'k', String(k)); pill('pillB', T('状态', 'STATES'), String(M.A.nodes.length)); pill('pillC', T('第一条', '1ST'), yes(h1)); pill('pillD', T('第二条', '2ND'), yes(h2));
  setRo([[T('定理', 'Theorem'), `${fmtRel(Md)} · ${Md.oeis.join(' ⊆ ')}`],
    [T('k（十进制 · 二进制）', 'k (decimal · binary)'), `${k} · ${bin(k)}₂`],
    [T('第一条方程', 'First equation'), `${Md.e1[0]}·${k} = ${BigInt(Md.e1[0]) * BigInt(k)} · C(${Md.e1[1]}, ${k}) = ${clmul(Md.e1[1], k)} · ${yes(h1)}`],
    [T('第二条方程', 'Second equation'), `${Md.e2[0]}·${k} = ${BigInt(Md.e2[0]) * BigInt(k)} · C(${Md.e2[1]}, ${k}) = ${clmul(Md.e2[1], k)} · ${yes(h2)}`],
    [T('乘积自动机：可达状态 · 边 · Lean 的 related 集合大小', 'Product automaton: reachable states · edges · size of Lean’s related set'), `${M.A.nodes.length} · ${M.A.edges.length} · ${Md.related}`]]);
  $('roNote').innerHTML = T(`k 的路径（低位先读）：${path.map((i) => pkey(M.A.nodes[i])).join(' → ')}；终点${M.A.cls[end] === 'both' ? '两条方程都成立' : M.A.cls[end] === 'second' ? '只有第二条成立' : M.A.cls[end] === 'first' ? '只有第一条成立' : '两条都不成立'}。`, `The path of k (lowest bit first): ${path.map((i) => pkey(M.A.nodes[i])).join(' → ')}; at the end ${M.A.cls[end] === 'both' ? 'both equations hold' : M.A.cls[end] === 'second' ? 'only the second holds' : M.A.cls[end] === 'first' ? 'only the first holds' : 'neither holds'}.`);
}
function syncControls() {
  const M = MODEL;
  document.querySelectorAll('#modChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.mod === M.mod)));
  document.querySelectorAll('#lenChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.len === M.len)));
}
const stateKey = () => `${S.mod}|${S.len}|${kNow()}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; toasted = false; syncControls(); $('marks').dataset.key = ''; glKey = ''; }
  if (!toasted && S.playing && S.nowFrac >= 1) {
    toasted = true; const M = MODEL;
    toast(T(`<b>0 ≤ k < 2^${M.len}</b>：第一条 ${M.c1} 个，第二条 ${M.c2} 个，${M.Md.kind === 'iff' ? '两个集合相同' : '第一个集合含在第二个里'}——Lean 证明对全部 k 都如此。`, `<b>0 ≤ k < 2^${M.len}</b>: ${M.c1} for the first equation, ${M.c2} for the second, ${M.Md.kind === 'iff' ? 'the same set' : 'the first set inside the second'} — Lean proves this for every k.`));
  }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  const M = MODEL, k = kNow();
  readouts();
  $('formula').innerHTML = T('C(u, k) 的第 t 位 = (Σ<sub>i</sub> u 的第 i 位 · k 的第 t − i 位) mod 2，即 GF(2) 上的多项式乘法（A048720）。', 'Bit t of C(u, k) = (Σ<sub>i</sub> bit i of u · bit t − i of k) mod 2: polynomial multiplication over GF(2) (A048720).');
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('modNote').innerHTML = T(`时间轴 = k，从 0 到 2^${M.len} − 1。状态 (c, d) 表示剩下的位还需要满足 m·k + c = C(u, k) xor d；读一位 b：e = (b ? u : 0) xor d，v = m·b + c，两者末位相同才继续，变成 (⌊v/2⌋, ⌊e/2⌋)，否则拒绝（∅）。读完时 c = d 就成立。`, `The time axis is k, from 0 to 2^${M.len} − 1. A state (c, d) means the remaining bits must still satisfy m·k + c = C(u, k) xor d; reading a bit b: e = (b ? u : 0) xor d, v = m·b + c, continue to (⌊v/2⌋, ⌊e/2⌋) if their last bits agree, otherwise reject (∅). When the input ends, the equation holds if c = d.`);
  $('litNote').innerHTML = T('乘积、自动机、路径与计数都由页面算出；冻结的是对全部 k ≥ 0 的四个等价或包含关系。', 'The products, the automaton, the paths and the counts are computed on the page; what is frozen are the four equivalences or containments for every k ≥ 0.');
  $('c1Title').textContent = T('两个集合的条码：哪些 k 满足哪条方程', 'Barcode of the two sets: which k satisfy which equation');
  $('c2Title').textContent = T(`当前 k = ${k} 的普通乘积与无进位乘积`, `Ordinary and carryless products for the current k = ${k}`);
  $('clock').innerHTML = `k = ${k}`;
  $('hudBig').textContent = `${fmtRel(M.Md)} · k = ${k}`;
  $('hudSub').textContent = T('节点 = 两条方程的状态对；边 = 读一位（青 = 1，灰 = 0），琥珀 = k 的路径。琥珀点：读完即两条都成立；紫：只有第二条成立；青：都不成立但还没被拒绝；灰：都被拒绝。品红（只有第一条成立）一个都没有。', 'Nodes = pairs of states of the two equations; edges = reading a bit (cyan = 1, grey = 0), amber = the path of k. Amber nodes: both would hold if the input ended there; violet: only the second; cyan: neither, not yet rejected; grey: both rejected. Magenta (only the first) never occurs.');
}
function syncRail() {
  const M = MODEL, key = `${M.id}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 'k = 0'], [0.5, `k = 2^${M.len - 1}`], [1, `k = 2^${M.len} − 1`]];
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
function custom() { S.preset = null; markPreset(); dirty = true; }
document.querySelectorAll('#modChips .chip').forEach((b) => b.addEventListener('click', () => { S.mod = MODS[b.dataset.mod] ? b.dataset.mod : 'A115801'; custom(); }));
document.querySelectorAll('#lenChips .chip').forEach((b) => b.addEventListener('click', () => { S.len = LENS.includes(+b.dataset.len) ? +b.dataset.len : 10; custom(); }));
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.mod = p.mod; S.len = p.len; S.preset = name; markPreset(); dirty = true; build(); dirty = false; syncedKey = ''; toasted = false; syncControls(); $('marks').dataset.key = ''; glKey = '';
  S.nowFrac = p.k / (2 ** p.len - 1); S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.nowFrac;
  setCamPreset('iso');
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo((kNow() + (ev.key === 'ArrowRight' ? 1 : -1)) / (MODEL.K - 1)); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(1);
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
    const k = `${MODEL.id}|${kNow()}`;
    if (k !== glKey) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.CL_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => {
    const M = MODEL, k = kNow(), path = walk(M.A, k);
    return { mod: M.mod, e1: M.Md.e1, e2: M.Md.e2, kind: M.Md.kind, len: M.len, K: M.K, k, c1: M.c1, c2: M.c2, bad: M.bad,
      states: M.A.nodes.length, edges: M.A.edges.length, related: M.Md.related, classes: M.A.cls.reduce((o, c) => { o[c] = (o[c] || 0) + 1; return o; }, {}),
      path: path.map((i) => pkey(M.A.nodes[i])), end: M.A.cls[path[path.length - 1]],
      p1: String(BigInt(M.Md.e1[0]) * BigInt(k)), cl1: String(clmul(M.Md.e1[1], k)), p2: String(BigInt(M.Md.e2[0]) * BigInt(k)), cl2: String(clmul(M.Md.e2[1], k)) };
  },
  members: (which) => { const M = MODEL, out = []; for (let k = 0; k < M.K; k++) if ((which === 1 ? M.m1 : M.m2)[k]) out.push(k); return out; },
  automaton: () => ({ nodes: MODEL.A.nodes, edges: MODEL.A.edges.map((e) => [e.from, e.to, e.b]), cls: MODEL.A.cls }),
  setFrac: (f) => { S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; }
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('member'); S.playing = false; setPlayUI(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 13; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('nine');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
