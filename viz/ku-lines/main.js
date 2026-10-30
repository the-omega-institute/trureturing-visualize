/* KU//LINES · near-line-avoiding saturated configurations on [k]^d
   A configuration contains no k − 1 points of any full line p + t·v (0 ≤ t < k, v ∈ {−1, 0, 1}^d nonzero); it is saturated
   if no point can be added. Ku's Conjecture 5.6: the largest saturated configuration fills 1 − 2/k of the board. Frozen in
   trureturing (KuGeometry.result): false at k = d = 3, where every configuration has at most 8 < 9 points. The page draws the
   lines, enumerates saturated configurations, and replays the Latin-square obstruction behind the proof.
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
const GREY = [0.55, 0.6, 0.68];
const BOARDS = ['3,2', '4,2', '5,2', '3,3', '4,3', '3,4'], ENUMERATED = ['3,2', '4,2', '3,3'], RUN = 20;
/* configurations found offline and stored as certificates; the page checks that each is valid and saturated */
const CERT = {
  '5,2': [0, 1, 2, 5, 6, 8, 10, 13, 14, 16, 17, 19, 22, 23, 24],
  '4,3': [0, 1, 4, 6, 9, 11, 14, 15, 16, 18, 22, 23, 24, 25, 29, 31, 33, 35, 36, 37, 42, 43, 44, 46, 50, 51, 53, 55, 56, 58, 60, 61],
  '3,4': [0, 5, 7, 11, 22, 29, 42, 46, 48, 64, 66]
};
const SUP = '⁰¹²³⁴⁵⁶⁷⁸⁹', sup = (n) => String(n).split('').map((c) => SUP[+c]).join('');
const boardName = (k, d) => `[${k}]${sup(d)}`;

/* =====================================================================
   2. The board, its lines, configurations
   ===================================================================== */
function geometry(k, d) {
  const N = k ** d, pts = [];
  for (let i = 0; i < N; i++) { const p = []; let x = i; for (let j = 0; j < d; j++) { p.push(x % k); x = Math.floor(x / k); } pts.push(p); }
  const index = (p) => p.reduce((s, c, j) => s + c * k ** j, 0), seen = new Set(), lines = [];
  for (let i = 0; i < N; i++) for (let vi = 0; vi < 3 ** d; vi++) {
    const v = []; let x = vi; for (let j = 0; j < d; j++) { v.push((x % 3) - 1); x = Math.floor(x / 3); }
    if (v.every((c) => c === 0)) continue;
    const L = []; let inside = true;
    for (let t = 0; t < k && inside; t++) { const q = pts[i].map((c, j) => c + t * v[j]); if (q.some((c) => c < 0 || c >= k)) inside = false; else L.push(index(q)); }
    if (!inside) continue;
    const key = L.slice().sort((a, b) => a - b).join(','); if (seen.has(key)) continue;
    seen.add(key); lines.push({ pts: L, kind: v.filter((c) => c !== 0).length });   // kind 1 = axis, 2 = face diagonal, 3+ = longer diagonals
  }
  const lineOf = Array.from({ length: N }, () => []); lines.forEach((L, li) => L.pts.forEach((p) => lineOf[p].push(li)));
  return { k, d, N, pts, lines, lineOf };
}
/* counts per line, violated lines (≥ k − 1 chosen), and points that could still be added */
function inspect(G, S) {
  const cnt = new Int32Array(G.lines.length), inS = new Uint8Array(G.N); S.forEach((p) => { inS[p] = 1; G.lineOf[p].forEach((li) => cnt[li]++); });
  const violated = []; cnt.forEach((c, li) => { if (c >= G.k - 1) violated.push(li); });
  const addable = []; for (let p = 0; p < G.N; p++) if (!inS[p] && G.lineOf[p].every((li) => cnt[li] + 1 <= G.k - 2)) addable.push(p);
  return { cnt, violated, addable, valid: violated.length === 0, saturated: violated.length === 0 && addable.length === 0 };
}
/* every saturated configuration, by backtracking over points in increasing order */
function enumerate(G) {
  const cnt = new Int32Array(G.lines.length), sel = [], out = [];
  const can = (p) => G.lineOf[p].every((li) => cnt[li] + 1 <= G.k - 2);
  const inSel = new Uint8Array(G.N);
  function maximal() { for (let p = 0; p < G.N; p++) if (!inSel[p] && can(p)) return false; return true; }
  (function rec(start) {
    if (maximal()) out.push(sel.slice());
    for (let p = start; p < G.N; p++) {
      if (!can(p)) continue;
      sel.push(p); inSel[p] = 1; G.lineOf[p].forEach((li) => cnt[li]++);
      rec(p + 1);
      sel.pop(); inSel[p] = 0; G.lineOf[p].forEach((li) => cnt[li]--);
    }
  })(0);
  out.sort((a, b) => b.length - a.length || a.join(',').localeCompare(b.join(','), 'en', { numeric: true }));
  return out;
}
/* the 12 Latin squares of order 3 and the 9-point configurations they define on [3]³: point (x, y, L(x, y)) */
function latinSquares() {
  const perms = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]], out = [];
  for (const a of perms) for (const b of perms) for (const c of perms) {
    const L = [a, b, c]; let ok = true;
    for (let y = 0; y < 3 && ok; y++) if (new Set([a[y], b[y], c[y]]).size < 3) ok = false;
    if (ok) out.push(L);
  }
  return out;
}

/* =====================================================================
   3. State and presets
   ===================================================================== */
const S = { board: '3,3', mode: 'configs', nowFrac: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { board: '3,3', mode: 'configs', frac: 0, play: false,
    zh: '3×3×3：猜想要求 9 个点（1 − 2/3 = 1/3），Lean 证明至多 8 个。页面完全枚举全部饱和配置，最大的只有 6 个点——这是其中之一。灰线是全部 49 条直线，青线经过选中点；没有一条直线上有两个选中点，也没有空格还能再加。',
    en: '3×3×3: the conjecture asks for 9 points (1 − 2/3 = 1/3), and Lean proves that at most 8 are possible. The page enumerates every saturated configuration, and the largest has only 6 points — this is one of them. Grey lines are all 49 lines, cyan lines pass through chosen points; no line holds two chosen points, and no empty cell can be added.' },
  latin: { board: '3,3', mode: 'latin', frac: 0, play: true,
    zh: '若有 9 个点，每条轴线恰有一个点，第三个坐标就是前两个坐标的 3 阶 Latin 方阵。时间轴逐个摆出全部 12 个 3 阶 Latin 方阵：每一个的主对角线或副对角线都有重复的值，重复的两个点在同一条面对角线上（品红）。这就是冻结证明的机制。',
    en: 'With 9 points every axis line holds exactly one point, so the third coordinate is a Latin square of order 3 in the first two. The timeline places all 12 Latin squares of order 3: each repeats a value on its main or anti-diagonal, and the two repeated points lie on one face diagonal (magenta). This is the mechanism of the frozen proof.' },
  all: { board: '3,3', mode: 'configs', frac: 0, play: true,
    zh: '逐个看 3×3×3 的全部 305 个饱和配置，从大到小：6 个点的有 8 个，5 个点的 120 个，4 个点的 176 个，还有只含中心一个点的那个——中心与其余 26 格都共线。',
    en: 'Step through all 305 saturated configurations of 3×3×3, largest first: 8 with 6 points, 120 with 5, 176 with 4, and the one holding only the centre — the centre is collinear with all 26 other cells.' },
  plane: { board: '3,2', mode: 'configs', frac: 0, play: false,
    zh: '平面 3×3：猜想要 3 个点，确实能做到，比如 (1, 1)、(2, 3)、(3, 2)。8 条直线（3 行、3 列、2 条对角线）各至多一个点。论文对 d = 2 给出了一般构造。',
    en: 'The plane 3×3: the conjecture asks for 3 points, and 3 are possible, for example (1, 1), (2, 3), (3, 2). The 8 lines (3 rows, 3 columns, 2 diagonals) hold at most one point each. The paper gives a general construction for d = 2.' },
  k43: { board: '4,3', mode: 'configs', frac: 0, play: false,
    zh: '4×4×4：每条直线至多 2 个点。上界是 (4 − 2)·4² = 32，这个离线找到的 32 点配置恰好达到——每条轴线正好 2 个点。这里猜想成立（页面数值，不是定理）。',
    en: '4×4×4: at most 2 points per line. The bound is (4 − 2)·4² = 32, and this configuration of 32 points, found offline, reaches it — every axis line holds exactly 2 points. Here the conjecture holds (page numbers, not a theorem).' },
  d4: { board: '3,4', mode: 'configs', frac: 0, play: false,
    zh: '3×3×3×3（画成三个立方体）：猜想要 27 个点，可完全搜索给出的最大值只有 11——这是其中一个配置。81 个点、272 条直线。最大值 11 来自测试里重跑的穷举，不是定理。',
    en: '3×3×3×3 (drawn as three cubes): the conjecture asks for 27 points, but the exhaustive maximum is only 11 — this is one such configuration. 81 points, 272 lines. The maximum 11 comes from an exhaustive search re-run in the tests, not from a theorem.' }
};

/* =====================================================================
   4. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
const cache = new Map();
const LATIN = latinSquares();
function build() {
  if (!BOARDS.includes(S.board)) S.board = '3,3';
  if (S.mode === 'latin' && S.board !== '3,3') S.mode = 'configs';
  const [k, d] = S.board.split(',').map(Number);
  if (!cache.has(S.board)) {
    const G = geometry(k, d), configs = ENUMERATED.includes(S.board) ? enumerate(G) : [CERT[S.board].slice()];
    const hist = new Map(); configs.forEach((c) => hist.set(c.length, (hist.get(c.length) || 0) + 1));
    cache.set(S.board, { G, configs, hist, enumerated: ENUMERATED.includes(S.board), best: Math.max(...configs.map((c) => c.length)) });
  }
  const B = cache.get(S.board), M = { id: ++modelId, board: S.board, k, d, mode: S.mode, ...B };
  M.ku = (1 - 2 / k) * k ** d;
  M.items = M.mode === 'latin' ? LATIN.map((L) => ({ S: [0, 1, 2].flatMap((x) => [0, 1, 2].map((y) => x + 3 * y + 9 * L[x][y])), L })) : M.configs.map((c) => ({ S: c }));
  MODEL = M;
}
function progress() {
  const M = MODEL, i = Math.round(S.nowFrac * (M.items.length - 1)), item = M.items[i];
  return { i, item, ins: inspect(M.G, item.S) };
}
const coordsOf = (M, p) => M.G.pts[p].map((c) => c + 1);
const fmtPt = (M, p) => `(${coordsOf(M, p).join(', ')})`;

/* =====================================================================
   5. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const fr = (x, d = 4) => (isFinite(x) ? x.toFixed(d) : '—');

/* =====================================================================
   6. 3D scene
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 8000, PTS_MAX = 600;
const CAMS = { iso: [0.65, 1.05, 16], front: [0.0001, 1.5707, 15], top: [0.0001, 0.0601, 16] };
const cam = { theta: 0.65, phi: 1.05, r: 16, tTheta: 0.65, tPhi: 1.05, tR: 16 };
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
/* coordinate 1 → across, 2 → depth, 3 → up; a fourth coordinate places three cubes side by side */
function posOf(M, p) {
  const c = M.G.pts[p], k = M.k, s = (M.d === 4 ? 3.4 : 5.2) / (k - 1), u = (j) => ((c[j] ?? 0) - (k - 1) / 2) * s;
  const off = M.d === 4 ? (c[3] - (k - 1) / 2) * 6.2 : 0;
  return [u(0) + off, M.d >= 3 ? u(2) : 0, u(1)];
}
function updateGL() {
  const M = MODEL, pr = progress(), ins = pr.ins, inS = new Set(pr.item.S), bad = new Set(ins.violated);
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (a, b, col, k) => { if (v + 2 > LINES_MAX) return; for (const p of [a, b]) { Pp[3 * v] = p[0]; Pp[3 * v + 1] = p[1]; Pp[3 * v + 2] = p[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, a, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = a; PT.aSize.array[np] = size; np++; };
  const many = M.G.lines.length > 120;
  M.G.lines.forEach((L, li) => {
    const a = posOf(M, L.pts[0]), b = posOf(M, L.pts[L.pts.length - 1]);
    if (bad.has(li)) seg(a, b, COL.magenta, 1);
    else if (ins.cnt[li] > 0) seg(a, b, COL.cyan, many ? 0.12 : 0.3);
    else seg(a, b, GREY, many ? 0.04 : 0.1);
  });
  const onBad = new Set(); ins.violated.forEach((li) => M.G.lines[li].pts.forEach((p) => { if (inS.has(p)) onBad.add(p); }));
  const addable = new Set(ins.addable);
  for (let p = 0; p < M.G.N; p++) {
    const q = posOf(M, p);
    if (inS.has(p)) dot(q, onBad.has(p) ? COL.magenta : COL.cyan, 1, onBad.has(p) ? 2.6 : 2.3);
    else if (addable.has(p)) dot(q, COL.amber, 0.9, 1.4);
    else dot(q, GREY, 0.45, 0.8);
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
  cam.tTheta = cam.theta + d; cam.tPhi = p[1]; cam.tR = p[2] * (MODEL && MODEL.d === 4 ? 1.35 : 1);
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
  if (drag.pts.size === 2) { const [a, b] = [...drag.pts.values()], d = Math.hypot(a.x - b.x, a.y - b.y); if (drag.pinch > 0) cam.tR = Math.min(40, Math.max(7, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(40, Math.max(7, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

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
  const M = MODEL, pr = progress(); let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  const corner = (c) => { const p = new Array(M.d).fill(0).map((_, j) => c[j] ?? 0); return M.G.pts.findIndex((q) => q.every((v, j) => v === p[j])); };
  const o = posOf(M, corner([0, 0, 0, 0]));
  put('x₁', posOf(M, corner([M.k - 1, 0, 0, 0])).map((v, j) => (j === 0 ? v + 0.6 : v)), 'cy');
  put('x₂', posOf(M, corner([0, M.k - 1, 0, 0])).map((v, j) => (j === 2 ? v + 0.6 : v)), 'cy');
  if (M.d >= 3) put('x₃', posOf(M, corner([0, 0, M.k - 1, 0])).map((v, j) => (j === 1 ? v + 0.5 : v)), 'cy');
  if (M.d === 4) for (let c = 0; c < M.k; c++) put(`x₄ = ${c + 1}`, posOf(M, corner([0, 0, M.k - 1, c])).map((v, j) => (j === 1 ? v + 1.1 : v)), 'cy');
  put('(1, …, 1)', o.map((v, j) => (j === 1 ? v - 0.5 : v)), 'cy');
  pr.ins.violated.slice(0, 3).forEach((li) => { const L = M.G.lines[li].pts, mid = posOf(M, L[Math.floor(L.length / 2)]); put(T(`违规：${fmtPt(M, L[0])} → ${fmtPt(M, L[L.length - 1])}`, `violated: ${fmtPt(M, L[0])} → ${fmtPt(M, L[L.length - 1])}`), mid.map((v, j) => (j === 1 ? v + 0.6 : v)), 'mg'); });
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
/* slices: one k × k grid in (x₁, x₂) for every value of the remaining coordinates */
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 10); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress(), inS = new Set(pr.item.S), k = M.k;
  const onBad = new Set(); pr.ins.violated.forEach((li) => M.G.lines[li].pts.forEach((p) => { if (inS.has(p)) onBad.add(p); }));
  if (M.mode === 'latin') {
    const L = pr.item.L, cell = Math.min(iw / 3, ih / 3) * 0.9, x0 = pl + (iw - 3 * cell) / 2, y0 = pt + (ih - 3 * cell) / 2;
    ctx.font = `${Math.round(cell * 0.42)}px ${TRV.fonts.data}`;
    for (let x = 0; x < 3; x++) for (let y = 0; y < 3; y++) {
      const p = x + 3 * y + 9 * L[x][y], X = x0 + x * cell, Y = y0 + (2 - y) * cell;
      ctx.fillStyle = onBad.has(p) ? 'rgba(255,47,208,0.35)' : 'rgba(25,240,255,0.12)'; ctx.fillRect(X + 2, Y + 2, cell - 4, cell - 4);
      ctx.strokeStyle = FAINT; ctx.strokeRect(X + 2, Y + 2, cell - 4, cell - 4);
      lab(ctx, String(L[x][y] + 1), X + cell / 2, Y + cell / 2, 'center', 'middle', onBad.has(p) ? MG : INK);
    }
    ctx.strokeStyle = 'rgba(255,200,61,0.6)'; ctx.setLineDash([4 * dpr, 3 * dpr]);
    ctx.beginPath(); ctx.moveTo(x0, y0 + 3 * cell); ctx.lineTo(x0 + 3 * cell, y0); ctx.moveTo(x0, y0); ctx.lineTo(x0 + 3 * cell, y0 + 3 * cell); ctx.stroke(); ctx.setLineDash([]);
    $('c1Meta').textContent = T('格子 (x₁, x₂) 里写的是 x₃ = L(x₁, x₂)；琥珀虚线是两条对角线，品红格是落在违规直线上的点', 'cell (x₁, x₂) holds x₃ = L(x₁, x₂); amber dashes are the two diagonals, magenta cells are points on a violated line');
    return;
  }
  const rest = M.d - 2, nb = rest === 0 ? 1 : k ** rest, cols = rest <= 1 ? nb : k, rows = Math.ceil(nb / cols);
  const gap = 8 * dpr, cell = Math.max(2, Math.min((iw - gap * (cols - 1)) / (cols * k), (ih - gap * (rows - 1) - 12 * dpr) / (rows * k)));
  const W0 = cols * k * cell + gap * (cols - 1), x0 = pl + (iw - W0) / 2;
  for (let b = 0; b < nb; b++) {
    const bc = b % cols, br = Math.floor(b / cols), gx = x0 + bc * (k * cell + gap), gy = pt + 12 * dpr + br * (k * cell + gap);
    lab(ctx, rest === 0 ? '' : rest === 1 ? `x₃ = ${b + 1}` : `(${(b % k) + 1}, ${Math.floor(b / k) + 1})`, gx, gy - 2 * dpr, 'left', 'bottom');
    for (let x = 0; x < k; x++) for (let y = 0; y < k; y++) {
      const p = x + k * y + k * k * b, X = gx + x * cell, Y = gy + (k - 1 - y) * cell;
      ctx.fillStyle = inS.has(p) ? (onBad.has(p) ? MG : CY) : 'rgba(110,140,170,0.14)'; ctx.fillRect(X + 1, Y + 1, cell - 2, cell - 2);
    }
  }
  $('c1Meta').textContent = T(`按切片展开：每个小方格是 (x₁, x₂) 平面，${M.d === 4 ? '标签是 (x₃, x₄)' : M.d === 3 ? '标签是 x₃' : '只有一片'}；青 = 选中的点`, `unfolded into slices: each small grid is the (x₁, x₂) plane, ${M.d === 4 ? 'labelled (x₃, x₄)' : M.d === 3 ? 'labelled x₃' : 'a single slice'}; cyan = chosen points`);
}
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 40); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress();
  const top = Math.ceil(Math.max(M.ku, M.best, M.board === '3,3' ? 9 : 0)) + 1, X = (s) => pl + iw * (s + 0.5) / (top + 1);
  const maxC = Math.max(...M.hist.values()), Y = (c) => pt + ih - ih * Math.log10(1 + c) / Math.log10(1 + maxC);
  for (const [s, c] of M.hist) { ctx.fillStyle = s === pr.item.S.length && M.mode === 'configs' ? AM : CY; const w = iw / (top + 1) * 0.6; ctx.fillRect(X(s) - w / 2, Y(c), w, pt + ih - Y(c)); lab(ctx, String(c), X(s), Y(c) - 2 * dpr, 'center', 'bottom', INK); }
  const vline = (s, col, txt) => { ctx.strokeStyle = col; ctx.setLineDash([5 * dpr, 4 * dpr]); ctx.beginPath(); ctx.moveTo(X(s), pt); ctx.lineTo(X(s), pt + ih); ctx.stroke(); ctx.setLineDash([]); lab(ctx, txt, X(s) + 3 * dpr, pt, 'left', 'top', col); };
  vline(M.ku, AM, `${T('猜想', 'conj.')} ${Math.round(M.ku)}`);
  if (M.board === '3,3') vline(8, OK, 'LEAN ≤ 8');
  if (M.mode === 'latin') { ctx.fillStyle = MG; ctx.beginPath(); ctx.arc(X(9), pt + ih - 6 * dpr, 4 * dpr, 0, 2 * Math.PI); ctx.fill(); }
  for (let s = 0; s <= top; s += Math.max(1, Math.round(top / 8))) lab(ctx, String(s), X(s), pt + ih + 4 * dpr, 'center', 'top');
  $('c2Meta').textContent = M.enumerated ? T(`饱和配置的大小分布（共 ${M.configs.length} 个，纵轴为对数）；琥珀 = 猜想的最大值${M.board === '3,3' ? '，绿 = Lean 的上界' : ''}`, `sizes of the saturated configurations (${M.configs.length} in all, log scale); amber = the conjectured maximum${M.board === '3,3' ? ', green = the Lean bound' : ''}`)
    : T('只有一个离线找到的证书配置（青）；琥珀 = 猜想的最大值', 'only one certificate configuration found offline (cyan); amber = the conjectured maximum');
}

/* =====================================================================
   10. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const kindName = (kd) => (kd === 1 ? T('轴线', 'axis line') : kd === 2 ? T('面对角线', 'face diagonal') : T('体对角线', 'space diagonal'));
function readouts() {
  const M = MODEL, pr = progress(), ins = pr.ins, size = pr.item.S.length, name = boardName(M.k, M.d);
  pill('pillA', T('棋盘', 'BOARD'), name); pill('pillB', '|S|', String(size)); pill('pillC', T('最大', 'MAX'), String(M.best)); pill('pillD', T('猜想', 'CONJ.'), String(Math.round(M.ku)));
  if (M.mode === 'latin') {
    const L = pr.item.L, kinds = ins.violated.map((li) => M.G.lines[li].kind);
    setRo([[T('棋盘 · 点数 · 直线数', 'Board · cells · lines'), `${name} · ${M.G.N} · ${M.G.lines.length}`],
      [T('Latin 方阵 · 各行（x₃ 的值）', 'Latin square · rows (values of x₃)'), `${pr.i + 1} / 12 · ${[0, 1, 2].map((y) => [0, 1, 2].map((x) => L[x][y] + 1).join('')).join(' / ')}`],
      [T('违规直线（≥ 2 个选中点）', 'Violated lines (≥ 2 chosen points)'), `${ins.violated.length} · ${[...new Set(kinds)].map(kindName).join('、')}`],
      [T('轴线上的点数', 'Points per axis line'), T(`每条恰 1 个（共 ${M.G.lines.filter((l) => l.kind === 1).length} 条）`, `exactly 1 on each (${M.G.lines.filter((l) => l.kind === 1).length} lines)`)],
      [T('对角线上的值', 'Values on the diagonals'), `${T('主', 'main')} ${[0, 1, 2].map((t) => L[t][t] + 1).join('')} · ${T('副', 'anti')} ${[0, 1, 2].map((t) => L[t][2 - t] + 1).join('')}`]]);
    $('roNote').innerHTML = T('9 个点让三个轴向都“每条线恰一个点”，所以 x₃ 必须是 Latin 方阵；主对角线或副对角线上的重复值给出两个落在同一条面对角线上的点。冻结引理 latin_diagonal 与 diag_common 对全部 12 个方阵证明了这一点。',
      'Nine points put exactly one point on every axis line in all three directions, so x₃ must be a Latin square; a repeated value on the main or anti-diagonal gives two points on one face diagonal. The frozen lemmas latin_diagonal and diag_common prove this for all 12 squares.');
    return;
  }
  const counts = [...M.hist.entries()].sort((a, b) => b[0] - a[0]).map(([s, c]) => `${s}→${c}`).join(', ');
  setRo([[T('棋盘 · 点数 · 直线数', 'Board · cells · lines'), `${name} · ${M.G.N} · ${M.G.lines.length}`],
    [T('猜想的最大值 (1 − 2/k)·kᵈ · 页面的最大值', 'Conjectured maximum (1 − 2/k)·kᵈ · page maximum'), `${Math.round(M.ku)} · ${M.best}${M.enumerated ? '' : T('（证书）', ' (certificate)')}`],
    [T('当前配置：大小 · 合法 · 饱和', 'Current configuration: size · valid · saturated'), `${size} · ${ins.valid ? T('合法', 'valid') : T('违规', 'violated')} · ${ins.saturated ? T('饱和', 'saturated') : T('未饱和', 'not saturated')}`],
    [T('密度 |S|/kᵈ 与 1 − 2/k', 'Density |S|/kᵈ and 1 − 2/k'), `${fr(size / M.G.N)} · ${fr(1 - 2 / M.k)}`],
    [M.enumerated ? T('饱和配置个数（按大小）', 'Saturated configurations (by size)') : T('来源', 'Source'), M.enumerated ? `${M.configs.length}: ${counts}` : T('离线搜索得到的证书，页面只核对合法与饱和', 'a certificate from an offline search; the page only checks validity and saturation')]]);
  $('roNote').innerHTML = T(`当前配置的点：${pr.item.S.slice(0, 12).map((p) => fmtPt(M, p)).join(' ')}${pr.item.S.length > 12 ? ' …' : ''}`, `Points of the current configuration: ${pr.item.S.slice(0, 12).map((p) => fmtPt(M, p)).join(' ')}${pr.item.S.length > 12 ? ' …' : ''}`);
}
function syncControls() {
  const M = MODEL;
  document.querySelectorAll('#boardChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.board === M.board)));
  document.querySelectorAll('#modeChips .chip').forEach((b) => { b.setAttribute('aria-pressed', String(b.dataset.mode === M.mode)); if (b.dataset.mode === 'latin') b.disabled = M.board !== '3,3'; });
}
const stateKey = () => `${S.board}|${S.mode}|${S.nowFrac}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; toasted = false; syncControls(); $('marks').dataset.key = ''; glKey = ''; }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  const M = MODEL, pr = progress();
  readouts();
  $('formula').innerHTML = `D(k, [k]<sup>d</sup>) = max |S| / k<sup>d</sup>, &nbsp; ${T('猜想', 'conjecture')} 1 − 2/k`;
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('modeNote').innerHTML = M.mode === 'latin' ? T('时间轴 = 12 个 3 阶 Latin 方阵，每个给出一个 9 点配置。', 'The time axis runs through the 12 Latin squares of order 3, each giving a 9-point configuration.')
    : T(`时间轴 = ${M.enumerated ? `全部 ${M.configs.length} 个饱和配置，从大到小` : '一个证书配置'}。每条直线至多 ${M.k - 2} 个点。`, `The time axis runs through ${M.enumerated ? `all ${M.configs.length} saturated configurations, largest first` : 'one certificate configuration'}. Every line may hold at most ${M.k - 2} points.`);
  $('litNote').innerHTML = T('直线、配置与分布都由页面按定义算出；冻结的是 3×3×3 至多 8 个点，因而猜想 5.6 不成立。', 'The lines, configurations and distribution are computed on the page from the definitions; what is frozen is that 3×3×3 allows at most 8 points, so Conjecture 5.6 fails.');
  $('c1Title').textContent = M.mode === 'latin' ? T('Latin 方阵：x₃ = L(x₁, x₂)', 'The Latin square: x₃ = L(x₁, x₂)') : T('按切片展开的配置', 'The configuration, slice by slice');
  $('c2Title').textContent = T('饱和配置的大小', 'Sizes of saturated configurations');
  $('clock').innerHTML = `${pr.i + 1}/${M.items.length}`;
  $('hudBig').textContent = M.mode === 'latin' ? `${boardName(M.k, M.d)} · Latin ${pr.i + 1}/12 · ${T('违规直线', 'violated lines')} ${pr.ins.violated.length}` : `${boardName(M.k, M.d)} · |S| = ${pr.item.S.length} · ${T('猜想', 'conjecture')} ${Math.round(M.ku)}`;
  $('hudSub').textContent = T('灰线 = 全部直线，青线 = 经过选中点的直线，品红 = 违规的直线；青点 = 选中的点，灰点 = 不能再加的点，琥珀点 = 还能加的点', 'grey lines = every line, cyan lines = lines through chosen points, magenta = violated lines; cyan points = chosen, grey points = cannot be added, amber points = could still be added');
  if (!toasted && S.playing && S.nowFrac >= 1) {
    toasted = true;
    toast(M.mode === 'latin' ? T('<b>12 个 Latin 方阵</b>：每一个都至少有一条违规的面对角线——9 个点不可能。', '<b>12 Latin squares</b>: each has at least one violated face diagonal — 9 points are impossible.')
      : T(`<b>${M.items.length} 个配置</b>：最大 ${M.best} 个点，猜想要 ${Math.round(M.ku)} 个。`, `<b>${M.items.length} configurations</b>: the largest has ${M.best} points; the conjecture asks for ${Math.round(M.ku)}.`));
  }
}
function syncRail() {
  const M = MODEL, key = `${M.id}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const n = M.items.length, marks = [[0, '1']];
  if (M.mode === 'configs' && n > 1) { const sizes = [...new Set(M.items.map((it) => it.S.length))]; for (const s of sizes.slice(1)) { const f = M.items.findIndex((it) => it.S.length === s) / (n - 1); if (f - marks[marks.length - 1][0] > 0.12 && 1 - f > 0.12) marks.push([f, `|S| = ${s}`]); } }
  if (n > 1) marks.push([1, String(n)]);
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
function custom() { S.preset = null; markPreset(); dirty = true; S.nowFrac = 0; $('now').value = 0; }
document.querySelectorAll('#boardChips .chip').forEach((b) => b.addEventListener('click', () => { S.board = BOARDS.includes(b.dataset.board) ? b.dataset.board : '3,3'; custom(); setCamPreset('iso'); }));
document.querySelectorAll('#modeChips .chip').forEach((b) => b.addEventListener('click', () => { S.mode = b.dataset.mode === 'latin' ? 'latin' : 'configs'; custom(); }));
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.board = p.board; S.mode = p.mode; S.preset = name; markPreset(); dirty = true;
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); const n = MODEL.items.length, i = progress().i + (ev.key === 'ArrowRight' ? 1 : -1); jumpTo(n > 1 ? Math.min(n - 1, Math.max(0, i)) / (n - 1) : 0); }
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
      S.nowFrac += S.dir * dtSec * S.speed / (MODEL.mode === 'latin' ? 14 : RUN);
      if (S.nowFrac >= 1) { S.nowFrac = 1; S.hold = 2.4; }
      if (S.nowFrac <= 0) { S.nowFrac = 0; S.hold = 1.2; }
    }
    $('now').value = S.nowFrac;
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    const k = `${MODEL.id}|${progress().i}`;
    if (k !== glKey) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.KU_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => {
    const M = MODEL, pr = progress();
    return { board: M.board, k: M.k, d: M.d, mode: M.mode, N: M.G.N, lines: M.G.lines.map((L) => L.pts), kinds: M.G.lines.map((L) => L.kind), i: pr.i, count: M.items.length,
      S: pr.item.S, L: pr.item.L || null, violated: pr.ins.violated, addable: pr.ins.addable, valid: pr.ins.valid, saturated: pr.ins.saturated,
      best: M.best, ku: M.ku, enumerated: M.enumerated, hist: [...M.hist.entries()].sort((a, b) => a[0] - b[0]) };
  },
  configs: () => MODEL.items.map((it) => it.S),
  setFrac: (f) => { S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; }
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('latin'); S.playing = false; setPlayUI(); S.nowFrac = 0; $('now').value = 0; setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 14; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
