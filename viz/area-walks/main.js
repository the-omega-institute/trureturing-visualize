/* AREA//WALKS · walks of near-maximal algebraic area are counted by theta coefficients (OEIS A385672)
   A385672 (Zabolotskii, 2025) counts n-step walks on the square lattice by their algebraic area, the integral of y dx: a
   right step adds the current height y and a left step subtracts it. Its FORMULA line conjectures T(2n, n² − k) = 2·A029552(k)
   and T(2n+1, n² + n − k) = 4·A098613(k) for k < n. Proved in trureturing (LatticeWalkNearMaximalArea.result): such walks use
   only right and up steps or only left and down steps, and an up-right word with u ups and r rights has area u·r minus its
   inversions, which are counted by partitions. The page lists every walk of the chosen area, draws it with the Young diagram
   it leaves in its box, and compares the counts with the formula up to and beyond k = n.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Areas, counts, partitions and the list of walks of a given area
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const LMAX = 24;
const STEP = { R: [1, 0], L: [-1, 0], U: [0, 1], D: [0, -1] };
const ARROW = { R: '→', L: '←', U: '↑', D: '↓' };
/* the area of a walk from the origin, as Lean's areaFrom: right adds y, left subtracts y */
const areaOf = (w) => { let y = 0, a = 0; for (const s of w) { if (s === 'R') a += y; else if (s === 'L') a -= y; else if (s === 'U') y++; else y--; } return a; };
/* partition numbers by Euler's pentagonal recurrence */
const PART = [1];
for (let m = 1; m <= 200; m++) { let s = 0; for (let k = 1; ; k++) { const g1 = k * (3 * k - 1) / 2, g2 = k * (3 * k + 1) / 2; if (g1 > m) break; const sg = k % 2 ? 1 : -1; s += sg * PART[m - g1]; if (g2 <= m) s += sg * PART[m - g2]; } PART.push(s); }
const a029552 = (k) => { let s = PART[k]; for (let j = 1; j * j <= k; j++) s += 2 * PART[k - j * j]; return s; };
const a098613 = (k) => { let s = 0; for (let j = 1; j * j - j <= k; j++) s += PART[k - (j * j - j)]; return s; };
const shape = (L) => { const n = Math.floor(L / 2), even = L % 2 === 0; return { n, even, max: even ? n * n : n * n + n }; };
const formula = (L, k) => (L % 2 === 0 ? 2 * a029552(k) : 4 * a098613(k));
/* one row of A385672 by dynamic programming over (height, area) */
const ROWS = new Map();
function rowOf(L) {
  if (ROWS.has(L)) return ROWS.get(L);
  let cur = new Map([[0, new Map([[0, 1]])]]);
  for (let s = 0; s < L; s++) {
    const nx = new Map(), add = (y, a, c) => { if (!nx.has(y)) nx.set(y, new Map()); const m = nx.get(y); m.set(a, (m.get(a) || 0) + c); };
    for (const [y, m] of cur) for (const [a, c] of m) { add(y, a + y, c); add(y, a - y, c); add(y + 1, a, c); add(y - 1, a, c); }
    cur = nx;
  }
  const out = new Map(); for (const m of cur.values()) for (const [a, c] of m) out.set(a, (out.get(a) || 0) + c);
  ROWS.set(L, out); return out;
}
/* B[y][s]: an upper bound for the area still to come from height y with s steps left (rights below y + ups, lefts above
   y − downs), used to prune the search */
const BOUND = new Map();
function boundTable(L) {
  if (BOUND.has(L)) return BOUND.get(L);
  const B = new Map();
  for (let y = -L; y <= L; y++) { const row = []; for (let s = 0; s <= L; s++) { let best = 0; for (let u = 0; u <= s; u++) for (let d = 0; u + d <= s; d++) for (let r = 0; u + d + r <= s; r++) { const l = s - u - d - r; best = Math.max(best, r * (y + u) + l * (d - y)); } row.push(best); } B.set(y, row); }
  BOUND.set(L, B); return B;
}
/* every walk of length L with area A, by depth-first search pruned with the bound */
const LISTS = new Map();
function walksWithArea(L, A) {
  const key = `${L}|${A}`; if (LISTS.has(key)) return LISTS.get(key);
  const B = boundTable(L), out = [], w = [];
  const rec = (y, a) => {
    const s = L - w.length;
    if (s === 0) { if (a === A) out.push(w.join('')); return; }
    if (a + B.get(y)[s] < A) return;
    for (const c of 'RULD') { w.push(c); rec(c === 'U' ? y + 1 : c === 'D' ? y - 1 : y, c === 'R' ? a + y : c === 'L' ? a - y : a); w.pop(); }
  };
  rec(0, 0);
  const info = out.map(describe);
  info.sort((p, q) => (p.kind - q.kind) || (q.u - q.r) - (p.u - p.r) || (p.w < q.w ? -1 : 1));
  LISTS.set(key, info); return info;
}
/* kind 0: right and up only; 1: left and down only; 2: anything else. For an up-right word the cells above the path in its
   u × r box form a Young diagram; its column heights are the ups still to come after each right step */
function describe(w) {
  const cnt = { R: 0, L: 0, U: 0, D: 0 }; for (const s of w) cnt[s]++;
  const kind = cnt.L + cnt.D === 0 ? 0 : cnt.R + cnt.U === 0 ? 1 : 2;
  const mono = kind === 0 ? w : kind === 1 ? [...w].map((s) => (s === 'L' ? 'R' : 'U')).join('') : null;
  let part = null, inv = null;
  if (mono) { part = []; let upsLeft = cnt.U + cnt.D; for (const s of mono) { if (s === 'U') upsLeft--; else part.push(upsLeft); } part = part.filter((x) => x > 0); inv = part.reduce((a, b) => a + b, 0); }
  return { w, kind, u: cnt.U + cnt.D, r: cnt.R + cnt.L, cnt, part, inv, area: areaOf(w) };
}

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean', L: 12, k: 3 };
const PRESETS = {
  lean: { L: 12, k: 3,
    zh: '12 步、面积 36 − 3 = 33：卷宗与 Lean 说这样的游走恰有 2·A029552(3) = 2·(p(3) + 2·p(2)) = 2·(3 + 4) = 14 条。每一条要么只往右、往上走，要么只往左、往下走；右上走法在 u × r 的盒子里留下一个 3 − j² 的杨图。',
    en: '12 steps, area 36 − 3 = 33: by the dossier and Lean there are exactly 2·A029552(3) = 2·(p(3) + 2·p(2)) = 2·(3 + 4) = 14 such walks. Each goes only right and up, or only left and down; a right-up walk leaves a Young diagram of 3 − j² cells in its u × r box.' },
  top: { L: 10, k: 0,
    zh: '面积最大：10 步最多围出 5² = 25。只有两条——先上 5 步再右 5 步，以及它的翻转（先下再左）。',
    en: 'The largest area: 10 steps enclose at most 5² = 25. Only two walks do — five ups then five rights, and its flip (downs then lefts).' },
  odd: { L: 13, k: 4,
    zh: '奇数步：13 步、面积 6² + 6 − 4 = 38，恰有 4·A098613(4) = 4·(p(4) + p(2)) = 4·(5 + 2) = 28 条。盒子是 (7 + j) × (6 − j)，j 和 −1 − j 两项相同，所以系数是 4。',
    en: 'An odd length: 13 steps and area 6² + 6 − 4 = 38 give exactly 4·A098613(4) = 4·(p(4) + p(2)) = 4·(5 + 2) = 28 walks. The box is (7 + j) × (6 − j); the terms for j and −1 − j agree, hence the factor 4.' },
  edge: { L: 8, k: 4,
    zh: '边界 k = n：8 步、面积 16 − 4 = 12。公式给 2·A029552(4) = 26，实际有 34 条——多出的 8 条既往右也往左（或既往上也往下），猜想只到 k < n 为止（页面数值）。',
    en: 'The boundary k = n: 8 steps and area 16 − 4 = 12. The formula gives 2·A029552(4) = 26, but there are 34 walks — the 8 extra ones go both right and left (or both up and down), and the conjecture stops at k < n (page numbers).' },
  small: { L: 4, k: 1,
    zh: '最小的例子：4 步、面积 4 − 1 = 3，2·A029552(1) = 2·(p(1) + 2·p(0)) = 2·(1 + 2) = 6 条：右上走法有 ↑→↑→（2 × 2 盒子缺一格）、↑↑↑→ 和 ↑→→→（3 × 1、1 × 3 盒子不缺），再加上它们的翻转。',
    en: 'The smallest example: 4 steps and area 4 − 1 = 3 give 2·A029552(1) = 2·(p(1) + 2·p(0)) = 2·(1 + 2) = 6 walks: the right-up ones are ↑→↑→ (the 2 × 2 box minus one cell), ↑↑↑→ and ↑→→→ (the full 3 × 1 and 1 × 3 boxes), and each has a left-down flip.' },
  big: { L: 24, k: 11,
    zh: '24 步、面积 144 − 11 = 133：2·A029552(11) = 2·(56 + 2·(42 + 15 + 2)) = 348 条，页面全部找出来并逐条画出。',
    en: '24 steps and area 144 − 11 = 133: 2·A029552(11) = 2·(56 + 2·(42 + 15 + 2)) = 348 walks, all found and drawn by the page.' }
};
let MODEL = null, dirty = true, modelId = 0, listKey = '';
function build() {
  const L = S.L, sh = shape(L), k = Math.min(S.k, sh.max), A = sh.max - k, list = walksWithArea(L, A), row = rowOf(L);
  const idx = Math.min(list.length - 1, Math.floor(S.t * list.length));
  const key = `${L}|${A}`; if (key !== listKey) { listKey = key; modelId++; }
  const ks = Array.from({ length: Math.min(sh.n + 2, sh.max + 1) }, (_, q) => ({ k: q, T: row.get(sh.max - q) || 0, F: formula(L, q) }));
  MODEL = { id: modelId, L, ...sh, k, A, list, idx, cur: list[idx], row, count: row.get(A) || 0, F: formula(L, k), ks,
    kinds: [0, 1, 2].map((q) => list.filter((x) => x.kind === q).length) };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const css = (c, a = 1) => `rgba(${c.map((x) => Math.round(255 * Math.min(1, x))).join(',')},${a})`;
const arrows = (w) => [...w].map((s) => ARROW[s]).join('');

/* =====================================================================
   4. 3D scene: the walk on the lattice, the cells it encloses, and the Young diagram left in its box
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const SIDE = 6.2, LINES_MAX = 9000, PTS_MAX = 2600;
const CAMS = { iso: [-0.5, 0.95, 11], side: [0.0001, 1.4, 10.5], top: [0.0001, 0.05, 10.5] };
const cam = { theta: -0.5, phi: 0.95, r: 11, tTheta: -0.5, tPhi: 0.95, tR: 11 };
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
  vec2 d = gl_PointCoord - 0.5;
  float r = length(d) * 2.0;
  float a = smoothstep(1.0, 0.6, r) * vA;
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
  pts = new THREE.Points(gp, new THREE.ShaderMaterial({ vertexShader: VS, fragmentShader: FS, uniforms: { uScale: { value: 60 } }, ...additive }));
  pts.frustumCulled = false; scene3.add(pts);
}
const pathOf = (w) => { const out = [[0, 0]]; let x = 0, y = 0; for (const s of w) { x += STEP[s][0]; y += STEP[s][1]; out.push([x, y]); } return out; };
/* lattice point (x, y) → world, centred on the walk's bounding box */
function frameFor(M) {
  const p = pathOf(M.cur.w), xs = p.map((q) => q[0]).concat([0]), ys = p.map((q) => q[1]).concat([0]);
  const x0 = Math.min(...xs), x1 = Math.max(...xs), y0 = Math.min(...ys), y1 = Math.max(...ys), c = SIDE / Math.max(4, x1 - x0, y1 - y0);
  return { c, cx: (x0 + x1) / 2, cy: (y0 + y1) / 2, x0, x1, y0, y1 };
}
const W = (F, x, y, h = 0) => [(x - F.cx) * F.c, h, -(y - F.cy) * F.c];
function updateGL() {
  const M = MODEL, F = frameFor(M), Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, col, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, al, size) => { if (np >= PTS_MAX) return; for (let k = 0; k < 3; k++) { PT.position.array[3 * np + k] = p[k]; PT.aColor.array[3 * np + k] = col[k]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const gray = [0.5, 0.6, 0.72], H = 0.32 * F.c;
  /* lattice and the x axis */
  for (let x = F.x0 - 1; x <= F.x1 + 1; x++) seg(W(F, x, F.y0 - 1), W(F, x, F.y1 + 1), gray, 0.1);
  for (let y = F.y0 - 1; y <= F.y1 + 1; y++) seg(W(F, F.x0 - 1, y), W(F, F.x1 + 1, y), gray, y === 0 ? 0.55 : 0.1);
  /* each right step at height y contributes the column of cells between the axis and y (cyan, +), each left step the same
     with the opposite sign (magenta, −) */
  const cube = (x, y, col, k, h) => {
    const a = W(F, x, y), b = W(F, x + 1, y), c2 = W(F, x + 1, y + 1), d = W(F, x, y + 1), up = (p) => [p[0], h, p[2]];
    for (const [p, q] of [[a, b], [b, c2], [c2, d], [d, a]]) { seg(up(p), up(q), col, k); }
    for (const p of [a, b, c2, d]) seg(p, up(p), col, k * 0.5);
    dot([(a[0] + c2[0]) / 2, h, (a[2] + c2[2]) / 2], col, 0.5, 2.6 * F.c);
  };
  let y = 0, x = 0;
  for (const s of M.cur.w) {
    if (s === 'R' || s === 'L') {
      const cx = s === 'R' ? x : x - 1, sign = (s === 'R' ? 1 : -1) * Math.sign(y);
      for (let q = Math.min(0, y); q < Math.max(0, y); q++) cube(cx, q, sign > 0 ? COL.cyan : COL.magenta, 0.55, H);
    }
    x += STEP[s][0]; y += STEP[s][1];
  }
  /* the box u × r of a monotone walk and the Young diagram of missing cells above the path */
  if (M.cur.kind < 2) {
    const sg = M.cur.kind === 0 ? 1 : -1, u = M.cur.u, r = M.cur.r;
    const corners = [[0, 0], [sg * r, 0], [sg * r, sg * u], [0, sg * u]];
    for (let q = 0; q < 4; q++) seg(W(F, ...corners[q], 0.02), W(F, ...corners[(q + 1) % 4], 0.02), COL.amber, 0.8);
    M.cur.part.forEach((h, col) => { for (let q = 0; q < h; q++) { const cx = sg > 0 ? col : -col - 1, cy = sg > 0 ? u - 1 - q : -u + q; const a = W(F, cx + 0.15, cy + 0.15, 0.03), b = W(F, cx + 0.85, cy + 0.85, 0.03); seg(a, [b[0], 0.03, a[2]], COL.magenta, 0.9); seg([b[0], 0.03, a[2]], b, COL.magenta, 0.9); seg(b, [a[0], 0.03, b[2]], COL.magenta, 0.9); seg([a[0], 0.03, b[2]], a, COL.magenta, 0.9); } });
  }
  /* the walk itself, raised above the cells */
  const p = pathOf(M.cur.w);
  for (let q = 0; q + 1 < p.length; q++) { seg(W(F, ...p[q], H + 0.05), W(F, ...p[q + 1], H + 0.05), WHITE, 1); dot(W(F, ...p[q + 1], H + 0.05), WHITE, 0.9, 2.2 * F.c); }
  dot(W(F, 0, 0, H + 0.05), COL.amber, 1, 3.4 * F.c);
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const at of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) at.needsUpdate = true;
  pts.material.uniforms.uScale.value = 60 * renderer.getPixelRatio() * (stage.clientHeight / 600);
}
const WHITE = [0.95, 0.97, 1];

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
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(28, Math.max(4, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.05, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(28, Math.max(4, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

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
  const M = MODEL, F = frameFor(M), cur = M.cur, H = 0.32 * F.c; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  put(T(`面积 ${cur.area}`, `area ${cur.area}`), W(F, (F.x0 + F.x1) / 2, F.y1 + 1.2, 0.3), 'am');
  if (cur.kind < 2) put(T(`${cur.u} × ${cur.r} 盒子缺 ${cur.inv} 格`, `${cur.u} × ${cur.r} box minus ${cur.inv} cells`), W(F, (F.x0 + F.x1) / 2, F.y0 - 1.2), 'w');
  else put(T('既有 → 又有 ←（或 ↑ 和 ↓）', 'both → and ← (or ↑ and ↓)'), W(F, (F.x0 + F.x1) / 2, F.y0 - 1.2), 'mg');
  put(T('原点', 'origin'), W(F, 0, 0, H + 0.9), 't');
  for (let i = k; i < tagPool.length; i++) tagPool[i].style.display = 'none';
}

/* =====================================================================
   7. 2D panels
   ===================================================================== */
function frame2d(cv, pl0 = 46) {
  const dpr = fitCanvas(cv), ctx = cv.getContext('2d'), Wd = cv.width, Hh = cv.height;
  ctx.clearRect(0, 0, Wd, Hh);
  const pl = pl0 * dpr, pr = 14 * dpr, pt = 12 * dpr, pb = 22 * dpr;
  ctx.font = `${9.5 * dpr}px ${TRV.fonts.data}`;
  return { dpr, ctx, W: Wd, Hh, pl, pt, iw: Wd - pl - pr, ih: Hh - pt - pb };
}
function lab(ctx, txt, x, y, al, bl, c = DIM) { ctx.fillStyle = c; ctx.textAlign = al; ctx.textBaseline = bl; ctx.fillText(txt, x, y); }
/* the whole row T(L, ·) of A385672, log scale, with the near-maximal window */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 36); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, keys = [...M.row.keys()].sort((a, b) => a - b), lo = keys[0], hi = keys[keys.length - 1];
  const top = Math.log10(Math.max(...M.row.values())), X = (a) => pl + iw * (a - lo) / Math.max(1, hi - lo), Y = (c) => pt + ih * (1 - Math.log10(c) / Math.max(1, top));
  ctx.fillStyle = 'rgba(255,200,61,0.12)'; ctx.fillRect(X(M.max - M.n + 0.5), pt, X(M.max + 0.5) - X(M.max - M.n + 0.5), ih);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  ctx.beginPath(); keys.forEach((a, q) => { const c = M.row.get(a); q ? ctx.lineTo(X(a), Y(c)) : ctx.moveTo(X(a), Y(c)); }); ctx.strokeStyle = CY; ctx.lineWidth = 1.3 * dpr; ctx.stroke();
  ctx.fillStyle = AM; ctx.beginPath(); ctx.arc(X(M.A), Y(Math.max(1, M.count)), 3.5 * dpr, 0, 2 * Math.PI); ctx.fill();
  [lo, 0, hi].forEach((a, q) => lab(ctx, String(a), X(a), pt + ih + 4 * dpr, ['left', 'center', 'right'][q], 'top'));
  [0, Math.floor(top)].forEach((e) => lab(ctx, `10^${e}`, pl - 4 * dpr, Y(10 ** e), 'right', 'middle'));
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>T(${M.L}, a)</span><span class="it"><i class="sw" style="--c:${AM}"></i>${T(`面积 ${M.A}`, `area ${M.A}`)}</span><span class="it">· ${T(`琥珀带：最大面积往下 ${M.n} 个`, `amber band: the top ${M.n} areas`)}</span>`;
}
/* T(L, max − k) against the formula, for k up to n + 1 */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 36); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, top = Math.max(...M.ks.map((q) => Math.max(q.T, q.F))) * 1.12, bw = iw / M.ks.length, Y = (v) => pt + ih * (1 - v / top);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  M.ks.forEach((q) => {
    const x = pl + q.k * bw, ok = q.T === q.F;
    ctx.fillStyle = q.k === M.k ? 'rgba(255,200,61,0.85)' : q.k < M.n ? 'rgba(25,240,255,0.55)' : 'rgba(255,47,208,0.45)';
    ctx.fillRect(x + bw * 0.18, Y(q.T), bw * 0.64, pt + ih - Y(q.T));
    ctx.strokeStyle = ok ? INK : MG; ctx.lineWidth = 2 * dpr; ctx.beginPath(); ctx.moveTo(x + bw * 0.08, Y(q.F)); ctx.lineTo(x + bw * 0.92, Y(q.F)); ctx.stroke();
    lab(ctx, String(q.k), x + bw / 2, pt + ih + 4 * dpr, 'center', 'top', q.k === M.n ? MG : DIM);
  });
  lab(ctx, String(Math.round(top / 1.12)), pl - 4 * dpr, Y(top / 1.12), 'right', 'middle'); lab(ctx, '0', pl - 4 * dpr, pt + ih, 'right', 'middle');
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>T(${M.L}, ${M.even ? 'n² − k' : 'n² + n − k'})</span><span class="it"><i class="sw" style="--c:${INK}"></i>${M.even ? '2·A029552(k)' : '4·A098613(k)'}</span><span class="it">· ${T(`k ≥ ${M.n} 不等`, `≠ from k = ${M.n}`)}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function expansion(M) {
  if (M.even) { const terms = [`p(${M.k})`]; for (let j = 1; j * j <= M.k; j++) terms.push(`2·p(${M.k - j * j})`); const vals = [PART[M.k]]; for (let j = 1; j * j <= M.k; j++) vals.push(`2·${PART[M.k - j * j]}`); return `A029552(${M.k}) = ${terms.join(' + ')} = ${vals.join(' + ')} = ${a029552(M.k)}`; }
  const terms = [], vals = []; for (let j = 1; j * j - j <= M.k; j++) { terms.push(`p(${M.k - (j * j - j)})`); vals.push(PART[M.k - (j * j - j)]); }
  return `A098613(${M.k}) = ${terms.join(' + ')} = ${vals.join(' + ')} = ${a098613(M.k)}`;
}
function readouts() {
  const M = MODEL, cur = M.cur, ok = M.count === M.F;
  pill('pillA', 'L', String(M.L)); pill('pillB', T('面积', 'area'), `${M.max} − ${M.k}`); pill('pillC', T('游走数', 'walks'), String(M.count)); pill('pillD', T('公式', 'formula'), String(M.F));
  setRo([
    [T('步数 L · n · 最大面积 · 目标面积', 'Steps L · n · largest area · target area'), `${M.L} · ${M.n} · ${M.max} · ${M.A}`],
    [T(`面积 ${M.A} 的游走数 · ${M.even ? '2·A029552(k)' : '4·A098613(k)'} · 判定`, `Walks of area ${M.A} · ${M.even ? '2·A029552(k)' : '4·A098613(k)'} · verdict`), `${M.count} · ${M.F} · ${M.k < M.n ? (ok ? T('相等（k < n，Lean）', 'equal (k < n, Lean)') : T('不等！', 'unequal!')) : (ok ? T('相等（k ≥ n）', 'equal (k ≥ n)') : T(`多出 ${M.count - M.F} 条（k ≥ n，猜想不涵盖）`, `${M.count - M.F} extra (k ≥ n, outside the conjecture)`))}`],
    [T('系数的展开', 'The coefficient expanded'), expansion(M)],
    [T(`第 ${M.idx + 1} / ${M.list.length} 条：步 · 面积 · 类型`, `Walk ${M.idx + 1} of ${M.list.length}: steps · area · type`), `${arrows(cur.w)} · ${cur.area} · ${[T('只往右、上', 'right and up only'), T('只往左、下', 'left and down only'), T('混合', 'mixed')][cur.kind]}`],
    [T('盒子 u × r · 缺的格子 m · m 的划分（各列高度）', 'Box u × r · missing cells m · the partition of m (column heights)'), cur.kind < 2 ? `${cur.u} × ${cur.r} · ${cur.inv} · ${cur.part.length ? cur.part.join(' + ') : '∅'}` : T('（混合游走没有盒子）', '(a mixed walk has no box)')]]);
  $('roNote').innerHTML = T(`Lean：对 k < n，${M.even ? `T(2n, n² − k) = 2·A029552(k)` : `T(2n + 1, n² + n − k) = 4·A098613(k)`}。这里 k = ${M.k}，n = ${M.n}。`, `Lean: for k < n, ${M.even ? `T(2n, n² − k) = 2·A029552(k)` : `T(2n + 1, n² + n − k) = 4·A098613(k)`}. Here k = ${M.k} and n = ${M.n}.`);
}
const stateKey = () => `${S.L}|${S.k}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; }
  const M = MODEL;
  if (!toasted && S.playing && S.t >= 1) { toasted = true; toast(T(`<b>面积 ${M.A} 的 ${M.list.length} 条游走</b>：${M.kinds[0]} 条只往右上，${M.kinds[1]} 条只往左下，${M.kinds[2]} 条混合。`, `<b>${M.list.length} walks of area ${M.A}</b>: ${M.kinds[0]} right-up, ${M.kinds[1]} left-down, ${M.kinds[2]} mixed.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('lIn').value = String(S.L); $('lOut').textContent = String(S.L);
  $('kIn').max = String(M.n + 1); $('kIn').value = String(S.k); $('kOut').textContent = String(M.k);
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T('面积是 ∫ y dx：往右一步加上当时的高度 y，往左一步减去 y，上下不计。滑块 k 可以越过 n，看公式在边界之外怎样失效。', 'The area is ∫ y dx: a right step adds the current height y, a left step subtracts it, up and down add nothing. The slider k may pass n, to see how the formula fails beyond the boundary.');
  $('litNote').innerHTML = T('OEIS 的 FORMULA 行写着 “It appears that”；Lean 把它对所有 n 与 k < n 证明了。', 'The OEIS FORMULA line says “It appears that”; Lean proves it for all n and k < n.');
  $('c1Title').textContent = T(`A385672 的第 ${M.L} 行：按面积数游走（对数刻度）`, `Row ${M.L} of A385672: walks by area (log scale)`);
  $('c2Title').textContent = T('最大面积附近：实数与公式', 'Near the maximum: counts vs formula');
  $('clock').innerHTML = T(`第 ${M.idx + 1} / ${M.list.length} 条`, `walk ${M.idx + 1} of ${M.list.length}`);
  $('hudBig').textContent = `T(${M.L}, ${M.A}) = ${M.count} ${M.count === M.F ? '=' : '≠'} ${M.F}`;
  $('hudSub').textContent = T('白线是游走，从琥珀点（原点）出发。往右的每一步在它下面立起一列青色格子（面积 +），往左的一步立起品红格子（面积 −）。单调的游走被包在琥珀色的 u × r 盒子里，盒子里路径上方缺的格子（品红方框）构成 m 的划分', 'The white line is the walk, starting at the amber dot (the origin). Each right step raises a column of cyan cells beneath it (area +), each left step magenta cells (area −). A monotone walk sits in its amber u × r box; the missing cells above the path (magenta squares) form a partition of m');
}
function syncRail() {
  const M = MODEL, key = `${M.list.length}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  $('marks').innerHTML = [[0, T('第 1 条', 'walk 1'), 'first'], [1, T(`第 ${M.list.length} 条`, `walk ${M.list.length}`), 'last']].map(([f, l, c]) => `<i class="${c}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { L: p.L, k: p.k, t: 0, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('lIn').addEventListener('input', () => { S.L = parseInt($('lIn').value, 10); S.k = Math.min(S.k, Math.floor(S.L / 2) + 1); custom(); });
$('kIn').addEventListener('input', () => { S.k = parseInt($('kIn').value, 10); custom(); });
const setT = (t) => { S.t = Math.min(1, Math.max(0, t)); $('now').value = S.t; dirty = true; };
$('now').addEventListener('input', () => { setT(parseFloat($('now').value)); S.hold = 0; });
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
const jumpTo = (t) => { S.playing = false; setPlayUI(); setT(t); };
/* the rail position of walk i, at the middle of its slot */
const slot = (i, n) => (Math.max(0, Math.min(n - 1, i)) + 0.5) / n;
document.addEventListener('keydown', (ev) => {
  if (ev.target && (ev.target.tagName === 'INPUT' && ev.target.type !== 'range')) return;
  if (drawer.isOpen()) return;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); const n = MODEL.list.length; jumpTo(slot(Math.min(n - 1, Math.floor(S.t * n)) + (ev.key === 'ArrowRight' ? 1 : -1), n)); }
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
/* about 0.8 s per walk at 1×, at most 40 s for the whole list */
const runSeconds = () => Math.min(40, Math.max(4, 0.8 * MODEL.list.length));
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : 1); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed / runSeconds());
      if (S.t >= 1) S.hold = 2.4;
      if (S.t <= 0 && S.dir < 0) S.hold = 1.2;
    }
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    const k = `${MODEL.id}|${MODEL.idx}`;
    if (glKey !== k) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.AW_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { L: M.L, n: M.n, even: M.even, max: M.max, k: M.k, A: M.A, count: M.count, F: M.F, idx: M.idx, kinds: M.kinds.slice(),
    list: M.list.map((x) => ({ w: x.w, kind: x.kind, u: x.u, r: x.r, part: x.part && x.part.slice(), inv: x.inv, area: x.area })), ks: M.ks.map((q) => ({ ...q })), row: [...M.row.entries()] }; },
  row: (L) => [...rowOf(L).entries()],
  walks: (L, A) => walksWithArea(L, A).map((x) => x.w),
  part: (m) => PART[m], a029552: (k) => a029552(k), a098613: (k) => a098613(k), area: (w) => areaOf(w),
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setT(slot(1, MODEL.list.length)); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 10; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
