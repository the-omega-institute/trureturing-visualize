/* CROSSWORD//ROOKS · every natural number is the rook-placement count of a crossword grid (Lewis–Won, Question 4.2)
   A crossword grid is a square array of white and black cells; an across (down) word is a maximal run of white cells in a row
   (column). A complete non-attacking rook placement puts exactly one rook in every across word and every down word, i.e. it is
   a perfect matching of the bipartite graph whose vertices are the words and whose edges are the white cells. Lewis and Won
   (arXiv:2609.03081) ask which counts r occur. Proved in trureturing (CrosswordRookCounts.result): every r ≥ 0 does, by an
   explicit family of grids of side max(5, 2r − 1) whose placements are indexed by the row of the one rook in column 2.
   Refuted in trureturing (CrosswordPermutationGridRefutation.result): their Conjecture 3.10, since the permutation grid of
   2 7 4 8 1 6 3 5 has 155 ≡ 3 (mod 4) placements. The page builds the grids, enumerates their placements as matchings, and
   draws the board, the rooks and the word graph.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Grids, words and rook placements
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const RMAX = 20;
/* Lean's family: gridSize, side, tip, rowLeft, rowRight; the white cells of row a < 2r − 1 are the interval [rowLeft, rowRight] */
const gridSize = (r) => Math.max(5, 2 * r - 1);
const side = (i) => (i % 2 === 0 ? 3 : 1), tip = (i) => (i % 2 === 0 ? 4 : 0);
const rowLeft = (r, a) => (a % 2 === 1 ? (a % 4 === 1 ? 2 : 0) : (a === 0 || (a === 2 * r - 2 && a % 4 === 2)) ? 2 : 1);
const rowRight = (r, a) => (a % 2 === 1 ? (a % 4 === 1 ? 4 : 2) : (a === 2 * r - 2 && a % 4 === 0) ? 2 : 3);
function familyGrid(r) {
  const N = gridSize(r), w = new Uint8Array(N * N);
  for (let a = 0; a < 2 * r - 1; a++) for (let b = rowLeft(r, a); b <= rowRight(r, a); b++) w[a * N + b] = 1;
  return { N, w };
}
/* Lean's candidate r k: the rook at (2k, 2), the singleton tips, and each side word's top cell before block k, bottom from k on */
function candidate(r, k) {
  const out = [[2 * k, 2]];
  for (let i = 0; i + 1 < r; i++) { out.push([2 * i + 1, tip(i)]); out.push([i < k ? 2 * i : 2 * i + 2, side(i)]); }
  return out;
}
/* the r = 0 grid of Lean's zeroWhite: white (0,1), (0,2), (1,0), (2,0) in a 3 × 3 square */
function zeroGrid() { const w = new Uint8Array(9); for (const [a, b] of [[0, 1], [0, 2], [1, 0], [2, 0]]) w[a * 3 + b] = 1; return { N: 3, w }; }
/* the permutation grid of w: black exactly at (i, w(i)); the witness is 2 7 4 8 1 6 3 5 in one-line notation */
const WITNESS = [2, 7, 4, 8, 1, 6, 3, 5];
function permGrid(p) { const N = p.length, w = new Uint8Array(N * N).fill(1); p.forEach((v, i) => { w[i * N + v - 1] = 0; }); return { N, w }; }
/* across and down words: maximal runs of white cells in rows and in columns */
function words(N, w) {
  const acr = new Int32Array(N * N).fill(-1), dn = new Int32Array(N * N).fill(-1); let na = 0, nd = 0;
  for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) if (w[r * N + c]) acr[r * N + c] = c > 0 && w[r * N + c - 1] ? acr[r * N + c - 1] : na++;
  for (let c = 0; c < N; c++) for (let r = 0; r < N; r++) if (w[r * N + c]) dn[r * N + c] = r > 0 && w[(r - 1) * N + c] ? dn[(r - 1) * N + c] : nd++;
  return { acr, dn, na, nd };
}
/* every placement, as a perfect matching: each across word picks one of its cells, no down word used twice */
function placements(N, w, limit = Infinity) {
  const { acr, dn, na, nd } = words(N, w); if (na !== nd) return [];
  const cellsOf = Array.from({ length: na }, () => []); for (let q = 0; q < N * N; q++) if (w[q]) cellsOf[acr[q]].push(q);
  const used = new Uint8Array(nd), cur = [], out = [];
  const rec = (a) => { if (out.length >= limit) return; if (a === na) { out.push(cur.slice()); return; } for (const q of cellsOf[a]) { if (used[dn[q]]) continue; used[dn[q]] = 1; cur.push(q); rec(a + 1); cur.pop(); used[dn[q]] = 0; } };
  rec(0); return out;
}
const countOf = (N, w) => placements(N, w).length;
/* the attained counts of all 2^(N²) grids of side N ≤ 4, and of all permutation grids of size n ≤ 7 */
const SMALL = {};
function smallSets() {
  if (SMALL.grids) return SMALL;
  SMALL.grids = [2, 3, 4].map((N) => { const s = new Set(); for (let m = 0; m < 1 << (N * N); m++) { const w = new Uint8Array(N * N); for (let q = 0; q < N * N; q++) w[q] = (m >> q) & 1; s.add(countOf(N, w)); } return { N, set: [...s].sort((a, b) => a - b) }; });
  SMALL.family = Array.from({ length: RMAX + 1 }, (_, r) => { const G = r === 0 ? zeroGrid() : familyGrid(r); return countOf(G.N, G.w); });
  SMALL.perms = [];
  for (let n = 1; n <= 7; n++) {
    const s = new Set(), a = Array.from({ length: n }, (_, q) => q + 1), c = new Array(n).fill(0), visit = () => s.add(countOf(n, permGrid(a).w));
    visit(); let i = 0;
    while (i < n) { if (c[i] < i) { if (i % 2 === 0) [a[0], a[i]] = [a[i], a[0]]; else [a[c[i]], a[i]] = [a[i], a[c[i]]]; visit(); c[i]++; i = 0; } else { c[i] = 0; i++; } }
    SMALL.perms.push({ n, set: [...s].sort((x, y) => x - y) });
  }
  return SMALL;
}
const setText = (arr) => { const out = []; let q = 0; while (q < arr.length) { let e = q; while (e + 1 < arr.length && arr[e + 1] === arr[e] + 1) e++; out.push(e - q >= 2 ? `${arr[q]}…${arr[e]}` : arr.slice(q, e + 1).join(', ')); q = e + 1; } return `{${out.join(', ')}}`; };

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean', mode: 'family', r: 5 };
const PRESETS = {
  lean: { mode: 'family', r: 5,
    zh: 'r = 5：9 × 9 的网格。中央第 2 列是一个 9 格的竖词，所以全盘只能有一个车落在它上面，而且必在偶数行 2k（k = 0 … 4）。四个单格竖词各自强制一个车；k 一定，三格的侧边竖词就都被逼到唯一的一端。于是恰好 5 种放法。',
    en: 'r = 5: a 9 × 9 grid. Column 2 is a single down word of 9 cells, so exactly one rook lies on it, in an even row 2k (k = 0 … 4). The four one-cell down words each force a rook, and once k is fixed every three-cell side word is pushed to one end. So there are exactly 5 placements.' },
  one: { mode: 'family', r: 1,
    zh: 'r = 1：5 × 5 的网格里只有一个白格，它自己既是横词又是竖词，唯一的放法就是在它上面放一个车。',
    en: 'r = 1: the 5 × 5 grid has a single white cell, which is both an across and a down word; the only placement puts a rook on it.' },
  three: { mode: 'family', r: 3,
    zh: 'r = 3：两个区块。第 1 行的 (1, 4) 与第 3 行的 (3, 0) 是单格竖词，必须放车；中央列的车在第 0、2、4 行之一，三种选择各对应一种放法。',
    en: 'r = 3: two blocks. The cells (1, 4) and (3, 0) are one-cell down words and must hold rooks; the rook of column 2 sits in row 0, 2 or 4, and each choice gives one placement.' },
  zero: { mode: 'family', r: 0,
    zh: 'r = 0：3 × 3 网格，第一行的两个白格 (0,1)、(0,2) 是同一个横词，却各自是单格竖词。两个竖词都要车，同一个横词只能有一个车——没有放法。',
    en: 'r = 0: a 3 × 3 grid whose first-row cells (0,1) and (0,2) form one across word but are each a one-cell down word. Both down words need a rook, and one across word can hold only one — no placement exists.' },
  big: { mode: 'family', r: 12,
    zh: 'r = 12：23 × 23 的网格，11 个区块，12 种放法。网格边长 2r − 1 随 r 线性增长；页面对每个 r ≤ 20 都数过放法，正好是 r。',
    en: 'r = 12: a 23 × 23 grid with 11 blocks and 12 placements. The side 2r − 1 grows linearly with r; the page counts the placements for every r ≤ 20 and gets exactly r.' },
  perm: { mode: 'perm', r: 5,
    zh: '置换网格 2 7 4 8 1 6 3 5：黑格恰在 (i, w(i))。Lewis 与 Won 的猜想 3.10 说置换网格的放法数不会 ≡ 3 (mod 4)；这个网格有 155 种，155 ≡ 3 (mod 4)，Lean 判定猜想不成立。',
    en: 'The permutation grid of 2 7 4 8 1 6 3 5: black cells exactly at (i, w(i)). Lewis and Won\'s Conjecture 3.10 says no permutation grid has a count ≡ 3 (mod 4); this grid has 155, and 155 ≡ 3 (mod 4), so Lean refutes the conjecture.' }
};
let MODEL = null, dirty = true, modelId = 0, modelKey = '';
const CACHE = new Map();
function build() {
  const key = S.mode === 'perm' ? 'perm' : `f${S.r}`;
  if (key !== modelKey) { modelKey = key; modelId++; }
  if (!CACHE.has(key)) {
    const G = S.mode === 'perm' ? permGrid(WITNESS) : S.r === 0 ? zeroGrid() : familyGrid(S.r);
    const Wd = words(G.N, G.w), list = placements(G.N, G.w);
    if (S.mode === 'family') list.sort((p, q) => p.find((c) => c % G.N === 2 && G.w[c]) - q.find((c) => c % G.N === 2 && G.w[c]));
    CACHE.set(key, { ...G, ...Wd, list, white: G.w.reduce((a, b) => a + b, 0) });
  }
  const G = CACHE.get(key), n = G.list.length, idx = n ? Math.min(n - 1, Math.floor(S.t * n)) : -1;
  MODEL = { id: modelId, mode: S.mode, r: S.r, ...G, n, idx, cur: idx >= 0 ? G.list[idx] : [] };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const cellRC = (M, q) => [Math.floor(q / M.N), q % M.N];

/* =====================================================================
   4. 3D scene: the board, black cells raised, rooks as pillars, and the two words of each rook
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const SIDE = 7, LINES_MAX = 60000, PTS_MAX = 1200;
const CAMS = { iso: [0.6, 0.9, 12], side: [0.0001, 1.35, 12], top: [0.0001, 0.05, 12] };
const cam = { theta: 0.6, phi: 0.9, r: 12, tTheta: 0.6, tPhi: 0.9, tR: 12 };
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
/* cell (row a, column b) → world, row 0 at the back, column 0 at the left */
const cellSize = (M) => SIDE / M.N;
const Wp = (M, a, b, h = 0) => { const c = cellSize(M); return [(b - M.N / 2) * c, h, (a - M.N / 2) * c]; };
function updateGL() {
  const M = MODEL, c = cellSize(M), Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, col, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, al, size) => { if (np >= PTS_MAX) return; for (let k = 0; k < 3; k++) { PT.position.array[3 * np + k] = p[k]; PT.aColor.array[3 * np + k] = col[k]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const gray = [0.5, 0.6, 0.72], WHITE = [0.95, 0.97, 1], hb = 0.45 * c;
  /* black cells: raised tops; white cells: flat outlined squares */
  for (let a = 0; a < M.N; a++) for (let b = 0; b < M.N; b++) {
    const white = M.w[a * M.N + b], h = white ? 0 : hb, k = white ? 0.75 : 0.16, col = white ? WHITE : gray;
    const p = [Wp(M, a, b, h), Wp(M, a, b + 1, h), Wp(M, a + 1, b + 1, h), Wp(M, a + 1, b, h)];
    for (let q = 0; q < 4; q++) seg(p[q], p[(q + 1) % 4], col, k);
    if (white) { const e = [Wp(M, a + 0.12, b + 0.12), Wp(M, a + 0.12, b + 0.88), Wp(M, a + 0.88, b + 0.88), Wp(M, a + 0.88, b + 0.12)]; for (let q = 0; q < 4; q++) seg(e[q], e[(q + 1) % 4], WHITE, 0.35); dot(Wp(M, a + 0.5, b + 0.5, 0.01), WHITE, 0.22, 3 * c); }
    else for (const t of p) seg(t, [t[0], 0, t[2]], gray, 0.1);
  }
  /* the words of the current rooks: across in cyan, down in magenta, raised slightly */
  const runOf = (q, across) => { const [a, b] = cellRC(M, q), id = across ? M.acr[q] : M.dn[q], cells = []; for (let x = 0; x < M.N; x++) { const qq = across ? a * M.N + x : x * M.N + b; if ((across ? M.acr[qq] : M.dn[qq]) === id) cells.push(x); } return [a, b, Math.min(...cells), Math.max(...cells)]; };
  for (const q of M.cur) {
    const [a, b, lo, hi] = runOf(q, true); seg(Wp(M, a + 0.5, lo + 0.15, 0.05), Wp(M, a + 0.5, hi + 0.85, 0.05), COL.cyan, 0.85);
    const [a2, b2, lo2, hi2] = runOf(q, false); seg(Wp(M, lo2 + 0.15, b2 + 0.5, 0.06), Wp(M, hi2 + 0.85, b2 + 0.5, 0.06), COL.magenta, 0.85);
  }
  /* rooks: a pillar with a crown */
  for (const q of M.cur) {
    const [a, b] = cellRC(M, q), base = Wp(M, a + 0.5, b + 0.5, 0), top = Wp(M, a + 0.5, b + 0.5, 1.4 * c);
    seg(base, top, COL.amber, 1);
    for (let s = 0; s < 6; s++) { const t0 = s / 6 * Math.PI * 2, t1 = (s + 1) / 6 * Math.PI * 2, rr = 0.3 * c; seg([top[0] + rr * Math.cos(t0), top[1], top[2] + rr * Math.sin(t0)], [top[0] + rr * Math.cos(t1), top[1], top[2] + rr * Math.sin(t1)], COL.amber, 0.9); }
    dot(top, COL.amber, 1, 4.5 * c);
  }
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const at of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) at.needsUpdate = true;
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
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.05, cam.tPhi - dy * 0.006));
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
  const M = MODEL, c = cellSize(M); let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  put(`${M.N} × ${M.N}`, Wp(M, -0.8, M.N / 2, 0), 'w');
  if (M.mode === 'family' && M.r > 0) {
    const q = M.cur.find((x) => x % M.N === 2), a = Math.floor(q / M.N);
    put(T(`中央列的车：第 ${a} 行`, `column 2 rook: row ${a}`), Wp(M, a + 0.5, 2.5, 1.6 * c), 'am');
  } else if (M.mode === 'perm') put(T('黑格 = 2 7 4 8 1 6 3 5', 'black cells = 2 7 4 8 1 6 3 5'), Wp(M, M.N + 0.8, M.N / 2, 0), 'mg');
  else put(T('两个单格竖词共用一个横词', 'two one-cell down words share an across word'), Wp(M, 0.5, 1.5, 0.3), 'mg');
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
/* which counts occur: all grids of side 2, 3, 4 and the family's side for each r (family mode); all permutation grids of size
   n ≤ 7 and the witness at n = 8 (permutation mode) */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 36); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, sm = smallSets();
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  if (M.mode === 'perm') {
    const RM = 160, X0 = (r) => pl + iw * r / RM, Y0 = (n) => pt + ih * (1 - n / 8.6);
    for (let r = 3; r <= RM; r += 4) { ctx.fillStyle = 'rgba(255,47,208,0.07)'; ctx.fillRect(X0(r - 0.5), pt, iw / RM, ih); }
    for (const { n, set } of sm.perms) for (const r of set) if (r <= RM) { ctx.fillStyle = CY; ctx.fillRect(X0(r) - 1.2 * dpr, Y0(n) - 1.2 * dpr, 2.4 * dpr, 2.4 * dpr); }
    ctx.fillStyle = MG; ctx.beginPath(); ctx.arc(X0(155), Y0(8), 4 * dpr, 0, 2 * Math.PI); ctx.fill();
    [1, 4, 8].forEach((n) => lab(ctx, `n=${n}`, pl - 4 * dpr, Y0(n), 'right', 'middle'));
    [0, 80, 160].forEach((r, q) => lab(ctx, String(r), X0(r), pt + ih + 4 * dpr, ['left', 'center', 'right'][q], 'top'));
    $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('n ≤ 7 的置换网格', 'permutation grids, n ≤ 7')}</span><span class="it"><i class="sw" style="--c:${MG}"></i>155 · n = 8</span><span class="it">· ${T('淡品红列：≡ 3 (mod 4)', 'pink columns: ≡ 3 (mod 4)')}</span>`;
  } else {
    const RM = RMAX, X0 = (r) => pl + iw * (r + 0.5) / (RM + 1), Y0 = (N) => pt + ih * (1 - N / 40);
    for (const { N, set } of sm.grids) for (const r of set) if (r <= RM) { ctx.fillStyle = CY; ctx.beginPath(); ctx.arc(X0(r), Y0(N), 2.6 * dpr, 0, 2 * Math.PI); ctx.fill(); }
    for (let r = 0; r <= RM; r++) { const N = r === 0 ? 3 : gridSize(r); ctx.fillStyle = r === M.r ? AM : 'rgba(255,200,61,0.45)'; ctx.beginPath(); ctx.arc(X0(r), Y0(N), (r === M.r ? 4.2 : 2.6) * dpr, 0, 2 * Math.PI); ctx.fill(); }
    [0, 20, 40].forEach((N) => lab(ctx, String(N), pl - 4 * dpr, Y0(N), 'right', 'middle'));
    [0, 10, 20].forEach((r) => lab(ctx, String(r), X0(r), pt + ih + 4 * dpr, 'center', 'top'));
    $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('边长 2–4 的所有网格', 'all grids, side 2–4')}</span><span class="it"><i class="sw" style="--c:${AM}"></i>${T('构造的边长', 'family side')}</span><span class="it">· ${T('横轴 r，纵轴边长', 'x r · y side')}</span>`;
  }
}
/* the word graph: across words on the left, down words on the right, white cells as edges, the placement as a matching */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 16); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, n = Math.max(M.na, M.nd, 1), YA = (k) => pt + ih * (k + 0.5) / Math.max(1, M.na), YD = (k) => pt + ih * (k + 0.5) / Math.max(1, M.nd), xa = pl + iw * 0.22, xd = pl + iw * 0.78;
  const on = new Set(M.cur);
  for (let q = 0; q < M.N * M.N; q++) if (M.w[q] && !on.has(q)) { ctx.strokeStyle = 'rgba(160,175,200,0.22)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(xa, YA(M.acr[q])); ctx.lineTo(xd, YD(M.dn[q])); ctx.stroke(); }
  for (const q of M.cur) { ctx.strokeStyle = AM; ctx.lineWidth = 1.8 * dpr; ctx.beginPath(); ctx.moveTo(xa, YA(M.acr[q])); ctx.lineTo(xd, YD(M.dn[q])); ctx.stroke(); }
  const rad = Math.min(4, Math.max(1.6, 160 / n)) * dpr;
  for (let k = 0; k < M.na; k++) { ctx.fillStyle = CY; ctx.beginPath(); ctx.arc(xa, YA(k), rad, 0, 2 * Math.PI); ctx.fill(); }
  for (let k = 0; k < M.nd; k++) { ctx.fillStyle = MG; ctx.beginPath(); ctx.arc(xd, YD(k), rad, 0, 2 * Math.PI); ctx.fill(); }
  lab(ctx, T('横词', 'across'), xa - 8 * dpr, pt + ih + 4 * dpr, 'center', 'top', CY); lab(ctx, T('竖词', 'down'), xd + 8 * dpr, pt + ih + 4 * dpr, 'center', 'top', MG);
  $('c2Meta').innerHTML = `<span class="it">${M.na} ${T('横', 'across')} · ${M.nd} ${T('竖', 'down')} · ${M.white} ${T('条边', 'edges')}</span><span class="it"><i class="sw" style="--c:${AM}"></i>${T('当前放法', 'placement')}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function readouts() {
  const M = MODEL, sm = smallSets(), fam = M.mode === 'family';
  pill('pillA', T('网格', 'grid'), `${M.N} × ${M.N}`); pill('pillB', T('白格', 'white'), String(M.white)); pill('pillC', T('放法', 'placements'), String(M.n)); pill('pillD', fam ? 'r' : 'mod 4', fam ? String(M.r) : String(M.n % 4));
  const central = fam && M.r > 0 && M.idx >= 0 ? Math.floor(M.cur.find((x) => x % M.N === 2) / M.N) : null;
  const singles = (() => { let s = 0; const cnt = new Map(); for (let q = 0; q < M.N * M.N; q++) if (M.w[q]) cnt.set(M.dn[q], (cnt.get(M.dn[q]) || 0) + 1); for (const v of cnt.values()) if (v === 1) s++; return s; })();
  const permThree = new Set(sm.perms.flatMap((p) => p.set.filter((r) => r % 4 === 3))).size;
  setRo([
    [T('网格 · 白格 · 横词 · 竖词', 'Grid · white cells · across words · down words'), `${M.N} × ${M.N} · ${M.white} · ${M.na} · ${M.nd}`],
    [fam ? T('放法数（页面枚举）· 目标 r · 判定', 'Placements (page count) · target r · verdict') : T('放法数（页面枚举）· mod 4 · 猜想 3.10', 'Placements (page count) · mod 4 · Conjecture 3.10'),
      fam ? `${M.n} · ${M.r} · ${M.n === M.r ? T('相等', 'equal') : T('不等！', 'unequal!')}` : `${M.n} · ${M.n % 4} · ${M.n % 4 === 3 ? T('≡ 3，猜想不成立', '≡ 3, the conjecture fails') : T('不矛盾', 'no contradiction')}`],
    [T('当前放法 · 车数 · 中央列的车', 'Current placement · rooks · the rook of column 2'), M.idx < 0 ? T('没有放法', 'no placement') : `${M.idx + 1} / ${M.n} · ${M.cur.length} · ${central === null ? '—' : T(`第 ${central} 行`, `row ${central}`)}`],
    [T('单格竖词（各强制一个车）· r ≤ 20 的构造中放法数恰为 r 的', 'One-cell down words (each forces a rook) · family grids with r ≤ 20 whose count is exactly r'), `${singles} · ${sm.family.filter((n, r) => n === r).length} / ${RMAX + 1}`],
    [T('边长 2、3、4 的全部网格能达到的放法数', 'Counts attained by all grids of side 2, 3, 4'), sm.grids.map(({ N, set }) => `${N}×${N} ${setText(set)}`).join(' · ')],
    [T('n ≤ 7 的置换网格中 ≡ 3 (mod 4) 的放法数', 'Counts ≡ 3 (mod 4) among permutation grids with n ≤ 7'), T(`${permThree} 个（共 ${new Set(sm.perms.flatMap((p) => p.set)).size} 个不同值）`, `${permThree} (of ${new Set(sm.perms.flatMap((p) => p.set)).size} distinct values)`)]]);
  $('roNote').innerHTML = T('放法就是词图的完美匹配：每个横词挑一个白格，挑出的格子落在不同的竖词里。所以放法数等于词图关联矩阵的积和式 perm(B)。', 'A placement is a perfect matching of the word graph: each across word picks one white cell, all in different down words. So the count is the permanent perm(B) of the word incidence matrix.');
}
const stateKey = () => `${S.mode}|${S.r}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; }
  const M = MODEL;
  if (!toasted && S.playing && S.t >= 1) { toasted = true; toast(M.mode === 'perm' ? T(`<b>${M.n} 种放法</b>：${M.n} = 4·${Math.floor(M.n / 4)} + ${M.n % 4}。`, `<b>${M.n} placements</b>: ${M.n} = 4·${Math.floor(M.n / 4)} + ${M.n % 4}.`) : T(`<b>${M.n} 种放法</b>：r = ${M.r}，中央列的车依次落在第 0 … ${Math.max(0, 2 * M.r - 2)} 行的偶数行。`, `<b>${M.n} placements</b>: r = ${M.r}; the rook of column 2 runs through the even rows 0 … ${Math.max(0, 2 * M.r - 2)}.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('rIn').value = String(S.r); $('rOut').textContent = S.mode === 'perm' ? '—' : String(S.r);
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T('r ≥ 1 时用 Lean 的构造：边长 max(5, 2r − 1)，白格在第 2 列和左右两侧的小块里；r = 0 用 3 × 3 的特例。', 'For r ≥ 1 the page uses Lean\'s construction: side max(5, 2r − 1), with white cells in column 2 and small blocks on either side; r = 0 uses a special 3 × 3 grid.');
  $('litNote').innerHTML = T('论文把乘积留给分块对角拼接：两个网格并排放，放法数相乘，所以只需处理素数 r。', 'The paper reduces products to block-diagonal juxtaposition: placing two grids side by side multiplies the counts, so only prime r need treatment.');
  $('c1Title').textContent = M.mode === 'perm' ? T('置换网格能达到的放法数', 'Counts attained by permutation grids') : T('哪些放法数出现：小网格与构造', 'Which counts occur: small grids and the family');
  $('c2Title').textContent = T('词图与当前的完美匹配', 'The word graph and the current matching');
  $('clock').innerHTML = M.idx < 0 ? T('没有放法', 'no placement') : T(`第 ${M.idx + 1} / ${M.n} 种`, `placement ${M.idx + 1} of ${M.n}`);
  $('hudBig').textContent = M.mode === 'perm' ? `|RP| = ${M.n} ≡ ${M.n % 4} (mod 4)` : `r = ${M.r} · |RP| = ${M.n}`;
  $('hudSub').textContent = T('凸起的是黑格，平的是白格。琥珀色的柱子是车；青线是车所在的横词，品红线是它所在的竖词——每个词恰好一个车', 'Raised squares are black, flat ones white. Amber pillars are rooks; the cyan line is a rook\'s across word and the magenta line its down word — every word holds exactly one rook');
}
function syncRail() {
  const M = MODEL, key = `${M.n}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  $('marks').innerHTML = M.n ? [[0, T('第 1 种', 'no. 1'), 'first'], [1, T(`第 ${M.n} 种`, `no. ${M.n}`), 'last']].map(([f, l, c]) => `<i class="${c}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('') : '';
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { mode: p.mode, r: p.r, t: 0, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('rIn').addEventListener('input', () => { S.r = parseInt($('rIn').value, 10); S.mode = 'family'; custom(); });
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
/* the rail position of placement i, at the middle of its slot */
const slot = (i, n) => (Math.max(0, Math.min(n - 1, i)) + 0.5) / n;
document.addEventListener('keydown', (ev) => {
  if (ev.target && (ev.target.tagName === 'INPUT' && ev.target.type !== 'range')) return;
  if (drawer.isOpen()) return;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); const n = Math.max(1, MODEL.n); jumpTo(slot(Math.min(n - 1, Math.floor(S.t * n)) + (ev.key === 'ArrowRight' ? 1 : -1), n)); }
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
/* about 1.2 s per placement at 1×, between 4 and 40 s for the whole list */
const runSeconds = () => Math.min(40, Math.max(4, 1.2 * MODEL.n));
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
window.CW_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { mode: M.mode, r: M.r, N: M.N, white: [...M.w], na: M.na, nd: M.nd, n: M.n, idx: M.idx, cur: M.cur.map((q) => [Math.floor(q / M.N), q % M.N]),
    list: M.list.map((p) => p.map((q) => [Math.floor(q / M.N), q % M.N])) }; },
  family: (r) => { const G = r === 0 ? zeroGrid() : familyGrid(r); return { N: G.N, white: [...G.w], count: countOf(G.N, G.w) }; },
  candidate: (r, k) => candidate(r, k),
  perm: (p) => { const G = permGrid(p); return countOf(G.N, G.w); },
  small: () => JSON.parse(JSON.stringify(smallSets())),
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setT(slot(2, MODEL.n)); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 10.5; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
