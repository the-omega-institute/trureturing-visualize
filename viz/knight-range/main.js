/* KNIGHT//RANGE · the expected range of a knight's random walk times 2^(3n−3) is an integer (OEIS A309221)
   A knight starts on an infinite chessboard and makes n moves, each chosen uniformly among its eight moves; E(n) is the
   expected number of distinct squares it visits, the start included. Sloane (2019) normalized a(n) = E(n)·2^(3n−3) and noted
   that its integrality was only a conjecture. Proved in trureturing (KnightWalkRangeIntegrality.result): the eight symmetries
   of the square lattice permute the eight moves simply transitively, so the walks split into eight classes by their first
   move with equal totals of visited squares, and the total S(n) over all 8ⁿ walks is divisible by 8.
   The page shows one walk with its seven images under those symmetries, and enumerates every walk for n ≤ 8.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Moves, their symmetries, and the enumeration of all walks
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const NMAX = 8;
/* Lean's move table: move 0 = (1, 2), then clockwise */
const MOVES = [[1, 2], [2, 1], [2, -1], [1, -2], [-1, -2], [-2, -1], [-2, 1], [-1, 2]];
/* Lean's sym: the permutation of moves sending move 0 to move m, and its inverse */
const sym = (m, i) => (m % 2 === 0 ? (m + i) % 8 : (m - i + 8) % 8);
const symInv = (m, i) => (m % 2 === 0 ? (i - m + 8) % 8 : (m - i + 8) % 8);
/* OEIS A309221, a(0) … a(20) */
const OEIS = ['1', '2', '23', '240', '2355', '22320', '205942', '1866592', '16664147', '147164464', '1287061400', '11174456704', '96362903378', '826641224992', '7055950608008', '59990171328640', '508090131646771', '4290071141315376', '36113651041694280', '303253863622924416', '2540231448366573400'];
const positions = (w) => { const out = [[0, 0]]; let x = 0, y = 0; for (const m of w) { x += MOVES[m][0]; y += MOVES[m][1]; out.push([x, y]); } return out; };
const rangeOf = (w) => new Set(positions(w).map(([x, y]) => `${x},${y}`)).size;
/* the image of walk w whose first move is m: replace every move i by sym(m, symInv(w₀, i)) */
const image = (w, m) => w.map((i) => sym(m, symInv(w[0], i)));
/* depth-first enumeration of all 8ⁿ walks: totals by first move and the distribution of the range */
const ENUM = new Map();
function enumerate(n) {
  if (ENUM.has(n)) return ENUM.get(n);
  const B = 2 * n + 2, Wd = 2 * B + 1, cnt = new Uint8Array(Wd * Wd), cls = new Array(8).fill(0), hist = new Array(n + 2).fill(0), hist0 = new Array(n + 2).fill(0);
  let x = 0, y = 0; cnt[B * Wd + B] = 1;
  const rec = (depth, vis, first) => {
    if (depth === n) { cls[first] += vis; hist[vis]++; if (first === 0) hist0[vis]++; return; }
    for (let m = 0; m < 8; m++) {
      x += MOVES[m][0]; y += MOVES[m][1]; const k = (x + B) * Wd + (y + B), nw = cnt[k] === 0 ? 1 : 0; cnt[k]++;
      rec(depth + 1, vis + nw, depth === 0 ? m : first);
      cnt[k]--; x -= MOVES[m][0]; y -= MOVES[m][1];
    }
  };
  rec(0, 1, 0);
  const S = cls.reduce((a, b) => a + b, 0), out = { n, S, cls, hist, hist0 };
  ENUM.set(n, out); return out;
}
const bgcd = (a, b) => { while (b) [a, b] = [b, a % b]; return a; };
function exactE(n, S) { const num = BigInt(S), den = 8n ** BigInt(n), g = bgcd(num, den); return [num / g, den / g]; }
function randomWalk(n, seed) { const r = TRV.mulberry32(seed); return Array.from({ length: n }, () => Math.floor(r() * 8)); }

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean', n: 6, walk: [], seed: 3 };
const PRESETS = {
  lean: { n: 6, walk: () => randomWalk(6, 3),
    zh: '六步的随机游走和它的七个像：把每一步换成对称后的那一步，整条路径就被旋转或翻转，访问的格子数不变。八条路径各从一个方向出发——所以全部 8⁶ 条游走按第一步分成八类，每类访问格数的总和相同，总和 S(6) = 1647536 = 8 × 205942。',
    en: 'A six-step random walk and its seven images: replacing every step by its symmetric counterpart rotates or reflects the whole path and keeps the number of visited squares. The eight paths start in the eight directions — so the 8⁶ walks split by their first step into eight classes with equal totals of visited squares, and S(6) = 1647536 = 8 × 205942.' },
  two: { n: 2, walk: () => [0, 4],
    zh: '两步：64 条游走里有 8 条第二步跳回原点，只访问 2 个格子，其余 56 条访问 3 个。总和 S(2) = 8·2 + 56·3 = 184 = 8 × 23，E(2) = 184/64 = 23/8。这里显示的是跳回原点的一条。',
    en: 'Two steps: of the 64 walks, 8 jump back to the start at the second step and visit 2 squares; the other 56 visit 3. The total is S(2) = 8·2 + 56·3 = 184 = 8 × 23, and E(2) = 184/64 = 23/8. The walk shown is one that jumps back.' },
  back: { n: 6, walk: () => [0, 4, 0, 4, 0, 4],
    zh: '来回跳六次：只访问 2 个格子。它的七个像也都只访问 2 个格子——对称不改变一条游走的访问格数。',
    en: 'Back and forth six times: only 2 squares are visited. Its seven images also visit only 2 squares each — a symmetry never changes the number of squares a walk visits.' },
  star: { n: 5, walk: () => [0, 0, 0, 0, 0],
    zh: '一直走同一个方向：五步访问 6 个格子。八个像组成一颗八角星，每条臂都是 6 个格子。',
    en: 'Always the same move: five steps visit 6 squares. The eight images form an eight-pointed star, each arm with 6 squares.' },
  seven: { n: 7, walk: () => randomWalk(7, 11),
    zh: '七步：卷宗穷举到这里，S(7) = 14932736 = 8 × 1866592，与 OEIS 一致。页面把 8⁷ = 2097152 条游走全部走一遍。',
    en: 'Seven steps: the dossier enumerated up to here, S(7) = 14932736 = 8 × 1866592, matching OEIS. The page runs through all 8⁷ = 2097152 walks.' },
  eight: { n: 8, walk: () => randomWalk(8, 5),
    zh: '八步：16777216 条游走，页面全部枚举（要一两秒），S(8) = 133313176 = 8 × 16664147，与 OEIS 的 a(8) 一致。Lean 对每个 n 都证明了整除。',
    en: 'Eight steps: 16777216 walks, all enumerated by the page (a second or two), S(8) = 133313176 = 8 × 16664147, matching OEIS a(8). Lean proves the divisibility for every n.' }
};
let MODEL = null, dirty = true, modelId = 0, geoKey = '';
function build() {
  const n = S.n, E = enumerate(n), j = Math.min(n, S.t * n);
  const copies = Array.from({ length: 8 }, (_, m) => { const w = image(S.walk, m); return { w, pos: positions(w), range: rangeOf(w) }; });
  const key = `${n}|${S.walk.join('')}`;
  if (key !== geoKey) { geoKey = key; modelId++; }
  MODEL = { id: modelId, n, j, E, copies, exact: exactE(n, E.S), a: E.S / 8, oeis: OEIS[n] };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const hue = (m) => { const h = m / 8, k = (n) => (n + h * 12) % 12, a = 0.9, l = 0.6; return [0, 8, 4].map((n) => l - a * Math.min(l, 1 - l) * Math.max(-1, Math.min(k(n) - 3, 9 - k(n), 1))); };
const css = (c, al = 1) => `rgba(${c.map((x) => Math.round(255 * Math.min(1, x))).join(',')},${al})`;
const grp = (x) => String(x).replace(/\B(?=(\d{3})+(?!\d))/g, ' ');
const mv = (m) => `(${MOVES[m][0]}, ${MOVES[m][1]})`;

/* =====================================================================
   4. 3D scene: the board, the walk and its seven images, hopping square by square
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const SIDE = 6.4, HOP = 0.5, LINES_MAX = 9000, PTS_MAX = 2600;
const CAMS = { iso: [0.0001, 0.85, 10.5], side: [0.0001, 1.35, 10], top: [0.0001, 0.05, 10] };
const cam = { theta: 0.0001, phi: 0.85, r: 10.5, tTheta: 0.0001, tPhi: 0.85, tR: 10.5 };
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
  vec2 d = abs(gl_PointCoord - 0.5) * 2.0;
  float r = max(d.x, d.y);
  float a = smoothstep(1.0, 0.75, r) * vA;
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
const extent = (M) => Math.max(3, ...M.copies.flatMap((c) => c.pos.map(([x, y]) => Math.max(Math.abs(x), Math.abs(y))))) + 1;
const sq = (M, x, y, h = 0) => { const c = SIDE / (2 * extent(M) + 1); return [x * c, h, -y * c]; };
function updateGL() {
  const M = MODEL, R = extent(M), c = SIDE / (2 * R + 1), Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, col, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, al, size) => { if (np >= PTS_MAX) return; for (let k = 0; k < 3; k++) { PT.position.array[3 * np + k] = p[k]; PT.aColor.array[3 * np + k] = col[k]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const gray = [0.5, 0.6, 0.72], ds = Math.min(2.4, 22 * c);
  /* the board: darker and lighter squares */
  for (let x = -R; x <= R; x++) for (let y = -R; y <= R; y++) dot(sq(M, x, y), gray, (x + y) % 2 ? 0.07 : 0.16, ds * 0.92);
  for (const s of [-R - 0.5, R + 0.5]) { seg(sq(M, -R - 0.5, s), sq(M, R + 0.5, s), gray, 0.3); seg(sq(M, s, -R - 0.5), sq(M, s, R + 0.5), gray, 0.3); }
  dot(sq(M, 0, 0, 0.02), WHITE, 0.9, ds * 1.15);
  /* each copy: hops drawn as arcs up to the current step, visited squares lit, the knight at its current place */
  const j = M.j, s = Math.floor(j), f = j - s;
  M.copies.forEach((cp, m) => {
    const col = hue(m), seen = new Set();
    for (let k = 0; k < cp.pos.length && k <= s; k++) { const [x, y] = cp.pos[k], key = `${x},${y}`; if (!seen.has(key)) { seen.add(key); dot(sq(M, x, y, 0.03 + 0.012 * m), col, 0.55, ds * 0.62); } }
    for (let k = 0; k < M.n && k <= s; k++) {
      const a = cp.pos[k], b = cp.pos[k + 1], upto = k < s ? 1 : f, N = 10;
      for (let q = 0; q < N; q++) {
        const u0 = q / N, u1 = (q + 1) / N; if (u0 >= upto) break; const e1 = Math.min(u1, upto);
        const P0 = sq(M, a[0] + (b[0] - a[0]) * u0, a[1] + (b[1] - a[1]) * u0, HOP * 4 * u0 * (1 - u0)), P1 = sq(M, a[0] + (b[0] - a[0]) * e1, a[1] + (b[1] - a[1]) * e1, HOP * 4 * e1 * (1 - e1));
        seg(P0, P1, col, 0.85);
      }
    }
    const a = cp.pos[s], b = cp.pos[Math.min(M.n, s + 1)], u = s < M.n ? f : 0;
    dot(sq(M, a[0] + (b[0] - a[0]) * u, a[1] + (b[1] - a[1]) * u, HOP * 4 * u * (1 - u) + 0.06), col, 1, ds * 1.3);
  });
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
  const M = MODEL, R = extent(M); let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  put(T('起点', 'start'), sq(M, 0, 0, 0.35), 'w');
  put(T(`八条路径 · 各访问 ${M.copies[0].range} 格`, `eight paths · ${M.copies[0].range} squares each`), sq(M, 0, -R - 1.2), 'am');
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
/* the eight class totals T_m(n): walks by first move */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 70); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, top = Math.max(...M.E.cls) * 1.15, bw = iw / 8, Y = (v) => pt + ih * (1 - v / top);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  M.E.cls.forEach((v, m) => { ctx.fillStyle = css(hue(m), 0.75); ctx.fillRect(pl + m * bw + bw * 0.15, Y(v), bw * 0.7, pt + ih - Y(v)); lab(ctx, `${MOVES[m][0]},${MOVES[m][1]}`.replace(/-/g, '−'), pl + (m + 0.5) * bw, pt + ih + 4 * dpr, 'center', 'top'); });
  ctx.strokeStyle = AM; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(pl, Y(M.a)); ctx.lineTo(pl + iw, Y(M.a)); ctx.stroke(); ctx.setLineDash([]);
  lab(ctx, grp(M.a), pl - 4 * dpr, Y(M.a), 'right', 'middle', AM); lab(ctx, '0', pl - 4 * dpr, pt + ih, 'right', 'middle');
  $('c1Meta').innerHTML = `<span class="it">${T(`每类 = a(${M.n}) = S(${M.n})/8`, `each class = a(${M.n}) = S(${M.n})/8`)}</span>`;
}
/* how many walks visit r squares, and eight times the count among walks starting with move 0 */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 44); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, H = M.E.hist, rs = H.map((_, r) => r).filter((r) => r >= 2), top = Math.max(...H) * 1.12, bw = iw / rs.length, Y = (v) => pt + ih * (1 - v / top);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  rs.forEach((r, k) => {
    const x = pl + k * bw; ctx.fillStyle = r === M.copies[0].range ? 'rgba(255,200,61,0.85)' : 'rgba(25,240,255,0.55)'; ctx.fillRect(x + bw * 0.18, Y(H[r]), bw * 0.64, pt + ih - Y(H[r]));
    ctx.strokeStyle = MG; ctx.lineWidth = 2 * dpr; ctx.beginPath(); ctx.moveTo(x + bw * 0.1, Y(8 * M.E.hist0[r])); ctx.lineTo(x + bw * 0.9, Y(8 * M.E.hist0[r])); ctx.stroke();
    lab(ctx, String(r), x + bw / 2, pt + ih + 4 * dpr, 'center', 'top');
  });
  lab(ctx, grp(Math.max(...H)), pl - 4 * dpr, Y(Math.max(...H)), 'right', 'middle'); lab(ctx, '0', pl - 4 * dpr, pt + ih, 'right', 'middle');
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('访问 r 格的游走数', 'walks visiting r squares')}</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('8 × 第一步为 (1, 2) 的', '8 × those starting (1, 2)')}</span><span class="it"><i class="sw" style="--c:${AM}"></i>${T('当前路径', 'the path shown')}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function readouts() {
  const M = MODEL, [p, q] = M.exact, ok = String(M.a) === M.oeis;
  pill('pillA', 'n', String(M.n)); pill('pillB', 'S(n)', grp(M.E.S)); pill('pillC', 'a(n) = S(n)/8', grp(M.a)); pill('pillD', T('路径访问', 'path visits'), String(M.copies[0].range));
  setRo([
    [T('步数 n · 全部游走 8ⁿ', 'Steps n · all walks 8ⁿ'), `${M.n} · ${grp(8 ** M.n)}`],
    [T('访问格数总和 S(n) · S(n)/8 · OEIS a(n)', 'Total visited S(n) · S(n)/8 · OEIS a(n)'), `${grp(M.E.S)} · ${grp(M.a)} · ${grp(M.oeis)} ${ok ? '✓' : '✗'}`],
    [T('期望访问格数 E(n) = S(n)/8ⁿ（约分）', 'Expected range E(n) = S(n)/8ⁿ (reduced)'), `${p}/${q} ≈ ${(Number(p) / Number(q)).toFixed(6)}`],
    [T('八类的总和：最小 · 最大', 'The eight class totals: least · greatest'), `${grp(Math.min(...M.E.cls))} · ${grp(Math.max(...M.E.cls))}`],
    [T('八条路径各自访问的格数 · 原路径的步', 'Squares visited by each of the eight paths · moves of the path'), `${M.copies.map((c) => c.range).join(' ')} · ${S.walk.map(mv).join(' ')}`]]);
  $('roNote').innerHTML = T(`Lean：对每个 n ≥ 1，E(n)·2^(3n−3) 是整数；这里 E(${M.n})·2^${3 * M.n - 3} = ${grp(M.a)}。`, `Lean: for every n ≥ 1, E(n)·2^(3n−3) is an integer; here E(${M.n})·2^${3 * M.n - 3} = ${grp(M.a)}.`);
}
const stateKey = () => `${S.n}|${S.walk.join('')}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; }
  const M = MODEL;
  if (!toasted && S.playing && S.t >= 1) { toasted = true; toast(T(`<b>八条路径各访问 ${M.copies[0].range} 格</b>：对称把一条游走变成另一条，访问格数不变。`, `<b>The eight paths visit ${M.copies[0].range} squares each</b>: a symmetry turns one walk into another without changing the count.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('nIn').value = String(S.n); $('nOut').textContent = String(S.n);
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T(`马的八种走法依顺时针编号，第 0 种是 (1, 2)。对 m = 0 … 7，把原路径的每一步 i 换成 sym(m, sym⁻¹(w₀, i))，得到第一步为第 m 种走法的像。`, `The eight knight moves are numbered clockwise, move 0 being (1, 2). For m = 0 … 7, replacing every step i of the path by sym(m, sym⁻¹(w₀, i)) gives its image whose first step is move m.`);
  $('litNote').innerHTML = T('OEIS 列出 a(0) … a(20)；页面对 n ≤ 8 逐条枚举复算。', 'OEIS lists a(0) … a(20); the page recomputes n ≤ 8 by enumerating every walk.');
  $('c1Title').textContent = T(`按第一步分类：八类访问格数总和`, `Split by the first step: the eight class totals`);
  $('c2Title').textContent = T(`访问格数的分布（n = ${M.n}）`, `Distribution of the range (n = ${M.n})`);
  $('clock').innerHTML = T(`第 ${Math.floor(M.j)} 步`, `step ${Math.floor(M.j)}`);
  $('hudBig').textContent = `n = ${M.n} · S(n) = ${grp(M.E.S)} = 8 × ${grp(M.a)}`;
  $('hudSub').textContent = T('一条随机游走（八种颜色之一）和它在格点八个对称下的像：每个像的第一步不同，访问的格子数相同。白点是起点', 'One random walk (one of the eight colours) and its images under the eight symmetries of the lattice: each image starts with a different move and visits the same number of squares. The white dot is the start');
}
function syncRail() {
  const M = MODEL, key = `${M.n}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  $('marks').innerHTML = [[0, T('起点', 'start'), 'first'], [1, T(`第 ${M.n} 步`, `step ${M.n}`), 'last']].map(([f, l, c]) => `<i class="${c}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { n: p.n, walk: p.walk(), t: 0, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('nIn').addEventListener('input', () => { S.n = parseInt($('nIn').value, 10); S.walk = randomWalk(S.n, S.seed); custom(); });
$('walkBtn').addEventListener('click', () => { S.seed += 1; S.walk = randomWalk(S.n, S.seed); custom(); toast(T(`新路径（种子 ${S.seed}）：访问 ${rangeOf(S.walk)} 格。`, `A new path (seed ${S.seed}): ${rangeOf(S.walk)} squares.`)); });
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
document.addEventListener('keydown', (ev) => {
  if (ev.target && (ev.target.tagName === 'INPUT' && ev.target.type !== 'range')) return;
  if (drawer.isOpen()) return;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo((Math.floor(S.t * S.n + 1e-9) + (ev.key === 'ArrowRight' ? 1 : -1)) / S.n); }
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
/* one hop every 0.9 s at 1× */
const runSeconds = () => 0.9 * S.n;
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
    const k = `${MODEL.id}|${MODEL.j.toFixed(3)}`;
    if (glKey !== k) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.KN_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { n: M.n, j: M.j, S: M.E.S, cls: [...M.E.cls], hist: [...M.E.hist], hist0: [...M.E.hist0], a: M.a, oeis: M.oeis, exact: M.exact.map(String),
    copies: M.copies.map((c) => ({ w: [...c.w], pos: c.pos.map((p) => p.slice()), range: c.range })), walk: [...S.walk] }; },
  enumerate: (n) => { const e = enumerate(n); return { S: e.S, cls: [...e.cls], hist: [...e.hist], hist0: [...e.hist0] }; },
  sym: (m, i) => sym(m, i), symInv: (m, i) => symInv(m, i), image: (w, m) => image(w, m), MOVES: MOVES.map((p) => p.slice()), OEIS: OEIS.slice(),
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setT(1); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 9.4; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
