/* MODES//EIGHTEEN · eighteen-mode bosonic occupation assignments exist exactly for even particle numbers
   Kurzyński (2017) puts N identical bosons on the 18 modes of the 18-vector Kochen–Specker set: mode v_ij lies in contexts i
   and j, and a non-contextual model assigns each mode an occupation so that every one of the nine contexts holds N
   particles. He showed that such an assignment exists for N = 2 and asked whether it fails for some N > 2. Proved in
   trureturing (EighteenModeBosonicAssignmentParity.result): an assignment exists if and only if N is even. Every mode is
   counted in two contexts, so 9N = 2 · (particles); for even N, m particles on each mode of a 9-cycle S give every context 2m.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Modes, contexts and assignments
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const WHITE = [0.92, 0.95, 1], GREY = [0.42, 0.5, 0.6], OK = [0.27, 1, 0.7];
const OKC = TRV.palette.ok;
/* Lean's modes: a mode is labelled by the two contexts that contain it */
const MODES = [[1, 2], [1, 6], [1, 7], [1, 8], [2, 3], [2, 8], [2, 9], [3, 4], [3, 7], [3, 9], [4, 5], [4, 7], [4, 8], [5, 6], [5, 8], [5, 9], [6, 7], [6, 9]];
/* Lean's even_assignment puts m on these nine modes: the edges of the cycle 1, 2, 8, 4, 7, 3, 9, 5, 6 */
const CYCLE = [1, 2, 8, 4, 7, 3, 9, 5, 6];
const modeIndex = (a, b) => MODES.findIndex(([x, y]) => (x === Math.min(a, b) && y === Math.max(a, b)));
const S_EDGES = CYCLE.map((c, i) => modeIndex(c, CYCLE[(i + 1) % 9]));
/* a matching of four cycle edges leaves only context 6 uncovered */
const MATCH = [[1, 2], [8, 4], [7, 3], [9, 5]].map(([a, b]) => modeIndex(a, b));
const NMAX = 12, STALL = 120, MAXMOVES = 900;
const sums = (v) => { const s = new Array(10).fill(0); MODES.forEach(([a, b], e) => { s[a] += v[e]; s[b] += v[e]; }); return s; };
const defect = (s, N) => { let d = 0; for (let i = 1; i <= 9; i++) d += Math.abs(s[i] - N); return d; };
/* a run is a list of moves (mode, ±1) starting from the empty assignment */
function lean(N) {
  const moves = [], m = Math.floor(N / 2);
  for (let r = 0; r < m; r++) for (const e of S_EDGES) moves.push([e, 1]);
  if (N % 2) for (const e of MATCH) moves.push([e, 1]);
  return moves;
}
/* local search: add or remove one particle; take a move that lowers the defect D, else a move that keeps it; stop at D = 0
   or after STALL moves without improvement */
function greedy(N, seed) {
  const rnd = TRV.mulberry32(seed * 7919 + N * 31 + 5), v = new Array(18).fill(0), moves = [];
  let s = sums(v), D = defect(s, N), best = D, stall = 0;
  while (D > 0 && stall < STALL && moves.length < MAXMOVES) {
    const down = [], flat = [];
    MODES.forEach(([a, b], e) => { for (const d of [1, -1]) { if (v[e] + d < 0) continue; const dd = Math.abs(s[a] + d - N) - Math.abs(s[a] - N) + Math.abs(s[b] + d - N) - Math.abs(s[b] - N); if (dd < 0) down.push([e, d]); else if (dd === 0) flat.push([e, d]); } });
    const pool = down.length ? down : flat; if (!pool.length) break;
    const [e, d] = pool[Math.floor(rnd() * pool.length)];
    v[e] += d; s = sums(v); D = defect(s, N); moves.push([e, d]);
    if (D < best) { best = D; stall = 0; } else stall++;
  }
  return moves;
}
function play(moves, k) { const v = new Array(18).fill(0); for (let i = 0; i < k; i++) v[moves[i][0]] += moves[i][1]; return v; }

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { N: 2, method: 'lean', seed: 1, t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { N: 2, method: 'lean', play: true,
    zh: 'N = 2：Lean 的构造（even_assignment，m = 1）在 9 个模式上各放 1 个粒子，它们是环 1 → 2 → 8 → 4 → 7 → 3 → 9 → 5 → 6 → 1 的边，每个语境恰好碰到其中两个。这正是 Kurzyński 说的“N = 2 时没有态无关的语境性”。',
    en: 'N = 2: Lean’s construction (even_assignment, m = 1) puts one particle on each of 9 modes, the edges of the cycle 1 → 2 → 8 → 4 → 7 → 3 → 9 → 5 → 6 → 1, and every context meets exactly two of them. This is Kurzyński’s observation that N = 2 shows no state-independent contextuality.' },
  one: { N: 1, method: 'greedy', play: true,
    zh: 'N = 1：一个粒子就是 18 矢量 Kochen–Specker 证明（Cabello 等，1996）。局部搜索把缺额 D = Σ|sᵢ − N| 降到 1 就再也降不下去：九个语境的和是粒子数的两倍，必为偶数，而 9N = 9 是奇数。',
    en: 'N = 1: a single particle is the 18-vector Kochen–Specker proof (Cabello et al., 1996). The local search brings the defect D = Σ|sᵢ − N| down to 1 and no further: the nine context sums total twice the number of particles, an even number, while 9N = 9 is odd.' },
  three: { N: 3, method: 'greedy', play: true,
    zh: 'N = 3：这正是原文问的“某个 N > 2”。答案是肯定的：奇数 N 都无法非语境地分配。搜索停在 D = 1；Lean 证明不存在 D = 0 的分配。',
    en: 'N = 3: exactly the “some N > 2” the paper asks about. The answer is yes: no odd N can be assigned non-contextually. The search stops at D = 1; Lean proves that no assignment reaches D = 0.' },
  six: { N: 6, method: 'greedy', play: true,
    zh: 'N = 6：局部搜索从空的分配出发，一个一个地加减粒子，找到一个 D = 0 的分配——和 Lean 的环构造不同，但同样合法（页面数值）。',
    en: 'N = 6: starting from the empty assignment and adding or removing one particle at a time, the local search finds an assignment with D = 0 — different from Lean’s cycle construction, but just as valid (page numbers).' },
  ten: { N: 10, method: 'lean', play: true,
    zh: 'N = 10：Lean 的环构造，m = 5：环上每个模式 5 个粒子，其余 9 个模式空着；每个语境 2 × 5 = 10。',
    en: 'N = 10: Lean’s cycle construction with m = 5: 5 particles on every mode of the cycle, the other 9 modes empty; every context holds 2 × 5 = 10.' },
  nine: { N: 9, method: 'lean', play: true,
    zh: 'N = 9：环构造放 4 轮得到 8，再加 4 个模式的匹配，只剩语境 6 少一个粒子：D = 1。对奇数 N 这已是最好——差一个粒子的那个语境可以挪动，但消不掉。',
    en: 'N = 9: four rounds of the cycle give 8, then a matching of 4 modes leaves only context 6 one particle short: D = 1. For odd N this is the best possible — the short context can move around, but it cannot disappear.' }
};
let MODEL = null, RUN = null, dirty = true, modelId = 0;
function build() {
  const key = `${S.N}|${S.method}|${S.seed}`;
  if (!RUN || RUN.key !== key) {
    const moves = S.method === 'lean' ? lean(S.N) : greedy(S.N, S.seed), traj = [], v = new Array(18).fill(0);
    traj.push(defect(sums(v), S.N)); for (const [e, d] of moves) { v[e] += d; traj.push(defect(sums(v), S.N)); }
    RUN = { key, moves, traj, final: v };
  }
  const Tn = RUN.moves.length, k = Math.min(Tn, Math.round(S.t * Tn)), v = play(RUN.moves, k), s = sums(v), D = defect(s, S.N);
  MODEL = { id: ++modelId, N: S.N, method: S.method, seed: S.seed, T: Tn, k, v, s, D, P: v.reduce((a, b) => a + b, 0), traj: RUN.traj, final: RUN.final, finalD: RUN.traj[Tn],
    last: k > 0 ? RUN.moves[k - 1] : null };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const mname = (m) => (m === 'lean' ? T('Lean 的环构造', 'Lean’s cycle') : T('局部搜索', 'local search'));
const SUP = (k) => String(k).replace(/\d/g, (c) => '₀₁₂₃₄₅₆₇₈₉'[c]);

/* =====================================================================
   4. 3D scene: the nine contexts on a torus (they form the 3 × 3 rook's graph), modes as arcs carrying their particles
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const RT = 2.35, AT = 1.15, LINES_MAX = 6000, PTS_MAX = 600;
/* context ↦ (row, column) of the 3 × 3 grid: same row or same column ⟺ the two contexts share a mode */
const GRID = { 1: [0, 0], 2: [0, 1], 8: [0, 2], 7: [1, 0], 3: [1, 1], 4: [1, 2], 6: [2, 0], 9: [2, 1], 5: [2, 2] };
const torus = (th, ph, lift = 0) => [(RT + (AT + lift) * Math.cos(ph)) * Math.cos(th), (AT + lift) * Math.sin(ph), (RT + (AT + lift) * Math.cos(ph)) * Math.sin(th)];
const angles = (c) => [2 * Math.PI * GRID[c][0] / 3 - Math.PI / 2, 2 * Math.PI * GRID[c][1] / 3 + Math.PI / 2];
const shortest = (a, b) => { let d = (b - a) % (2 * Math.PI); if (d > Math.PI) d -= 2 * Math.PI; if (d < -Math.PI) d += 2 * Math.PI; return d; };
/* the arc of mode e at parameter f ∈ [0, 1]: along the tube for contexts in one row, around the ring for one column */
function arcAt(e, f, lift = 0) {
  const [a, b] = MODES[e], [t1, p1] = angles(a), [t2, p2] = angles(b);
  return torus(t1 + shortest(t1, t2) * f, p1 + shortest(p1, p2) * f, lift);
}
const CAMS = { iso: [0.0001, 0.95, 9.2], side: [0.0001, 1.5, 8.6], top: [0.0001, 0.06, 9.4] };
const cam = { theta: 0, phi: 0.95, r: 9.2, tTheta: 0, tPhi: 0.95, tR: 9.2 };
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
  float a = smoothstep(1.0, 0.45, r) * vA;
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
function updateGL() {
  const M = MODEL, Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; for (let j = 0; j < 3; j++) { PT.position.array[3 * np + j] = p[j]; PT.aColor.array[3 * np + j] = c[j]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  /* a faint torus wireframe */
  for (let i = 0; i < 12; i++) { const th = 2 * Math.PI * i / 12 - Math.PI / 2 + Math.PI / 12; for (let s = 0; s < 32; s++) seg(torus(th, 2 * Math.PI * s / 32), torus(th, 2 * Math.PI * (s + 1) / 32), GREY, 0.16); }
  for (let j = 0; j < 6; j++) { const ph = 2 * Math.PI * j / 6 + Math.PI / 2 + Math.PI / 6; for (let s = 0; s < 64; s++) seg(torus(2 * Math.PI * s / 64, ph), torus(2 * Math.PI * (s + 1) / 64, ph), GREY, 0.16); }
  /* the 18 modes: amber with their particles when occupied, grey when empty; the cycle S of Lean's construction in white when empty */
  MODES.forEach((_, e) => {
    const occ = M.v[e], onS = S_EDGES.includes(e), justNow = M.last && M.last[0] === e;
    const c = justNow ? COL.magenta : occ ? COL.amber : onS && M.method === 'lean' ? WHITE : GREY;
    for (let s = 0; s < 24; s++) seg(arcAt(e, s / 24), arcAt(e, (s + 1) / 24), c, occ ? 0.95 : 0.4);
    for (let j = 0; j < occ; j++) dot(arcAt(e, (j + 1) / (occ + 1), 0.08), justNow ? COL.magenta : COL.amber, 1, 1.25);
  });
  /* the nine contexts: green when their sum is N, magenta otherwise */
  for (let i = 1; i <= 9; i++) { const [th, ph] = angles(i), good = M.s[i] === M.N; dot(torus(th, ph), good ? OK : COL.magenta, 1, 3.2); }
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
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.4 : 1);
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
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(24, Math.max(3.5, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(24, Math.max(3.5, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

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
  for (let i = 1; i <= 9; i++) { const [th, ph] = angles(i); put(`C${SUP(i)} · ${M.s[i]}`, torus(th, ph, 0.45), M.s[i] === M.N ? 'gn' : 'mg'); }
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
/* the nine context sums against N */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 34); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, top = Math.max(M.N + 1, ...M.s.slice(1)) * 1.08, bw = iw / 9, Y = (y) => pt + ih * (1 - y / top);
  for (let i = 1; i <= 9; i++) { const x = pl + (i - 1) * bw, h = M.s[i], good = h === M.N; ctx.fillStyle = good ? 'rgba(70,255,178,0.7)' : 'rgba(255,47,208,0.75)'; ctx.fillRect(x + bw * 0.18, Y(h), bw * 0.64, Y(0) - Y(h)); lab(ctx, String(h), x + bw / 2, Y(h) - 2 * dpr, 'center', 'bottom', INK); lab(ctx, `C${SUP(i)}`, x + bw / 2, Y(0) + 4 * dpr, 'center', 'top'); }
  ctx.strokeStyle = AM; ctx.setLineDash([5 * dpr, 4 * dpr]); ctx.lineWidth = 1.4 * dpr; ctx.beginPath(); ctx.moveTo(pl, Y(M.N)); ctx.lineTo(pl + iw, Y(M.N)); ctx.stroke(); ctx.setLineDash([]);
  lab(ctx, `N = ${M.N}`, pl - 4 * dpr, Y(M.N), 'right', 'middle', AM);
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${OKC}"></i>${T('和 = N', 'sum = N')}</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('和 ≠ N', 'sum ≠ N')}</span><span class="it">· Σ = ${M.s.reduce((a, b) => a + b, 0)} = 2 × ${M.P}</span>`;
}
/* the defect D = Σ|s_i − N| along the run: its parity never changes */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 34); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, tr = M.traj, top = Math.max(2, ...tr) * 1.08, n = Math.max(1, tr.length - 1), X = (k) => pl + iw * k / n, Y = (d) => pt + ih * (1 - d / top);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
  if (M.N % 2) { ctx.strokeStyle = MG; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(pl, Y(1)); ctx.lineTo(pl + iw, Y(1)); ctx.stroke(); ctx.setLineDash([]); lab(ctx, 'D = 1', pl + iw, Y(1) - 3 * dpr, 'right', 'bottom', MG); }
  ctx.strokeStyle = CY; ctx.lineWidth = 1.6 * dpr; ctx.beginPath(); tr.forEach((d, k) => (k ? ctx.lineTo(X(k), Y(d)) : ctx.moveTo(X(k), Y(d)))); ctx.stroke();
  ctx.strokeStyle = AM; ctx.lineWidth = 1 * dpr; ctx.beginPath(); ctx.moveTo(X(M.k), Y(0)); ctx.lineTo(X(M.k), Y(top)); ctx.stroke();
  ctx.fillStyle = CY; ctx.beginPath(); ctx.arc(X(M.k), Y(M.D), 3.4 * dpr, 0, 2 * Math.PI); ctx.fill();
  lab(ctx, '0', pl - 4 * dpr, Y(0), 'right', 'middle'); lab(ctx, String(tr[0]), pl - 4 * dpr, Y(tr[0]), 'right', 'middle');
  lab(ctx, T('步', 'move'), pl + iw, pt + ih + 5 * dpr, 'right', 'top');
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>D = Σ|sᵢ − N|</span><span class="it">· ${M.N % 2 ? T('N 奇：D 始终为奇数', 'odd N: D is always odd') : T('N 偶：D 始终为偶数', 'even N: D is always even')}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function readouts() {
  const M = MODEL, occ = MODES.map((p, e) => [p, M.v[e]]).filter(([, x]) => x > 0);
  pill('pillA', 'N', String(M.N)); pill('pillB', T('步', 'move'), `${M.k} / ${M.T}`); pill('pillC', 'D', String(M.D)); pill('pillD', T('分配', 'assignment'), M.N % 2 ? '✗' : '✓');
  setRo([
    [T('粒子数 N · 方法 · 步数', 'Particles N · method · moves'), `${M.N} · ${mname(M.method)}${M.method === 'greedy' ? ` #${M.seed}` : ''} · ${M.k} / ${M.T}`],
    [T('九个语境的和 s₁ … s₉', 'The nine context sums s₁ … s₉'), M.s.slice(1).join(' ')],
    [T('缺额 D = Σ|sᵢ − N| · Σ sᵢ = 2 × 粒子数 · 9N', 'Defect D = Σ|sᵢ − N| · Σ sᵢ = 2 × particles · 9N'), `${M.D} · ${M.s.reduce((a, b) => a + b, 0)} = 2 × ${M.P} · ${9 * M.N}`],
    [T('有粒子的模式 (i, j): 个数', 'Occupied modes (i, j): count'), occ.length ? occ.map(([[a, b], x]) => `(${a},${b}):${x}`).join(' ') : '—'],
    [T('结论（Lean）', 'Verdict (Lean)'), M.N % 2 ? T(`N = ${M.N} 是奇数：不存在非语境分配`, `N = ${M.N} is odd: no non-contextual assignment exists`) : T(`N = ${M.N} 是偶数：存在非语境分配`, `N = ${M.N} is even: a non-contextual assignment exists`)]]);
  $('roNote').innerHTML = M.N % 2
    ? T(`每个模式属于两个语境，所以九个和加起来是粒子数的两倍——偶数；可九个和都等于 N 时总和是 9N = ${9 * M.N}，奇数。D 因此永远是奇数，至少为 1。`, `Every mode lies in two contexts, so the nine sums add up to twice the number of particles — an even number; if all nine equalled N they would total 9N = ${9 * M.N}, which is odd. So D is always odd, at least 1.`)
    : T(`N 是偶数：Lean 的构造在环 S 的 9 个模式上各放 ${M.N / 2} 个粒子，每个语境恰好碰到 S 的两个模式。`, `N is even: Lean’s construction puts ${M.N / 2} particles on each of the 9 modes of the cycle S, and every context meets exactly two modes of S.`);
}
const stateKey = () => `${S.N}|${S.method}|${S.seed}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; }
  const M = MODEL;
  if (!toasted && S.playing && M.k >= M.T) { toasted = true; toast(M.D === 0 ? T(`<b>D = 0</b>：每个语境恰好 ${M.N} 个粒子。`, `<b>D = 0</b>: every context holds exactly ${M.N} particles.`) : T(`<b>D = ${M.D}</b>：N = ${M.N} 是奇数，D 降不到 0。`, `<b>D = ${M.D}</b>: N = ${M.N} is odd, and D cannot reach 0.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('nIn').value = String(S.N); $('nOut').textContent = String(S.N);
  document.querySelectorAll('#methodChips [data-method]').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.method === S.method)));
  $('reseed').disabled = S.method !== 'greedy';
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = M.method === 'lean'
    ? T(`Lean 的环构造：每一步给环 1 → 2 → 8 → 4 → 7 → 3 → 9 → 5 → 6 的下一个模式加 1 个粒子${M.N % 2 ? '；N 为奇数时最后再加 4 个模式的匹配' : ''}。`, `Lean’s cycle: each move adds one particle to the next mode of the cycle 1 → 2 → 8 → 4 → 7 → 3 → 9 → 5 → 6${M.N % 2 ? '; for odd N a matching of 4 modes comes last' : ''}.`)
    : T(`局部搜索：每一步加或减一个粒子，优先让 D 下降，否则保持；D = 0 或连续 ${STALL} 步不再下降时停止。`, `Local search: each move adds or removes one particle, lowering D when possible and otherwise keeping it; it stops at D = 0 or after ${STALL} moves without improvement.`);
  $('litNote').innerHTML = T('Lean 证明的是每个 N：偶数存在、奇数不存在；具体的搜索过程与步数是页面数值。', 'Lean proves every N: even numbers admit an assignment and odd numbers do not; the particular searches and move counts are page numbers.');
  $('c1Title').textContent = T('九个语境里的粒子数', 'Particles in the nine contexts');
  $('c2Title').textContent = T('缺额 D 随步数', 'The defect D move by move');
  $('clock').innerHTML = T(`第 ${M.k} 步`, `move ${M.k}`);
  $('hudBig').textContent = `N = ${M.N} · D = ${M.D}${M.N % 2 ? ' · 9N ' + T('奇', 'odd') : ''}`;
  $('hudSub').textContent = T('环面上的九个点是语境，十八条弧是模式；同一行或同一列的两个语境共享一个模式。弧上的琥珀点是粒子，语境的和等于 N 时变绿', 'The nine points on the torus are the contexts and the eighteen arcs the modes; two contexts in the same row or column share a mode. Amber dots on an arc are particles, and a context turns green when its sum equals N');
}
function syncRail() {
  const M = MODEL, key = `${M.T}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, T('空', 'empty')], [1, T(`第 ${M.T} 步`, `move ${M.T}`)]];
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : 'last'}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { N: p.N, method: p.method, seed: 1, t: 0, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('nIn').addEventListener('input', () => { S.N = parseInt($('nIn').value, 10); custom(); });
document.querySelectorAll('#methodChips [data-method]').forEach((b) => b.addEventListener('click', () => { S.method = b.dataset.method; custom(); }));
$('reseed').addEventListener('click', () => { S.seed++; custom(); });
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); const Tn = Math.max(1, MODEL.T); jumpTo((MODEL.k + (ev.key === 'ArrowRight' ? 1 : -1)) / Tn); }
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
/* a run lasts 0.3 s per move at 1×, between 5 and 16 seconds */
const runSeconds = (Tn) => Math.min(16, Math.max(5, 0.3 * Tn));
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : 1); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed / runSeconds(MODEL.T));
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
window.MD_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { N: M.N, method: M.method, seed: M.seed, T: M.T, k: M.k, v: M.v.slice(), s: M.s.slice(), D: M.D, P: M.P, traj: M.traj.slice(), final: M.final.slice(), finalD: M.finalD, last: M.last }; },
  modes: () => MODES.map((p) => p.slice()),
  cycle: () => S_EDGES.map((e) => MODES[e].slice()),
  grid: () => JSON.parse(JSON.stringify(GRID)),
  run: (N, method, seed) => { const mv = method === 'lean' ? lean(N) : greedy(N, seed || 1); return { moves: mv.map((m) => m.slice()), final: play(mv, mv.length) }; },
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('ten'); S.playing = false; setPlayUI(); setT(1); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 8.4; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
