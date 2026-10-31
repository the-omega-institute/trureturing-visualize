/* SANDPILE//TORUS · the n × 1 torus sandpile topples A023855(n − 1) times in every order
   OEIS A293452 (Arndt, 2017) counts the topplings of the sandpile of A249872 on the n × k torus — 4 grains on every cell except
   c[0,0], which never gains — and conjectures T(n,1) = A023855(n). The printed index is off by one; trureturing proves the
   corrected identity (TorusColumnToppling.result): for n ≥ 2 a final state is reachable and every legal toppling sequence that
   ends in one has exactly A023855(n − 1) = Σ_{1 ≤ j ≤ ⌊n/2⌋} j(n − j) topplings. On the n × 1 torus the four neighbours of cell
   i are i ± 1 and the cell itself twice, so a toppling keeps 2 of its 4 grains.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. The sandpile
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const WHITE = [0.92, 0.95, 1], GREY = [0.42, 0.5, 0.6];
const NMIN = 2, NMAX = 80, CK = 128;
/* A023855(m) as Lean defines it: Σ_{j ∈ [1, ⌊(m+1)/2⌋]} j (m + 1 − j) */
const a023855 = (m) => { let s = 0; for (let j = 1; j <= Math.floor((m + 1) / 2); j++) s += j * (m + 1 - j); return s; };
/* the target odometer u(x) = (x(n − x) + [n even]·min(x, n − x)) / 2 */
const uStar = (n, x) => (x * (n - x) + (n % 2 === 0 ? Math.min(x, n - x) : 0)) / 2;
/* one toppling of cell p ≠ 0, as in Lean's topple: p loses 4, each of its neighbours p + 1, p − 1, p, p gains 1 unless it is cell 0 */
function topple(c, p, n) { c[p] -= 4; let lost = 0; for (const q of [(p + 1) % n, (p - 1 + n) % n, p, p]) { if (q !== 0) c[q] += 1; else lost++; } return lost; }
const ORDERS = ['left', 'right', 'max', 'random', 'parallel'];
/* a legal sequence that ends in a final state, chosen by the order rule */
function simulate(n, order, seed) {
  const c = new Int32Array(n).fill(4); c[0] = 0;
  const v = new Int32Array(n), seq = [], cks = [], rnd = TRV.mulberry32(seed * 7919 + n);
  let lost = 0, maxPile = 4, round = [];
  const unstable = () => { const u = []; for (let i = 1; i < n; i++) if (c[i] >= 4) u.push(i); return u; };
  for (let guard = 0; guard < 200000; guard++) {
    if (seq.length % CK === 0 && cks.length === seq.length / CK) cks.push({ c: c.slice(), v: v.slice(), lost });
    let p;
    if (order === 'parallel') { if (!round.length) round = unstable(); if (!round.length) break; p = round.shift(); }
    else {
      const U = unstable(); if (!U.length) break;
      if (order === 'left') p = U[0];
      else if (order === 'right') p = U[U.length - 1];
      else if (order === 'max') p = U.reduce((b, i) => (c[i] > c[b] ? i : b), U[0]);
      else p = U[Math.floor(rnd() * U.length)];
    }
    if (c[p] < 4) throw new Error('illegal toppling');
    lost += topple(c, p, n); v[p]++; seq.push(p);
    for (let i = 1; i < n; i++) if (c[i] > maxPile) maxPile = c[i];
  }
  return { seq: Int16Array.from(seq), cks, final: c, v, lost, maxPile };
}
/* the configuration, odometer and lost grains after the first k topplings */
function stateAt(run, n, k) {
  const ck = run.cks[Math.min(run.cks.length - 1, Math.floor(k / CK))], c = ck.c.slice(), v = ck.v.slice(); let lost = ck.lost;
  for (let s = Math.floor(k / CK) * CK; s < k; s++) { const p = run.seq[s]; lost += topple(c, p, n); v[p]++; }
  return { c, v, lost };
}

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { n: 10, order: 'left', seed: 1, t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { n: 10, order: 'left', play: true,
    zh: 'n = 10：每次推倒最左边的不稳定格子。共 95 次——这是 A293452 第一列的第十个数据项，等于 A023855(9) = 1·9 + 2·8 + 3·7 + 4·6 + 5·5。Lean 证明：对任何 n ≥ 2，任何以终态结束的合法顺序都恰好推倒 A023855(n − 1) 次。',
    en: 'n = 10, always toppling the leftmost unstable cell: 95 topplings — the tenth data term of the first column of A293452, equal to A023855(9) = 1·9 + 2·8 + 3·7 + 4·6 + 5·5. Lean proves that for every n ≥ 2 every legal order that ends in a final state topples exactly A023855(n − 1) times.' },
  shuffle: { n: 10, order: 'random', play: true,
    zh: '同样的 n = 10，每一步随机挑一个不稳定格子。顺序完全不同，次数仍是 95，每个格子被推倒的次数（里圈的柱子）也和左序完全相同——这正是 Lean 证明的与顺序无关。按“换一个随机顺序”再试。',
    en: 'The same n = 10, toppling a random unstable cell at each step. The order is entirely different, yet the count is again 95, and so is the number of topplings of every cell (the inner bars) — exactly the order independence Lean proves. Press “another random order” to try again.' },
  odd: { n: 9, order: 'max', play: true,
    zh: 'n = 9，每次推倒最高的一堆：60 次 = A023855(8)。n 为奇数时终态每格 3 粒，里圈柱子的高度是抛物线 u(x) = x(9 − x)/2。',
    en: 'n = 9, always toppling the highest pile: 60 topplings = A023855(8). For odd n the final state has 3 grains on every cell, and the inner bars follow the parabola u(x) = x(9 − x)/2.' },
  even: { n: 8, order: 'right', play: true,
    zh: 'n = 8，每次推倒最右边的不稳定格子：50 次 = A023855(7)。n 为偶数时 u(x) 多了 min(x, 8 − x)/2：正对汇点的格子 x = 4 推倒 10 次（只看 x(8 − x)/2 是 8 次），终态里这一格只剩 2 粒。',
    en: 'n = 8, always toppling the rightmost unstable cell: 50 topplings = A023855(7). For even n the target u(x) gains min(x, 8 − x)/2: the cell opposite the sink, x = 4, topples 10 times (x(8 − x)/2 alone would give 8), and in the final state it holds only 2 grains.' },
  printed: { n: 5, order: 'left', play: true,
    zh: 'OEIS 印出的猜想是 T(n,1) = A023855(n)。n = 5 时实际推倒 10 次，而 A023855(5) = 1·5 + 2·4 + 3·3 = 22；10 是 A023855(4)。印出的等式在每个 n 都不成立，下标差了一位——Lean 证明的是改正后的 T(n,1) = A023855(n − 1)。',
    en: 'OEIS prints the conjecture T(n,1) = A023855(n). For n = 5 the pile topples 10 times, while A023855(5) = 1·5 + 2·4 + 3·3 = 22; 10 is A023855(4). The printed identity fails at every n — the index is off by one — and Lean proves the corrected T(n,1) = A023855(n − 1).' },
  big: { n: 40, order: 'parallel', play: true,
    zh: 'n = 40，按轮推倒：每一轮把当时所有不稳定的格子各推倒一次。共 5530 次 = A023855(39)，约为 n³/12（页面数值）。',
    en: 'n = 40 in rounds: each round topples every cell that is unstable at its start once. 5530 topplings = A023855(39), about n³/12 (page numbers).' }
};
let MODEL = null, RUN = null, dirty = true, modelId = 0;
function build() {
  const n = S.n, key = `${n}|${S.order}|${S.seed}`;
  if (!RUN || RUN.key !== key) RUN = { key, ...simulate(n, S.order, S.seed) };
  const Tn = RUN.seq.length, k = Math.min(Tn, Math.round(S.t * Tn)), st = stateAt(RUN, n, k);
  const u = Array.from({ length: n }, (_, x) => uStar(n, x));
  const unstable = []; for (let i = 1; i < n; i++) if (st.c[i] >= 4) unstable.push(i);
  let atTarget = 0, maxDef = 0; for (let i = 1; i < n; i++) { if (st.v[i] === u[i]) atTarget++; maxDef = Math.max(maxDef, u[i] - st.v[i]); }
  MODEL = { id: ++modelId, n, order: S.order, seed: S.seed, T: Tn, k, c: st.c, v: st.v, lost: st.lost, u, unstable, atTarget, maxDef,
    last: k > 0 ? RUN.seq[k - 1] : null, next: k < Tn ? RUN.seq[k] : null, a: a023855(n - 1), printed: a023855(n), maxPile: RUN.maxPile, final: RUN.final, finalV: RUN.v, finalLost: RUN.lost };
}
/* the column T(n, 1) for every n, by simulation with the current order rule */
const COLUMN = new Map();
function columnOf(order, seed) {
  const key = `${order}|${seed}`; if (COLUMN.has(key)) return COLUMN.get(key);
  const out = []; for (let n = NMIN; n <= NMAX; n++) out.push(simulate(n, order, seed).seq.length);
  COLUMN.set(key, out); return out;
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const ORDER_NAMES = { left: ['最左', 'leftmost'], right: ['最右', 'rightmost'], max: ['最高', 'highest'], random: ['随机', 'random'], parallel: ['按轮', 'in rounds'] };
const oname = (o) => T(...ORDER_NAMES[o]);

/* =====================================================================
   4. 3D scene: the ring of cells with their grains, and the odometer crown inside
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const RR = 2.7, RIN = 1.75, HB = 2.3, LINES_MAX = 6000, PTS_MAX = 2000;
const CAMS = { iso: [0.0001, 1.05, 9.2], side: [0.0001, 1.45, 8.6], top: [0.0001, 0.06, 9.2] };
const cam = { theta: 0, phi: 1.05, r: 9.2, tTheta: 0, tPhi: 1.05, tR: 9.2 };
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
/* cell i sits at angle 2πi/n, cell 0 (the sink) in front */
const ang = (M, i) => 2 * Math.PI * i / M.n + Math.PI / 2;
const at = (M, i, r, y) => [r * Math.cos(ang(M, i)), y, r * Math.sin(ang(M, i))];
const grainH = (M) => Math.min(0.26, 2.2 / (M.maxPile + 1));
function updateGL() {
  const M = MODEL, Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; for (let j = 0; j < 3; j++) { PT.position.array[3 * np + j] = p[j]; PT.aColor.array[3 * np + j] = c[j]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const n = M.n, w = Math.min(0.42, 2 * Math.PI * RR / n * 0.42), gh = grainH(M), ds = Math.min(1.5, 9 / Math.max(6, n) + 0.35);
  /* the ring and the cell tiles */
  for (let s = 0; s < 96; s++) { const a0 = 2 * Math.PI * s / 96, a1 = 2 * Math.PI * (s + 1) / 96; seg([RR * Math.cos(a0), 0, RR * Math.sin(a0)], [RR * Math.cos(a1), 0, RR * Math.sin(a1)], GREY, 0.35); seg([RIN * Math.cos(a0), 0, RIN * Math.sin(a0)], [RIN * Math.cos(a1), 0, RIN * Math.sin(a1)], GREY, 0.2); }
  const uMax = Math.max(1, ...M.u);
  for (let i = 0; i < n; i++) {
    const sink = i === 0, hot = i === M.next, was = i === M.last;
    if (sink) { for (let s = 0; s < 24; s++) { const a0 = 2 * Math.PI * s / 24, a1 = 2 * Math.PI * (s + 1) / 24, p = at(M, 0, RR, 0); seg([p[0] + 0.22 * Math.cos(a0), 0, p[2] + 0.22 * Math.sin(a0)], [p[0] + 0.22 * Math.cos(a1), 0, p[2] + 0.22 * Math.sin(a1)], COL.magenta, 0.9); } continue; }
    /* grains stacked in a column: amber if the cell is unstable, cyan if not; the cell about to topple in magenta */
    const col = hot ? COL.magenta : M.c[i] >= 4 ? COL.amber : COL.cyan;
    for (let j = 0; j < M.c[i]; j++) dot(at(M, i, RR, 0.12 + j * gh), col, hot || M.c[i] >= 4 ? 1 : 0.8, ds);
    /* the odometer crown: v(i) as a bar inside, u(i) as a ring tick */
    /* the odometer crown: v(i) as a bright bar (three strands), the rest of the way to u(i) dim, and an amber cap at u(i) */
    const hv = HB * M.v[i] / uMax, hu = HB * M.u[i] / uMax, full = M.v[i] === M.u[i], dw = Math.min(0.05, w * 0.18) / RIN * n / (2 * Math.PI);
    for (const o of [-dw, 0, dw]) if (M.v[i] > 0) seg(at(M, i + o, RIN, 0), at(M, i + o, RIN, hv), full ? COL.cyan : WHITE, full ? 0.95 : 0.6);
    if (!full) seg(at(M, i, RIN, hv), at(M, i, RIN, hu), GREY, 0.45);
    dot(at(M, i, RIN, hu), COL.amber, 0.95, ds * 0.75);
    if (was) dot(at(M, i, RIN, hv), COL.magenta, 1, ds * 0.9);
  }
  /* the toppling that is about to happen: arcs to the two neighbours (to the sink they are lost) */
  if (M.next !== null) {
    const p = M.next, top = at(M, p, RR, 0.12 + Math.max(0, M.c[p] - 1) * gh);
    for (const q of [(p + 1) % n, (p - 1 + n) % n]) {
      const tq = at(M, q, RR, 0.12 + (q === 0 ? 0 : M.c[q]) * gh);
      for (let s = 0; s < 10; s++) { const f0 = s / 10, f1 = (s + 1) / 10, P = (f) => [top[0] + (tq[0] - top[0]) * f, top[1] + (tq[1] - top[1]) * f + 0.6 * Math.sin(Math.PI * f), top[2] + (tq[2] - top[2]) * f]; seg(P(f0), P(f1), q === 0 ? COL.magenta : COL.amber, 0.85); }
    }
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
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.4 : 1);
  camera.position.set(r * sp * Math.sin(cam.theta), r * Math.cos(cam.phi) + 0.9, r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(0, 0.9, 0);
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
  put(T(`汇点 c[0,0] · 丢失 ${M.lost}`, `sink c[0,0] · lost ${M.lost}`), at(M, 0, RR + 0.55, 0), 'mg');
  if (M.next !== null) put(T(`下一个：x = ${M.next}`, `next: x = ${M.next}`), at(M, M.next, RR + 0.6, 0.3 + M.c[M.next] * grainH(M)), 'am');
  if (M.n % 2 === 0) put(`x = ${M.n / 2}`, at(M, M.n / 2, RR + 0.55, 0), 't');
  put(T('里圈：v(x) 与 u(x)', 'inside: v(x) and u(x)'), [0, HB + 0.35, 0], 't');
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
const disc = (ctx, x, y, r, c) => { ctx.fillStyle = c; ctx.beginPath(); ctx.arc(x, y, r, 0, 2 * Math.PI); ctx.fill(); };
/* the odometer v(x) as bars against the target u(x), and the grains c(x) as dots */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 40); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, n = M.n, uMax = Math.max(1, ...M.u), bw = iw / (n + 1), X = (x) => pl + bw * (x + 0.5), Y = (y) => pt + ih * (1 - y / (uMax * 1.08));
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
  for (let x = 0; x < n; x++) { const v = M.v[x], full = v === M.u[x]; ctx.fillStyle = full ? 'rgba(25,240,255,0.75)' : 'rgba(212,239,255,0.45)'; ctx.fillRect(X(x) - bw * 0.36, Y(v), bw * 0.72, Y(0) - Y(v)); }
  ctx.strokeStyle = AM; ctx.lineWidth = 1.6 * dpr; ctx.beginPath(); for (let x = 0; x <= n; x++) { const y = Y(uStar(n, x)); x ? ctx.lineTo(X(x), y) : ctx.moveTo(X(x), y); } ctx.stroke();
  if (M.last !== null) disc(ctx, X(M.last), Y(M.v[M.last]) - 3 * dpr, 2.6 * dpr, MG);
  lab(ctx, '0', pl - 4 * dpr, Y(0), 'right', 'middle'); lab(ctx, String(+uMax.toFixed(1)), pl - 4 * dpr, Y(uMax), 'right', 'middle');
  lab(ctx, 'x = 0', X(0), Y(0) + 4 * dpr, 'center', 'top'); lab(ctx, `x = ${n}`, X(n), Y(0) + 4 * dpr, 'center', 'top');
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('v(x)，已到 u(x)', 'v(x), at u(x)')}</span><span class="it"><i class="sw" style="--c:${INK}"></i>${T('v(x)，未到', 'v(x), below')}</span><span class="it"><i class="sw" style="--c:${AM}"></i>u(x)</span>`;
}
/* the first column T(n, 1), n = 2 … 80: simulation in the current order against A023855(n − 1) and the printed A023855(n) */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 40); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, col = columnOf(M.order, M.seed), top = Math.log10(a023855(NMAX) * 1.6);
  const X = (n) => pl + iw * (n - 1) / (NMAX - 1), Y = (v) => pt + ih * (1 - Math.log10(Math.max(1, v)) / top);
  [1, 10, 100, 1000, 10000].forEach((v) => { ctx.strokeStyle = FAINT; ctx.globalAlpha = 0.5; ctx.beginPath(); ctx.moveTo(pl, Y(v)); ctx.lineTo(pl + iw, Y(v)); ctx.stroke(); ctx.globalAlpha = 1; lab(ctx, v >= 1000 ? `10${'³⁴'[Math.log10(v) - 3]}` : String(v), pl - 4 * dpr, Y(v), 'right', 'middle'); });
  ctx.strokeStyle = MG; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.lineWidth = 1.2 * dpr; ctx.beginPath(); for (let n = 1; n <= NMAX; n++) (n === 1 ? ctx.moveTo(X(n), Y(a023855(n))) : ctx.lineTo(X(n), Y(a023855(n)))); ctx.stroke(); ctx.setLineDash([]);
  ctx.strokeStyle = AM; ctx.lineWidth = 1.4 * dpr; ctx.beginPath(); for (let n = 2; n <= NMAX; n++) (n === 2 ? ctx.moveTo(X(n), Y(a023855(n - 1))) : ctx.lineTo(X(n), Y(a023855(n - 1)))); ctx.stroke();
  col.forEach((t, j) => disc(ctx, X(j + NMIN), Y(t), (j + NMIN === M.n ? 3.6 : 1.7) * dpr, j + NMIN === M.n ? CY : INK));
  lab(ctx, 'n', pl + iw, pt + ih + 5 * dpr, 'right', 'top'); lab(ctx, '2', X(2), pt + ih + 5 * dpr, 'center', 'top'); lab(ctx, String(NMAX), X(NMAX), pt + ih + 5 * dpr, 'center', 'top');
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${INK}"></i>${T(`模拟（${oname(M.order)}）`, `simulated (${oname(M.order)})`)}</span><span class="it"><i class="sw" style="--c:${AM}"></i>A023855(n − 1)</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('印出的 A023855(n)', 'printed A023855(n)')}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function readouts() {
  const M = MODEL, grains = M.c.reduce((s, x) => s + x, 0);
  pill('pillA', 'n', String(M.n)); pill('pillB', 'k', `${M.k} / ${M.T}`); pill('pillC', 'T(n,1)', String(M.T)); pill('pillD', T('丢失', 'lost'), String(M.lost));
  setRo([
    [T('n · 顺序 · 已推倒 k / 总数', 'n · order · toppled k / total'), `${M.n} · ${oname(M.order)}${M.order === 'random' ? ` #${M.seed}` : ''} · ${M.k} / ${M.T}`],
    [T('上一次推倒 · 下一次 · 不稳定的格子', 'Last toppling · next · unstable cells'), `${M.last === null ? '—' : `x = ${M.last}`} · ${M.next === null ? T('无（终态）', 'none (final)') : `x = ${M.next}`} · ${M.unstable.length ? M.unstable.slice(0, 12).join(' ') + (M.unstable.length > 12 ? ' …' : '') : '—'}`],
    [T('里程表 Σ v = k · 已到 u 的格子 · max (u − v)', 'Odometer Σ v = k · cells at u · max (u − v)'), `${M.v.reduce((s, x) => s + x, 0)} · ${M.atTarget} / ${M.n - 1} · ${+M.maxDef.toFixed(1)}`],
    [T('T(n,1)（这一顺序）· A023855(n − 1) · 印出的 A023855(n)', 'T(n,1) (this order) · A023855(n − 1) · printed A023855(n)'), `${M.T} · ${M.a}${M.T === M.a ? ' ✓' : ' ✗'} · ${M.printed}${M.printed === M.T ? ' ✓' : ' ✗'}`],
    [T('沙粒：环上 · 落入汇点', 'Grains: on the ring · lost into the sink'), `${grains} · ${M.lost}  (${T('共', 'total')} 4(n − 1) = ${4 * (M.n - 1)})`]]);
  $('roNote').innerHTML = M.k < M.T
    ? T(`还有 ${M.unstable.length} 个格子不稳定。Lean 保证：无论接下来怎样选，到终态时总数都是 ${M.a}。`, `${M.unstable.length} cells are still unstable. Lean guarantees that however the next cells are chosen, the total at the final state is ${M.a}.`)
    : T(`终态：每格至多 3 粒${M.n % 2 === 0 ? `（x = ${M.n / 2} 只有 2 粒）` : ''}，共推倒 ${M.T} = A023855(${M.n - 1}) 次，每个格子都恰好推倒 u(x) 次。`, `Final state: at most 3 grains per cell${M.n % 2 === 0 ? ` (2 at x = ${M.n / 2})` : ''}, ${M.T} = A023855(${M.n - 1}) topplings, every cell toppled exactly u(x) times.`);
}
const stateKey = () => `${S.n}|${S.order}|${S.seed}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; }
  const M = MODEL;
  if (!toasted && S.playing && M.k >= M.T) { toasted = true; toast(T(`<b>k = ${M.T}</b>：终态。${M.T} = A023855(${M.n - 1})，与顺序无关。`, `<b>k = ${M.T}</b>: final state. ${M.T} = A023855(${M.n - 1}), whatever the order.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('nIn').value = String(S.n); $('nOut').textContent = String(S.n);
  document.querySelectorAll('#orderChips [data-order]').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.order === S.order)));
  $('reseed').disabled = S.order !== 'random';
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T(`n × 1 环面上，格子 x 的四个邻居是 x ± 1 与它自己两次，所以推倒一次留下 2 粒、各送 1 粒给左右；送进 c[0,0] 的沙粒丢失。`, `On the n × 1 torus the four neighbours of cell x are x ± 1 and the cell itself twice, so a toppling keeps 2 grains and sends 1 to each side; grains sent to c[0,0] are lost.`);
  $('litNote').innerHTML = T('Lean 证明的是所有 n ≥ 2 与所有合法顺序；具体的顺序、步数图与 n ≤ 80 的整列是页面模拟。', 'Lean proves every n ≥ 2 and every legal order; the particular orders, the step-by-step pictures and the column up to n = 80 are page simulations.');
  $('c1Title').textContent = T('每个格子被推倒的次数 v(x) 与 u(x)', 'Topplings per cell v(x) against u(x)');
  $('c2Title').textContent = T('第一列 T(n,1)，对数刻度', 'The first column T(n,1), log scale');
  $('clock').innerHTML = `k = ${M.k}`;
  $('hudBig').textContent = `n = ${M.n} · k = ${M.k} / ${M.T} = A023855(${M.n - 1})`;
  $('hudSub').textContent = T('外圈是 n 个格子，每一粒沙是一个点：青色稳定、琥珀色不稳定（≥ 4 粒）、品红是下一个被推倒的格子；前方的品红圈是汇点 c[0,0]。里圈的柱子是每个格子已推倒的次数 v(x)，琥珀短线是终点 u(x)', 'The outer ring holds the n cells, one dot per grain: cyan stable, amber unstable (≥ 4 grains), magenta the next cell to topple; the magenta circle in front is the sink c[0,0]. The inner bars count the topplings v(x) of each cell so far, and the amber ticks mark the end values u(x)');
}
function syncRail() {
  const M = MODEL, key = `${M.T}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 'k = 0'], [0.5, `k = ${Math.round(M.T / 2)}`], [1, `k = ${M.T}`]];
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { n: p.n, order: p.order, seed: 1, t: 0, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('nIn').addEventListener('input', () => { S.n = parseInt($('nIn').value, 10); custom(); });
document.querySelectorAll('#orderChips [data-order]').forEach((b) => b.addEventListener('click', () => { S.order = b.dataset.order; custom(); }));
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); const Tn = MODEL.T; jumpTo((MODEL.k + (ev.key === 'ArrowRight' ? 1 : -1)) / Tn); }
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
/* a run lasts 0.12 s per toppling at 1×, between 6 and 20 seconds */
const runSeconds = (Tn) => Math.min(20, Math.max(6, 0.12 * Tn));
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
window.SP_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { n: M.n, order: M.order, seed: M.seed, T: M.T, k: M.k, c: [...M.c], v: [...M.v], lost: M.lost, u: M.u.slice(), unstable: M.unstable.slice(), atTarget: M.atTarget, maxDef: M.maxDef,
    last: M.last, next: M.next, a: M.a, printed: M.printed, maxPile: M.maxPile, final: [...M.final], finalV: [...M.finalV], finalLost: M.finalLost }; },
  seq: () => [...RUN.seq],
  sequence: (n, order, seed) => [...simulate(n, order, seed || 1).seq],
  column: (order, seed) => columnOf(order, seed || 1).slice(),
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setT(0.42); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 7.8; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
