/* YB//AUTOMATON · Yang–Baxter cellular automata over a field of order 2ⁿ
   Araoka and Tokihiro (2026) run the R-matrix R(x, y) = (y + f(x + y), x − f(x + y)) along a row of N cells with a helical
   boundary and conjecture that, over a field of order q = 2ⁿ and for a bijective f solving the reduced Yang–Baxter equation
   f(x) + f(x + f(y)) = f(x + f(y + f(x))), the period divides q. Proved in trureturing
   (YangBaxterAutomatonPeriod.result): step^q = id for every such field, f and N. Only the additive group is used, so the
   field elements are n-bit numbers added by XOR.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. The automaton, the solutions and the periods
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.5, 0.58, 0.68], WHITE = [0.92, 0.95, 1];
const HMAX = 65536, SAMPLE = 4096, NMAX = 12;
const hexs = '0123456789abcdef';
const dec = (s) => [...s].map((c) => parseInt(c, 16));
const show = (f) => f.map((v) => hexs[v]).join('');
/* eight bijective solutions for q = 16, found offline by randomized backtracking (the first three have a state of period 16) */
const Q16 = ['a869bfce2d315740', '764d3251fec8ba09', '30167a52bc94f8de', 'eba96f8d034127c5', 'f37bc048d15e926a', '3af6105cb27e98d4', '9423d06718ab5cef', '01235476ab89fedc'].map(dec);
/* a bijection of F_8 that violates the equation, for contrast */
const BROKEN = [4, 2, 5, 0, 7, 6, 3, 1];
const fybViolations = (f, q) => { let v = 0; for (let x = 0; x < q; x++) for (let y = 0; y < q; y++) if ((f[x] ^ f[x ^ f[y]]) !== f[x ^ f[y ^ f[x]]]) v++; return v; };
/* all bijective solutions for q = 4 and 8, by running through the permutations in lexicographic order */
function solutions(q) {
  const out = [], p = Array.from({ length: q }, (_, i) => i), used = new Array(q).fill(false), cur = [];
  (function rec() {
    if (cur.length === q) { if (fybViolations(cur, q) === 0) out.push(cur.slice()); return; }
    for (const v of p) if (!used[v]) { used[v] = true; cur.push(v); rec(); cur.pop(); used[v] = false; }
  })();
  return out;
}
const SOLS = {};
const sols = (q) => SOLS[q] || (SOLS[q] = q === 16 ? Q16 : solutions(q));
/* one step: the auxiliary value y starts at the boundary b; at each cell (x, y) ↦ (y + f(x + y), x + f(x + y)) */
function step(f, xs, b) { const out = new Array(xs.length); let y = b; for (let i = 0; i < xs.length; i++) { const s = f[xs[i] ^ y]; out[i] = y ^ s; y = xs[i] ^ s; } return [out, y]; }
function period(f, xs, b, cap = 100000) { let a = xs, c = b; for (let k = 1; k <= cap; k++) { [a, c] = step(f, a, c); if (c === b && a.every((v, i) => v === xs[i])) return k; } return Infinity; }
const translations = (f, q) => { const u = []; for (let t = 1; t < q; t++) { let ok = true; for (let x = 0; x < q && ok; x++) if (f[x ^ t] !== (f[x] ^ t)) ok = false; if (ok) u.push(t); } return u; };
const isAdditive = (f, q) => { for (let a = 0; a < q; a++) for (let b = 0; b < q; b++) if (f[a ^ b] !== (f[a] ^ f[b])) return false; return true; };
/* the period of every initial state (or of SAMPLE seeded ones): counts by period */
function histogram(f, q, N, seed) {
  const total = q ** (N + 1), counts = new Map(); let n = 0;
  const add = (xs, b) => { const p = period(f, xs, b); counts.set(p, (counts.get(p) || 0) + 1); n++; };
  if (total <= HMAX) { for (let code = 0; code < total; code++) { let c = code; const xs = []; for (let i = 0; i < N; i++) { xs.push(c % q); c = Math.floor(c / q); } add(xs, c % q); } }
  else { const rnd = TRV.mulberry32(seed * 7919 + 17); for (let s = 0; s < SAMPLE; s++) { const xs = Array.from({ length: N }, () => Math.floor(rnd() * q)); add(xs, Math.floor(rnd() * q)); } }
  return { counts, n, exhaustive: total <= HMAX, total };
}
function initialState(q, N, seed) { const rnd = TRV.mulberry32(seed * 104729 + q * 31 + N); return [Array.from({ length: N }, () => Math.floor(rnd() * q)), Math.floor(rnd() * q)]; }

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { q: 16, fi: 0, N: 2, seed: 1, init: null, broken: false, t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { q: 16, fi: 0, N: 2, init: [[12, 3], 5], broken: false, play: true,
    zh: 'q = 16：一个离线找到的非加法解 f，两个格子，初态 (12, 3)、边界 5。它的周期正好是 16 = q——达到了定理允许的上限；这个 f 的全部 16³ = 4096 个初态周期都是 16（页面穷举）。Lean 对所有 2ⁿ 与所有 N 证明 step^q = id。',
    en: 'q = 16: a non-additive solution f found offline, two cells, initial state (12, 3) with boundary 5. Its period is exactly 16 = q — the most the theorem allows; all 16³ = 4096 initial states of this f have period 16 (page enumeration). Lean proves step^q = id for every 2ⁿ and every N.' },
  even: { q: 8, fi: 'f8', N: 4, init: null, broken: false, play: true,
    zh: 'q = 8、N = 4：这个 f 的 8⁵ = 32768 个初态全部周期为 8（页面穷举）。8 是 q，Lean 保证不会更长，也不会出现别的周期。',
    en: 'q = 8, N = 4: all 8⁵ = 32768 initial states of this f have period 8 (page enumeration). 8 is q; Lean guarantees nothing longer and no other period.' },
  odd: { q: 8, fi: 'f8', N: 3, init: null, broken: false, play: true,
    zh: '同一个 f，N = 3：全部 8⁴ = 4096 个初态的周期只有 2 与 4（页面穷举）。周期仍然整除 8，只是到不了 8——格子数的奇偶会影响周期分布，这一点定理没有说。',
    en: 'The same f with N = 3: all 8⁴ = 4096 initial states have period 2 or 4 (page enumeration). The periods still divide 8 but never reach it — the parity of N changes the distribution, which the theorem does not address.' },
  four: { q: 4, fi: 6, N: 6, init: null, broken: false, play: true,
    zh: 'q = 4：原文已经证明的情形。页面在 24 个排列里找到 16 个满足方程的双射；这里取编号 6 的 f = 1230，N = 6 时 4⁷ = 16384 个初态的周期全是 4（页面穷举）。',
    en: 'q = 4: the case the paper already proves. Of the 24 permutations, 16 bijections solve the equation; with f = 1230 (number 6) and N = 6, all 4⁷ = 16384 initial states have period 4 (page enumeration).' },
  linear: { q: 16, fi: 7, N: 6, init: null, broken: false, play: true,
    zh: '加法的对合 f（f(a + b) = f(a) + f(b)，f∘f = id）：自动机是线性的。抽样的 4096 个初态周期都是 2；全零的状态不动，周期为 1。页面数值。',
    en: 'An additive involution f (f(a + b) = f(a) + f(b), f∘f = id): the automaton is linear. All 4096 sampled initial states have period 2; the all-zero state is fixed, with period 1. Page numbers.' },
  broken: { q: 8, fi: 0, N: 2, init: null, broken: true, play: true,
    zh: '对照：f = 42507631 是双射，但有 44 对 (x, y) 不满足方程。R 对任何 f 都可逆，所以自动机仍有周期，可 N = 2 时 512 个初态的周期全是 6 或 10，都不整除 8（页面穷举）。方程不能少。',
    en: 'A contrast: f = 42507631 is a bijection, but 44 pairs (x, y) violate the equation. R is invertible for any f, so the automaton is still periodic, yet for N = 2 all 512 initial states have period 6 or 10, neither dividing 8 (page enumeration). The equation cannot be dropped.' }
};
const F8 = [7, 6, 5, 4, 2, 1, 0, 3];
let MODEL = null, HIST = null, dirty = true, modelId = 0;
function build() {
  const q = S.q, list = sols(q), f = S.broken ? BROKEN : list[Math.min(S.fi, list.length - 1)];
  const [xs, b] = S.init ? [S.init[0].slice(0, S.N).concat(Array(Math.max(0, S.N - S.init[0].length)).fill(0)), S.init[1]] : initialState(q, S.N, S.seed);
  const p = period(f, xs, b), T2 = Math.min(64, 2 * q), rows = [[xs, b]];
  for (let k = 0; k < T2; k++) { const [a, c] = step(f, rows[k][0], rows[k][1]); rows.push([a, c]); }
  const hkey = `${q}|${show(f)}|${S.N}|${S.seed}`;
  if (!HIST || HIST.key !== hkey) HIST = { key: hkey, ...histogram(f, q, S.N, S.seed) };
  const tk = Math.min(T2, Math.round(S.t * T2));
  MODEL = { id: ++modelId, q, f, fi: S.broken ? null : list.indexOf(f), count: list.length, xs, b, N: S.N, p, rows, T2, tk, H: HIST,
    U: translations(f, q), additive: isAdditive(f, q), viol: fybViolations(f, q), broken: S.broken };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
/* q colours around the hue circle */
const hue = (v, q) => { const h = v / q, k = (n) => (n + h * 12) % 12, a = 0.85, l = 0.58; return [0, 8, 4].map((n) => l - a * Math.min(l, 1 - l) * Math.max(-1, Math.min(k(n) - 3, 9 - k(n), 1))); };
const css = (c) => `rgb(${c.map((x) => Math.round(255 * x)).join(',')})`;

/* =====================================================================
   4. 3D scene: the space-time helix, one turn per time step
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 12000, PTS_MAX = 1400;
const CAMS = { iso: [0.6, 1.2, 10.5], front: [0.0001, 1.5708, 10], top: [0.0001, 0.06, 10] };
const cam = { theta: 0.6, phi: 1.2, r: 10.5, tTheta: 0.6, tPhi: 1.2, tR: 10.5 };
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
const HR = 2.2, HH = 5.2;
const helixAt = (M, g) => { const a = 2 * Math.PI * g / (M.N + 1); return [HR * Math.cos(a), -HH / 2 + HH * g / ((M.T2 + 1) * (M.N + 1)), HR * Math.sin(a)]; };
const helixPos = (M, t, k) => helixAt(M, t * (M.N + 1) + k);
const same = (r, M) => r[1] === M.b && r[0].every((v, i) => v === M.xs[i]);
function updateGL() {
  const M = MODEL;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = c[0]; PT.aColor.array[3 * np + 1] = c[1]; PT.aColor.array[3 * np + 2] = c[2]; PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const ring = (t, c, k, r = HR + 0.28) => { const y = helixPos(M, t, 0)[1] + HH / ((M.T2 + 1) * 2); for (let s = 0; s < 64; s++) { const a0 = 2 * Math.PI * s / 64, a1 = 2 * Math.PI * (s + 1) / 64; seg([r * Math.cos(a0), y, r * Math.sin(a0)], [r * Math.cos(a1), y, r * Math.sin(a1)], c, k); } };
  M.rows.forEach((row, t) => {
    const vals = [...row[0], row[1]], now = t === M.tk, past = t <= M.tk;
    vals.forEach((val, k) => {
      const p = helixPos(M, t, k);
      /* the helix itself, drawn as arcs between consecutive points */
      if (t + k > 0) { const g = t * (M.N + 1) + k; for (let s = 0; s < 6; s++) seg(helixAt(M, g - 1 + s / 6), helixAt(M, g - 1 + (s + 1) / 6), GREY, past ? 0.35 : 0.14); }
      dot(p, hue(val, M.q), past ? (now ? 1 : 0.9) : 0.45, now ? 2.2 : k === M.N ? 1.7 : 1.4);
    });
    if (t > 0 && same(row, M)) ring(t, WHITE, 0.55);
  });
  ring(0, WHITE, 0.55); ring(M.tk, COL.cyan, 0.9, HR + 0.45);
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
function updateTags() {
  const M = MODEL; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  const side = (t) => { const p = helixPos(M, t, 0); return [HR + 0.9, p[1], 0]; };
  put('t = 0', side(0), 't');
  M.rows.forEach((row, t) => { if (t > 0 && same(row, M)) put(T(`t = ${t} = 初态`, `t = ${t} = start`), side(t), 'p'); });
  put(`t = ${M.tk}`, [-HR - 0.9, helixPos(M, M.tk, 0)[1], 0], 'cy');
  put('b', helixPos(M, M.tk, M.N).map((x, i) => (i === 1 ? x + 0.25 : x * 1.12)), 't');
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
/* the space-time diagram: one row per time step, the N cells, a gap, then the boundary value */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 40); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, cols = M.N + 2, rows = M.T2 + 1;
  const cw = Math.min(iw / cols, 48 * dpr), rh = ih / rows, x0 = pl + (iw - cw * cols) / 2;
  M.rows.forEach((row, t) => {
    const vals = [...row[0], null, row[1]];
    vals.forEach((val, k) => { if (val === null) return; ctx.fillStyle = css(hue(val, M.q)); ctx.globalAlpha = t <= M.tk ? 1 : 0.35; ctx.fillRect(x0 + k * cw + 1, pt + t * rh + 0.5, cw - 2, Math.max(1, rh - 1)); });
    ctx.globalAlpha = 1;
    if (t > 0 && same(row, M)) { ctx.strokeStyle = INK; ctx.lineWidth = 1.5 * dpr; ctx.strokeRect(x0 - 2 * dpr, pt + t * rh, cw * cols + 4 * dpr, rh); lab(ctx, `t = ${t}`, x0 - 6 * dpr, pt + (t + 0.5) * rh, 'right', 'middle', INK); }
  });
  ctx.strokeStyle = CY; ctx.lineWidth = 1.2 * dpr; ctx.strokeRect(x0 - 1, pt + M.tk * rh - 1, cw * cols + 2, rh + 2);
  lab(ctx, 't = 0', x0 - 6 * dpr, pt + rh / 2, 'right', 'middle');
  lab(ctx, T('格子 1 … N', 'cells 1 … N'), x0 + cw * M.N / 2, pt + ih + 4 * dpr, 'center', 'top'); lab(ctx, 'b', x0 + cw * (M.N + 1.5), pt + ih + 4 * dpr, 'center', 'top');
  $('c1Meta').innerHTML = `<span class="it">${T(`颜色 = F_${M.q} 的元素`, `colour = element of F_${M.q}`)}</span><span class="it"><i class="sw" style="--c:${INK}"></i>${T('回到初态', 'back to the start')}</span>`;
}
/* the periods of all (or sampled) initial states: divisors of q in cyan, anything else in magenta */
function drawSide() {
  const M = MODEL, H = M.H, F2 = frame2d(cv2, 40); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, cats = []; for (let d = 1; d <= M.q; d *= 2) cats.push(d);
  [...H.counts.keys()].filter((p) => !cats.includes(p)).sort((a, b) => a - b).forEach((p) => cats.push(p));
  const bw = iw / cats.length, mx = Math.max(...H.counts.values()), Y = (c) => pt + ih - ih * c / mx;
  cats.forEach((p, i) => {
    const c = H.counts.get(p) || 0, x = pl + i * bw + bw * 0.18, w = bw * 0.64, div = M.q % p === 0;
    ctx.fillStyle = div ? 'rgba(25,240,255,0.75)' : 'rgba(255,47,208,0.8)'; ctx.fillRect(x, Y(c), w, pt + ih - Y(c));
    lab(ctx, String(c), x + w / 2, Y(c) - 2 * dpr, 'center', 'bottom', c ? INK : DIM); lab(ctx, `p = ${p}`, x + w / 2, pt + ih + 4 * dpr, 'center', 'top', p === M.p ? AM : DIM);
  });
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('p 整除 q', 'p divides q')}</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('不整除', 'does not divide')}</span><span class="it">· ${H.exhaustive ? T(`全部 ${H.n} 个初态`, `all ${H.n} initial states`) : T(`抽样 ${H.n} 个初态`, `${H.n} sampled initial states`)}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const nbits = (q) => Math.round(Math.log2(q));
function readouts() {
  const M = MODEL, H = M.H, divides = M.q % M.p === 0, row = M.rows[M.tk];
  pill('pillA', 'q', String(M.q)); pill('pillB', 'N', String(M.N)); pill('pillC', 'p', `${M.p}${divides ? ' | q' : ' ∤ q'}`); pill('pillD', 'FYB', M.viol ? '✗' : '✓');
  const periods = [...H.counts.keys()].sort((a, b) => a - b);
  setRo([
    [T(`F_${M.q} 的加法：${nbits(M.q)} 位二进制按位异或 · 满足方程的双射`, `Addition in F_${M.q}: ${nbits(M.q)}-bit XOR · bijections solving the equation`), M.q === 16 ? T('页面内嵌 8 个（f(0) = 0 的解共 16816 个，离线计数）', '8 embedded (16816 with f(0) = 0, offline count)') : T(`全部 ${M.count} 个（页面枚举 ${M.q}! 个排列）`, `all ${M.count} (page enumeration of ${M.q}! permutations)`)],
    [T('f（第 x 位是 f(x)，十六进制）· 平移 u：f(x + u) = f(x) + u · 加法的？· 违反方程的 (x, y) 对数', 'f (the x-th digit is f(x), hex) · translations u with f(x + u) = f(x) + u · additive? · pairs (x, y) violating the equation'), `${show(M.f)} · {${M.U.map((u) => hexs[u]).join(', ')}} · ${M.additive ? T('是', 'yes') : T('否', 'no')} · ${M.viol}`],
    [T('初态 (x₁ … x_N; b) · 周期 p', 'Initial state (x₁ … x_N; b) · period p'), `(${M.xs.map((v) => hexs[v]).join(' ')}; ${hexs[M.b]}) · p = ${M.p} ${divides ? T(`整除 ${M.q}`, `divides ${M.q}`) : T(`不整除 ${M.q}`, `does not divide ${M.q}`)}`],
    [H.exhaustive ? T(`全部 ${M.q}^${M.N + 1} = ${H.n} 个初态的周期`, `Periods of all ${M.q}^${M.N + 1} = ${H.n} initial states`) : T(`${H.n} 个抽样初态的周期`, `Periods of ${H.n} sampled initial states`), periods.map((p) => `${p}: ${H.counts.get(p)}`).join(' · ')],
    [T(`第 t = ${M.tk} 步的状态`, `State at step t = ${M.tk}`), `(${row[0].map((v) => hexs[v]).join(' ')}; ${hexs[row[1]]})${M.tk > 0 && same(row, M) ? T(' = 初态', ' = start') : ''}`]]);
  $('roNote').innerHTML = M.viol ? T(`这个 f 不满足方程（${M.viol} 对 (x, y) 违反），定理不适用：周期 ${periods.filter((p) => M.q % p).join('、')} 不整除 ${M.q}。`, `This f does not solve the equation (${M.viol} pairs (x, y) violate it), so the theorem does not apply: the periods ${periods.filter((p) => M.q % p).join(', ')} do not divide ${M.q}.`)
    : T(`f 满足方程且是双射：Lean 证明 step^${M.q} = id，所以每个周期都整除 ${M.q}。这里看到的周期：${periods.join('、')}。`, `f is a bijective solution: Lean proves step^${M.q} = id, so every period divides ${M.q}. Periods seen here: ${periods.join(', ')}.`);
}
const stateKey = () => `${S.q}|${S.fi}|${S.N}|${S.seed}|${S.broken}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; }
  const M = MODEL;
  if (!toasted && S.playing && M.tk >= M.p && M.p <= M.T2) { toasted = true; toast(T(`<b>t = ${M.p}</b>：回到初态。周期 ${M.p}${M.q % M.p === 0 ? `，整除 q = ${M.q}` : `，不整除 q = ${M.q}`}。`, `<b>t = ${M.p}</b>: back to the initial state. Period ${M.p}${M.q % M.p === 0 ? `, dividing q = ${M.q}` : `, not dividing q = ${M.q}`}.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  document.querySelectorAll('#qChips [data-q]').forEach((b) => b.setAttribute('aria-pressed', String(Number(b.dataset.q) === S.q && !S.broken)));
  $('fIn').max = String(sols(S.q).length - 1); $('fIn').value = String(S.fi); $('fOut').textContent = S.broken ? '—' : String(S.fi); $('fIn').disabled = S.broken;
  $('nIn').value = String(S.N); $('nOut').textContent = String(S.N);
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T(`时间轴走 ${M.T2} 步（两倍的 q，至多 64）。`, `The time rail runs ${M.T2} steps (twice q, at most 64).`);
  $('litNote').innerHTML = T('Lean 证明的是所有 2ⁿ 与所有 N；具体的 f、初态与周期分布是页面数值。', 'Lean proves every 2ⁿ and every N; the particular maps, initial states and period counts are page numbers.');
  $('c1Title').textContent = T('时空图：每行一个时间步', 'Space-time diagram: one row per time step');
  $('c2Title').textContent = T('初态的周期分布', 'Periods of the initial states');
  $('clock').innerHTML = `t = ${M.tk}`;
  $('hudBig').textContent = `q = ${M.q} · N = ${M.N} · t = ${M.tk} · p = ${M.p}${M.q % M.p === 0 ? ` | ${M.q}` : ` ∤ ${M.q}`}`;
  $('hudSub').textContent = T('螺旋的每一圈是一个时间步，圈上依次是 N 个格子与边界值 b，颜色是元素的值；白环是回到初态的时刻，青环是当前一步', 'Each turn of the helix is one time step, carrying the N cells and then the boundary b, coloured by value; white rings mark returns to the initial state and the cyan ring the current step');
}
function syncRail() {
  const M = MODEL, key = `${M.T2}|${M.p}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 't = 0']]; if (M.p < M.T2) marks.push([M.p / M.T2, `p = ${M.p}`]); marks.push([1, `t = ${M.T2}`]);
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  const fi = p.fi === 'f8' ? sols(8).findIndex((f) => show(f) === show(F8)) : p.fi;
  Object.assign(S, { q: p.q, fi, N: p.N, init: p.init, broken: p.broken, seed: 1, t: 0, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; S.init = null; markPreset(); dirty = true; toasted = false; };
document.querySelectorAll('#qChips [data-q]').forEach((b) => b.addEventListener('click', () => { S.q = Number(b.dataset.q); S.fi = 0; S.broken = false; custom(); }));
$('fIn').addEventListener('input', () => { S.fi = parseInt($('fIn').value, 10); custom(); });
$('nIn').addEventListener('input', () => { S.N = parseInt($('nIn').value, 10); custom(); });
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); const T2 = MODEL.T2; jumpTo((MODEL.tk + (ev.key === 'ArrowRight' ? 1 : -1)) / T2); }
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
/* one time step takes STEP seconds at 1× */
const STEP = 0.45;
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : 1); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed / (STEP * MODEL.T2));
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
window.YB_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { q: M.q, f: M.f.slice(), fi: M.fi, count: M.count, N: M.N, xs: M.xs.slice(), b: M.b, p: M.p, T2: M.T2, tk: M.tk, rows: M.rows.map((r) => [r[0].slice(), r[1]]), U: M.U.slice(), additive: M.additive, viol: M.viol, broken: M.broken,
    hist: { counts: [...M.H.counts.entries()].sort((a, b) => a[0] - b[0]), n: M.H.n, exhaustive: M.H.exhaustive } }; },
  solutions: (q) => sols(q).map(show),
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setT(0.5); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 9.5; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
