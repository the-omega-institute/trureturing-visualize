/* ZECKENDORF//CHAIN · OEIS A370630, the greedy chain whose neighbours share exactly one Zeckendorf term
   a(1) = 1 and a(n+1) is the least unused positive integer whose Zeckendorf expansion shares exactly one Fibonacci term with
   that of a(n). Frozen in trureturing (ZeckendorfGreedyPermutation.result): the chain never stops, never repeats and visits
   every positive integer. The page computes the chain, weaves its digits in 3D with the shared term of each step, and tracks
   the smallest number not yet seen; two neighbouring rules (A370631, A226077) are numerical comparisons only.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Constants
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.55, 0.6, 0.68];
const RULES = ['one', 'atleast', 'binary'], NMAXES = [300, 3000, 30000], RUN = 24, WIN = 100;
/* the data of the OEIS record A370630 (revision 16), used to confirm the computation */
const OEIS = [1, 4, 3, 11, 8, 9, 6, 5, 7, 2, 10, 12, 14, 13, 15, 16, 18, 17, 20, 23, 21, 22, 19, 25, 26, 24, 27, 29, 28, 30, 35, 33, 37, 32, 38, 34, 36, 31, 41, 42, 39, 43, 47, 40, 44, 48, 45, 49, 46, 52, 60, 53, 56, 51, 58, 50, 59, 55, 57, 54, 61, 63, 62, 64, 68, 65, 69];
const FIB = (() => { const f = [0, 1]; while (f.length < 46) f.push(f[f.length - 1] + f[f.length - 2]); return f; })();

/* =====================================================================
   2. Digits and the greedy chain
   ===================================================================== */
/* Zeckendorf digits as a bit mask: bit k − 2 stands for F(k), k ≥ 2, taken greedily from the largest Fibonacci number */
function zeckMask(m) { let mask = 0; for (let k = 44; k >= 2 && m > 0; k--) if (FIB[k] <= m) { m -= FIB[k]; mask |= 1 << (k - 2); k--; } return mask >>> 0; }
const popcount = (x) => { x = x - ((x >>> 1) & 0x55555555); x = (x & 0x33333333) + ((x >>> 2) & 0x33333333); return (((x + (x >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24; };
const top = (x) => 31 - Math.clz32(x);
const RULE = {
  one: { digits: zeckMask, ok: (c) => popcount(c) === 1, base: 2 },
  atleast: { digits: zeckMask, ok: (c) => c !== 0, base: 2 },
  binary: { digits: (m) => m >>> 0, ok: (c) => popcount(c) === 1, base: 0 }
};
/* the chain itself: the least unused m whose digits meet the rule against the previous term */
function chain(rule, nmax) {
  const R = RULE[rule]; let cap = 4 * nmax + 64;
  let seen = new Uint8Array(cap), dig = new Int32Array(cap);
  const grow = (m) => { while (m >= cap) { const c2 = cap * 2, s2 = new Uint8Array(c2), d2 = new Int32Array(c2); s2.set(seen); d2.set(dig); for (let q = cap; q < c2; q++) d2[q] = R.digits(q); seen = s2; dig = d2; cap = c2; } };
  for (let m = 1; m < cap; m++) dig[m] = R.digits(m);
  const a = new Int32Array(nmax + 1), shared = new Int32Array(nmax + 1), mstar = new Int32Array(nmax + 1), maxSoFar = new Int32Array(nmax + 1);
  a[1] = 1; seen[1] = 1; let low = 1, mx = 1;
  while (seen[low]) low++;
  mstar[1] = low; maxSoFar[1] = 1;
  for (let n = 1; n < nmax; n++) {
    const z = dig[a[n]]; let m = low;
    for (;; m++) { grow(m + 1); if (!seen[m] && R.ok(z & dig[m])) break; }
    a[n + 1] = m; seen[m] = 1; shared[n + 1] = z & dig[m];
    while (seen[low]) { low++; grow(low + 1); }
    mstar[n + 1] = low; mx = Math.max(mx, m); maxSoFar[n + 1] = mx;
  }
  const tau = new Map(); for (let n = 1; n <= nmax; n++) tau.set(a[n], n);
  let waitM = 1, wait = 0; for (let m = 1; m < mstar[nmax]; m++) { const w = tau.get(m) - m; if (w > wait) { wait = w; waitM = m; } }
  let maxDisp = 0, dispN = 1; for (let n = 1; n <= nmax; n++) if (Math.abs(a[n] - n) > maxDisp) { maxDisp = Math.abs(a[n] - n); dispN = n; }
  let lead = 0; for (let n = 2; n <= nmax; n++) { const c = shared[n], t = top(c); if (c && t === top(dig[a[n - 1]]) && t === top(dig[a[n]])) lead++; }
  const digitsOf = (m) => { grow(m + 1); return dig[m]; };
  return { rule, nmax, a, shared, mstar, maxSoFar, tau, waitM, wait, maxDisp, dispN, lead: lead / Math.max(1, nmax - 1), digitsOf };
}

/* =====================================================================
   3. State and presets
   ===================================================================== */
const S = { rule: 'one', nmax: 300, nowFrac: 0, playing: true, dir: 1, speed: 1, hold: 0, preset: 'start' };
const PRESETS = {
  start: { rule: 'one', nmax: 300, n: 1, play: true,
    zh: '链的开头：1 = F(2)，4 = F(4) + F(2)，3 = F(4)，11 = F(6) + F(4)，8 = F(6)，9 = F(6) + F(2)，… 每一步琥珀线连起的就是相邻两项共享的那一项。前 67 项与 OEIS 记录的数据逐项相同。',
    en: 'The start of the chain: 1 = F(2), 4 = F(4) + F(2), 3 = F(4), 11 = F(6) + F(4), 8 = F(6), 9 = F(6) + F(2), … At every step the amber line joins the term shared by the two neighbours. The first 67 terms agree with the data of the OEIS record term by term.' },
  two: { rule: 'one', nmax: 300, n: 10, play: false,
    zh: '2 = F(3) 要等到第 10 步：前面的项 1, 4, 3, 11, 8, 9, 6, 5, 7 里，只有 7 = F(5) + F(3) 含 F(3)，它在第 9 步出现，于是第 10 步 2 才第一次合格并立刻被选中。',
    en: '2 = F(3) waits until step 10: among the earlier terms 1, 4, 3, 11, 8, 9, 6, 5, 7 only 7 = F(5) + F(3) contains F(3); it appears at step 9, so 2 becomes eligible for the first time at step 10 and is chosen at once.' },
  long: { rule: 'one', nmax: 30000, n: 1, play: true,
    zh: '前 30000 步。左下图里 a(n) − n 在零附近来回摆动：链偶尔向前跳，之后再回头补上漏掉的数。右下图是最小未出现数 m*(n)，冻结定理保证它趋于无穷。',
    en: 'The first 30000 steps. In the lower left chart a(n) − n swings around zero: the chain sometimes jumps ahead and later comes back for the numbers it skipped. The lower right chart is the smallest number not yet seen, m*(n), which the frozen theorem sends to infinity.' },
  wait: { rule: 'one', nmax: 30000, n: 'wait', play: false,
    zh: '在前 30000 步里等得最久的数：26073 直到第 29428 步才出现，比自己的大小晚了 3355 步。定理只保证它终会出现，不给等待时间的上界（OPEN）。',
    en: 'The number that waits longest within the first 30000 steps: 26073 only appears at step 29428, 3355 steps later than its own size. The theorem only guarantees that it appears eventually and gives no bound on the wait (OPEN).' },
  atleast: { rule: 'atleast', nmax: 3000, n: 1, play: true,
    zh: '把条件放宽为“至少一项相同”（A370631）。前 16 项与 A370630 相同，之后链几乎按顺序走过整数。OEIS 评注说它也是排列；本库没有核对这个陈述，这里只是数值对照。',
    en: 'Relax the condition to “at least one common term” (A370631). The first 16 terms agree with A370630, after which the chain walks the integers almost in order. The OEIS comment says it is a permutation too; this library has not checked that statement, so this is a numerical comparison only.' },
  binary: { rule: 'binary', nmax: 3000, n: 1, play: true,
    zh: '换成普通二进制、相邻两项恰有一个公共 1 位（A226077）。数字织锦里的纵深变成二进制位。OEIS 评注说它是排列；本库没有核对这个陈述，这里只是数值对照。',
    en: 'Switch to ordinary binary, with exactly one common 1-bit between neighbours (A226077). The depth of the digit weave becomes the binary bit position. The OEIS comment says it is a permutation; this library has not checked that statement, so this is a numerical comparison only.' }
};

/* =====================================================================
   4. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
const cache = new Map();
function build() {
  if (!RULES.includes(S.rule)) S.rule = 'one';
  if (!NMAXES.includes(S.nmax)) S.nmax = 300;
  const key = `${S.rule}|${S.nmax}`;
  if (!cache.has(key)) cache.set(key, chain(S.rule, S.nmax));
  MODEL = { id: ++modelId, ...cache.get(key) };
}
const fracOf = (n) => (n - 1) / Math.max(1, MODEL.nmax - 1);
function progress() {
  const M = MODEL, n = 1 + Math.round(S.nowFrac * (M.nmax - 1));
  return { n, a: M.a[n], digits: M.digitsOf(M.a[n]), shared: M.shared[n], mstar: M.mstar[n], max: M.maxSoFar[n] };
}
const kOf = (bitIndex) => bitIndex + RULE[MODEL.rule].base;
const termName = (k) => (MODEL.rule === 'binary' ? `2^${k}` : `F(${k})`);
const termValue = (k) => (MODEL.rule === 'binary' ? 2 ** k : FIB[k]);
function expansion(m) { const d = MODEL.digitsOf(m), out = []; for (let b = 31; b >= 0; b--) if (d >>> b & 1) out.push(kOf(b)); return out; }

/* =====================================================================
   5. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const fmt = (n) => n.toLocaleString('en-US');

/* =====================================================================
   6. 3D scene
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 12000, PTS_MAX = 3000;
const CAMS = { iso: [0.6, 1.0, 17], front: [0.0001, 1.5707, 16], top: [0.0001, 0.0601, 17] };
const cam = { theta: 0.6, phi: 1.0, r: 17, tTheta: 0.6, tPhi: 1.0, tR: 17 };
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
/* a window of WIN steps ending at the current step: step across, digit index in depth, the term's rank in the window as height */
function windowOf(pr) { const M = MODEL, i1 = pr.n, i0 = Math.max(1, i1 - WIN + 1); let kmax = 3, amin = Infinity, amax = -Infinity; for (let i = i0; i <= Math.min(M.nmax, i0 + WIN - 1); i++) { kmax = Math.max(kmax, kOf(top(M.digitsOf(M.a[i])))); amin = Math.min(amin, M.a[i]); amax = Math.max(amax, M.a[i]); } return { i0, i1, kmax, amin, amax }; }
const wx = (W, i) => -7 + 13 * (i - W.i0) / (WIN - 1);
const wz = (W, k) => { const k0 = RULE[MODEL.rule].base; return -4 + 8 * (k - k0) / Math.max(1, W.kmax - k0); };
const wy = (W, a) => 0.6 + 2.2 * (a - W.amin) / Math.max(1, W.amax - W.amin);
function updateGL() {
  const M = MODEL, pr = progress(), W = windowOf(pr);
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (a, b, col, k) => { if (v + 2 > LINES_MAX) return; for (const p of [a, b]) { Pp[3 * v] = p[0]; Pp[3 * v + 1] = p[1]; Pp[3 * v + 2] = p[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, a, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = a; PT.aSize.array[np] = size; np++; };
  const k0 = RULE[M.rule].base;
  for (let k = k0; k <= W.kmax; k++) seg([wx(W, W.i0), 0, wz(W, k)], [wx(W, W.i0 + WIN - 1), 0, wz(W, k)], GREY, 0.12);
  let prev = null;
  for (let i = W.i0; i <= W.i1; i++) {
    const d = M.digitsOf(M.a[i]), cur = i === W.i1;
    for (let b = 0; b < 32; b++) if (d >>> b & 1) dot([wx(W, i), 0, wz(W, kOf(b))], cur ? [1, 1, 1] : COL.cyan, cur ? 1 : 0.75, cur ? 1.8 : 1.1);
    if (i - 1 >= W.i0) { const c = M.shared[i]; for (let b = 0; b < 32; b++) if (c >>> b & 1) seg([wx(W, i - 1), 0, wz(W, kOf(b))], [wx(W, i), 0, wz(W, kOf(b))], COL.amber, 0.95); }
    const p = [wx(W, i), wy(W, M.a[i]), 0 - 4.6];
    if (prev) seg(prev, p, COL.magenta, 0.7);
    dot(p, cur ? COL.amber : COL.magenta, cur ? 1 : 0.6, cur ? 2 : 0.9);
    prev = p;
  }
  const xc = wx(W, W.i1);
  seg([xc, 0, -4.6], [xc, wy(W, pr.a), -4.6], COL.amber, 0.6);
  seg([xc, 0, -4.6], [xc, 0, wz(W, W.kmax)], [1, 1, 1], 0.25);
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
  cam.tTheta = cam.theta + d; cam.tPhi = p[1]; cam.tR = p[2];
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
  if (drag.pts.size === 2) { const [a, b] = [...drag.pts.values()], d = Math.hypot(a.x - b.x, a.y - b.y); if (drag.pinch > 0) cam.tR = Math.min(34, Math.max(7, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(34, Math.max(7, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

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
  const M = MODEL, pr = progress(), W = windowOf(pr); let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  const k0 = RULE[M.rule].base, step = Math.max(1, Math.ceil((W.kmax - k0) / 6));
  for (let kk = k0; kk <= W.kmax; kk += step) put(termName(kk), [wx(W, W.i0) - 0.7, 0, wz(W, kk)], 'cy');
  put(`a(${fmt(pr.n)}) = ${fmt(pr.a)}`, [wx(W, W.i1), wy(W, pr.a) + 0.45, -4.6], 'hot');
  put(`n = ${fmt(W.i0)}`, [wx(W, W.i0), -0.5, wz(W, W.kmax) + 0.5], 'cy');
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
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 46); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress();
  let lim = 1; for (let n = 1; n <= M.nmax; n++) lim = Math.max(lim, Math.abs(M.a[n] - n));
  const X = (n) => pl + iw * (n - 1) / Math.max(1, M.nmax - 1), Y = (d) => pt + ih / 2 - (ih / 2 - 2 * dpr) * d / lim;
  ctx.strokeStyle = FAINT; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
  const stride = Math.max(1, Math.floor(M.nmax / 6000));
  ctx.fillStyle = 'rgba(25,240,255,0.25)'; for (let n = 1; n <= M.nmax; n += stride) ctx.fillRect(X(n), Y(M.a[n] - n), 1.2 * dpr, 1.2 * dpr);
  ctx.fillStyle = CY; for (let n = 1; n <= pr.n; n += stride) ctx.fillRect(X(n), Y(M.a[n] - n), 1.6 * dpr, 1.6 * dpr);
  ctx.strokeStyle = AM; ctx.beginPath(); ctx.moveTo(X(pr.n), pt); ctx.lineTo(X(pr.n), pt + ih); ctx.stroke();
  lab(ctx, `+${fmt(lim)}`, pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, '0', pl - 4 * dpr, Y(0), 'right', 'middle'); lab(ctx, `−${fmt(lim)}`, pl - 4 * dpr, pt + ih, 'right', 'bottom');
  lab(ctx, 'n = 1', pl, pt + ih + 4 * dpr, 'left', 'top'); lab(ctx, `n = ${fmt(M.nmax)}`, pl + iw, pt + ih + 4 * dpr, 'right', 'top');
  $('c1Meta').textContent = T('每一步的 a(n) − n：亮青 = 已走过的步，暗青 = 之后的步；琥珀 = 当前步', 'a(n) − n at every step: bright cyan = steps taken, dim cyan = steps to come; amber = the current step');
}
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 46); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress();
  const top2 = M.maxSoFar[M.nmax], X = (n) => pl + iw * (n - 1) / Math.max(1, M.nmax - 1), Y = (v) => pt + ih - ih * v / top2;
  ctx.strokeStyle = FAINT; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(X(1), Y(1)); ctx.lineTo(X(M.nmax), Y(M.nmax)); ctx.stroke(); ctx.setLineDash([]);
  const stride = Math.max(1, Math.floor(M.nmax / 3000));
  for (const [arr, col] of [[M.maxSoFar, MG], [M.mstar, AM]]) { ctx.strokeStyle = col; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); for (let n = 1; n <= M.nmax; n += stride) { const x = X(n), y = Y(arr[n]); if (n === 1) ctx.moveTo(x, y); else ctx.lineTo(x, y); } ctx.stroke(); ctx.lineWidth = 1; }
  ctx.strokeStyle = INK; ctx.beginPath(); ctx.moveTo(X(pr.n), pt); ctx.lineTo(X(pr.n), pt + ih); ctx.stroke();
  lab(ctx, fmt(top2), pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, '1', pl - 4 * dpr, pt + ih, 'right', 'bottom');
  lab(ctx, 'n = 1', pl, pt + ih + 4 * dpr, 'left', 'top'); lab(ctx, `n = ${fmt(M.nmax)}`, pl + iw, pt + ih + 4 * dpr, 'right', 'top');
  $('c2Meta').textContent = T('琥珀 = 最小未出现数 m*(n)，品红 = 至今最大的项，灰虚线 = n；白 = 当前步', 'amber = the smallest number not yet seen m*(n), magenta = the largest term so far, grey dashes = n; white = the current step');
}

/* =====================================================================
   10. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const sum = (ks) => ks.map(termName).join(' + ');
function readouts() {
  const M = MODEL, pr = progress(), ks = expansion(pr.a), sh = []; for (let b = 31; b >= 0; b--) if (pr.shared >>> b & 1) sh.push(kOf(b));
  const oeisOK = M.rule === 'one' ? OEIS.every((v, j) => j + 1 > M.nmax || M.a[j + 1] === v) : null;
  setRo([[T('步数 n · 这一项 a(n)', 'Step n · term a(n)'), `n = ${fmt(pr.n)} · a(n) = ${fmt(pr.a)}`],
    [T('展开', 'Expansion'), `${fmt(pr.a)} = ${sum(ks)}`],
    [T('与上一项共享的项', 'Term shared with the previous one'), pr.n === 1 ? T('（第一项）', '(first term)') : `${sh.map((k) => `${termName(k)} = ${fmt(termValue(k))}`).join(' + ')} · ${sh.length} ${T('项', sh.length === 1 ? 'term' : 'terms')}`],
    [T('偏离对角线 a(n) − n · 至今最大的项', 'Distance a(n) − n · largest term so far'), `${pr.a - pr.n >= 0 ? '+' : '−'}${fmt(Math.abs(pr.a - pr.n))} · ${fmt(pr.max)}`],
    [T('最小未出现数 m*(n) · 它在第几步出现', 'Smallest unseen m*(n) · the step where it appears'), `${fmt(pr.mstar)} · ${M.tau.has(pr.mstar) ? fmt(M.tau.get(pr.mstar)) : T(`> ${fmt(M.nmax)}`, `> ${fmt(M.nmax)}`)}`]]);
  pill('pillA', 'n', fmt(pr.n)); pill('pillB', 'a(n)', fmt(pr.a)); pill('pillC', 'm*', fmt(pr.mstar)); pill('pillD', T('规则', 'RULE'), M.rule === 'one' ? 'A370630' : M.rule === 'atleast' ? 'A370631' : 'A226077');
  $('roNote').innerHTML = T(`前 ${fmt(M.nmax)} 步：|a(n) − n| 最大为 ${fmt(M.maxDisp)}（n = ${fmt(M.dispN)}）；在已出现的数里等得最久的是 ${fmt(M.waitM)}，晚了 ${fmt(M.wait)} 步；${(100 * M.lead).toFixed(1)}% 的相邻两项共享双方的最高项。${oeisOK === null ? '' : oeisOK ? `前 ${Math.min(67, M.nmax)} 项与 OEIS 记录的数据一致。` : '与 OEIS 记录的数据不一致！'}`,
    `First ${fmt(M.nmax)} steps: |a(n) − n| is at most ${fmt(M.maxDisp)} (n = ${fmt(M.dispN)}); among the numbers already seen the longest wait is ${fmt(M.waitM)}, ${fmt(M.wait)} steps late; ${(100 * M.lead).toFixed(1)}% of consecutive pairs share the leading term of both.${oeisOK === null ? '' : oeisOK ? ` The first ${Math.min(67, M.nmax)} terms agree with the data of the OEIS record.` : ' The terms disagree with the data of the OEIS record!'}`);
}
function syncControls() {
  const M = MODEL;
  document.querySelectorAll('#ruleChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.rule === M.rule)));
  document.querySelectorAll('#nChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.n === M.nmax)));
}
const stateKey = () => `${S.rule}|${S.nmax}|${S.nowFrac}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; toasted = false; syncControls(); $('marks').dataset.key = ''; }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  const M = MODEL, pr = progress();
  readouts();
  $('formula').innerHTML = M.rule === 'one' ? 'a(n+1) = min{ m ∉ {a(1), …, a(n)} : |Z(m) ∩ Z(a(n))| = 1 }' : M.rule === 'atleast' ? 'a(n+1) = min{ m ∉ {a(1), …, a(n)} : |Z(m) ∩ Z(a(n))| ≥ 1 }' : 'a(n+1) = min{ m ∉ {a(1), …, a(n)} : popcount(m AND a(n)) = 1 }';
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('modeNote').innerHTML = T(`时间轴 = 步数 n，从 1 到 ${fmt(M.nmax)}；三维视图显示当前步之前的 ${WIN} 步。${M.rule === 'one' ? '这是冻结定理所说的序列。' : '这条规则只是数值对照，不在冻结定理之内。'}`,
    `The time axis is the step n, from 1 to ${fmt(M.nmax)}; the 3D view shows the ${WIN} steps up to the current one. ${M.rule === 'one' ? 'This is the sequence of the frozen theorem.' : 'This rule is a numerical comparison only, outside the frozen theorem.'}`);
  $('litNote').innerHTML = T('链、展开和统计都由页面按定义算出；冻结的是 A370630 是正整数的排列。', 'The chain, the expansions and the statistics are computed on the page from the definition; what is frozen is that A370630 is a permutation of the positive integers.');
  $('c1Title').textContent = T('偏离对角线 a(n) − n', 'Distance from the diagonal a(n) − n');
  $('c2Title').textContent = T('最小未出现数与最大项', 'Smallest unseen number and largest term');
  $('clock').innerHTML = `n ${fmt(pr.n)}`;
  $('hudBig').textContent = `a(${fmt(pr.n)}) = ${fmt(pr.a)} = ${sum(expansion(pr.a))}`;
  $('hudSub').textContent = T(`横向 = 步数（最近 ${WIN} 步），纵深 = ${M.rule === 'binary' ? '二进制位' : 'Fibonacci 下标 k'}；青点 = 这一项展开里的项，琥珀线 = 与上一项共享的项；品红折线 = 各项在窗口里的大小；白 = 当前步`,
    `across = step (the last ${WIN}), depth = ${M.rule === 'binary' ? 'binary bit' : 'Fibonacci index k'}; cyan points = terms of each expansion, amber lines = the term shared with the previous step; magenta polyline = the size of each term within the window; white = the current step`);
  if (!toasted && S.playing && S.nowFrac >= 1) {
    toasted = true;
    toast(T(`<b>${fmt(M.nmax)} 步</b>：最小未出现数 ${fmt(M.mstar[M.nmax])}，至今最大的项 ${fmt(M.maxSoFar[M.nmax])}；|a(n) − n| 最大 ${fmt(M.maxDisp)}。`, `<b>${fmt(M.nmax)} steps</b>: smallest unseen number ${fmt(M.mstar[M.nmax])}, largest term so far ${fmt(M.maxSoFar[M.nmax])}; |a(n) − n| at most ${fmt(M.maxDisp)}.`));
  }
}
function syncRail() {
  const M = MODEL, key = `${M.id}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 'n = 1']];
  const tw = M.tau.get(M.waitM), fw = fracOf(tw);
  if (M.wait > 0 && fw > 0.12 && fw < 0.88) marks.push([fw, T(`最久的等待 ${fmt(M.waitM)}`, `longest wait ${fmt(M.waitM)}`)]);
  marks.push([1, `n = ${fmt(M.nmax)}`]);
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
function custom() { S.preset = null; markPreset(); dirty = true; }
document.querySelectorAll('#ruleChips .chip').forEach((b) => b.addEventListener('click', () => { S.rule = RULES.includes(b.dataset.rule) ? b.dataset.rule : 'one'; S.nowFrac = 0; $('now').value = 0; custom(); }));
document.querySelectorAll('#nChips .chip').forEach((b) => b.addEventListener('click', () => { const n = +b.dataset.n; S.nmax = NMAXES.includes(n) ? n : 300; S.nowFrac = 0; $('now').value = 0; custom(); }));
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.rule = p.rule; S.nmax = p.nmax; S.preset = name; markPreset();
  build(); dirty = true;
  const n = p.n === 'wait' ? MODEL.tau.get(MODEL.waitM) : p.n;
  S.nowFrac = fracOf(n); S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.nowFrac;
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); const n = progress().n + (ev.key === 'ArrowRight' ? 1 : -1); jumpTo(fracOf(Math.min(MODEL.nmax, Math.max(1, n)))); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(1);
});

/* =====================================================================
   11. Main loop
   ===================================================================== */
let lastT = performance.now(), frameCount = 0;
function resize() {
  if (!glOK) return;
  const r = stage.getBoundingClientRect();
  renderer.setSize(Math.max(1, r.width), Math.max(1, r.height), false);
  camera.aspect = Math.max(0.2, r.width / Math.max(1, r.height)); camera.updateProjectionMatrix();
}
let glKey = '';
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
    const k = `${MODEL.id}|${progress().n}`;
    if (k !== glKey) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.ZC_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => {
    const M = MODEL, pr = progress();
    return { rule: M.rule, nmax: M.nmax, n: pr.n, a: pr.a, digits: pr.digits, shared: pr.shared, mstar: pr.mstar, max: pr.max, expansion: expansion(pr.a),
      waitM: M.waitM, wait: M.wait, tauWait: M.tau.get(M.waitM), maxDisp: M.maxDisp, dispN: M.dispN, lead: M.lead, oeis: OEIS };
  },
  seq: (from, to) => Array.from(MODEL.a.subarray(from, to + 1)),
  mstarSeq: (from, to) => Array.from(MODEL.mstar.subarray(from, to + 1)),
  sharedSeq: (from, to) => Array.from(MODEL.shared.subarray(from, to + 1)),
  setFrac: (f) => { S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; }
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('long'); S.playing = false; setPlayUI(); S.nowFrac = 0.004; $('now').value = S.nowFrac; setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 15; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
applyPreset('start');
setPlayUI();
requestAnimationFrame(frame);
})();
