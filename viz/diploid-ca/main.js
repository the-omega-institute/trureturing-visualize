/* CA//DIPLOID · the diploid cellular automaton 10-245 has density exactly 1/4 + λ/2 from the first step
   Fukś and Fatès (2026) let every cell of ℤ apply elementary rule 10 with probability 1 − λ and rule 245 with probability λ,
   independently, starting from the fair Bernoulli measure; local structure theory of order three predicts the asymptotic
   density 1/4 + λ/2 and §5 asks whether it is exact. Proved in trureturing (Diploid10245Density.result): for every λ ∈ [0, 1]
   and every t ≥ 1 the density is exactly 1/4 + λ/2. The page runs the automaton on a ring as a space-time tower, computes
   the exact cylinder probabilities of the process on ℤ for the first steps, and contrasts mean field and rule 36-219.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Rules, exact cylinder laws, the ring simulation and mean field
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const L = 240, TMAX = 160, EXT = 8, LAMS = 21;
const RULES = { '10-245': [10, 245], '36-219': [36, 219] };
/* Wolfram numbering: rule r sends the neighbourhood (x, y, z) to bit 4x + 2y + z of r */
const bit = (r, x, y, z) => (r >> (4 * x + 2 * y + z)) & 1;
const w1 = (rule, lam, x, y, z) => { const [f, g] = RULES[rule]; return (1 - lam) * bit(f, x, y, z) + lam * bit(g, x, y, z); };
const leanD = (lam) => 0.25 + lam / 2;
/* the process on ℤ through its cylinder probabilities: the law of a block of length n at time t + 1 comes from the law of
   its n + 2 parents at time t by independent updates. One pass replaces the parents by children left to right. */
const CYL = new Map();
function cylinder(rule, lam, p, Tn = EXT) {
  const key = `${rule}|${lam}|${p}|${Tn}`; if (CYL.has(key)) return CYL.get(key);
  let N = 2 * Tn + 3, A = new Float64Array(1 << N), B = new Float64Array(1 << N);
  for (let s = 0; s < 1 << N; s++) { let pr = 1; for (let k = 0; k < N; k++) pr *= (s >> k) & 1 ? p : 1 - p; A[s] = pr; }
  const W = Array.from({ length: 8 }, (_, c) => w1(rule, lam, (c >> 2) & 1, (c >> 1) & 1, c & 1));
  const d = [], q = [];
  const measure = () => { let a = 0, b = 0; for (let s = 0; s < 1 << N; s++) { const v = A[s]; if (s & 1) a += v; else if ((s >> 2) & 1) b += v; } d.push(a); q.push(b); };
  measure();
  for (let t = 1; t <= Tn; t++) {
    const n = N - 2, size = 1 << N;
    for (let j = 0; j < n; j++) {
      B.fill(0, 0, size);
      for (let s = 0; s < size; s++) { const v = A[s]; if (!v) continue; const w = W[(((s >> j) & 1) << 2) | (((s >> (j + 1)) & 1) << 1) | ((s >> (j + 2)) & 1)], s0 = s & ~(1 << j); B[s0] += v * (1 - w); B[s0 | (1 << j)] += v * w; }
      [A, B] = [B, A];
    }
    const mask = (1 << n) - 1; B.fill(0, 0, 1 << n);
    for (let s = 0; s < size; s++) B[s & mask] += A[s];
    [A, B] = [B, A]; N = n; measure();
  }
  const out = { d, q }; CYL.set(key, out); return out;
}
/* the automaton on a ring of L cells; the coin of every cell at every step is kept */
function simulate(rule, lam, p, seed, steps = TMAX, size = L) {
  const [f, g] = RULES[rule], rnd = TRV.mulberry32(seed), X = new Uint8Array((steps + 1) * size), G = new Uint8Array((steps + 1) * size);
  for (let i = 0; i < size; i++) X[i] = rnd() < p ? 1 : 0;
  for (let t = 1; t <= steps; t++) {
    const o = (t - 1) * size, n = t * size;
    for (let i = 0; i < size; i++) {
      const x = X[o + (i - 1 + size) % size], y = X[o + i], z = X[o + (i + 1) % size], useG = rnd() < lam;
      G[n + i] = useG ? 1 : 0; X[n + i] = bit(useG ? g : f, x, y, z);
    }
  }
  const dens = [], qs = [];
  for (let t = 0; t <= steps; t++) {
    let a = 0, b = 0; const o = t * size;
    for (let i = 0; i < size; i++) { a += X[o + i]; if (!X[o + (i - 1 + size) % size] && X[o + (i + 1) % size]) b++; }
    dens.push(a / size); qs.push(b / size);
  }
  return { X, G, dens, qs, steps, size };
}
/* mean field replaces q by d(1 − d): d_{t+1} = λ + (1 − 2λ) d_t (1 − d_t), the same for both rules */
const meanField = (lam, p, steps = TMAX) => { const a = 1 - 2 * lam, m = [p]; for (let t = 1; t <= steps; t++) { const x = m[t - 1]; m.push(lam + a * x * (1 - x)); } return m; };
const mfFixed = (lam) => { const a = 1 - 2 * lam; return Math.abs(a) < 1e-12 ? 0.5 : (-lam + Math.sqrt(lam * (1 - lam))) / a; };
/* time-averaged ring density over 40 ≤ t ≤ 200 for 21 values of λ */
const SWEEP = new Map();
function sweep(rule, p, seed) {
  const key = `${rule}|${p}|${seed}`; if (SWEEP.has(key)) return SWEEP.get(key);
  const out = [];
  for (let k = 0; k < LAMS; k++) { const lam = k / (LAMS - 1), r = simulate(rule, lam, p, seed + 101 * k, 200); let s = 0; for (let t = 40; t <= 200; t++) s += r.dens[t]; out.push([lam, s / 161]); }
  SWEEP.set(key, out); return out;
}

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean', lam: 0.3, p: 0.5, rule: '10-245', seed: 1 };
const PRESETS = {
  lean: { lam: 0.3, p: 0.5, rule: '10-245',
    zh: 'λ = 0.3：每个格子每一步以 0.7 的概率用规则 10、以 0.3 的概率用规则 245。从公平的 Bernoulli 初态出发，Lean 证明了从第一步起密度恰好是 1/4 + λ/2 = 0.4。环上模拟的密度围绕 0.4 起伏；平均场给的不动点是 0.3957，差一点点。',
    en: 'λ = 0.3: at every step every cell uses rule 10 with probability 0.7 and rule 245 with probability 0.3. From the fair Bernoulli start, Lean proves that the density is exactly 1/4 + λ/2 = 0.4 from the first step on. The density on the ring fluctuates around 0.4; mean field gives the fixed point 0.3957, just short of it.' },
  half: { lam: 0.5, p: 0.5, rule: '10-245',
    zh: 'λ = 1/2：两条规则各占一半，每个格子不论邻居如何都以 1/2 的概率变成 1，所以公平的 Bernoulli 分布一直保持（卷宗的论证）。密度是 1/2，邻居之间也没有关联。',
    en: 'λ = 1/2: each rule half of the time, so every cell becomes 1 with probability 1/2 whatever its neighbours, and the fair Bernoulli law persists (the dossier’s argument). The density is 1/2 and neighbouring cells stay uncorrelated.' },
  zero: { lam: 0, p: 0.5, rule: '10-245',
    zh: 'λ = 0：只用规则 10，过程是确定的——一个格子变成 1，当且仅当它左边是 0、右边是 1。密度从第一步起是 1/4。平均场却预测密度一路降到 0：它把“左 0 右 1”的概率当成 d(1 − d)。',
    en: 'λ = 0: rule 10 alone, and the process is deterministic — a cell becomes 1 exactly when its left neighbour is 0 and its right neighbour is 1. The density is 1/4 from the first step on. Mean field instead predicts a decay to 0: it takes the probability of “0 on the left, 1 on the right” to be d(1 − d).' },
  one: { lam: 1, p: 0.5, rule: '10-245',
    zh: 'λ = 1：只用规则 245，即规则 10 的补。密度从第一步起是 3/4；平均场预测趋向 1。',
    en: 'λ = 1: rule 245 alone, the complement of rule 10. The density is 3/4 from the first step on; mean field predicts a climb to 1.' },
  start: { lam: 0.2, p: 0.1, rule: '10-245',
    zh: '换一个初态：每个格子以 0.1 的概率为 1。这时“左 0 右 1”的概率是 0.09 而不是 1/4，密度不再一步到位，而是按卷宗的公式 d_{t+1} = 1/4 + λ/2 + α^{2t+1}(q₀ − 1/4) 以 α² = 0.36 的比例几何收敛到 0.35（卷宗的论证，未形式化）。',
    en: 'A different start: every cell is 1 with probability 0.1. Now “0 on the left, 1 on the right” has probability 0.09 instead of 1/4, so the density no longer settles at once; by the dossier’s formula d_{t+1} = 1/4 + λ/2 + α^{2t+1}(q₀ − 1/4) it converges geometrically to 0.35 with ratio α² = 0.36 (the dossier’s argument, not formalized).' },
  r36: { lam: 1 / 7, p: 0.5, rule: '36-219',
    zh: '对照：规则 36-219 的平均场方程与 10-245 完全相同，但精确密度在第二步就离开 1/4 + λ/2：λ = 1/7 时 d₂ = 1389/5488 ≈ 0.2531，而 1/4 + λ/2 = 9/28 ≈ 0.3214（卷宗记录，页面复算）。10-245 的密度能精确算出，靠的是这条规则自己的结构。',
    en: 'Contrast: rule 36-219 has exactly the same mean-field equation as 10-245, but its exact density leaves 1/4 + λ/2 at the second step: at λ = 1/7, d₂ = 1389/5488 ≈ 0.2531 while 1/4 + λ/2 = 9/28 ≈ 0.3214 (recorded in the dossier, recomputed by the page). That 10-245 can be solved exactly is a property of this particular rule.' }
};
let GEO = null, geoId = 0, MODEL = null, dirty = true;
function geometry() {
  const key = `${S.rule}|${S.lam}|${S.p}|${S.seed}`;
  if (GEO && GEO.key === key) return GEO;
  const sim = simulate(S.rule, S.lam, S.p, S.seed), ex = cylinder(S.rule, S.lam, S.p), mf = meanField(S.lam, S.p);
  let avg = 0; for (let t = 20; t <= TMAX; t++) avg += sim.dens[t]; avg /= TMAX - 19;
  let dev = 0; for (let t = 1; t <= EXT; t++) dev = Math.max(dev, Math.abs(ex.d[t] - leanD(S.lam)));
  GEO = { key, id: ++geoId, rule: S.rule, lam: S.lam, p: S.p, alpha: 1 - 2 * S.lam, sim, ex, mf, avg, dev, dstar: mfFixed(S.lam),
    leanApplies: S.rule === '10-245' && S.p === 0.5, sweep: sweep(S.rule, S.p, 7) };
  return GEO;
}
function build() {
  const G = geometry(), t = Math.min(TMAX, Math.floor(S.t * TMAX + 1e-9));
  MODEL = Object.assign({}, G, { t, dRing: G.sim.dens[t], qRing: G.sim.qs[t], dEx: t <= EXT ? G.ex.d[t] : null, qEx: t <= EXT ? G.ex.q[t] : null });
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const css = (c, a = 1) => `rgba(${c.map((x) => Math.round(255 * Math.min(1, x))).join(',')},${a})`;
const f4 = (x) => x.toFixed(4);
const fl = (x) => (Math.abs(x - 1 / 7) < 1e-12 ? '1/7' : String(+x.toFixed(2)));

/* =====================================================================
   4. 3D scene: the ring's history as a tower, time going up; 1-cells lit by the rule that produced them
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const RAD = 2.6, HGT = 4.0, Y0 = -2.0, LINES_MAX = 4000, PTS_MAX = 62000;
const CAMS = { iso: [0.55, 1.2, 11.5], side: [0.0001, 1.5, 10.5], top: [0.0001, 0.05, 10] };
const cam = { theta: 0.55, phi: 1.2, r: 11.5, tTheta: 0.55, tPhi: 1.2, tR: 11.5 };
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
  float a = smoothstep(1.0, 0.5, r) * vA;
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
const rowY = (t) => Y0 + HGT * t / TMAX;
const cellPos = (i, t, r = RAD) => { const a = 2 * Math.PI * i / L; return [r * Math.cos(a), rowY(t), r * Math.sin(a)]; };
function updateGL() {
  const M = MODEL, Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; for (let k = 0; k < 3; k++) { PT.position.array[3 * np + k] = p[k]; PT.aColor.array[3 * np + k] = c[k]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const { X, G } = M.sim, gray = [0.6, 0.68, 0.78];
  /* the rings at the bottom and at the current row */
  for (const [t, k] of [[0, 0.3], [M.t, 0.7]]) for (let s = 0; s < 96; s++) { const a0 = 2 * Math.PI * s / 96, a1 = 2 * Math.PI * (s + 1) / 96, r = RAD + 0.32; seg([r * Math.cos(a0), rowY(t), r * Math.sin(a0)], [r * Math.cos(a1), rowY(t), r * Math.sin(a1)], t ? COL.amber : gray, k); }
  for (let s = 0; s < 12; s++) seg(cellPos(s * L / 12, 0, RAD + 0.32), cellPos(s * L / 12, TMAX, RAD + 0.32), gray, 0.07);
  for (let t = 0; t <= M.t; t++) {
    const top = t === M.t, o = t * L, al = top ? 1 : 0.18 + 0.5 * Math.pow(t / Math.max(1, M.t), 3);
    for (let i = 0; i < L; i++) {
      if (X[o + i]) dot(cellPos(i, t), t === 0 ? gray : G[o + i] ? COL.magenta : COL.cyan, al, top ? 1.5 : 0.95);
      else if (top) dot(cellPos(i, t), gray, 0.18, 1.1);
    }
  }
  /* the pattern “0 at i − 1, 1 at i + 1” in the current row, whose probability q pins the density */
  const o = M.t * L;
  for (let i = 0; i < L; i++) if (!X[o + (i - 1 + L) % L] && X[o + (i + 1) % L]) dot(cellPos(i, M.t, RAD + 0.2), COL.amber, 0.95, 1.2);
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
  camera.position.set(r * sp * Math.sin(cam.theta), r * Math.cos(cam.phi) + 0.5, r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(0, 0.2, 0);
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
  const M = MODEL; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  put(T(`t = ${M.t} · 环上密度 ${f4(M.dRing)}`, `t = ${M.t} · ring density ${f4(M.dRing)}`), [RAD * 0.75, rowY(M.t) + 0.4, RAD * 0.75], 'am');
  put(T(`t = 0 · Bernoulli(${fl(M.p)})`, `t = 0 · Bernoulli(${fl(M.p)})`), [0, rowY(0) - 0.4, RAD + 0.6], 'w');
  put(T(`${L} 个格子的环`, `a ring of ${L} cells`), [-RAD - 0.9, rowY(0), 0], 't');
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
/* d_t and q_t against √t: the ring, the exact law on ℤ (t ≤ 8), Lean's constant and mean field */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 30); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, X = (t) => pl + iw * Math.sqrt(t / TMAX), Y = (v) => pt + ih * (1 - v);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  ctx.setLineDash([3 * dpr, 3 * dpr]); ctx.strokeStyle = 'rgba(111,142,165,0.6)'; ctx.beginPath(); ctx.moveTo(pl, Y(0.25)); ctx.lineTo(pl + iw, Y(0.25)); ctx.stroke();
  if (M.leanApplies) { ctx.strokeStyle = AM; ctx.lineWidth = 1.4 * dpr; ctx.beginPath(); ctx.moveTo(X(1), Y(leanD(M.lam))); ctx.lineTo(pl + iw, Y(leanD(M.lam))); ctx.stroke(); }
  ctx.setLineDash([]);
  const line = (arr, col, lw) => { ctx.beginPath(); arr.forEach((v, t) => (t ? ctx.lineTo(X(t), Y(v)) : ctx.moveTo(X(t), Y(v)))); ctx.strokeStyle = col; ctx.lineWidth = lw * dpr; ctx.stroke(); };
  line(M.sim.qs, 'rgba(212,239,255,0.35)', 1); line(M.mf, MG, 1.4); line(M.sim.dens, CY, 1.3);
  M.ex.d.forEach((v, t) => { ctx.fillStyle = INK; ctx.beginPath(); ctx.arc(X(t), Y(v), 2.6 * dpr, 0, 2 * Math.PI); ctx.fill(); });
  ctx.strokeStyle = INK; ctx.setLineDash([2 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(X(M.t), pt); ctx.lineTo(X(M.t), pt + ih); ctx.stroke(); ctx.setLineDash([]);
  [0, 0.25, 0.5, 0.75, 1].forEach((v) => lab(ctx, String(v), pl - 4 * dpr, Y(v), 'right', 'middle'));
  [0, 1, 2, 4, 8, 20, 40, 80, 160].forEach((t) => lab(ctx, String(t), X(t), pt + ih + 4 * dpr, t === 0 ? 'left' : t === TMAX ? 'right' : 'center', 'top'));
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('环上 d_t', 'ring d_t')}</span><span class="it"><i class="sw" style="--c:${INK}"></i>${T('ℤ 上精确 d_t（t ≤ 8）', 'exact d_t on ℤ (t ≤ 8)')}</span>${M.leanApplies ? `<span class="it"><i class="sw" style="--c:${AM}"></i>Lean 1/4 + λ/2</span>` : ''}<span class="it"><i class="sw" style="--c:${MG}"></i>${T('平均场', 'mean field')}</span><span class="it"><i class="sw" style="--c:${FAINT}"></i>${T('环上 q_t，虚线 1/4', 'ring q_t, dashed 1/4')}</span>`;
}
/* the limit density against λ */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 30); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, X = (l) => pl + iw * l, Y = (v) => pt + ih * (1 - v);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  ctx.strokeStyle = AM; ctx.lineWidth = 1.6 * dpr; ctx.beginPath(); ctx.moveTo(X(0), Y(0.25)); ctx.lineTo(X(1), Y(0.75)); ctx.stroke();
  ctx.beginPath(); for (let k = 0; k <= 200; k++) { const l = k / 200; k ? ctx.lineTo(X(l), Y(mfFixed(l))) : ctx.moveTo(X(l), Y(mfFixed(l))); } ctx.strokeStyle = MG; ctx.lineWidth = 1.4 * dpr; ctx.stroke();
  M.sweep.forEach(([l, v]) => { ctx.strokeStyle = CY; ctx.lineWidth = 1.4 * dpr; ctx.beginPath(); ctx.arc(X(l), Y(v), 3 * dpr, 0, 2 * Math.PI); ctx.stroke(); });
  ctx.strokeStyle = INK; ctx.setLineDash([2 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(X(M.lam), pt); ctx.lineTo(X(M.lam), pt + ih); ctx.stroke(); ctx.setLineDash([]);
  ctx.fillStyle = INK; ctx.beginPath(); ctx.arc(X(M.lam), Y(M.avg), 3.5 * dpr, 0, 2 * Math.PI); ctx.fill();
  [0, 0.25, 0.5, 0.75, 1].forEach((v) => lab(ctx, String(v), pl - 4 * dpr, Y(v), 'right', 'middle'));
  [0, 0.5, 1].forEach((l, k) => lab(ctx, `λ = ${l}`, X(l), pt + ih + 4 * dpr, ['left', 'center', 'right'][k], 'top'));
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${AM}"></i>1/4 + λ/2</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('平均场不动点', 'mean-field fixed point')}</span><span class="it"><i class="sw" style="--c:${CY}"></i>${T(`环上平均（${M.rule}）`, `ring average (${M.rule})`)}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function readouts() {
  const M = MODEL;
  pill('pillA', T('规则', 'rule'), M.rule); pill('pillB', 'λ', fl(M.lam)); pill('pillC', '1/4 + λ/2', f4(leanD(M.lam))); pill('pillD', 't', String(M.t));
  setRo([
    [T('λ · α = 1 − 2λ · 初态 Bernoulli(p)', 'λ · α = 1 − 2λ · start Bernoulli(p)'), `${fl(M.lam)} · ${(+M.alpha.toFixed(4))} · p = ${fl(M.p)}`],
    [T(`t = ${M.t}：环上密度 · ℤ 上的精确密度`, `t = ${M.t}: ring density · exact density on ℤ`), `${f4(M.dRing)} · ${M.dEx === null ? T('（只算到 t = 8）', '(computed up to t = 8)') : M.dEx.toFixed(6)}`],
    [T('1/4 + λ/2 · ℤ 上 1 ≤ t ≤ 8 的最大偏差', '1/4 + λ/2 · largest deviation on ℤ for 1 ≤ t ≤ 8'), `${f4(leanD(M.lam))} · ${M.dev < 1e-12 ? '< 10⁻¹²' : M.dev.toFixed(6)}`],
    [T('q_t = P(左 0、右 1)：环上 · ℤ 上精确', 'q_t = P(0 on the left, 1 on the right): ring · exact on ℤ'), `${f4(M.qRing)} · ${M.qEx === null ? '—' : M.qEx.toFixed(6)}`],
    [T('平均场不动点 · 环上 t ≥ 20 的时间平均', 'Mean-field fixed point · ring time average over t ≥ 20'), `${f4(M.dstar)} · ${f4(M.avg)}`]]);
  $('roNote').innerHTML = M.leanApplies
    ? T(`Lean：对每个 λ ∈ [0, 1]，ℤ 上的过程从第一步起密度恰为 1/4 + λ/2，这里是 ${f4(leanD(M.lam))}。`, `Lean: for every λ ∈ [0, 1] the process on ℤ has density exactly 1/4 + λ/2 from the first step on, here ${f4(leanD(M.lam))}.`)
    : M.rule === '10-245' ? T('换了初态：Lean 的定理只管公平的 Bernoulli 初态；这里的精确值是页面计算。', 'A different start: Lean’s theorem covers only the fair Bernoulli start; the exact values here are page computations.')
      : T('规则 36-219 不在 Lean 定理里；这里的精确值是页面计算。', 'Rule 36-219 is not covered by Lean’s theorem; the exact values here are page computations.');
}
const stateKey = () => `${S.rule}|${S.lam}|${S.p}|${S.seed}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; }
  const M = MODEL;
  if (!toasted && S.playing && S.t >= 1) { toasted = true; toast(T(`<b>环上平均 ${f4(M.avg)}</b>，1/4 + λ/2 = ${f4(leanD(M.lam))}，平均场 ${f4(M.dstar)}。`, `<b>Ring average ${f4(M.avg)}</b>; 1/4 + λ/2 = ${f4(leanD(M.lam))}; mean field ${f4(M.dstar)}.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('lamIn').value = String(S.lam); $('lamOut').textContent = fl(S.lam); $('pIn').value = String(S.p); $('pOut').textContent = fl(S.p);
  document.querySelectorAll('#ruleChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.rule === S.rule)));
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  const [f, g] = RULES[S.rule];
  $('sysNote').innerHTML = T(`每个格子每一步独立地掷一枚硬币：以 1 − λ 的概率用规则 ${f}，以 λ 的概率用规则 ${g}。三维塔里青色的 1 来自规则 ${f}，品红的 1 来自规则 ${g}。`, `At every step every cell tosses its own coin: rule ${f} with probability 1 − λ, rule ${g} with probability λ. In the 3D tower cyan 1s come from rule ${f} and magenta 1s from rule ${g}.`);
  $('litNote').innerHTML = T('原文用局部结构理论（三阶）预测 1/4 + λ/2，并在 §5 问它是否精确；Lean 给出肯定回答。', 'The source predicts 1/4 + λ/2 by third-order local structure theory and asks in §5 whether it is exact; Lean answers yes.');
  $('c1Title').textContent = T('密度 d_t 与相关 q_t（横轴为 √t）', 'Density d_t and correlation q_t (√t axis)');
  $('c2Title').textContent = T('极限密度与 λ', 'Limit density against λ');
  $('clock').innerHTML = `t = ${M.t}`;
  $('hudBig').textContent = `${M.rule} · λ = ${fl(M.lam)} · ${M.leanApplies ? `d_t = 1/4 + λ/2 = ${f4(leanD(M.lam))}` : `d_${Math.min(M.t, EXT)} = ${M.ex.d[Math.min(M.t, EXT)].toFixed(4)}`}`;
  $('hudSub').textContent = S.rule === '10-245' ? T(`环上 ${L} 个格子，时间向上。青色的 1 来自规则 ${f}，品红的 1 来自规则 ${g}；顶层琥珀点标出“左 0、右 1”的位置，它们的比例 q 决定下一步的密度`, `A ring of ${L} cells, time going up. Cyan 1s come from rule ${f}, magenta 1s from rule ${g}; amber dots on the top row mark “0 on the left, 1 on the right”, whose fraction q sets the next density`)
    : T(`环上 ${L} 个格子，时间向上。青色的 1 来自规则 ${f}，品红的 1 来自规则 ${g}；顶层琥珀点仍标出“左 0、右 1”，但对这条规则它们不决定下一步的密度`, `A ring of ${L} cells, time going up. Cyan 1s come from rule ${f}, magenta 1s from rule ${g}; amber dots on the top row still mark “0 on the left, 1 on the right”, but for this rule they do not set the next density`);
}
function syncRail() {
  const key = `${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 't = 0', 'first'], [0.5, `t = ${TMAX / 2}`, ''], [1, `t = ${TMAX}`, 'last']];
  $('marks').innerHTML = marks.map(([f, l, c]) => `<i class="${c}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { lam: p.lam, p: p.p, rule: p.rule, seed: 1, t: 0, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('lamIn').addEventListener('input', () => { S.lam = parseFloat($('lamIn').value); custom(); });
$('pIn').addEventListener('input', () => { S.p = parseFloat($('pIn').value); custom(); });
document.querySelectorAll('#ruleChips .chip').forEach((b) => b.addEventListener('click', () => { S.rule = b.dataset.rule; custom(); }));
$('seedBtn').addEventListener('click', () => { S.seed += 1; custom(); toast(T(`新的随机种子 ${S.seed}：环上的轨迹变了，ℤ 上的精确值不变。`, `New random seed ${S.seed}: the ring’s history changes, the exact values on ℤ do not.`)); });
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo((Math.floor(S.t * TMAX + 1e-9) + (ev.key === 'ArrowRight' ? 1 : -1)) / TMAX); }
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
const RUN_SECONDS = 14;
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : 1); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed / RUN_SECONDS);
      if (S.t >= 1) S.hold = 2.4;
      if (S.t <= 0 && S.dir < 0) S.hold = 1.2;
    }
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    const k = `${MODEL.id}|${MODEL.t}`;
    if (glKey !== k) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.DP_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { rule: M.rule, lam: M.lam, p: M.p, alpha: M.alpha, t: M.t, dRing: M.dRing, qRing: M.qRing, dEx: M.dEx, qEx: M.qEx, exD: [...M.ex.d], exQ: [...M.ex.q],
    ringD: [...M.sim.dens], ringQ: [...M.sim.qs], mf: [...M.mf], dstar: M.dstar, avg: M.avg, dev: M.dev, leanApplies: M.leanApplies, sweep: M.sweep.map((r) => r.slice()) }; },
  row: (t) => [...MODEL.sim.X.slice(t * L, (t + 1) * L)],
  coins: (t) => [...MODEL.sim.G.slice(t * L, (t + 1) * L)],
  cylinder: (rule, lam, p, Tn) => { const c = cylinder(rule, lam, p, Tn); return { d: [...c.d], q: [...c.q] }; },
  mfFixed: (lam) => mfFixed(lam),
  L, TMAX,
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setT(1); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 10.2; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
