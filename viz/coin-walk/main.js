/* COIN//WALK · the symmetric coin (1, i)/√2 maximizes the full-mode geometric entanglement of the Hadamard walk on every circle
   Donkersloot, Sondenheimer and Sperling (2026) run the Hadamard walk on a circle of P sites with one photon starting at
   site 0 in coin state c, and measure the geometric entanglement E_g across all 2P optical modes; they expect the coin
   (1, i)/√2 to give the maximum for every circle size and time. Proved in trureturing
   (SymmetricCoinMaximalWalkEntanglement.result): for every P ≥ 1, every time n and every unit coin c,
   E_g(walk from c) ≤ E_g(walk from (1, i)/√2). The page paints E_g over the Bloch sphere of initial coins, shows the walk's
   probabilities on the circle with its reflection pairs, and plots E_g in time and along the source's interpolation.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. The walk, the single-photon W vector and its maximal product overlap
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const NMAX = 32, NS = 1400, MER = 121, R2 = Math.SQRT1_2;
const STAR = [Math.PI / 2, Math.PI / 2];
/* the walks from the two basis coins, u = Tⁿ|0, 0⟩ and w = Tⁿ|1, 0⟩; they stay real. Mode (b, x) has index b·P + x */
const BASIS = new Map();
function basis(P, n) {
  const key = `${P}|${n}`; if (BASIS.has(key)) return BASIS.get(key);
  const run = (b0) => {
    let s = new Float64Array(2 * P); s[b0 * P] = 1;
    for (let k = 0; k < n; k++) {
      const t = new Float64Array(2 * P);
      for (let x = 0; x < P; x++) { const r = (x + 1) % P, l = (x - 1 + P) % P; t[x] = (s[r] + s[P + r]) * R2; t[P + x] = (s[l] - s[P + l]) * R2; }
      s = t;
    }
    return s;
  };
  const out = { u: run(0), w: run(1) }; BASIS.set(key, out); return out;
}
/* coin (cos θ/2, e^{iφ} sin θ/2): by linearity the walk is cos(θ/2)·u + e^{iφ} sin(θ/2)·w */
function probs(P, n, th, ph) {
  const { u, w } = basis(P, n), a = Math.cos(th / 2), b = Math.sin(th / 2), cp = Math.cos(ph), out = new Float64Array(2 * P);
  for (let k = 0; k < 2 * P; k++) out[k] = a * a * u[k] * u[k] + b * b * w[k] * w[k] + 2 * a * b * cp * u[k] * w[k];
  return out;
}
/* g_max of Σ λ_k |1_k⟩ over products of unit two-component factors, from the stationary equations of
   F(t) = Σ c_k t_k / Π √(1 + t_k²), c_k = |λ_k|: c_k(1 + t_k²) = S t_k with S = Σ c_k t_k. Candidates: every t_k on its
   smaller root; the largest mode on its larger root; and the edge value max c_k². */
function gW(p) {
  const c = []; for (const v of p) if (v > 1e-28) c.push(Math.sqrt(v));
  c.sort((x, y) => y - x);
  const n = c.length; if (!n) return 0; if (n === 1) return Math.min(1, c[0] * c[0]);
  let best = c[0] * c[0];
  const logF = (S, big) => { let lf = Math.log(S); for (let k = 0; k < n; k++) { const d = Math.sqrt(Math.max(0, S * S - 4 * c[k] * c[k])), t = (k === big ? S + d : S - d) / (2 * c[k]); lf -= 0.5 * Math.log(1 + t * t); } return 2 * lf; };
  const sq = (S, x) => Math.sqrt(Math.max(0, S * S - 4 * x * x));
  const G = (S) => { let s = -(n - 2) * S; for (let k = 0; k < n; k++) s += sq(S, c[k]); return s; };
  const bisect = (f, lo, hi) => { let flo = f(lo); for (let it = 0; it < 90; it++) { const mid = (lo + hi) / 2, fm = f(mid); if ((fm < 0) === (flo < 0)) { lo = mid; flo = fm; } else hi = mid; } return (lo + hi) / 2; };
  const lo = 2 * c[0];
  if (G(lo) < 0) { let hi = 2 * lo; while (G(hi) < 0) hi *= 2; best = Math.max(best, Math.exp(logF(bisect(G, lo, hi), -1))); }
  const H = (S) => { let s = -(n - 2) * S - sq(S, c[0]); for (let k = 1; k < n; k++) s += sq(S, c[k]); return s; };
  let a = lo * (1 + 1e-12), ha = H(a);
  for (let k = 1; k <= 750; k++) { const b = lo * Math.exp(0.02 * k), hb = H(b); if (ha * hb <= 0) best = Math.max(best, Math.exp(logF(bisect(H, a, b), 0))); a = b; ha = hb; }
  return Math.min(1, best);
}
const Eg = (p) => Math.max(0, 1 - gW(p));
/* the Bloch sphere of coins as a Fibonacci lattice */
const SPHERE = Array.from({ length: NS }, (_, i) => { const z = 1 - 2 * (i + 0.5) / NS, r = Math.sqrt(1 - z * z), a = i * Math.PI * (3 - Math.sqrt(5)); return { th: Math.acos(z), ph: Math.atan2(r * Math.sin(a), r * Math.cos(a)), v: [r * Math.cos(a), r * Math.sin(a), z] }; });
const SCACHE = new Map();
function sphere(P, n) {
  const key = `${P}|${n}`; if (SCACHE.has(key)) return SCACHE.get(key);
  const E = new Float64Array(NS); let mx = -1, mi = 2, arg = 0;
  SPHERE.forEach((s, i) => { E[i] = Eg(probs(P, n, s.th, s.ph)); if (E[i] > mx) { mx = E[i]; arg = i; } mi = Math.min(mi, E[i]); });
  const out = { E, max: mx, min: mi, arg }; SCACHE.set(key, out); return out;
}

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean', P: 8, th: 0, ph: 0, nmax: 12 };
const PRESETS = {
  lean: { P: 8, th: 0, ph: 0, nmax: 12,
    zh: '八个格点的圆环，光子从格点 0 出发，硬币是 |0⟩。播放时间：每一步 E_g 都不超过从 (1, i)/√2 出发的值（琥珀色曲线），这正是 Lean 证明的不等式。球面上的颜色是所有初始硬币的 E_g，最亮处在 c*。',
    en: 'A circle of eight sites; the photon starts at site 0 with coin |0⟩. Play the time: at every step E_g stays at or below the value from (1, i)/√2 (the amber curve), exactly the inequality Lean proves. The colours on the sphere are E_g for every initial coin, brightest at c*.' },
  one: { P: 1, th: 0, ph: 0, nmax: 8,
    zh: 'P = 1：只有一个格点、两个模，平移不起作用，每一步只做 Hadamard。两个模的 E_g 是两个概率中较小的那个，最多 1/2；c* 每一步都把概率平分，所以每一步都达到 1/2。Lean 的定理包括这个情形。',
    en: 'P = 1: a single site with two modes, where the shift does nothing and each step is just the Hadamard coin. For two modes E_g is the smaller of the two probabilities, at most 1/2; c* splits the probability evenly at every step and so reaches 1/2 every time. Lean’s theorem includes this case.' },
  conj: { P: 8, th: Math.PI / 2, ph: -Math.PI / 2, nmax: 12,
    zh: '共轭硬币 (1, −i)/√2：它的演化是 c* 演化的复共轭，各模的概率完全相同，所以 E_g 也一样大（卷宗的论证）。最大值不唯一——两个硬币只差一个相位，却不是同一个态。',
    en: 'The conjugate coin (1, −i)/√2: its evolution is the complex conjugate of the one from c*, with exactly the same mode probabilities, so E_g is just as large (the dossier’s argument). The maximum is not unique — the two coins differ by more than a global phase.' },
  interp: { P: 8, th: Math.PI / 4, ph: Math.PI / 2, nmax: 12,
    zh: '原文的插值 c_θ = (cos θ/2, i sin θ/2) 走到一半，θ = π/4。右下图是沿这条经线的 E_g：从 |0⟩ 到 c*（θ 从 0 到 π/2）单调上升——原文观察到，卷宗给了论证（未形式化）。',
    en: 'Halfway along the source’s interpolation c_θ = (cos θ/2, i sin θ/2), at θ = π/4. The lower-right chart shows E_g along this meridian: it rises monotonically from |0⟩ to c* (θ from 0 to π/2) — observed by the source, argued in the dossier (not formalized).' },
  plus: { P: 8, th: Math.PI / 2, ph: 0, nmax: 12,
    zh: '|+⟩ = (1, 1)/√2 也在赤道上，但相位不对：反射对 (0, x) 与 (1, −x) 的概率不平衡，E_g 比 c* 小。在赤道上只有 φ = ±π/2 让每一对都平衡。',
    en: '|+⟩ = (1, 1)/√2 also lies on the equator, but with the wrong phase: the reflection pairs (0, x) and (1, −x) are unbalanced and E_g falls below c*. On the equator only φ = ±π/2 balances every pair.' },
  big: { P: 16, th: 1.1, ph: 2.3, nmax: 32,
    zh: '十六个格点、32 个模、走 32 步，硬币取一般的 θ = 1.1、φ = 2.3。每一步 E_g 仍低于 c*。球面网格上 1400 个硬币的最大值也从不超过 c*（页面数值）。',
    en: 'Sixteen sites, 32 modes, 32 steps, with a generic coin θ = 1.1, φ = 2.3. At every step E_g stays below c*. The largest value over the 1400 coins of the sphere grid never exceeds c* either (page numbers).' }
};
let MODEL = null, dirty = true, modelId = 0;
function build() {
  const n = Math.min(S.nmax, Math.round(S.t * S.nmax)), P = S.P;
  const pc = probs(P, n, S.th, S.ph), ps = probs(P, n, STAR[0], STAR[1]);
  const curve = (th, ph) => Array.from({ length: S.nmax + 1 }, (_, k) => Eg(probs(P, k, th, ph)));
  const pairs = (p) => { let imb = 0, sum = 0; for (let x = 0; x < P; x++) { const a = p[x], b = p[P + (P - x) % P]; imb = Math.max(imb, Math.abs(a - b)); } return imb; };
  let sumDiff = 0; for (let x = 0; x < P; x++) { const j = P + (P - x) % P; sumDiff = Math.max(sumDiff, Math.abs(pc[x] + pc[j] - ps[x] - ps[j])); }
  const mer = (ph) => Array.from({ length: MER }, (_, k) => Eg(probs(P, n, Math.PI * k / (MER - 1), ph)));
  MODEL = { id: ++modelId, P, n, th: S.th, ph: S.ph, nmax: S.nmax, pc, ps, Ec: Eg(pc), Es: Eg(ps), norm: pc.reduce((a, b) => a + b, 0),
    imbC: pairs(pc), imbS: pairs(ps), sumDiff, sph: sphere(P, n), curveC: curve(S.th, S.ph), curveS: curve(STAR[0], STAR[1]), curve0: curve(0, 0),
    merStar: mer(Math.PI / 2), merSel: mer(S.ph), pmax: Math.max(...pc, ...ps) };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const css = (c, a = 1) => `rgba(${c.map((x) => Math.round(255 * Math.min(1, x))).join(',')},${a})`;
const f4 = (x) => x.toFixed(4);
const ang = (x) => { const k = [[0, '0'], [Math.PI / 4, 'π/4'], [Math.PI / 2, 'π/2'], [-Math.PI / 2, '−π/2'], [Math.PI, 'π']].find(([v]) => Math.abs(v - x) < 1e-9); return k ? k[1] : x.toFixed(2); };
/* dark blue → cyan → amber → white for E_g relative to the sphere's range */
const heat = (f) => { const st = [[0.05, 0.08, 0.3], [0.1, 0.75, 0.95], [1, 0.75, 0.2], [1, 0.97, 0.85]], x = Math.min(0.999, Math.max(0, f)) * 3, i = Math.floor(x), r = x - i; return st[i].map((v, k) => v + (st[i + 1][k] - v) * r); };

/* =====================================================================
   4. 3D scene: the Bloch sphere of initial coins coloured by E_g, and the walk on its circle
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const SC = [-2.5, 0.5, 0], SR = 1.75, RC = [2.5, -0.9, 0], RR = 1.7, BARH = 2.8, LINES_MAX = 4000, PTS_MAX = 2200;
const CAMS = { iso: [0.0001, 1.2, 11], side: [0.0001, 1.5, 10.5], top: [0.0001, 0.05, 10.5] };
const cam = { theta: 0.0001, phi: 1.2, r: 11, tTheta: 0.0001, tPhi: 1.2, tR: 11 };
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
  float a = smoothstep(1.0, 0.55, r) * vA;
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
/* Bloch vector (x, y, z) → world: z up, the y axis (where c* sits) toward the viewer */
const bloch = (v, r = SR) => [SC[0] + r * v[0], SC[1] + r * v[2], SC[2] + r * v[1]];
const coinVec = (th, ph) => [Math.sin(th) * Math.cos(ph), Math.sin(th) * Math.sin(ph), Math.cos(th)];
const site = (P, x, off, h = 0) => { const a = 2 * Math.PI * x / P - Math.PI / 2 + off; return [RC[0] + RR * Math.cos(a), RC[1] + h, RC[2] - RR * Math.sin(a)]; };
function updateGL() {
  const M = MODEL, Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; for (let k = 0; k < 3; k++) { PT.position.array[3 * np + k] = p[k]; PT.aColor.array[3 * np + k] = c[k]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const gray = [0.55, 0.65, 0.78], sp = M.sph, span = Math.max(1e-9, sp.max - sp.min);
  /* sphere: the colour of each coin is its E_g at the current time, relative to the sphere's range */
  SPHERE.forEach((s, i) => dot(bloch(s.v), heat((sp.E[i] - sp.min) / span), 0.85, 0.95));
  for (const [axis, k] of [[[0, 0, 1], 0], [[1, 0, 0], 1]]) for (let s = 0; s < 72; s++) {
    const a0 = 2 * Math.PI * s / 72, a1 = 2 * Math.PI * (s + 1) / 72, pnt = (a) => (k === 0 ? [Math.cos(a), Math.sin(a), 0] : [0, Math.cos(a), Math.sin(a)]);
    seg(bloch(pnt(a0), SR * 1.01), bloch(pnt(a1), SR * 1.01), gray, 0.18);
  }
  seg(bloch([0, 0, -1.25]), bloch([0, 0, 1.25]), gray, 0.3);
  const sel = coinVec(M.th, M.ph);
  seg(bloch([0, 0, 0]), bloch(sel, SR * 1.12), WHITE, 0.8); dot(bloch(sel, SR * 1.12), WHITE, 1, 3.2);
  dot(bloch([0, 1, 0], SR * 1.06), COL.amber, 1, 4.2); dot(bloch([0, -1, 0], SR * 1.06), COL.amber, 0.7, 3);
  const am = SPHERE[sp.arg].v; dot(bloch(am, SR * 1.04), COL.magenta, 0.9, 2.4);
  /* the circle: two bars per site, coin 0 cyan and coin 1 magenta, height ∝ √probability; c* as thin white ticks */
  const P = M.P, off = Math.min(0.12, Math.PI / (3 * P));
  for (let s = 0; s < 96; s++) { const a0 = 2 * Math.PI * s / 96, a1 = 2 * Math.PI * (s + 1) / 96; seg([RC[0] + RR * Math.cos(a0), RC[1], RC[2] - RR * Math.sin(a0)], [RC[0] + RR * Math.cos(a1), RC[1], RC[2] - RR * Math.sin(a1)], gray, 0.25); }
  for (let x = 0; x < P; x++) {
    for (const [b, o, col] of [[0, -off, COL.cyan], [1, off, COL.magenta]]) {
      const h = BARH * Math.sqrt(M.pc[b * P + x]), hs = BARH * Math.sqrt(M.ps[b * P + x]);
      seg(site(P, x, o), site(P, x, o, h), col, 0.95); dot(site(P, x, o, h), col, 1, 1.6);
      seg(site(P, x, o * 1.6, hs), site(P, x, o * 0.4, hs), WHITE, 0.55);
    }
    dot(site(P, x, 0), x === 0 ? COL.amber : gray, x === 0 ? 1 : 0.6, x === 0 ? 2.2 : 1.4);
    /* the reflection pair (0, x) – (1, −x) as a chord on the floor, brighter when unbalanced */
    const j = (P - x) % P, imb = Math.abs(M.pc[x] - M.pc[P + j]) / Math.max(1e-9, M.pmax);
    if (x <= j) seg(site(P, x, -off, 0.01), site(P, j, off, 0.01), imb > 1e-6 ? COL.magenta : WHITE, 0.12 + 0.8 * Math.min(1, imb));
  }
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const a of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) a.needsUpdate = true;
  pts.material.uniforms.uScale.value = 60 * renderer.getPixelRatio() * (stage.clientHeight / 600);
}
const WHITE = [0.95, 0.97, 1];

/* =====================================================================
   5. Camera
   ===================================================================== */
function updateCamera(dtSec) {
  const k = reduceMotion ? 1 : 1 - Math.pow(0.001, dtSec);
  cam.theta += (cam.tTheta - cam.theta) * k; cam.phi += (cam.tPhi - cam.phi) * k; cam.r += (cam.tR - cam.r) * k;
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.5 : 1);
  camera.position.set(r * sp * Math.sin(cam.theta), r * Math.cos(cam.phi) + 0.3, r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(0, 0.3, 0);
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
  put(`c* · E_g = ${f4(M.Es)}`, [SC[0] + SR * 0.95, SC[1] - SR * 1.2, SC[2] + SR * 0.7], 'am');
  put(T(`硬币 · E_g = ${f4(M.Ec)}`, `coin · E_g = ${f4(M.Ec)}`), bloch(coinVec(M.th, M.ph), SR * 1.6), 'w');
  put('|0⟩', bloch([0, 0, 1], SR * 1.25), 't'); put('|1⟩', bloch([0, 0, -1], SR * 1.25), 't');
  put(T(`${M.P} 个格点 · 第 ${M.n} 步`, `${M.P} sites · step ${M.n}`), [RC[0], RC[1] - 0.45, RC[2] + RR + 0.3], 't');
  put(T('格点 0', 'site 0'), site(M.P, 0, 0, -0.3), 'am');
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
const yr = (arrs) => { let lo = 1, hi = 0; for (const a of arrs) for (const v of a) { lo = Math.min(lo, v); hi = Math.max(hi, v); } const pad = Math.max(0.02, (hi - lo) * 0.08); return [Math.max(0, lo - pad), Math.min(1, hi + pad)]; };
/* E_g over time for c*, the chosen coin and |0⟩ */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 34); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, [y0, y1] = yr([M.curveS, M.curveC, M.curve0]), X = (n) => pl + iw * n / M.nmax, Y = (v) => pt + ih * (1 - (v - y0) / (y1 - y0));
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  const line = (arr, col, lw, dash) => { ctx.setLineDash(dash ? [3 * dpr, 3 * dpr] : []); ctx.beginPath(); arr.forEach((v, n) => (n ? ctx.lineTo(X(n), Y(v)) : ctx.moveTo(X(n), Y(v)))); ctx.strokeStyle = col; ctx.lineWidth = lw * dpr; ctx.stroke(); ctx.setLineDash([]); arr.forEach((v, n) => { ctx.fillStyle = col; ctx.beginPath(); ctx.arc(X(n), Y(v), 2 * dpr, 0, 2 * Math.PI); ctx.fill(); }); };
  line(M.curve0, 'rgba(212,239,255,0.45)', 1, true); line(M.curveS, AM, 1.8); line(M.curveC, CY, 1.4);
  ctx.strokeStyle = INK; ctx.setLineDash([2 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(X(M.n), pt); ctx.lineTo(X(M.n), pt + ih); ctx.stroke(); ctx.setLineDash([]);
  [y0, (y0 + y1) / 2, y1].forEach((v) => lab(ctx, v.toFixed(2), pl - 4 * dpr, Y(v), 'right', 'middle'));
  [0, Math.round(M.nmax / 2), M.nmax].forEach((n, k) => lab(ctx, String(n), X(n), pt + ih + 4 * dpr, ['left', 'center', 'right'][k], 'top'));
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${AM}"></i>c* = (1, i)/√2</span><span class="it"><i class="sw" style="--c:${CY}"></i>${T('所选硬币', 'chosen coin')}</span><span class="it"><i class="sw" style="--c:${FAINT}"></i>|0⟩</span>`;
}
/* E_g along meridians θ ∈ [0, π]: the source's interpolation φ = π/2, and the chosen φ */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 34); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, [y0, y1] = yr([M.merStar, M.merSel]), X = (th) => pl + iw * th / Math.PI, Y = (v) => pt + ih * (1 - (v - y0) / (y1 - y0));
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt); ctx.lineTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  const line = (arr, col, lw) => { ctx.beginPath(); arr.forEach((v, k) => { const x = X(Math.PI * k / (MER - 1)); k ? ctx.lineTo(x, Y(v)) : ctx.moveTo(x, Y(v)); }); ctx.strokeStyle = col; ctx.lineWidth = lw * dpr; ctx.stroke(); };
  line(M.merSel, CY, 1.3); line(M.merStar, AM, 1.8);
  ctx.fillStyle = AM; ctx.beginPath(); ctx.arc(X(Math.PI / 2), Y(M.Es), 3.5 * dpr, 0, 2 * Math.PI); ctx.fill();
  ctx.strokeStyle = INK; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); ctx.arc(X(M.th), Y(M.Ec), 4 * dpr, 0, 2 * Math.PI); ctx.stroke();
  [y0, (y0 + y1) / 2, y1].forEach((v) => lab(ctx, v.toFixed(2), pl - 4 * dpr, Y(v), 'right', 'middle'));
  [[0, 'θ = 0 |0⟩'], [Math.PI / 2, 'π/2'], [Math.PI, 'π |1⟩']].forEach(([th, s], k) => lab(ctx, s, X(th), pt + ih + 4 * dpr, ['left', 'center', 'right'][k], 'top'));
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${AM}"></i>φ = π/2 (c_θ)</span><span class="it"><i class="sw" style="--c:${CY}"></i>φ = ${ang(M.ph)}</span><span class="it">· ${T(`第 ${M.n} 步`, `step ${M.n}`)}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const sci = (x) => (x < 1e-12 ? '< 10⁻¹²' : x.toExponential(1));
function readouts() {
  const M = MODEL, d = M.Es - M.Ec, a = SPHERE[M.sph.arg];
  pill('pillA', 'P', String(M.P)); pill('pillB', 'n', String(M.n)); pill('pillC', 'E_g(c*)', f4(M.Es)); pill('pillD', T('硬币', 'coin'), f4(M.Ec));
  setRo([
    [T('格点 P · 模数 2P · 第 n 步 · 硬币 (θ, φ)', 'Sites P · modes 2P · step n · coin (θ, φ)'), `${M.P} · ${2 * M.P} · ${M.n} · (${ang(M.th)}, ${ang(M.ph)})`],
    [T('E_g(硬币) · E_g(c*) · 差', 'E_g(coin) · E_g(c*) · difference'), `${f4(M.Ec)} · ${f4(M.Es)} · ${d >= -1e-12 ? '+' : '−'}${f4(Math.abs(d))}`],
    [T('反射对 (0, x)、(1, −x) 的最大不平衡：硬币 · c* · 对和之差', 'Largest reflection-pair imbalance (0, x), (1, −x): coin · c* · pair-sum difference'), `${f4(M.imbC)} · ${sci(M.imbS)} · ${sci(M.sumDiff)}`],
    [T(`球面上 ${NS} 个硬币的最大 E_g · 位置 (θ, φ)`, `Largest E_g over ${NS} coins of the sphere · at (θ, φ)`), `${f4(M.sph.max)} · (${a.th.toFixed(2)}, ${a.ph.toFixed(2)}) · ${M.sph.max <= M.Es + 1e-9 ? T('≤ c*', '≤ c*') : T('> c*！', '> c*!')}`],
    [T('总概率 · 最大的模概率', 'Total probability · largest mode probability'), `${M.norm.toFixed(12)} · ${f4(Math.max(...M.pc))}`]]);
  $('roNote').innerHTML = T(`Lean：对每个 P ≥ 1、每个 n 与每个单位硬币，E_g 不超过 c* 的值；这里 ${f4(M.Ec)} ≤ ${f4(M.Es)}。`, `Lean: for every P ≥ 1, every n and every unit coin, E_g is at most the value for c*; here ${f4(M.Ec)} ≤ ${f4(M.Es)}.`);
}
const stateKey = () => `${S.P}|${S.th}|${S.ph}|${S.nmax}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; }
  const M = MODEL;
  if (!toasted && S.playing && S.t >= 1) {
    toasted = true; const gap = Math.min(...M.curveS.map((v, k) => v - M.curveC[k])), ok = gap >= -1e-12;
    toast(ok ? T(`<b>${M.nmax + 1} 个时刻全部满足 E_g(硬币) ≤ E_g(c*)</b>，最小差 ${f4(Math.max(0, gap))}。`, `<b>All ${M.nmax + 1} times satisfy E_g(coin) ≤ E_g(c*)</b>; smallest gap ${f4(Math.max(0, gap))}.`)
      : T(`<b>有时刻 E_g(硬币) &gt; E_g(c*)</b>，差 ${f4(gap)}。`, `<b>Some time has E_g(coin) &gt; E_g(c*)</b>; gap ${f4(gap)}.`));
  }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('pIn').value = String(S.P); $('pOut').textContent = String(S.P);
  $('thIn').value = String(S.th); $('thOut').textContent = ang(S.th); $('phIn').value = String(S.ph); $('phOut').textContent = ang(S.ph);
  document.querySelectorAll('#coinChips .chip').forEach((b) => { const [th, ph] = COINS[b.dataset.coin]; b.setAttribute('aria-pressed', String(Math.abs(th - S.th) < 1e-9 && Math.abs(ph - S.ph) < 1e-9)); });
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T(`初始硬币 (cos θ/2, e^{iφ} sin θ/2) 放在格点 0；每一步先做 Hadamard，再把分量 0 左移、分量 1 右移（周期边界）。c* 是 θ = φ = π/2。`, `The initial coin (cos θ/2, e^{iφ} sin θ/2) sits at site 0; each step applies the Hadamard coin, then shifts component 0 left and component 1 right (periodic). c* is θ = φ = π/2.`);
  $('litNote').innerHTML = T('原文对试过的所有圆环大小和时刻都观察到 c* 最大；Lean 对所有 P ≥ 1 和所有 n 证明了它。', 'The source observed c* to be maximal for all circle sizes and times it tested; Lean proves it for every P ≥ 1 and every n.');
  $('c1Title').textContent = T('E_g 随时间：c* 始终在上', 'E_g over time: c* stays on top');
  $('c2Title').textContent = T('沿经线的 E_g（θ 从 |0⟩ 到 |1⟩）', 'E_g along meridians (θ from |0⟩ to |1⟩)');
  $('clock').innerHTML = `n = ${M.n}`;
  $('hudBig').textContent = `P = ${M.P} · n = ${M.n} · E_g = ${f4(M.Ec)} ≤ E_g(c*) = ${f4(M.Es)}`;
  $('hudSub').textContent = T('左：初始硬币的 Bloch 球，颜色是这一步的 E_g（越亮越大），琥珀点是 c* = (1, i)/√2，白线是所选硬币。右：圆环上的行走，青色是分量 0、品红是分量 1，柱高 ∝ √概率，白色短线是 c* 的值；地面上的弦连起反射对 (0, x)、(1, −x)', 'Left: the Bloch sphere of initial coins, coloured by E_g at this step (brighter is larger); the amber dot is c* = (1, i)/√2, the white line the chosen coin. Right: the walk on the circle, component 0 cyan and component 1 magenta, bar height ∝ √probability, white ticks for c*; chords on the floor join the reflection pairs (0, x), (1, −x)');
}
function syncRail() {
  const M = MODEL, key = `${M.nmax}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 'n = 0', 'first'], [1, `n = ${M.nmax}`, 'last']];
  $('marks').innerHTML = marks.map(([f, l, c]) => `<i class="${c}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
const COINS = { star: STAR, conj: [Math.PI / 2, -Math.PI / 2], zero: [0, 0], one: [Math.PI, 0], plus: [Math.PI / 2, 0] };
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { P: p.P, th: p.th, ph: p.ph, nmax: p.nmax, t: 0, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('pIn').addEventListener('input', () => { S.P = parseInt($('pIn').value, 10); custom(); });
$('thIn').addEventListener('input', () => { S.th = parseFloat($('thIn').value); custom(); });
$('phIn').addEventListener('input', () => { S.ph = parseFloat($('phIn').value); custom(); });
document.querySelectorAll('#coinChips .chip').forEach((b) => b.addEventListener('click', () => { [S.th, S.ph] = COINS[b.dataset.coin]; custom(); }));
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo((Math.round(S.t * S.nmax) + (ev.key === 'ArrowRight' ? 1 : -1)) / S.nmax); }
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
/* about 0.6 s per step at 1× */
const runSeconds = () => 0.6 * S.nmax;
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
    if (glKey !== `${MODEL.P}|${MODEL.n}|${MODEL.th}|${MODEL.ph}`) { updateGL(); glKey = `${MODEL.P}|${MODEL.n}|${MODEL.th}|${MODEL.ph}`; }
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
  info: () => { const M = MODEL; return { P: M.P, n: M.n, th: M.th, ph: M.ph, nmax: M.nmax, pc: [...M.pc], ps: [...M.ps], Ec: M.Ec, Es: M.Es, norm: M.norm, imbC: M.imbC, imbS: M.imbS, sumDiff: M.sumDiff,
    sphMax: M.sph.max, sphMin: M.sph.min, sphArg: [SPHERE[M.sph.arg].th, SPHERE[M.sph.arg].ph], curveC: [...M.curveC], curveS: [...M.curveS], curve0: [...M.curve0], merStar: [...M.merStar], merSel: [...M.merSel] }; },
  basis: (P, n) => { const b = basis(P, n); return { u: [...b.u], w: [...b.w] }; },
  probs: (P, n, th, ph) => [...probs(P, n, th, ph)],
  gW: (p) => gW(p),
  sphere: (P, n) => { const s = sphere(P, n); return { max: s.max, min: s.min, E: [...s.E], coins: SPHERE.map((q) => [q.th, q.ph]) }; },
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setT(0.5); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 10; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
