/* GRONWALL//EDGE · how close σ(n) comes to e^γ n log log n
   The Robin ratio R(n) = σ(n)/(e^γ n log log n). Frozen in trureturing: its upper limit is exactly 1, with primorial powers as
   the lower witnesses (Gronwall envelopes); a bounded exponent of a fixed prime p caps it eventually at 1 − p^(−A−1); and a zero
   of ζ with real part β > 1/2 makes the weighted theta tail u·e^((1−β)u)·f(u) exceed every c < m/(|ρ||ρ−1|) arbitrarily late.
   The page sieves σ(n) to 10⁶, evaluates primorial powers through sums of logarithms, and integrates the tail of one
   hypothetical zero pair. Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Constants
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG, ok: OK } = TRV.palette;
const GREEN = [0.27, 1, 0.7], WHITE = [0.8, 0.85, 0.9];
const MODES = ['layers', 'witness', 'echo'];
const RUN = { layers: 26, witness: 22, echo: 26 };
const EG = Math.exp(0.5772156649015329);
const NMAX = 1000000, BINS = 120, LAYERS = 7, LN3 = Math.log(3), LNN = Math.log(NMAX);
const PMAX = 1500000, A_LIST = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
const GAMMAS = [14.134725141734693, 21.022039638771555, 25.010857580145688];
const U0 = 2, U1 = 160, H = 0.01, WIN = 0.2, HALFW = 5;
const ECHO_BETAS = [0.5, 0.55, 0.6, 0.65, 0.7, 0.75, 0.8, 0.85, 0.9, 0.95];
const SUP = '⁰¹²³⁴⁵⁶⁷⁸⁹', sup = (k) => String(k).split('').map((d) => SUP[+d]).join('');

/* =====================================================================
   2. Arithmetic
   ===================================================================== */
let SIG = null;
const robin = (n) => SIG[n] / (EG * n * Math.log(Math.log(n)));
const vp = (n, p) => { let k = 0; while (n % p === 0) { n /= p; k++; } return k; };
const binOf = (n) => Math.min(BINS - 1, Math.max(0, Math.floor((Math.log(n) - LN3) / (LNN - LN3) * BINS)));
const cap = (p, v) => 1 - Math.pow(p, -(v + 1));
let LAYER_DATA = null;
function sieveSigma() {
  if (SIG) return;
  SIG = new Float64Array(NMAX + 1);
  for (let d = 1; d <= NMAX; d++) for (let m = d; m <= NMAX; m += d) SIG[m] += d;
  const env = new Float64Array(BINS).fill(-1), lo = new Int32Array(BINS), hi = new Int32Array(BINS), layer = {};
  for (const p of [2, 3, 5]) layer[p] = new Float64Array(LAYERS * BINS).fill(-1);
  const viol = [], top = [], records = [];
  let best = 0;
  for (let n = 3; n <= NMAX; n++) {
    const r = robin(n), b = binOf(n);
    if (!lo[b]) lo[b] = n; hi[b] = n;
    if (r > env[b]) env[b] = r;
    for (const p of [2, 3, 5]) { const k = Math.min(LAYERS - 1, vp(n, p)), i = k * BINS + b; if (r > layer[p][i]) layer[p][i] = r; }
    if (n <= 5040 && r >= 1) viol.push(n);
    if (n > 5040) { if (r >= 0.95) top.push(n); if (r > best) { best = r; records.push([n, r]); } }
  }
  LAYER_DATA = { env, lo, hi, layer, viol, top, records };
}
let PRIMES = null, WIT = null, ZINV = null;
function sievePrimes() {
  if (PRIMES) return;
  const c = new Uint8Array(PMAX + 1), P = [];
  for (let i = 2; i <= PMAX; i++) if (!c[i]) { P.push(i); for (let j = i * i; j <= PMAX; j += i) c[j] = 1; }
  PRIMES = Int32Array.from(P);
  const K = PRIMES.length, theta = new Float64Array(K + 1);
  for (let k = 1; k <= K; k++) theta[k] = theta[k - 1] + Math.log(PRIMES[k - 1]);
  WIT = { K, theta, R: {}, lsig: {} };
  for (const a of A_LIST) {   // R((p_k#)^a) = exp(Σ log((1 − p^(−a−1))/(1 − 1/p))) / (e^γ log(a·θ(p_k)))
    const R = new Float64Array(K + 1), ls = new Float64Array(K + 1); let s = 0;
    for (let k = 1; k <= K; k++) { const p = PRIMES[k - 1]; s += Math.log1p(-Math.pow(p, -(a + 1))) - Math.log1p(-1 / p); ls[k] = s; const ll = Math.log(a * theta[k]); R[k] = ll > 0 ? Math.exp(s) / (EG * ll) : NaN; }
    WIT.R[a] = R; WIT.lsig[a] = ls;
  }
  ZINV = {};
  for (const a of A_LIST) { const s = a + 1, M = 2000; let z = 0; for (let n = 1; n < M; n++) z += Math.pow(n, -s); z += Math.pow(M, 1 - s) / (s - 1) + 0.5 * Math.pow(M, -s) + s * Math.pow(M, -s - 1) / 12; ZINV[a] = 1 / z; }
}
const KS = (K) => { const out = []; for (let i = 0; i <= 150; i++) { const k = Math.round(Math.exp(Math.log(2) + i / 150 * (Math.log(K) - Math.log(2)))); if (!out.length || k > out[out.length - 1]) out.push(k); } return out; };

/* the weighted tail of one hypothetical zero pair: f(u) = 2m ∫_u^∞ Re(e^((ρ−1)v)/ρ)·(v + 1)/v² dv (Simpson, backwards) */
function tailOf(beta, gamma, m) {
  const d = beta * beta + gamma * gamma, vEnd = U1 + 40 / (1 - beta), n = Math.ceil((vEnd - 1) / H);
  const g = (v) => 2 * m * Math.exp((beta - 1) * v) * (beta * Math.cos(gamma * v) + gamma * Math.sin(gamma * v)) / d * (v + 1) / (v * v);
  const f = new Float64Array(n + 1); let acc = 0, g1 = g(1 + n * H);
  for (let i = n; i > 0; i--) { const v1 = 1 + i * H, v0 = v1 - H, g0 = g(v0); acc += (g0 + 4 * g(v0 + H / 2) + g1) * H / 6; f[i - 1] = acc; g1 = g0; }
  return f;   // f[i] = f(1 + i·H)
}
const fIdx = (u) => Math.round((u - 1) / H);
const envelope = (u) => 7 * Math.exp(-u / 2);
function windowMax(f) { const out = [], w = Math.round(WIN / H); for (let i = fIdx(U0); i + w <= f.length && 1 + i * H < U1; i += w) { let mx = 0; for (let j = i; j < i + w; j++) mx = Math.max(mx, Math.abs(f[j])); out.push([1 + i * H, mx]); } return out; }   // max |f| over windows of length 0.2
const cstarOf = (beta, gamma, m) => m / (Math.hypot(beta, gamma) * Math.hypot(beta - 1, gamma));
function crossing(f) { for (let i = fIdx(3); i < f.length && 1 + i * H <= U1; i++) { const u = 1 + i * H; if (Math.abs(f[i]) > envelope(u)) return u; } return null; }

/* =====================================================================
   3. State and presets
   ===================================================================== */
const S = { mode: 'layers', p: 2, a: 5, beta: 0.75, g: 0, m: 1, nowFrac: 0, playing: true, dir: 1, speed: 1, hold: 0, preset: 'edge' };
const PRESETS = {
  edge: { mode: 'layers', p: 2, frac: 0, play: true,
    zh: 'Robin 比值 R(n) = σ(n)/(e^γ n log log n)。三维里每一层是 2 的指数 v₂(n) 相同的数，折线是这一层在每一小段 log n 里的最大值。所有层都压在 R = 1 这条绿线下面慢慢往上爬：Gronwall 证明 R(n) 的上极限恰好是 1（已冻结）。',
    en: 'The Robin ratio R(n) = σ(n)/(e^γ n log log n). Each layer in 3D holds the numbers with the same exponent of 2, v₂(n), and its polyline is the layer’s maximum over each short stretch of log n. Every layer creeps up under the green line R = 1: Gronwall proved that the upper limit of R(n) is exactly 1 (frozen).' },
  violations: { mode: 'layers', p: 2, cutN: 5040, play: false,
    zh: 'n ≤ 5040 时有 26 个数使 R(n) ≥ 1（品红点），最大的是 5040。Robin（1984）证明：黎曼猜想成立当且仅当 5040 之后再没有这样的数。页面在 10⁶ 以内没有找到；这只是数值，不是证明。',
    en: 'For n ≤ 5040, 26 numbers have R(n) ≥ 1 (magenta dots); the largest is 5040. Robin (1984) proved that the Riemann hypothesis holds exactly when no such number appears after 5040. The page finds none up to 10⁶; that is numerics, not a proof.' },
  odd: { mode: 'layers', p: 2, frac: 1, play: false,
    zh: '只看 2 的指数不超过 A 的数：本库证明（已冻结）它们的 R(n) 最终不超过 1 − 2^(−A−1) + ε，例如奇数（A = 0）最终不超过 1/2 + ε。绿色短线是各层的上限，右下图把每层在最后一个十倍区间里的最大值和上限并排比较。收敛极慢：10⁶ 以内有的层还在上限之上。',
    en: 'Keep only the numbers whose exponent of 2 is at most A: this library proves (frozen) that their R(n) eventually stays below 1 − 2^(−A−1) + ε; odd numbers (A = 0), for example, eventually stay below 1/2 + ε. The short green lines are the caps of the layers, and the lower right chart sets each layer’s maximum over the last factor of ten beside its cap. Convergence is very slow: up to 10⁶ some layers are still above their caps.' },
  three: { mode: 'layers', p: 3, frac: 1, play: false,
    zh: '换成 p = 3：3 的指数为 0 的数，上限是 1 − 1/3 = 2/3；指数为 1 的是 8/9；指数越高上限越接近 1。',
    en: 'Switch to p = 3: numbers not divisible by 3 have cap 1 − 1/3 = 2/3, those with exponent 1 have 8/9, and the caps approach 1 as the exponent grows.' },
  primorial: { mode: 'witness', a: 5, frac: 0, play: true,
    zh: '素数阶乘的幂 n = (2·3·5·…·p_k)^a。σ(n)/n = ∏ (1 − p^(−a−1))/(1 − 1/p)；固定 a、k → ∞ 时 R(n) 趋于 1/ζ(a + 1)，a 变大时 1/ζ(a + 1) → 1。这就是 Gronwall 下包络的证人（已冻结：对每个 ε 有任意大的素数阶乘的幂使 R(n) ≥ 1 − ε）。收敛按 log 的速度，很慢。',
    en: 'Primorial powers n = (2·3·5·…·p_k)^a. Here σ(n)/n = ∏ (1 − p^(−a−1))/(1 − 1/p); with a fixed and k → ∞, R(n) tends to 1/ζ(a + 1), and 1/ζ(a + 1) → 1 as a grows. These are the witnesses of the lower Gronwall envelope (frozen: for every ε there are arbitrarily large primorial powers with R(n) ≥ 1 − ε). Convergence runs at a logarithmic pace, slowly.' },
  zeta: { mode: 'witness', a: 1, frac: 1, play: false,
    zh: 'a = 1：n 是素数阶乘本身。∏ (1 − p^(−2)) = 1/ζ(2) = 6/π² ≈ 0.6079，所以 R(n) 停在约 0.608，远离 1。要逼近 1，指数 a 也必须变大。',
    en: 'a = 1: n is a primorial itself. Since ∏ (1 − p^(−2)) = 1/ζ(2) = 6/π² ≈ 0.6079, R(n) settles near 0.608, far from 1. To approach 1, the exponent a must grow too.' },
  echo75: { mode: 'echo', beta: 0.75, g: 0, m: 1, frac: 0, play: true,
    zh: '假想 ζ 在 ρ = 0.75 + 14.13i 有一个零点（真实的第一个零点在临界线上，这是反事实）。按 Lean 的定义取 θ(x) − x 的加权尾项 f(u)；冻结定理说，只要有实部大于 1/2 的零点，u·e^((1−β)u)·f(u) 就会在任意晚的地方超过任何小于 m/(|ρ||ρ − 1|) 的数（左下图的绿线）。页面只放这一对零点来画这个机制。',
    en: 'Suppose ζ had a zero at ρ = 0.75 + 14.13i (the actual first zero lies on the critical line; this is a counterfactual). Take the weighted tail f(u) of θ(x) − x as defined in Lean; the frozen theorem says that, given a zero with real part above 1/2, u·e^((1−β)u)·f(u) exceeds every number below m/(|ρ||ρ − 1|) arbitrarily late (the green lines in the lower left chart). The page keeps this one zero pair to draw the mechanism.' },
  echo60: { mode: 'echo', beta: 0.6, g: 0, m: 1, frac: 1, play: false,
    zh: 'β = 0.6：零点离临界线越近，尾项比 e^(−u/2) 衰减得慢得越少，越过 7e^(−u/2) 也就越晚（右下图）。把这种越过变成真实的 Robin 反例，还需要一座尚未建成的算术桥。',
    en: 'β = 0.6: the closer the zero is to the critical line, the less slowly the tail decays compared with e^(−u/2), and the later it crosses 7e^(−u/2) (lower right chart). Turning such a crossing into an actual Robin violation needs an arithmetic bridge that has not been built.' }
};

/* =====================================================================
   4. The model
   ===================================================================== */
let MODEL = null, dirty = true;
const tailCache = new Map();
function tailCached(beta, gamma, m) { const key = `${beta.toFixed(3)}|${gamma}|${m}`; if (!tailCache.has(key)) { if (tailCache.size > 24) tailCache.clear(); tailCache.set(key, tailOf(beta, gamma, m)); } return tailCache.get(key); }
function build() {
  const M = { mode: S.mode };
  if (S.mode === 'layers') { sieveSigma(); Object.assign(M, { p: S.p, D: LAYER_DATA }); }
  else if (S.mode === 'witness') { sievePrimes(); Object.assign(M, { a: S.a, K: WIT.K, ks: KS(WIT.K) }); }
  else {
    const gamma = GAMMAS[S.g], f = tailCached(S.beta, gamma, S.m), cst = cstarOf(S.beta, gamma, S.m);
    const layers = ECHO_BETAS.map((b) => ({ beta: b, f: tailCached(b, gamma, S.m) }));
    const peaks = []; let up = false;
    for (let i = fIdx(U0); 1 + i * H <= U1; i++) { const u = 1 + i * H, nv = u * Math.exp((1 - S.beta) * u) * f[i]; if (nv > cst && !up) { up = true; peaks.push(u); } else if (nv < cst) up = false; }
    Object.assign(M, { beta: S.beta, gamma, m: S.m, f, cstar: cst, cross: crossing(f), layers, peaks });
  }
  MODEL = M;
}
function progress() {
  const M = MODEL;
  if (M.mode === 'layers') {
    const D = M.D; let b = Math.min(BINS - 1, Math.floor(S.nowFrac * BINS)); while (b > 0 && !D.hi[b]) b--;
    const nCut = D.hi[b];
    const viol = D.viol.filter((n) => n <= nCut), recs = D.records.filter(([n]) => n <= nCut), best = recs.length ? recs[recs.length - 1] : null;
    let bLo = b; for (let c = b - 1; c >= 0; c--) { if (!D.lo[c]) continue; if (D.lo[c] > nCut / 10) bLo = c; else break; }
    const decade = []; for (let v = 0; v < LAYERS; v++) { let mx = -1; for (let k = bLo; k <= b; k++) mx = Math.max(mx, D.layer[M.p][v * BINS + k]); decade.push(mx); }
    return { b, nCut, viol, best, bLo, nLo: D.lo[bLo], decade };
  }
  if (M.mode === 'witness') { const k = Math.max(2, Math.min(M.K, Math.round(Math.exp(S.nowFrac * Math.log(M.K))))); return { k, pk: PRIMES[k - 1], R: A_LIST.map((a) => WIT.R[a][k]), log10n: M.a * WIT.theta[k] / Math.LN10 }; }
  const u = U0 + S.nowFrac * (U1 - U0), i = fIdx(u), f = M.f[i];
  const lo = Math.max(U0, Math.min(U1 - 2 * HALFW, u - HALFW)), hi = lo + 2 * HALFW;
  return { u, f, norm: u * Math.exp((1 - M.beta) * u) * f, env: envelope(u), lo, hi, wpeaks: M.peaks.filter((x) => x >= lo && x <= hi) };
}

/* =====================================================================
   5. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const layerCol = (v) => { const t = v / (LAYERS - 1); return [COL.cyan[0] * (1 - t) + COL.magenta[0] * t, COL.cyan[1] * (1 - t) + COL.magenta[1] * t, COL.cyan[2] * (1 - t) + COL.magenta[2] * t]; };
const fmtN = (n) => n.toLocaleString('en-US');
const sci = (x, d = 3) => { if (!isFinite(x) || x === 0) return String(x); const e = Math.floor(Math.log10(Math.abs(x))); return Math.abs(e) < 4 ? x.toFixed(Math.max(0, d - e)) : `${(x / Math.pow(10, e)).toFixed(d)}·10${e < 0 ? '⁻' : ''}${sup(Math.abs(e))}`; };

/* =====================================================================
   6. 3D scene
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 120000, PTS_MAX = 1600;
const CAMS = { iso: [0.62, 1.12, 19], front: [0.0001, 1.5, 18], side: [1.5707, 1.32, 18] };
const cam = { theta: 0.62, phi: 1.12, r: 19, tTheta: 0.62, tPhi: 1.12, tR: 19 };
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
const YR = (r) => Math.max(0, (Math.min(1.3, r) - 0.4) * 6.5);         // ratio height, clipped above 1.3 (tiny n blow up)
const XL = (n) => ((Math.log(n) - LN3) / (LNN - LN3) - 0.5) * 12;        // log n across
const ZL = (v) => (v - 3) * 1.15;                                       // layer depth
const XK = (k, K) => (Math.log(k) / Math.log(K) - 0.5) * 12;
const ZA = (a) => (a - 5.5) * 0.85;
const XU = (u) => ((u - U0) / (U1 - U0) - 0.5) * 12;
const ZB = (b) => (b - 0.725) / 0.45 * 7;
const YL = (l) => Math.max(0, (l + 36) * 0.13);
function updateGL() {
  const M = MODEL, pr = progress();
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (a, b, col, k) => { if (v + 2 > LINES_MAX) return; for (const p of [a, b]) { Pp[3 * v] = p[0]; Pp[3 * v + 1] = p[1]; Pp[3 * v + 2] = p[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, a, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = a; PT.aSize.array[np] = size; np++; };
  const dash = (a, b, col, k, n = 24) => { for (let i = 0; i < n; i += 2) seg(a.map((x, j) => x + (b[j] - x) * i / n), a.map((x, j) => x + (b[j] - x) * (i + 1) / n), col, k); };
  if (M.mode === 'layers') {
    const D = M.D, x0 = XL(3), x1 = XL(NMAX);
    for (let L = 0; L < LAYERS; L++) {
      const z = ZL(L), col = layerCol(L);
      seg([x0, 0, z], [x1, 0, z], COL.cyan, 0.08);
      seg([x0, YR(1), z], [x1, YR(1), z], GREEN, 0.35);
      dash([x0, YR(cap(M.p, L)), z], [x1, YR(cap(M.p, L)), z], GREEN, 0.75, 40);
      let prev = null;
      for (let b = 0; b <= pr.b; b++) { const r = D.layer[M.p][L * BINS + b]; if (r < 0) continue; const x = XL(D.lo[b]), q = [x, YR(r), z]; if (prev) seg(prev, q, col, 0.95); prev = q; }
    }
    for (const n of D.viol) if (n <= pr.nCut) dot([XL(n), YR(robin(n)), ZL(Math.min(LAYERS - 1, vp(n, M.p)))], COL.magenta, 1, 1.7);
    for (const n of D.top) if (n <= pr.nCut) dot([XL(n), YR(robin(n)), ZL(Math.min(LAYERS - 1, vp(n, M.p)))], COL.cyan, 0.8, 1.0);
    const xc = XL(pr.nCut); seg([xc, 0, ZL(0) - 0.6], [xc, 0, ZL(LAYERS - 1) + 0.6], COL.amber, 0.8); seg([xc, 0, ZL(0) - 0.6], [xc, YR(1.05), ZL(0) - 0.6], COL.amber, 0.5);
    if (pr.best) dot([XL(pr.best[0]), YR(pr.best[1]), ZL(Math.min(LAYERS - 1, vp(pr.best[0], M.p)))], COL.amber, 1, 2.6);
  } else if (M.mode === 'witness') {
    const K = M.K, ks = M.ks;
    for (const a of A_LIST) {
      const z = ZA(a), sel = a === M.a, col = sel ? COL.amber : COL.cyan, R = WIT.R[a]; let prev = null;
      for (const k of ks) { if (k > pr.k) break; const r = R[k]; if (!isFinite(r)) continue; const q = [XK(k, K), YR(Math.min(1.25, r)), z]; if (prev) seg(prev, q, r > 1 ? COL.magenta : col, sel ? 1 : 0.55); prev = q; }
      seg([XK(2, K), YR(1), z], [XK(K, K), YR(1), z], GREEN, 0.3);
      dash([XK(K, K) - 1.6, YR(ZINV[a]), z], [XK(K, K) + 0.3, YR(ZINV[a]), z], WHITE, 0.7, 8);
    }
    ks.forEach((k, i) => { if (i % 15 || k > pr.k) return; let prev = null; for (const a of A_LIST) { const r = WIT.R[a][k]; if (!isFinite(r)) continue; const q = [XK(k, K), YR(Math.min(1.25, r)), ZA(a)]; if (prev) seg(prev, q, COL.cyan, 0.25); prev = q; } });
    const xc = XK(pr.k, K); seg([xc, 0, ZA(1) - 0.5], [xc, 0, ZA(10) + 0.5], COL.amber, 0.8);
    A_LIST.forEach((a, i) => { const r = pr.R[i]; if (isFinite(r)) dot([xc, YR(Math.min(1.25, r)), ZA(a)], a === M.a ? COL.amber : COL.cyan, a === M.a ? 1 : 0.6, a === M.a ? 2.4 : 1.3); });
  } else {
    const drawLayer = (beta, f, col, k) => { let prev = null; for (const [u, mx] of windowMax(f)) { const q = [XU(u), YL(Math.log10(mx || 1e-300)), ZB(beta)]; if (prev) seg(prev, q, col, k); prev = q; } };
    for (const L of M.layers) {
      const sel = Math.abs(L.beta - M.beta) < 1e-9; if (sel) continue;
      drawLayer(L.beta, L.f, L.beta === 0.5 ? COL.cyan : COL.magenta, L.beta === 0.5 ? 0.7 : 0.4);
      dash([XU(U0), YL(Math.log10(envelope(U0))), ZB(L.beta)], [XU(U1), YL(Math.log10(envelope(U1))), ZB(L.beta)], WHITE, 0.35, 30);
      const c = crossing(L.f); if (c) dot([XU(c), YL(Math.log10(envelope(c))), ZB(L.beta)], COL.magenta, 0.9, 1.6);
    }
    drawLayer(M.beta, M.f, COL.amber, 1);
    dash([XU(U0), YL(Math.log10(envelope(U0))), ZB(M.beta)], [XU(U1), YL(Math.log10(envelope(U1))), ZB(M.beta)], WHITE, 0.8, 30);
    if (M.cross) dot([XU(M.cross), YL(Math.log10(envelope(M.cross))), ZB(M.beta)], COL.amber, 1, 2.6);
    const xc = XU(pr.u); seg([xc, 0, ZB(0.5) - 0.6], [xc, 0, ZB(0.95) + 0.6], COL.amber, 0.8);
    dot([xc, YL(Math.max(Math.log10(Math.abs(pr.f) || 1e-300), Math.log10(pr.env) - 8)), ZB(M.beta)], COL.amber, 1, 2.2);
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
  camera.up.set(0, 1, 0); camera.lookAt(0, 2, 0);
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
  const w = el.offsetWidth, W = stage.clientWidth, x = Math.min(W - w / 2 - 6, Math.max(w / 2 + 6, q.x));
  el.style.left = x + 'px'; el.style.top = q.y + 'px';
}
function updateTags() {
  const M = MODEL, pr = progress(); let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  if (M.mode === 'layers') {
    for (const L of [0, 2, 4, 6]) put(`v${['₂', '₃', '₅'][[2, 3, 5].indexOf(M.p)]} = ${L}${L === LAYERS - 1 ? '+' : ''}`, [XL(3) - 1.1, 0.2, ZL(L)], 'cy');
    put('R = 1', [XL(NMAX) + 1, YR(1), ZL(0)], 'gn');
    put(`1 − ${M.p}⁻¹`, [XL(NMAX) + 1.1, YR(cap(M.p, 0)), ZL(0)], 'gn');
    put(`n = ${fmtN(pr.nCut)}`, [XL(pr.nCut), -0.4, ZL(0) - 0.8], 'hot');
    put('n = 3', [XL(3), -0.4, ZL(LAYERS - 1) + 0.9], 'cy'); put('n = 10⁶', [XL(NMAX), -0.4, ZL(LAYERS - 1) + 0.9], 'cy');
  } else if (M.mode === 'witness') {
    for (const a of [1, 5, 10]) put(`a = ${a}`, [XK(2, M.K) - 1, 0.2, ZA(a)], a === M.a ? 'hot' : 'cy');
    put('R = 1', [XK(M.K, M.K) + 1, YR(1), ZA(10)], 'gn');
    put('1/ζ(a+1)', [XK(M.K, M.K) + 1.4, YR(ZINV[1]), ZA(1)], 'cy');
    put(`k = ${fmtN(pr.k)}`, [XK(pr.k, M.K), -0.4, ZA(1) - 0.8], 'hot');
  } else {
    put('β = 0.50', [XU(U0) - 1.2, 0.2, ZB(0.5)], 'cy'); put('β = 0.95', [XU(U0) - 1.2, 0.2, ZB(0.95)], 'cy');
    put(`β = ${M.beta.toFixed(2)}`, [XU(U1) + 1, YL(Math.log10(envelope(U1))) + 0.6, ZB(M.beta)], 'hot');
    put('7e^(−u/2)', [XU(U0) + 0.4, YL(Math.log10(envelope(U0))) + 0.5, ZB(0.95) + 0.6], 'cy');
    put(`u = ${pr.u.toFixed(1)}`, [XU(pr.u), -0.4, ZB(0.5) - 0.8], 'hot');
  }
  for (let i = k; i < tagPool.length; i++) tagPool[i].style.display = 'none';
}

/* =====================================================================
   9. 2D panels
   ===================================================================== */
function frame2d(cv, pl0 = 46) {
  const dpr = fitCanvas(cv), ctx = cv.getContext('2d'), Wd = cv.width, Hh = cv.height;
  ctx.clearRect(0, 0, Wd, Hh);
  const pl = pl0 * dpr, pr = 12 * dpr, pt = 10 * dpr, pb = 20 * dpr;
  ctx.font = `${9.5 * dpr}px ${TRV.fonts.data}`;
  return { dpr, ctx, W: Wd, Hh, pl, pt, iw: Wd - pl - pr, ih: Hh - pt - pb };
}
function hline(F, y, color, dashed) { const { ctx, dpr, pl, iw } = F; ctx.strokeStyle = color; ctx.lineWidth = 1; ctx.setLineDash(dashed ? [4 * dpr, 3 * dpr] : []); ctx.beginPath(); ctx.moveTo(pl, y); ctx.lineTo(pl + iw, y); ctx.stroke(); ctx.setLineDash([]); }
function axisText(F, rows) { const { ctx, dpr } = F; ctx.fillStyle = DIM; for (const [txt, x, y, al, bl] of rows) { ctx.textAlign = al; ctx.textBaseline = bl; ctx.fillText(txt, x, y); } void dpr; }
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 40); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress();
  if (M.mode === 'layers') {
    const D = M.D, lx0 = Math.log10(3), lx1 = 6, X = (n) => pl + iw * (Math.log10(n) - lx0) / (lx1 - lx0), Y = (r) => pt + ih - ih * (Math.min(1.2, Math.max(0.3, r)) - 0.3) / 0.9;
    hline(F, Y(1), OK);
    ctx.strokeStyle = CY; ctx.lineWidth = 1.4 * dpr; ctx.beginPath(); let first = true;
    for (let b = 0; b <= pr.b; b++) { if (D.env[b] < 0) continue; const x = X(D.lo[b]), y = Y(D.env[b]); if (first) { ctx.moveTo(x, y); first = false; } else ctx.lineTo(x, y); } ctx.stroke(); ctx.lineWidth = 1;
    ctx.fillStyle = MG; for (const n of pr.viol) { ctx.beginPath(); ctx.arc(X(n), Y(robin(n)), 2.6 * dpr, 0, 2 * Math.PI); ctx.fill(); }
    if (pr.best) { ctx.fillStyle = AM; ctx.beginPath(); ctx.arc(X(pr.best[0]), Y(pr.best[1]), 3.4 * dpr, 0, 2 * Math.PI); ctx.fill(); }
    ctx.strokeStyle = AM; ctx.beginPath(); ctx.moveTo(X(pr.nCut), pt); ctx.lineTo(X(pr.nCut), pt + ih); ctx.stroke();
    ctx.strokeStyle = FAINT; ctx.setLineDash([2 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(X(5040), pt); ctx.lineTo(X(5040), pt + ih); ctx.stroke(); ctx.setLineDash([]);
    axisText(F, [['1', pl - 4 * dpr, Y(1), 'right', 'middle'], ['0.3', pl - 4 * dpr, pt + ih, 'right', 'middle'], ['1.2', pl - 4 * dpr, pt, 'right', 'top'], ['n=3', X(3), pt + ih + 4 * dpr, 'left', 'top'], ['5040', X(5040), pt + ih + 4 * dpr, 'center', 'top'], ['10⁶', X(NMAX), pt + ih + 4 * dpr, 'right', 'top']]);
    $('c1Meta').textContent = T('青 = 每段 log n 里的最大 R(n) · 品红 = R ≥ 1 · 绿 = 1 · 琥珀 = 5040 之后的最大值', 'cyan = the largest R(n) in each stretch of log n · magenta = R ≥ 1 · green = 1 · amber = the largest after 5040');
  } else if (M.mode === 'witness') {
    const K = M.K, lx1 = Math.log10(K), X = (k) => pl + iw * Math.log10(k) / lx1, Y = (r) => pt + ih - ih * (Math.min(1.3, Math.max(0.4, r)) - 0.4) / 0.9, R = WIT.R[M.a];
    hline(F, Y(1), OK); hline(F, Y(ZINV[M.a]), DIM, true);
    ctx.strokeStyle = CY; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); let first = true;
    for (const k of M.ks) { if (!isFinite(R[k])) continue; const x = X(k), y = Y(R[k]); if (first) { ctx.moveTo(x, y); first = false; } else ctx.lineTo(x, y); } ctx.stroke(); ctx.lineWidth = 1;
    ctx.fillStyle = MG; for (const k of M.ks) if (R[k] > 1) { ctx.beginPath(); ctx.arc(X(k), Y(R[k]), 2.4 * dpr, 0, 2 * Math.PI); ctx.fill(); }
    const r = R[pr.k]; ctx.strokeStyle = AM; ctx.beginPath(); ctx.moveTo(X(pr.k), pt); ctx.lineTo(X(pr.k), pt + ih); ctx.stroke();
    if (isFinite(r)) { ctx.fillStyle = AM; ctx.beginPath(); ctx.arc(X(pr.k), Y(r), 3.4 * dpr, 0, 2 * Math.PI); ctx.fill(); }
    axisText(F, [['1', pl - 4 * dpr, Y(1), 'right', 'middle'], ['0.4', pl - 4 * dpr, pt + ih, 'right', 'middle'], ['k=1', X(1), pt + ih + 4 * dpr, 'left', 'top'], ['k=100', X(100), pt + ih + 4 * dpr, 'center', 'top'], [`k=${fmtN(K)}`, X(K), pt + ih + 4 * dpr, 'right', 'top']]);
    $('c1Meta').textContent = T(`青 = R((p_k#)^${M.a}) · 虚线 = 1/ζ(${M.a + 1}) = ${ZINV[M.a].toFixed(4)} · 绿 = 1`, `cyan = R((p_k#)^${M.a}) · dashes = 1/ζ(${M.a + 1}) = ${ZINV[M.a].toFixed(4)} · green = 1`);
  } else {
    const c = M.cstar, top = 3 * c, X = (u) => pl + iw * (u - pr.lo) / (pr.hi - pr.lo), Y = (y) => pt + ih / 2 - (ih / 2) * Math.max(-1, Math.min(1, y / top));
    hline(F, Y(c), OK); hline(F, Y(-c), OK); hline(F, Y(2 * c), DIM, true); hline(F, Y(-2 * c), DIM, true); hline(F, Y(0), FAINT);
    ctx.strokeStyle = CY; ctx.lineWidth = 1.2 * dpr; ctx.beginPath();
    for (let i = fIdx(pr.lo), first = true; 1 + i * H <= pr.hi + 1e-9; i++) { const u = 1 + i * H, y = Y(u * Math.exp((1 - M.beta) * u) * M.f[i]); if (first) { ctx.moveTo(X(u), y); first = false; } else ctx.lineTo(X(u), y); }
    ctx.stroke(); ctx.lineWidth = 1;
    ctx.fillStyle = MG; for (const u of pr.wpeaks) { ctx.beginPath(); ctx.arc(X(u), Y(c), 2.2 * dpr, 0, 2 * Math.PI); ctx.fill(); }
    ctx.strokeStyle = AM; ctx.beginPath(); ctx.moveTo(X(pr.u), pt); ctx.lineTo(X(pr.u), pt + ih); ctx.stroke();
    axisText(F, [['+c*', pl - 4 * dpr, Y(c), 'right', 'middle'], ['−c*', pl - 4 * dpr, Y(-c), 'right', 'middle'], [`u=${pr.lo.toFixed(1)}`, X(pr.lo), pt + ih + 4 * dpr, 'left', 'top'], [`u=${pr.hi.toFixed(1)}`, X(pr.hi), pt + ih + 4 * dpr, 'right', 'top']]);
    $('c1Meta').textContent = T(`青 = u·e^((1−β)u)·f(u) · 绿 = ±c*（定理的门槛）· 虚线 = ±2c*（模型的振幅）`, `cyan = u·e^((1−β)u)·f(u) · green = ±c* (the theorem’s threshold) · dashes = ±2c* (the model’s amplitude)`);
  }
}
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 30); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, pr = progress();
  if (M.mode === 'layers') {
    const w = iw / LAYERS, Y = (r) => pt + ih - ih * Math.max(0, Math.min(1.1, r) - 0.3) / 0.8;
    hline(F, Y(1), OK);
    pr.decade.forEach((r, L) => {
      const x = pl + L * w, c = cap(M.p, L), col = layerCol(L);
      if (r > 0) { ctx.fillStyle = `rgba(${col.map((t) => Math.round(t * 255)).join(',')}, ${r > c ? 0.85 : 0.5})`; ctx.fillRect(x + 5 * dpr, Y(r), w - 10 * dpr, pt + ih - Y(r)); }
      ctx.strokeStyle = OK; ctx.lineWidth = 2 * dpr; ctx.beginPath(); ctx.moveTo(x + 2 * dpr, Y(c)); ctx.lineTo(x + w - 2 * dpr, Y(c)); ctx.stroke(); ctx.lineWidth = 1;
      ctx.fillStyle = DIM; ctx.textAlign = 'center'; ctx.textBaseline = 'top'; ctx.fillText(L === LAYERS - 1 ? `${L}+` : String(L), x + w / 2, pt + ih + 4 * dpr);
    });
    $('c2Meta').textContent = T(`每层 v${['₂', '₃', '₅'][[2, 3, 5].indexOf(M.p)]} 在 [${fmtN(pr.nLo)}, ${fmtN(pr.nCut)}] 的最大 R · 绿 = 上限 1 − ${M.p}^(−v−1)`, `each layer’s largest R on [${fmtN(pr.nLo)}, ${fmtN(pr.nCut)}] · green = cap 1 − ${M.p}^(−v−1)`);
  } else if (M.mode === 'witness') {
    const n = A_LIST.length, w = iw / n, Y = (r) => pt + ih - ih * Math.max(0, Math.min(1.25, r) - 0.4) / 0.85;
    hline(F, Y(1), OK);
    A_LIST.forEach((a, i) => {
      const r = pr.R[i], x = pl + i * w;
      if (isFinite(r)) { ctx.fillStyle = a === M.a ? 'rgba(255, 200, 61, 0.85)' : r > 1 ? 'rgba(255, 79, 216, 0.7)' : 'rgba(25, 224, 255, 0.5)'; ctx.fillRect(x + 4 * dpr, Y(r), w - 8 * dpr, pt + ih - Y(r)); }
      ctx.strokeStyle = INK; ctx.setLineDash([3 * dpr, 2 * dpr]); ctx.beginPath(); ctx.moveTo(x + 2 * dpr, Y(ZINV[a])); ctx.lineTo(x + w - 2 * dpr, Y(ZINV[a])); ctx.stroke(); ctx.setLineDash([]);
      ctx.fillStyle = DIM; ctx.textAlign = 'center'; ctx.textBaseline = 'top'; ctx.fillText(`a=${a}`, x + w / 2, pt + ih + 4 * dpr);
    });
    $('c2Meta').textContent = T(`k = ${fmtN(pr.k)} 时各个 a 的 R · 白虚线 = 1/ζ(a + 1)`, `R for each a at k = ${fmtN(pr.k)} · white dashes = 1/ζ(a + 1)`);
  } else {
    const X = (u) => pl + iw * (u - U0) / (U1 - U0), l0 = Math.log10(envelope(U1)) - 6, l1 = 1.5, Y = (l) => pt + ih - ih * (Math.max(l0, Math.min(l1, l)) - l0) / (l1 - l0);
    ctx.strokeStyle = DIM; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.beginPath(); ctx.moveTo(X(U0), Y(Math.log10(envelope(U0)))); ctx.lineTo(X(U1), Y(Math.log10(envelope(U1)))); ctx.stroke(); ctx.setLineDash([]);
    const half = M.layers[0].f;
    const curve = (f, color, wd) => { ctx.strokeStyle = color; ctx.lineWidth = wd * dpr; ctx.beginPath(); windowMax(f).forEach(([u, mx], i) => { const y = Y(Math.log10(mx || 1e-300)); if (i) ctx.lineTo(X(u), y); else ctx.moveTo(X(u), y); }); ctx.stroke(); ctx.lineWidth = 1; };
    curve(half, 'rgba(25, 224, 255, 0.45)', 1); curve(M.f, CY, 1.5);
    if (M.cross) { ctx.fillStyle = MG; ctx.beginPath(); ctx.arc(X(M.cross), Y(Math.log10(envelope(M.cross))), 3.4 * dpr, 0, 2 * Math.PI); ctx.fill(); }
    ctx.strokeStyle = AM; ctx.beginPath(); ctx.moveTo(X(pr.u), pt); ctx.lineTo(X(pr.u), pt + ih); ctx.stroke();
    axisText(F, [['u=2', X(U0), pt + ih + 4 * dpr, 'left', 'top'], ['u=80', X(80), pt + ih + 4 * dpr, 'center', 'top'], ['u=160', X(U1), pt + ih + 4 * dpr, 'right', 'top'], [`10${sup(1)}`, pl - 4 * dpr, Y(1), 'right', 'middle']]);
    $('c2Meta').textContent = T('log|f(u)|（每 0.2 取最大）· 淡青 = 同高度的临界线零点 · 虚线 = 7e^(−u/2) · 品红 = 越过', 'log|f(u)| (maximum over each 0.2) · pale cyan = an on-line zero at the same height · dashes = 7e^(−u/2) · magenta = crossing');
  }
}

/* =====================================================================
   10. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
function readouts() {
  const M = MODEL, pr = progress();
  if (M.mode === 'layers') {
    const lastV = pr.viol.length ? pr.viol[pr.viol.length - 1] : null;
    setRo([[T('已扫描到', 'Scanned up to'), `n ≤ ${fmtN(pr.nCut)}`],
      [T('(5040, n] 上最大的 R(n)', 'Largest R(n) on (5040, n]'), pr.best ? `${pr.best[1].toFixed(6)} · n = ${fmtN(pr.best[0])}` : '—'],
      [T('R(n) ≥ 1 的数', 'Numbers with R(n) ≥ 1'), pr.viol.length ? T(`${pr.viol.length} 个，最大 ${fmtN(lastV)}`, `${pr.viol.length}, the largest ${fmtN(lastV)}`) : '—'],
      [T(`p = ${M.p} 的层上限 1 − p^(−v−1)`, `Layer caps 1 − p^(−v−1), p = ${M.p}`), [0, 1, 2, 3].map((v) => cap(M.p, v).toFixed(4)).join(' · ') + ' …'],
      [T('结论', 'Verdict'), pr.nCut <= 5040 ? T('5040 以内：Robin 不等式有反例', 'up to 5040: Robin’s inequality has violations') : T(`5040 之后到 ${fmtN(pr.nCut)} 没有 R ≥ 1（页面数值）；上极限是 1（冻结定理）`, `no R ≥ 1 after 5040 up to ${fmtN(pr.nCut)} (page numerics); the upper limit is 1 (frozen theorem)`)]]);
    pill('pillA', T('模式', 'MODE'), T('分层', 'LAYERS')); pill('pillB', 'n', fmtN(pr.nCut)); pill('pillC', T('5040 后最大 R', 'MAX R > 5040'), pr.best ? pr.best[1].toFixed(4) : '—'); pill('pillD', 'R ≥ 1', String(pr.viol.length));
    $('roNote').innerHTML = pr.best ? T(`对数余量 −log R 在这里是 ${(-Math.log(pr.best[1])).toFixed(5)}；冻结定理说它的下极限是 0。`, `The logarithmic margin −log R is ${(-Math.log(pr.best[1])).toFixed(5)} here; the frozen theorem says its lower limit is 0.`) : T('R(n) 在 5040 以内有 26 次达到或超过 1。', 'Up to 5040, R(n) reaches or exceeds 1 twenty-six times.');
  } else if (M.mode === 'witness') {
    const i = A_LIST.indexOf(M.a), r = pr.R[i];
    setRo([[T('k · 第 k 个素数', 'k · the k-th prime'), `k = ${fmtN(pr.k)} · p_k = ${fmtN(pr.pk)}`], [T(`log₁₀ n，n = (p_k#)^${M.a}`, `log₁₀ n, n = (p_k#)^${M.a}`), pr.log10n < 1e4 ? pr.log10n.toFixed(2) : sci(pr.log10n, 4)],
      [T('R(n)', 'R(n)'), isFinite(r) ? r.toFixed(6) : '—'], [T(`极限 1/ζ(${M.a + 1})`, `Limit 1/ζ(${M.a + 1})`), ZINV[M.a].toFixed(6)],
      [T('结论', 'Verdict'), isFinite(r) && r >= 1 ? T('R ≥ 1：这是 5040 以内的 Robin 反例', 'R ≥ 1: a Robin violation within 5040') : T('R < 1，随 k 慢慢爬向 1/ζ(a + 1)；a 越大越接近 1（冻结：任意大的 n 使 R ≥ 1 − ε）', 'R < 1, creeping towards 1/ζ(a + 1) as k grows; closer to 1 for larger a (frozen: arbitrarily large n with R ≥ 1 − ε)')]]);
    pill('pillA', T('模式', 'MODE'), T('素数阶乘幂', 'PRIMORIALS')); pill('pillB', 'a', String(M.a)); pill('pillC', 'R', isFinite(r) ? r.toFixed(4) : '—'); pill('pillD', 'k', fmtN(pr.k));
    $('roNote').innerHTML = isFinite(r) ? T(`对数余量 −log R = ${(-Math.log(r)).toFixed(4)}；极限处是 −log(1/ζ(${M.a + 1})) = ${(-Math.log(ZINV[M.a])).toFixed(4)}。`, `Logarithmic margin −log R = ${(-Math.log(r)).toFixed(4)}; at the limit it is −log(1/ζ(${M.a + 1})) = ${(-Math.log(ZINV[M.a])).toFixed(4)}.`) : '';
  } else {
    setRo([[T('假想零点 ρ · 重数', 'Hypothetical zero ρ · multiplicity'), `${M.beta.toFixed(2)} + ${M.gamma.toFixed(2)}i · m = ${M.m}`], [T('门槛 c* = m/(|ρ||ρ − 1|)', 'Threshold c* = m/(|ρ||ρ − 1|)'), sci(M.cstar, 4)],
      [T(`u = ${pr.u.toFixed(2)} 处的 u·e^((1−β)u)·f(u)`, `u·e^((1−β)u)·f(u) at u = ${pr.u.toFixed(2)}`), `${sci(pr.norm, 4)}  (${(pr.norm / M.cstar).toFixed(2)} c*)`],
      [T('|f(u)| 与 7e^(−u/2)', '|f(u)| and 7e^(−u/2)'), `${sci(Math.abs(pr.f), 3)} · ${sci(pr.env, 3)}`],
      [T('越过 7e^(−u/2) 的第一个 u', 'First u crossing 7e^(−u/2)'), M.cross ? `u ≈ ${M.cross.toFixed(2)}` : T('u ≤ 160 内没有越过', 'no crossing for u ≤ 160')]]);
    pill('pillA', T('模式', 'MODE'), T('离线零点', 'OFF-LINE')); pill('pillB', 'β', M.beta.toFixed(2)); pill('pillC', 'c*', sci(M.cstar, 2)); pill('pillD', 'u', pr.u.toFixed(1));
    $('roNote').innerHTML = T(`窗口 [${pr.lo.toFixed(1)}, ${pr.hi.toFixed(1)}] 里归一化尾项越过门槛 c* ${pr.wpeaks.length} 次，从 2 到 160 共 ${M.peaks.length} 次；振幅约 2c*，因为一对共轭零点各贡献一份。`, `In the window [${pr.lo.toFixed(1)}, ${pr.hi.toFixed(1)}] the normalized tail rises above the threshold c* ${pr.wpeaks.length} times, ${M.peaks.length} times from 2 to 160; its amplitude is about 2c*, since each of the two conjugate zeros contributes one share.`);
  }
}
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; toasted = false; }
  const M = MODEL, key = `${S.mode}|${S.nowFrac}|${TRV.lang()}`;
  if (key === syncedKey) return; syncedKey = key;
  const pr = progress();
  readouts();
  document.querySelectorAll('#modeChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.mode === S.mode)));
  document.querySelectorAll('#pChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.p === S.p)));
  document.querySelectorAll('#aChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.a === S.a)));
  document.querySelectorAll('#gChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.g === S.g)));
  document.querySelectorAll('#mChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.m === S.m)));
  $('pChips').hidden = S.mode !== 'layers'; $('aChips').hidden = S.mode !== 'witness'; $('echoBox').hidden = S.mode !== 'echo';
  $('beta').value = S.beta; $('oBeta').textContent = S.beta.toFixed(2);
  $('formula').innerHTML = M.mode === 'echo' ? 'f(u) = −∫<sub>u</sub><sup>∞</sup> e<sup>−v</sup>(θ(e<sup>v</sup>) − e<sup>v</sup>)·(v + 1)/v² dv' : M.mode === 'witness' ? 'σ(n)/n = ∏<sub>p ≤ p_k</sub> (1 − p<sup>−a−1</sup>)/(1 − 1/p)' : 'R(n) = σ(n) / (e<sup>γ</sup> n log log n)';
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('modeNote').innerHTML = M.mode === 'layers' ? T('时间轴 = log n，从 3 扫到 10⁶。', 'The time axis is log n, swept from 3 to 10⁶.') : M.mode === 'witness' ? T('时间轴 = log k：素数阶乘乘到第 k 个素数。', 'The time axis is log k: the primorial runs up to the k-th prime.') : T('时间轴 = u = log x，从 2 到 160。', 'The time axis is u = log x, from 2 to 160.');
  $('litNote').innerHTML = T('三维与两张图的每个数都是页面算的；冻结的是上面三条定理。', 'Every number in the 3D view and the two charts is computed on the page; what is frozen are the three theorems above.');
  $('c1Title').textContent = M.mode === 'layers' ? T('R(n) 对 log n', 'R(n) against log n') : M.mode === 'witness' ? T(`素数阶乘的 ${M.a} 次幂`, `Primorials to the power ${M.a}`) : T('当前 u 附近：归一化尾项与定理门槛', 'Around the current u: the normalized tail and the theorem’s threshold');
  $('c2Title').textContent = M.mode === 'layers' ? T('最后一个十倍区间：各层最大值与上限', 'The last factor of ten: each layer against its cap') : M.mode === 'witness' ? T('同一个 k、不同的 a', 'One k, every a') : T('尾项与 7e^(−u/2)', 'The tail against 7e^(−u/2)');
  $('clock').innerHTML = M.mode === 'layers' ? `n ${fmtN(pr.nCut)}` : M.mode === 'witness' ? `k ${fmtN(pr.k)}` : `u ${pr.u.toFixed(1)}`;
  $('hudBig').textContent = M.mode === 'layers' ? `R(n) · v${['₂', '₃', '₅'][[2, 3, 5].indexOf(M.p)]}(n) · n ≤ ${fmtN(pr.nCut)}` : M.mode === 'witness' ? `R((p_k#)^a) · k = ${fmtN(pr.k)}` : `ρ = ${M.beta.toFixed(2)} + ${M.gamma.toFixed(2)}i · u = ${pr.u.toFixed(1)}`;
  $('hudSub').textContent = M.mode === 'layers' ? T(`横 = log n，纵深 = p 的指数（青到品红），高 = R(n)；绿 = 1 与各层上限，品红点 = 26 个反例，琥珀 = 当前截止与 5040 之后的最大值`, `across = log n, depth = exponent of p (cyan to magenta), height = R(n); green = 1 and the layer caps, magenta dots = the 26 violations, amber = the current cutoff and the largest value after 5040`)
    : M.mode === 'witness' ? T('横 = log k，纵深 = 指数 a，高 = R；琥珀 = 当前的 a 与 k，品红 = R > 1，白虚线 = 1/ζ(a + 1)', 'across = log k, depth = exponent a, height = R; amber = the current a and k, magenta = R > 1, white dashes = 1/ζ(a + 1)')
    : T('横 = u，纵深 = β，高 = log|f(u)|；琥珀 = 当前的 β，淡青 = 临界线上的零点，白虚线 = 7e^(−u/2)，点 = 越过的位置', 'across = u, depth = β, height = log|f(u)|; amber = the current β, pale cyan = a zero on the critical line, white dashes = 7e^(−u/2), dots = crossings');
  if (!toasted && S.playing && S.nowFrac >= 1) {
    toasted = true;
    toast(M.mode === 'layers' ? T(`<b>n ≤ 10⁶</b>：5040 之后最大的 R(n) = ${pr.best[1].toFixed(4)}（n = ${fmtN(pr.best[0])}），没有 R ≥ 1。这是数值，不是证明。`, `<b>n ≤ 10⁶</b>: after 5040 the largest R(n) is ${pr.best[1].toFixed(4)} (n = ${fmtN(pr.best[0])}), and none has R ≥ 1. Numerics, not a proof.`)
      : M.mode === 'witness' ? T(`<b>k = ${fmtN(pr.k)}</b>：a = ${M.a} 时 R = ${pr.R[A_LIST.indexOf(M.a)].toFixed(4)}，极限 1/ζ(${M.a + 1}) = ${ZINV[M.a].toFixed(4)}。`, `<b>k = ${fmtN(pr.k)}</b>: for a = ${M.a}, R = ${pr.R[A_LIST.indexOf(M.a)].toFixed(4)}, with limit 1/ζ(${M.a + 1}) = ${ZINV[M.a].toFixed(4)}.`)
      : T(`<b>u = 160</b>：${M.cross ? `尾项在 u ≈ ${M.cross.toFixed(1)} 越过 7e^(−u/2)` : '尾项在 160 以内没有越过 7e^(−u/2)'}；归一化后它反复越过门槛 c*。`, `<b>u = 160</b>: ${M.cross ? `the tail crosses 7e^(−u/2) at u ≈ ${M.cross.toFixed(1)}` : 'the tail does not cross 7e^(−u/2) up to 160'}; normalized, it repeatedly rises above the threshold c*.`));
  }
}
function syncRail() {
  const M = MODEL, key = `${M.mode}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  let marks;
  if (M.mode === 'layers') marks = [[0, 'n=3'], [(Math.log(5040) - LN3) / (LNN - LN3), '5040'], [1, 'n=10⁶']];
  else if (M.mode === 'witness') marks = [[0, 'k=1'], [Math.log(100) / Math.log(M.K), 'k=100'], [1, `k=${fmtN(M.K)}`]];
  else marks = [[0, 'u=2'], [(80 - U0) / (U1 - U0), 'u=80'], [1, 'u=160']];
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
function custom() { S.preset = null; markPreset(); dirty = true; }
document.querySelectorAll('#modeChips .chip').forEach((b) => b.addEventListener('click', () => { const m = MODES.includes(b.dataset.mode) ? b.dataset.mode : 'layers'; if (S.mode === m) return; S.mode = m; custom(); }));
document.querySelectorAll('#pChips .chip').forEach((b) => b.addEventListener('click', () => { S.p = [2, 3, 5].includes(+b.dataset.p) ? +b.dataset.p : 2; custom(); }));
document.querySelectorAll('#aChips .chip').forEach((b) => b.addEventListener('click', () => { S.a = A_LIST.includes(+b.dataset.a) ? +b.dataset.a : 5; custom(); }));
document.querySelectorAll('#gChips .chip').forEach((b) => b.addEventListener('click', () => { S.g = [0, 1, 2].includes(+b.dataset.g) ? +b.dataset.g : 0; custom(); }));
document.querySelectorAll('#mChips .chip').forEach((b) => b.addEventListener('click', () => { S.m = +b.dataset.m === 2 ? 2 : 1; custom(); }));
$('beta').addEventListener('input', () => { S.beta = Math.min(0.95, Math.max(0.55, Math.round(parseFloat($('beta').value) * 100) / 100)); custom(); });
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.mode = p.mode; if (p.p) S.p = p.p; if (p.a) S.a = p.a; if (p.beta) S.beta = p.beta; if (p.g !== undefined) S.g = p.g; if (p.m) S.m = p.m;
  S.preset = name; markPreset(); dirty = true;
  S.nowFrac = p.cutN ? Math.min(1, (binOf(p.cutN) + 0.5) / BINS) : p.frac; S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.nowFrac;
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(S.nowFrac + (ev.key === 'ArrowRight' ? 1 : -1) / BINS); }
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
      S.nowFrac += S.dir * dtSec * S.speed / RUN[MODEL.mode];
      if (S.nowFrac >= 1) { S.nowFrac = 1; S.hold = 2.4; }
      if (S.nowFrac <= 0) { S.nowFrac = 0; S.hold = 1.2; }
    }
    $('now').value = S.nowFrac;
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    const pr = progress(), k = `${S.mode}|${S.p}|${S.a}|${S.beta}|${S.g}|${S.m}|${pr.b ?? pr.k ?? Math.round(pr.u * 10)}`;
    if (k !== glKey) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.GE_DEBUG = {
  pending: () => dirty || syncedKey !== `${S.mode}|${S.nowFrac}|${TRV.lang()}`,
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => {
    const M = MODEL, pr = progress();
    if (M.mode === 'layers') return { mode: M.mode, p: M.p, b: pr.b, nCut: pr.nCut, nLo: pr.nLo, viol: pr.viol, best: pr.best, decade: pr.decade, caps: Array.from({ length: LAYERS }, (_, v) => cap(M.p, v)), env: Array.from(M.D.env), lo: Array.from(M.D.lo), hi: Array.from(M.D.hi), top: M.D.top.length };
    if (M.mode === 'witness') return { mode: M.mode, a: M.a, K: M.K, k: pr.k, pk: pr.pk, R: pr.R, log10n: pr.log10n, zinv: A_LIST.map((a) => ZINV[a]) };
    const samples = [5, 10, 20, 40, 80, 120].map((u) => [u, M.f[fIdx(u)]]);
    return { mode: M.mode, beta: M.beta, gamma: M.gamma, m: M.m, cstar: M.cstar, cross: M.cross, peaks: M.peaks, u: pr.u, f: pr.f, norm: pr.norm, samples, layerCross: M.layers.map((L) => [L.beta, crossing(L.f)]) };
  },
  robinAt: (n) => (SIG ? robin(n) : null),
  witnessAt: (a, k) => (WIT ? WIT.R[a][k] : null),
  setFrac: (f) => { S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; }
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('primorial'); S.playing = false; setPlayUI(); S.nowFrac = 1; $('now').value = S.nowFrac; setCamPreset('iso'); cam.theta = cam.tTheta = 0.7; cam.phi = cam.tPhi = 1.05; cam.r = cam.tR = 17; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
applyPreset('edge');
setPlayUI();
requestAnimationFrame(frame);
})();
