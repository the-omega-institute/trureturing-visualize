/* LINDBLAD//ZERO · zero in the spectrum of a lattice Lindbladian
   A finite-range translation-invariant Lindblad generator t acts on kernels ρ ∈ ℓ²(ℤ × ℤ). Klausen (2025) asked to prove
   0 ∈ σ(t) for rank-one jumps. Frozen in trureturing (LatticeLindbladianZeroSpectrum.result) without any rank, sign or
   self-adjointness condition: the truncated trace ρ ↦ Σ_{|x| ≤ n} (tρ)(x, x) = ⟨P_n, tρ⟩ only sees coefficients near the
   corners (±n, ±n), so it is bounded by K‖ρ‖ uniformly in n, while ‖P_n‖ = √(2n + 1) grows; an inverse S would force
   √(2n + 1) ≤ K‖S‖ for all n. The page computes that functional for three generators and the spectrum of the same
   generator on a finite ring.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Constants and complex arithmetic
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.5, 0.58, 0.68];
const NMAX = 16, RINGS = [12, 24, 48], RUN = 16;
const add = (a, b) => [a[0] + b[0], a[1] + b[1]], mul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const conj = (a) => [a[0], -a[1]], sc = (a, s) => [a[0] * s, a[1] * s], cabs = (a) => Math.hypot(a[0], a[1]);
const fmtC = (c, d = 3) => { const re = Math.abs(c[0]) < 5e-13 ? 0 : c[0], im = Math.abs(c[1]) < 5e-13 ? 0 : c[1]; if (im === 0) return re.toFixed(d); if (re === 0) return `${im.toFixed(d)}i`; return `${re.toFixed(d)}${im < 0 ? '−' : '+'}${Math.abs(im).toFixed(d)}i`; };

/* =====================================================================
   2. Generators: h(x, y) = h0(y − x), ℓ(k, x, y) = l0(x − k, y − k), range r
   ===================================================================== */
/* a fixed random range-one generator with rank-three jumps: entries drawn once from mulberry32(20251) */
const RAND = (() => {
  const rnd = TRV.mulberry32(20251), c = () => [Math.round((rnd() - 0.5) * 1000) / 1000, Math.round((rnd() - 0.5) * 1000) / 1000];
  const h1 = c(), l = {}; for (let a = -1; a <= 1; a++) for (let b = -1; b <= 1; b++) l[`${a},${b}`] = c();
  return { h: { '-1': conj(h1), 0: [Math.round(rnd() * 1000) / 1000, 0], 1: h1 }, l };
})();
const GENS = {
  deph: { r: 1, h: { '-1': [1, 0], 1: [1, 0] }, l: { '0,0': [1, 0] },
    zh: '去相位跳跃：H = S + S*，L_k = |k⟩⟨k|', en: 'Dephased hopping: H = S + S*, L_k = |k⟩⟨k|', rank: 1 },
  jump: { r: 1, h: {}, l: { '1,0': [1, 0] },
    zh: '向右跳：H = 0，L_k = |k + 1⟩⟨k|', en: 'Jumps to the right: H = 0, L_k = |k + 1⟩⟨k|', rank: 1 },
  rand: { r: 1, h: RAND.h, l: RAND.l,
    zh: '随机的力程 1 生成元（L_k 秩 3）', en: 'A random range-one generator (L_k of rank 3)', rank: 3 }
};
const genOf = (name, g) => { const G = GENS[name]; return { name, r: G.r, g, h0: (d) => G.h[d] || [0, 0], l0: (a, b) => G.l[`${a},${b}`] || [0, 0] }; };

/* coefficients of ρ(u, v) in (tρ)(x, y), straight from the Lindblad entry; Map "u,v" → complex */
function coeffs(G, x, y) {
  const { r, g, h0, l0 } = G, h = (a, b) => h0(b - a), l = (k, a, b) => l0(a - k, b - k), m = new Map();
  const put = (u, v, c) => { if (c[0] === 0 && c[1] === 0) return; const key = u + ',' + v; m.set(key, add(m.get(key) || [0, 0], c)); };
  for (let z = x - r; z <= x + r; z++) put(z, y, mul([0, -1], h(x, z)));            // −i Σ_z h(x, z) ρ(z, y)
  for (let z = y - r; z <= y + r; z++) put(x, z, mul([0, 1], h(z, y)));             // + i Σ_z ρ(x, z) h(z, y)
  for (let k = Math.min(x, y) - r; k <= Math.max(x, y) + r; k++) {
    for (let u = k - r; u <= k + r; u++) for (let v = k - r; v <= k + r; v++) put(u, v, sc(mul(l(k, x, u), conj(l(k, y, v))), g));
    for (let z = k - r; z <= k + r; z++) { let s = [0, 0]; for (let w = k - r; w <= k + r; w++) s = add(s, mul(conj(l(k, w, x)), l(k, w, z))); put(z, y, sc(s, -g / 2)); }
    for (let z = k - r; z <= k + r; z++) { let s = [0, 0]; for (let w = k - r; w <= k + r; w++) s = add(s, mul(conj(l(k, w, z)), l(k, w, y))); put(x, z, sc(s, -g / 2)); }
  }
  for (const [key, c] of m) if (cabs(c) < 1e-13) m.delete(key);
  return m;
}
/* the truncated trace ρ ↦ Σ_{|x| ≤ n} (tρ)(x, x) as coefficients a_n(p), and the coefficient mass Σ_x |c(x, x; p)| before summing */
function functional(G, n) {
  const a = new Map(), mass = new Map();
  for (let x = -n; x <= n; x++) for (const [key, c] of coeffs(G, x, x)) { a.set(key, add(a.get(key) || [0, 0], c)); mass.set(key, (mass.get(key) || 0) + cabs(c)); }
  for (const [key, c] of a) if (cabs(c) < 1e-12) a.delete(key);
  let s = 0; for (const c of a.values()) s += c[0] ** 2 + c[1] ** 2;
  return { a, mass, norm: Math.sqrt(s) };
}

/* =====================================================================
   3. Spectrum of the same generator on the ring ℤ_N (a finite Lindbladian)
   ===================================================================== */
/* translation invariance splits the N² × N² generator into N blocks: ρ(x, x + s′) = e^{iqx} δ, q = 2πj/N */
function block(G, N, q) {
  const Br = new Float64Array(N * N), Bi = new Float64Array(N * N), mod = (a) => ((a % N) + N) % N;
  for (let s = 0; s < N; s++) {
    const y = s <= N / 2 ? s : s - N;
    for (const [key, c] of coeffs(G, 0, y)) {
      const [u, v] = key.split(',').map(Number), sp = mod(v - u), cr = Math.cos(q * u), ci = Math.sin(q * u);
      Br[s * N + sp] += c[0] * cr - c[1] * ci; Bi[s * N + sp] += c[0] * ci + c[1] * cr;
    }
  }
  return { Br, Bi };
}
/* eigenvalues of a complex matrix: Householder reduction to Hessenberg form, then shifted QR with Givens rotations */
function eigC(n, Ar, Ai) {
  const R = Float64Array.from(Ar), I = Float64Array.from(Ai), at = (i, j) => i * n + j;
  for (let k = 0; k < n - 2; k++) {
    let alpha = 0; for (let i = k + 1; i < n; i++) alpha += R[at(i, k)] ** 2 + I[at(i, k)] ** 2;
    alpha = Math.sqrt(alpha); if (alpha < 1e-300) continue;
    const x0r = R[at(k + 1, k)], x0i = I[at(k + 1, k)], x0a = Math.hypot(x0r, x0i), pr = x0a > 0 ? x0r / x0a : 1, pi = x0a > 0 ? x0i / x0a : 0;
    const vr = new Float64Array(n), vi = new Float64Array(n);
    for (let i = k + 1; i < n; i++) { vr[i] = R[at(i, k)]; vi[i] = I[at(i, k)]; }
    vr[k + 1] += pr * alpha; vi[k + 1] += pi * alpha;
    let vn = 0; for (let i = k + 1; i < n; i++) vn += vr[i] ** 2 + vi[i] ** 2; if (vn < 1e-300) continue;
    for (let j = 0; j < n; j++) { let sr = 0, si = 0; for (let i = k + 1; i < n; i++) { sr += vr[i] * R[at(i, j)] + vi[i] * I[at(i, j)]; si += vr[i] * I[at(i, j)] - vi[i] * R[at(i, j)]; } sr *= 2 / vn; si *= 2 / vn; for (let i = k + 1; i < n; i++) { R[at(i, j)] -= vr[i] * sr - vi[i] * si; I[at(i, j)] -= vr[i] * si + vi[i] * sr; } }
    for (let i = 0; i < n; i++) { let sr = 0, si = 0; for (let j = k + 1; j < n; j++) { sr += R[at(i, j)] * vr[j] - I[at(i, j)] * vi[j]; si += R[at(i, j)] * vi[j] + I[at(i, j)] * vr[j]; } sr *= 2 / vn; si *= 2 / vn; for (let j = k + 1; j < n; j++) { R[at(i, j)] -= sr * vr[j] + si * vi[j]; I[at(i, j)] -= si * vr[j] - sr * vi[j]; } }
  }
  const out = []; let hi = n - 1, iter = 0;
  while (hi >= 0) {
    if (hi === 0) { out.push([R[0], I[0]]); hi--; continue; }
    let lo = hi;
    while (lo > 0) { const s = Math.hypot(R[at(lo, lo)], I[at(lo, lo)]) + Math.hypot(R[at(lo - 1, lo - 1)], I[at(lo - 1, lo - 1)]); if (Math.hypot(R[at(lo, lo - 1)], I[at(lo, lo - 1)]) <= 1e-14 * (s || 1)) { R[at(lo, lo - 1)] = 0; I[at(lo, lo - 1)] = 0; break; } lo--; }
    if (lo === hi) { out.push([R[at(hi, hi)], I[at(hi, hi)]]); hi--; iter = 0; continue; }
    if (++iter > 400) throw new Error('QR did not converge');
    const ar = R[at(hi - 1, hi - 1)], ai = I[at(hi - 1, hi - 1)], br = R[at(hi - 1, hi)], bi = I[at(hi - 1, hi)], cr = R[at(hi, hi - 1)], ci = I[at(hi, hi - 1)], dr = R[at(hi, hi)], di = I[at(hi, hi)];
    const tr = (ar + dr) / 2, ti = (ai + di) / 2, er = (ar - dr) / 2, ei = (ai - di) / 2;
    const qr = er * er - ei * ei + (br * cr - bi * ci), qi = 2 * er * ei + (br * ci + bi * cr), m = Math.hypot(qr, qi);
    const sr = Math.sqrt((m + qr) / 2), si = Math.sign(qi || 1) * Math.sqrt(Math.max(0, (m - qr) / 2));
    const mu1 = [tr + sr, ti + si], mu2 = [tr - sr, ti - si];
    let mu = Math.hypot(mu1[0] - dr, mu1[1] - di) < Math.hypot(mu2[0] - dr, mu2[1] - di) ? mu1 : mu2;
    if (iter % 11 === 10) mu = [dr + Math.abs(cr) * 0.75, di];
    for (let i = lo; i <= hi; i++) { R[at(i, i)] -= mu[0]; I[at(i, i)] -= mu[1]; }
    const G = [];
    for (let k = lo; k < hi; k++) {
      const xr = R[at(k, k)], xi = I[at(k, k)], yr = R[at(k + 1, k)], yi = I[at(k + 1, k)];
      const nx = Math.hypot(xr, xi), ny = Math.hypot(yr, yi), nn = Math.hypot(nx, ny);
      let c, s_r, s_i;
      if (nn === 0) { c = 1; s_r = 0; s_i = 0; } else if (nx === 0) { c = 0; s_r = yr / ny; s_i = -yi / ny; } else { c = nx / nn; const ur = xr / nx, ui = xi / nx; s_r = (ur * yr + ui * yi) / nn; s_i = (ui * yr - ur * yi) / nn; }
      for (let j = k; j < n; j++) {
        const a_r = R[at(k, j)], a_i = I[at(k, j)], b_r = R[at(k + 1, j)], b_i = I[at(k + 1, j)];
        R[at(k, j)] = c * a_r + (s_r * b_r - s_i * b_i); I[at(k, j)] = c * a_i + (s_r * b_i + s_i * b_r);
        R[at(k + 1, j)] = -(s_r * a_r + s_i * a_i) + c * b_r; I[at(k + 1, j)] = -(s_r * a_i - s_i * a_r) + c * b_i;
      }
      G.push([c, s_r, s_i]);
    }
    for (let k = lo; k < hi; k++) {
      const [c, s_r, s_i] = G[k - lo];
      for (let i = 0; i <= Math.min(hi, k + 2); i++) {
        const a_r = R[at(i, k)], a_i = I[at(i, k)], b_r = R[at(i, k + 1)], b_i = I[at(i, k + 1)];
        R[at(i, k)] = c * a_r + (s_r * b_r + s_i * b_i); I[at(i, k)] = c * a_i + (s_r * b_i - s_i * b_r);
        R[at(i, k + 1)] = -(s_r * a_r - s_i * a_i) + c * b_r; I[at(i, k + 1)] = -(s_r * a_i + s_i * a_r) + c * b_i;
      }
    }
    for (let i = lo; i <= hi; i++) { R[at(i, i)] += mu[0]; I[at(i, i)] += mu[1]; }
  }
  return out;
}
function ringSpectrum(G, N) {
  const ev = [];
  for (let j = 0; j < N; j++) { const q = 2 * Math.PI * j / N, { Br, Bi } = block(G, N, q); for (const e of eigC(N, Br, Bi)) ev.push({ re: e[0], im: e[1], j }); }
  return ev;
}

/* =====================================================================
   4. State and presets
   ===================================================================== */
const S = { gen: 'deph', g: 1, N: 24, nowFrac: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'deph' };
const PRESETS = {
  deph: { gen: 'deph', g: 1, N: 24, frac: 0, play: true, cam: 'iso',
    zh: 'Klausen 自己的例子：H = S + S*（相邻跳跃），L_k = |k⟩⟨k|（去相位），g = 1。时间轴把 n 从 0 推到 16：青柱是 P_n，灰柱是各个 (tρ)(x, x) 用到的系数，品红柱是它们加起来之后剩下的——只剩角上 4 个系数，范数恒为 2，而 ‖P_n‖ = √(2n + 1) 一直长。',
    en: 'Klausen’s own example: H = S + S* (nearest-neighbour hopping), L_k = |k⟩⟨k| (dephasing), g = 1. The time axis takes n from 0 to 16: cyan bars are P_n, grey bars the coefficients used by the individual (tρ)(x, x), magenta bars what is left after adding them — only 4 coefficients at the corners, norm always 2, while ‖P_n‖ = √(2n + 1) keeps growing.' },
  jump: { gen: 'jump', g: 1, N: 24, frac: 0, play: true, cam: 'iso',
    zh: '纯跳跃：L_k = |k + 1⟩⟨k|，粒子只向右跳。对角线上就是经典随机游走，截断迹只剩两项 g(ρ(−n−1, −n−1) − ρ(n, n))：从左边流进来、从右边流出去，范数 g√2。环上的谱是一个过原点的圆 g(e^{−iq} − 1)。',
    en: 'Pure jumps: L_k = |k + 1⟩⟨k|, the particle only hops to the right. On the diagonal this is a classical random walk, and the truncated trace keeps two terms g(ρ(−n−1, −n−1) − ρ(n, n)): what flows in on the left and out on the right, norm g√2. On the ring the spectrum is a circle through the origin, g(e^{−iq} − 1).' },
  rand: { gen: 'rand', g: 0.5, N: 24, frac: 0.5, play: false, cam: 'iso',
    zh: '一个固定的随机生成元：力程 1，每个 L_k 是秩 3 的随机 3×3 块。Klausen 的问题要求秩 1；冻结的定理不要求秩、不要求 H 自伴、也不要求 g 的符号。截断迹的系数仍只在两个角上，个数远小于 Lean 证明里的上界 2(4r + 1)(8r + 1) = 90。',
    en: 'A fixed random generator: range 1, every L_k a random 3×3 block of rank 3. Klausen’s question asks for rank one; the frozen theorem needs no rank condition, no self-adjoint H and no sign of g. The truncated trace still has its coefficients only at the two corners, far fewer than the bound 2(4r + 1)(8r + 1) = 90 in the Lean proof.' },
  neg: { gen: 'deph', g: -1, N: 24, frac: 1, play: false, cam: 'iso',
    zh: 'g = −1：耗散项反号，已经不是物理的 Lindblad 生成元（谱跑到右半平面）。定理照样成立——证明只用到“完整的迹把每个矩阵单位送到 0”，与正性无关。截断迹与 g = 1 时完全相同。',
    en: 'g = −1: the dissipator changes sign and this is no longer a physical Lindblad generator (the spectrum moves to the right half plane). The theorem still holds — the proof only uses that the full trace sends every matrix unit to 0, which has nothing to do with positivity. The truncated trace is the same as at g = 1.' },
  ring: { gen: 'deph', g: 1, N: 48, frac: 1, play: false, cam: 'top',
    zh: '环 ℤ₄₈：把同一个生成元放到 48 个格点的环上，它变成 2304 维的矩阵，按动量 q 分成 48 块。q = 0 那一块含精确的 0（迹守恒），其余本征值在 q → 0 时挤向 0。这是有限体积的页面数值，不是定理；卷宗把有限体积能隙的问题列为未决。',
    en: 'The ring ℤ₄₈: on 48 sites the same generator is a 2304-dimensional matrix, split by momentum q into 48 blocks. The q = 0 block contains an exact 0 (the trace is conserved), and the other eigenvalues crowd towards 0 as q → 0. These are finite-volume page numbers, not theorems; the dossier lists the finite-volume gap as open.' },
  edge: { gen: 'deph', g: 1, N: 24, frac: 0.75, play: false, cam: 'top',
    zh: 'n = 12，俯视。琥珀框是 Lean 证明 boundary_estimate 允许系数出现的区域：u 距 ±n 不超过 2r，v 距 u 不超过 4r，至多 2(4r + 1)(8r + 1) = 90 个位置。内部的每个系数都被 trace_single_zero 抵消：完整的迹把每个矩阵单位送到 0。',
    en: 'n = 12, from above. The amber frames are where the Lean proof (boundary_estimate) allows coefficients: u within 2r of ±n and v within 4r of u, at most 2(4r + 1)(8r + 1) = 90 places. Every interior coefficient cancels by trace_single_zero: the full trace sends every matrix unit to 0.' }
};

/* =====================================================================
   5. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
const specCache = new Map();
function build() {
  if (!GENS[S.gen]) S.gen = 'deph';
  if (!RINGS.includes(S.N)) S.N = 24;
  if (!isFinite(S.g)) S.g = 1;
  const G = genOf(S.gen, S.g), F = [];
  for (let n = 0; n <= NMAX; n++) F.push(functional(G, n));
  const K = Math.max(...F.map((f) => f.norm));
  const key = `${S.gen}|${S.g}|${S.N}`;
  if (!specCache.has(key)) specCache.set(key, ringSpectrum(G, S.N));
  const spec = specCache.get(key);
  const zeros = spec.filter((e) => Math.hypot(e.re, e.im) < 1e-9).length;
  let gap = Infinity, gapJ = -1; for (const e of spec) { const a = Math.hypot(e.re, e.im); if (a >= 1e-9 && a < gap) { gap = a; gapJ = e.j; } }
  const bound = 2 * (4 * G.r + 1) * (8 * G.r + 1);
  let nStar = NMAX; for (let n = 0; n <= NMAX; n++) if (Math.sqrt(2 * n + 1) > 2 * K) { nStar = n; break; }
  MODEL = { id: ++modelId, gen: S.gen, g: S.g, N: S.N, G, F, K, spec, zeros, gap, gapJ, bound, nStar, W: NMAX + 6 * G.r };
}
const nNow = () => Math.round(S.nowFrac * NMAX);
/* the Lean edge region: u within 2r of ±n, v within 4r of u */
const inEdge = (M, n, u, v) => { const r = M.G.r; return (Math.abs(u - n) <= 2 * r || Math.abs(u + n) <= 2 * r) && Math.abs(v - u) <= 4 * r; };

/* =====================================================================
   6. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const fr = (x, d = 4) => (isFinite(x) ? x.toFixed(d) : '—');

/* =====================================================================
   7. 3D scene: the (u, v) plane of kernel coordinates
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 12000, PTS_MAX = 3000;
const CAMS = { iso: [-0.45, 0.98, 21], front: [-0.785, 1.4, 19], top: [-0.785, 0.0601, 21] };
const cam = { theta: -0.45, phi: 0.98, r: 21, tTheta: -0.45, tPhi: 0.98, tR: 21 };
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
  camera = new THREE.PerspectiveCamera(38, 1, 0.05, 200);
  const g = new THREE.BufferGeometry(); dyn(g, 'position', LINES_MAX, 3); dyn(g, 'color', LINES_MAX, 3);
  lines = new THREE.LineSegments(g, new THREE.LineBasicMaterial({ vertexColors: true, ...additive })); lines.frustumCulled = false; scene3.add(lines);
  const gp = new THREE.BufferGeometry(); dyn(gp, 'position', PTS_MAX, 3); dyn(gp, 'aColor', PTS_MAX, 3); dyn(gp, 'aAlpha', PTS_MAX, 1); dyn(gp, 'aSize', PTS_MAX, 1);
  pts = new THREE.Points(gp, new THREE.ShaderMaterial({ vertexShader: EVT_VS, fragmentShader: DOT_FS, uniforms: { uScale: { value: 60 } }, ...additive }));
  pts.frustumCulled = false; scene3.add(pts);
}
/* kernel coordinate (u, v) → across, depth; height up */
const CELL = 0.36, HMAX = 3.2;
const posOf = (u, v, h = 0) => [u * CELL, h, v * CELL];
function heightScale(M, n) { let m = 0; for (const v of M.F[n].mass.values()) m = Math.max(m, v); return m > 0 ? HMAX / m : 1; }
function updateGL() {
  const M = MODEL, n = nNow(), f = M.F[n], W = M.W, hs = heightScale(M, n);
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (a, b, col, k) => { if (v + 2 > LINES_MAX) return; for (const p of [a, b]) { Pp[3 * v] = p[0]; Pp[3 * v + 1] = p[1]; Pp[3 * v + 2] = p[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, a, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = a; PT.aSize.array[np] = size; np++; };
  /* floor grid every 4 cells, and the axes u = 0, v = 0 */
  for (let c = -W; c <= W; c++) if (c % 4 === 0) { const k = c === 0 ? 0.6 : 0.26; seg(posOf(c, -W), posOf(c, W), GREY, k); seg(posOf(-W, c), posOf(W, c), GREY, k); }
  /* the full diagonal and P_n on it */
  seg(posOf(-W, -W), posOf(W, W), COL.cyan, 0.18);
  for (let x = -n; x <= n; x++) { seg(posOf(x, x, 0), posOf(x, x, 0.55), COL.cyan, 0.9); dot(posOf(x, x, 0.55), COL.cyan, 0.9, 0.9); }
  /* coefficient mass before summation (grey) and the surviving coefficients (magenta) */
  for (const [key, m] of f.mass) { const [u, w] = key.split(',').map(Number); if (Math.abs(u) > W || Math.abs(w) > W) continue; seg(posOf(u + 0.12, w + 0.12, 0), posOf(u + 0.12, w + 0.12, m * hs), GREY, 0.42); }
  for (const [key, c] of f.a) { const [u, w] = key.split(',').map(Number), h = cabs(c) * hs; seg(posOf(u, w, 0), posOf(u, w, h), COL.magenta, 1); dot(posOf(u, w, h), COL.magenta, 1, 1.3); }
  /* the Lean edge region around (±n, ±n) */
  const r = M.G.r;
  for (const s of [1, -1]) {
    const uL = s * n - 2 * r - 0.5, uR = s * n + 2 * r + 0.5, w = 4 * r + 0.5;
    const poly = [[uL, uL - w], [uL, uL + w], [uR, uR + w], [uR, uR - w]];
    for (let i = 0; i < 4; i++) { const a = poly[i], b = poly[(i + 1) % 4]; seg(posOf(a[0], a[1], 0.02), posOf(b[0], b[1], 0.02), COL.amber, 0.75); }
  }
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const a of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) a.needsUpdate = true;
  pts.material.uniforms.uScale.value = 60 * renderer.getPixelRatio() * (stage.clientHeight / 600);
}

/* =====================================================================
   8. Camera
   ===================================================================== */
function updateCamera(dtSec) {
  const k = reduceMotion ? 1 : 1 - Math.pow(0.001, dtSec);
  cam.theta += (cam.tTheta - cam.theta) * k; cam.phi += (cam.tPhi - cam.phi) * k; cam.r += (cam.tR - cam.r) * k;
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.45 : 1);
  camera.position.set(r * sp * Math.sin(cam.theta), r * Math.cos(cam.phi), r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(0, 0.6, 0);
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
  if (drag.pts.size === 2) { const [a, b] = [...drag.pts.values()], d = Math.hypot(a.x - b.x, a.y - b.y); if (drag.pinch > 0) cam.tR = Math.min(60, Math.max(8, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(60, Math.max(8, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

/* =====================================================================
   9. Tags
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
  const M = MODEL, n = nNow(), W = M.W; let k = 0;
  const put = (text, p, cls) => { const el = tagAt(k++, cls); el.textContent = text; placeTag(el, p); };
  put('u', posOf(W + 1.5, 0), 'cy'); put('v', posOf(0, W + 1.5), 'cy');
  put(`P_${n}`, posOf(0, 0, 0.95), 'cy');
  if (n >= 3) put(T('内部：Σ = 0', 'inside: Σ = 0'), posOf(Math.floor(n / 2), Math.floor(n / 2), 1.6), 'gr');
  if (n > 0) { put(`(${n}, ${n})`, posOf(n + 2, n + 2, 0.2), 'mg'); put(`(−${n}, −${n})`, posOf(-n - 2, -n - 2, 0.2), 'mg'); }
  else put('(0, 0)', posOf(2, 2, 0.2), 'mg');
  for (let i = k; i < tagPool.length; i++) tagPool[i].style.display = 'none';
}

/* =====================================================================
   10. 2D panels
   ===================================================================== */
function frame2d(cv, pl0 = 46) {
  const dpr = fitCanvas(cv), ctx = cv.getContext('2d'), Wd = cv.width, Hh = cv.height;
  ctx.clearRect(0, 0, Wd, Hh);
  const pl = pl0 * dpr, pr = 12 * dpr, pt = 12 * dpr, pb = 20 * dpr;
  ctx.font = `${9.5 * dpr}px ${TRV.fonts.data}`;
  return { dpr, ctx, W: Wd, Hh, pl, pt, iw: Wd - pl - pr, ih: Hh - pt - pb };
}
function lab(ctx, txt, x, y, al, bl, col = DIM) { ctx.fillStyle = col; ctx.textAlign = al; ctx.textBaseline = bl; ctx.fillText(txt, x, y); }
/* ‖P_n‖, the norm of the truncated trace and the lower bound √(2n + 1)/K any inverse would need */
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 38); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, n = nNow();
  const top = Math.max(Math.sqrt(2 * NMAX + 1), M.K) * 1.08, X = (k) => pl + iw * k / NMAX, Y = (y) => pt + ih - ih * y / top;
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, pt + ih); ctx.lineTo(pl + iw, pt + ih); ctx.stroke();
  for (let y = 0; y <= top; y += top > 8 ? 2 : 1) lab(ctx, String(y), pl - 4 * dpr, Y(y), 'right', 'middle');
  for (let k = 0; k <= NMAX; k += 4) lab(ctx, String(k), X(k), pt + ih + 4 * dpr, 'center', 'top');
  const curve = (f, col, dash) => { ctx.strokeStyle = col; ctx.lineWidth = 2 * dpr; ctx.setLineDash(dash ? [5 * dpr, 4 * dpr] : []); ctx.beginPath(); for (let k = 0; k <= NMAX; k++) { const p = [X(k), Y(f(k))]; if (k) ctx.lineTo(...p); else ctx.moveTo(...p); } ctx.stroke(); ctx.setLineDash([]); for (let k = 0; k <= NMAX; k++) { ctx.fillStyle = col; ctx.beginPath(); ctx.arc(X(k), Y(f(k)), 2.2 * dpr, 0, 2 * Math.PI); ctx.fill(); } };
  curve((k) => Math.sqrt(2 * k + 1), CY);
  curve((k) => M.F[k].norm, MG);
  if (M.K > 0) curve((k) => Math.sqrt(2 * k + 1) / M.K, AM, true);
  ctx.strokeStyle = 'rgba(255,255,255,0.35)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(X(n), pt); ctx.lineTo(X(n), pt + ih); ctx.stroke();
  lab(ctx, 'n', pl + iw, pt + ih + 4 * dpr, 'right', 'top');
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>‖P<sub>n</sub>‖ = √(2n + 1)</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('截断迹泛函的范数', 'norm of the truncated trace')}</span><span class="it"><i class="sw" style="--c:${AM}"></i>${T('逆的范数下界', 'lower bound for an inverse')} √(2n + 1)/K</span>`;
}
/* the ring spectrum in the complex plane, coloured by momentum */
function drawSide() {
  const M = MODEL, F = frame2d(cv2, 40); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F;
  let x0 = 0, x1 = 0, y0 = 0, y1 = 0; for (const e of M.spec) { x0 = Math.min(x0, e.re); x1 = Math.max(x1, e.re); y0 = Math.min(y0, e.im); y1 = Math.max(y1, e.im); }
  const padX = (x1 - x0) * 0.08 + 0.05, padY = (y1 - y0) * 0.08 + 0.05; x0 -= padX; x1 += padX; y0 -= padY; y1 += padY;
  const X = (x) => pl + iw * (x - x0) / (x1 - x0), Y = (y) => pt + ih - ih * (y - y0) / (y1 - y0);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(X(x0), Y(0)); ctx.lineTo(X(x1), Y(0)); ctx.moveTo(X(0), Y(y0)); ctx.lineTo(X(0), Y(y1)); ctx.stroke();
  lab(ctx, 'Re λ', pl + iw, Y(0) - 3 * dpr, 'right', 'bottom'); lab(ctx, 'Im λ', X(0) + 4 * dpr, pt, 'left', 'top');
  lab(ctx, fr(x0, 1), pl, pt + ih + 4 * dpr, 'left', 'top'); lab(ctx, fr(x1, 1), pl + iw, pt + ih + 4 * dpr, 'right', 'top');
  lab(ctx, fr(y1, 1), pl - 4 * dpr, pt, 'right', 'top'); lab(ctx, fr(y0, 1), pl - 4 * dpr, pt + ih, 'right', 'bottom');
  for (const e of M.spec) {
    const qa = Math.min(e.j, M.N - e.j) / (M.N / 2), t = Math.pow(qa, 0.6);
    ctx.fillStyle = `rgba(${Math.round(255 * (1 - t) + 25 * t)},${Math.round(47 * (1 - t) + 240 * t)},${Math.round(208 * (1 - t) + 255 * t)},0.85)`;
    ctx.beginPath(); ctx.arc(X(e.re), Y(e.im), 2 * dpr, 0, 2 * Math.PI); ctx.fill();
  }
  ctx.strokeStyle = AM; ctx.lineWidth = 1.5 * dpr; ctx.beginPath(); ctx.arc(X(0), Y(0), 6 * dpr, 0, 2 * Math.PI); ctx.stroke();
  lab(ctx, '0', X(0) - 8 * dpr, Y(0) + 8 * dpr, 'right', 'top', AM);
  $('c2Meta').textContent = T(`环 ℤ${M.N} 上的 ${M.spec.length} 个本征值；颜色 = 动量 |q|（品红 q ≈ 0，青 q ≈ π），琥珀圈 = 0`, `${M.spec.length} eigenvalues on the ring ℤ${M.N}; colour = momentum |q| (magenta q ≈ 0, cyan q ≈ π), amber ring = 0`);
}

/* =====================================================================
   11. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const gText = (g) => (g < 0 ? '−' : '') + Math.abs(g).toFixed(1);
function readouts() {
  const M = MODEL, n = nNow(), f = M.F[n], Gd = GENS[M.gen];
  pill('pillA', 'n', String(n)); pill('pillB', '‖P_n‖²', String(2 * n + 1)); pill('pillC', T('泛函范数', 'TRACE NORM'), fr(f.norm, 3)); pill('pillD', 'g', gText(M.g));
  setRo([[T('生成元 · 力程 r · g', 'Generator · range r · g'), `${T(Gd.zh, Gd.en)} · r = ${M.G.r} · g = ${gText(M.g)}`],
    [T('‖P_n‖² = 2n + 1', '‖P_n‖² = 2n + 1'), `n = ${n} · ${2 * n + 1}`],
    [T('截断迹 ρ ↦ Σ_{|x|≤n} (tρ)(x, x)：范数 · 非零系数个数（Lean 的上界）', 'Truncated trace ρ ↦ Σ_{|x|≤n} (tρ)(x, x): norm · nonzero coefficients (Lean’s bound)'), `${fr(f.norm)} · ${f.a.size} (≤ ${M.bound})`],
    [T('若 t 可逆：‖t⁻¹‖ ≥ √(2n + 1)/K', 'If t were invertible: ‖t⁻¹‖ ≥ √(2n + 1)/K'), M.K > 0 ? `K = ${fr(M.K)} · ${fr(Math.sqrt(2 * n + 1) / M.K)}` : '—'],
    [T('环 ℤ_N：本征值个数 · 零本征值 · 最小非零 |λ|', 'Ring ℤ_N: eigenvalues · zero eigenvalues · smallest nonzero |λ|'), `N = ${M.N}: ${M.spec.length} · ${M.zeros} · ${fr(M.gap)}${M.gapJ >= 0 ? ` (q = ${M.gapJ <= M.N / 2 ? '' : '−'}2π·${Math.min(M.gapJ, M.N - M.gapJ)}/${M.N})` : ''}`]]);
  const corner = [...f.a.entries()].slice(0, 4).map(([key, c]) => `${fmtC(c, 2)}·ρ(${key.replace(',', ', ')})`).join(' + ').replace(/\+ -/g, '− ');
  $('roNote').innerHTML = T(`当前 n 的截断迹：${corner}${f.a.size > 4 ? ' + …' : ''}。内部的系数加起来都是 0，因为完整的迹把每个矩阵单位送到 0（trace_single_zero）。`, `The truncated trace at this n: ${corner}${f.a.size > 4 ? ' + …' : ''}. The interior coefficients all add up to 0, because the full trace sends every matrix unit to 0 (trace_single_zero).`);
}
function syncControls() {
  const M = MODEL;
  document.querySelectorAll('#genChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.gen === M.gen)));
  document.querySelectorAll('#ringChips .chip').forEach((b) => b.setAttribute('aria-pressed', String(+b.dataset.ring === M.N)));
  $('gSlider').value = M.g; $('gVal').textContent = gText(M.g);
}
const stateKey = () => `${S.gen}|${S.g}|${S.N}|${nNow()}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; toasted = false; syncControls(); $('marks').dataset.key = ''; glKey = ''; }
  if (!toasted && S.playing && S.nowFrac >= 1) {
    toasted = true; const M = MODEL;
    toast(T(`<b>n = ${NMAX}</b>：‖P_n‖ = √${2 * NMAX + 1} ≈ ${fr(Math.sqrt(2 * NMAX + 1), 2)}，截断迹的范数仍是 ${fr(M.K, 3)}——逆若存在，范数至少 ${fr(Math.sqrt(2 * NMAX + 1) / M.K, 2)}，并随 n 无界。`, `<b>n = ${NMAX}</b>: ‖P_n‖ = √${2 * NMAX + 1} ≈ ${fr(Math.sqrt(2 * NMAX + 1), 2)}, while the truncated trace still has norm ${fr(M.K, 3)} — an inverse would need norm at least ${fr(Math.sqrt(2 * NMAX + 1) / M.K, 2)}, and unboundedly more as n grows.`));
  }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  const M = MODEL, n = nNow();
  readouts();
  $('formula').innerHTML = `⟨P<sub>n</sub>, tρ⟩ = Σ<sub>|x|≤n</sub> (tρ)(x, x), &nbsp; |⟨P<sub>n</sub>, tρ⟩| ≤ K‖ρ‖, &nbsp; ‖P<sub>n</sub>‖ = √(2n + 1)`;
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('genNote').innerHTML = T(`时间轴 = n，从 0 到 ${NMAX}。g 只乘耗散项；g = 0 时只剩 −i[H, ρ]。`, `The time axis is n, from 0 to ${NMAX}. g multiplies the dissipator only; at g = 0 only −i[H, ρ] remains.`);
  $('litNote').innerHTML = T('系数、范数与环上的谱都由页面按 Lindblad 矩阵元公式算出；冻结的是对 ℓ²(ℤ × ℤ) 上任意有限力程、平移不变的生成元都有 0 ∈ σ(t)。', 'The coefficients, norms and ring spectra are computed on the page from the Lindblad matrix-entry formula; what is frozen is that 0 ∈ σ(t) for every finite-range translation-invariant generator on ℓ²(ℤ × ℤ).');
  $('c1Title').textContent = T('范数随 n：‖P_n‖ 增长，截断迹不增长', 'Norms against n: ‖P_n‖ grows, the truncated trace does not');
  $('c2Title').textContent = T('同一个生成元在环 ℤ_N 上的谱（页面数值）', 'The same generator on the ring ℤ_N (page numbers)');
  $('clock').innerHTML = `n = ${n}`;
  $('hudBig').textContent = `n = ${n} · ‖P_n‖ = √${2 * n + 1} · ${T('截断迹范数', 'trace norm')} ${fr(M.F[n].norm, 3)}`;
  $('hudSub').textContent = T('平面是核的坐标 (u, v)；青柱 = P_n（对角线上 |x| ≤ n 处为 1），灰柱 = 各个 (tρ)(x, x) 用到的系数之和 Σ|c|，品红柱 = 加起来以后剩下的系数 |a_n|，琥珀框 = Lean 证明允许系数出现的边界区域', 'The plane holds kernel coordinates (u, v); cyan bars = P_n (1 on the diagonal for |x| ≤ n), grey bars = the summed size Σ|c| of the coefficients used by the individual (tρ)(x, x), magenta bars = the coefficients |a_n| left after adding, amber frames = the boundary region where the Lean proof allows coefficients');
}
function syncRail() {
  const M = MODEL, key = `${M.id}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, 'n = 0']];
  const f = M.nStar / NMAX; if (M.nStar < NMAX && f > 0.12 && f < 0.88) marks.push([f, T(`‖P_n‖ > 2K（n = ${M.nStar}）`, `‖P_n‖ > 2K (n = ${M.nStar})`)]);
  marks.push([1, `n = ${NMAX}`]);
  $('marks').innerHTML = marks.map(([x, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(x * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
function custom() { S.preset = null; markPreset(); dirty = true; }
document.querySelectorAll('#genChips .chip').forEach((b) => b.addEventListener('click', () => { S.gen = GENS[b.dataset.gen] ? b.dataset.gen : 'deph'; custom(); }));
document.querySelectorAll('#ringChips .chip').forEach((b) => b.addEventListener('click', () => { S.N = RINGS.includes(+b.dataset.ring) ? +b.dataset.ring : 24; custom(); }));
$('gSlider').addEventListener('input', () => { S.g = Math.round(parseFloat($('gSlider').value) * 10) / 10; custom(); });
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.gen = p.gen; S.g = p.g; S.N = p.N; S.preset = name; markPreset(); dirty = true;
  S.nowFrac = p.frac; S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.nowFrac;
  build(); setCamPreset(p.cam);
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo((nNow() + (ev.key === 'ArrowRight' ? 1 : -1)) / NMAX); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(1);
});

/* =====================================================================
   12. Main loop
   ===================================================================== */
let lastT = performance.now(), frameCount = 0, glKey = '';
function resize() {
  if (!glOK) return;
  const r = stage.getBoundingClientRect();
  renderer.setSize(Math.max(1, r.width), Math.max(1, r.height), false);
  camera.aspect = Math.max(0.2, r.width / Math.max(1, r.height)); camera.updateProjectionMatrix();
}
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
    const k = `${MODEL.id}|${nNow()}`;
    if (k !== glKey) { updateGL(); glKey = k; }
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.LZ_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => {
    const M = MODEL, n = nNow(), f = M.F[n];
    return { gen: M.gen, g: M.g, N: M.N, r: M.G.r, n, nmax: NMAX, norm: f.norm, K: M.K, bound: M.bound, nStar: M.nStar,
      a: [...f.a.entries()].map(([key, c]) => [...key.split(',').map(Number), c[0], c[1]]),
      norms: M.F.map((x) => x.norm), counts: M.F.map((x) => x.a.size),
      zeros: M.zeros, gap: M.gap, gapJ: M.gapJ, nev: M.spec.length };
  },
  /* the generator's defining tables, so a test can rebuild the operator itself */
  genData: (name) => { const G = GENS[name]; return G ? { r: G.r, h: Object.entries(G.h).map(([d, c]) => [+d, c[0], c[1]]), l: Object.entries(G.l).map(([ab, c]) => [...ab.split(',').map(Number), c[0], c[1]]) } : null; },
  spectrum: () => MODEL.spec.map((e) => [e.re, e.im, e.j]),
  setFrac: (f) => { S.nowFrac = Math.min(1, Math.max(0, f)); $('now').value = S.nowFrac; }
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('deph'); S.playing = false; setPlayUI(); S.nowFrac = 0.5; $('now').value = 0.5; setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 19; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('deph');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
