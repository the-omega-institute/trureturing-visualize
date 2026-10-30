/* CATER//PAIRS · caterpillars that only the third principal specialization cannot tell apart
   Bingham, Celano, Commins, Orellana, Pan and Simone (2026, Remark 3.11) asked (1) whether α_j = (5, j, j, 4, 3) and
   β_j = (4, j, j, 5, 3) have ps(·, 2) different and ps(·, 3) equal for every j, and (2) whether, with (5, 4, 3)/(4, 5, 3),
   they are the only such pairs. Frozen in trureturing: (1) holds for every j (BinghamCaterpillarPs3Family.result), (2) fails
   (BinghamCaterpillarUniquenessRefutation.result) with the 18-vertex pair (2,2,2,2,2,1,4,3)/(2,2,3,2,3,4,2). The page
   computes ps with a transfer matrix along the spine and searches every admissible composition up to n = 18.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Constants and polynomials
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.5, 0.58, 0.68], VIOLET = '#9d8cff', VIO3 = [0.62, 0.55, 1];
const JMAX = 12, NMIN = 6, NMAX = 18;
/* a polynomial is an array of integer coefficients, index = degree */
function pmul(a, b) { const r = new Array(a.length + b.length - 1).fill(0); for (let i = 0; i < a.length; i++) if (a[i]) for (let j = 0; j < b.length; j++) r[i + j] += a[i] * b[j]; return r; }
function padd(a, b) { const r = new Array(Math.max(a.length, b.length)).fill(0); a.forEach((v, i) => { r[i] += v; }); b.forEach((v, i) => { r[i] += v; }); return r; }
const psub = (a, b) => padd(a, b.map((v) => -v));
const trim = (a) => { const r = a.slice(); while (r.length > 1 && r[r.length - 1] === 0) r.pop(); return r; };
const peq = (a, b) => { const x = trim(a), y = trim(b); return x.length === y.length && x.every((v, i) => v === y[i]); };
/* block weight of a spine vertex of colour c with m − 1 leaves: X^c·(Σ_{d≠c} X^d)^{m−1} */
const blockCache = new Map();
function block(m, c, k) {
  const key = `${m}|${c}|${k}`; if (blockCache.has(key)) return blockCache.get(key);
  const leaf = Array.from({ length: k }, (_, d) => (d === c ? 0 : 1));
  let p = new Array(c + 1).fill(0); p[c] = 1;
  for (let i = 1; i < m; i++) p = pmul(p, leaf);
  blockCache.set(key, p); return p;
}
/* ps(C_a, k) by a transfer matrix along the spine: vec[c] sums the spine colourings ending in colour c */
function ps(a, k) {
  let vec = Array.from({ length: k }, (_, c) => block(a[0], c, k));
  for (let i = 1; i < a.length; i++) {
    const tot = vec.reduce(padd, [0]);
    vec = vec.map((v, c) => pmul(block(a[i], c, k), psub(tot, v)));
  }
  return trim(vec.reduce(padd, [0]));
}
const alpha = (j) => [5, j, j, 4, 3], beta = (j) => [4, j, j, 5, 3];
const BASE = [[5, 4, 3], [4, 5, 3]], WITNESS = [[2, 2, 2, 2, 2, 1, 4, 3], [2, 2, 3, 2, 3, 4, 2]];
const rev = (a) => a.slice().reverse();
const lexLE = (a, b) => { for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) return a[i] < b[i]; return a.length <= b.length; };
const canon = (a) => (lexLE(a, rev(a)) ? a.slice() : rev(a));
const same = (a, b) => a.length === b.length && a.every((v, i) => v === b[i]);
const samePair = (p, q) => { const [a, b] = p.map(canon), [c, d] = q.map(canon); return (same(a, c) && same(b, d)) || (same(a, d) && same(b, c)); };
/* listed: the base pair or some α_j/β_j, up to reversal and swapping (j ≤ n bounds the family) */
function listedAs(p) {
  if (samePair(p, BASE)) return 'base';
  const n = p[0].reduce((s, v) => s + v, 0);
  for (let j = 1; 2 * j + 12 <= n; j++) if (samePair(p, [alpha(j), beta(j)])) return `j = ${j}`;
  return null;
}
const admissible = (a) => (a.length === 1 && a[0] === 1) || (a[0] >= 2 && a[a.length - 1] >= 2);

/* =====================================================================
   2. The exhaustive search, one n per frame
   ===================================================================== */
const SEARCH = new Map();   /* n → { classes, pairs: [[a, b, listed]] } */
function searchN(n) {
  const groups = new Map(); let classes = 0;
  const walkComp = (rest, pre) => {
    if (rest === 0) { if (admissible(pre) && lexLE(pre, rev(pre))) { classes++; const key = ps(pre, 3).join(','); if (!groups.has(key)) groups.set(key, []); groups.get(key).push(pre.slice()); } return; }
    for (let f = 1; f <= rest; f++) { pre.push(f); walkComp(rest - f, pre); pre.pop(); }
  };
  walkComp(n, []);
  const pairs = [];
  /* ps(·, 2) once per member: a group can be large, so the pairwise loop only compares keys */
  for (const g of groups.values()) { const k2 = g.map((a) => ps(a, 2).join(',')); for (let x = 0; x < g.length; x++) for (let y = x + 1; y < g.length; y++) if (k2[x] !== k2[y]) pairs.push([g[x], g[y], listedAs([g[x], g[y]])]); }
  SEARCH.set(n, { classes, pairs });
}
let searchNext = 1;
const searchDone = () => searchNext > NMAX;

/* =====================================================================
   3. State and presets
   ===================================================================== */
const S = { mode: 'family', j: 1, n: 12, pick: 0, fixed: null, t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'family' };
const PRESETS = {
  family: { mode: 'family', j: 1, play: true,
    zh: '名单里的整族 α_j = (5, j, j, 4, 3)、β_j = (4, j, j, 5, 3)，j 从 1 走到 12。每个 j 上两条三色主特化完全相同（天际线两两等高），二色主特化却是 X^{j+5} + X^{j+7} 对 2X^{j+6}。Lean 对所有正整数 j 证明了这一点。',
    en: 'The listed family α_j = (5, j, j, 4, 3), β_j = (4, j, j, 5, 3), with j running from 1 to 12. For every j the two three-colour specializations agree exactly (the skyline bars come in equal pairs), while the two-colour ones are X^{j+5} + X^{j+7} against 2X^{j+6}. Lean proves this for every positive integer j.' },
  base: { mode: 'fixed', pair: BASE, play: false,
    zh: '原文的基本对 (5, 4, 3) 与 (4, 5, 3)，12 个顶点：二色主特化 X⁵ + X⁷ 对 2X⁶，三色主特化的 17 个系数 1, 7, 31, …, 1102, …, 7, 1 完全相同。',
    en: 'The source’s base pair (5, 4, 3) and (4, 5, 3), 12 vertices: two-colour specializations X⁵ + X⁷ against 2X⁶, while the 17 coefficients 1, 7, 31, …, 1102, …, 7, 1 of the three-colour specialization agree.' },
  witness: { mode: 'fixed', pair: WITNESS, play: false,
    zh: 'Lean 的反例：(2, 2, 2, 2, 2, 1, 4, 3) 与 (2, 2, 3, 2, 3, 4, 2)，各 18 个顶点。二色主特化 X⁸ + X¹⁰ 对 2X⁹，三色主特化相同；前者的脊柱有 8 段，名单里的毛毛虫都不到 8 段，所以这对不在名单里——第二问不成立。',
    en: 'Lean’s counterexample: (2, 2, 2, 2, 2, 1, 4, 3) and (2, 2, 3, 2, 3, 4, 2), 18 vertices each. Two-colour specializations X⁸ + X¹⁰ against 2X⁹, equal three-colour ones; the first spine has 8 parts while every listed caterpillar has fewer, so the pair is not listed — the second question fails.' },
  search: { mode: 'search', n: NMIN, play: true,
    zh: '对 n = 6 到 18 的全部可容许组合（每对反转只取一个）按三色主特化分组，列出组内二色主特化不同的成对。n ≤ 17 只出现名单里的成对（n = 12、14、16），n = 18 一下子出现 6 对：1 对是名单里的 j = 3，另外 5 对不在名单里。页面数值。',
    en: 'Every admissible composition with n = 6 to 18 (one of each reversal pair) is grouped by its three-colour specialization, and the pairs in a group with different two-colour ones are listed. Up to n = 17 only listed pairs appear (n = 12, 14, 16); at n = 18 six pairs appear at once: one is the listed j = 3, the other five are unlisted. Page numbers.' },
  other: { mode: 'search', n: 18, pickPair: [[3, 3, 3, 4, 5], [3, 3, 3, 5, 4]], play: false,
    zh: '搜索在 n = 18 找到的另一对名单外的成对：(3, 3, 3, 4, 5) 与 (3, 3, 3, 5, 4)——像基本对 (3, 4, 5)/(3, 5, 4) 前面接上两段 3。它是否属于某个无限族，卷宗列为未决。页面数值，不是定理。',
    en: 'Another unlisted pair the search finds at n = 18: (3, 3, 3, 4, 5) and (3, 3, 3, 5, 4) — like the base pair (3, 4, 5)/(3, 5, 4) with two parts 3 in front. Whether it belongs to an infinite family is open in the dossier. Page numbers, not a theorem.' },
  big: { mode: 'family', j: 5, play: false,
    zh: 'j = 5：α₅ = (5, 5, 5, 4, 3)、β₅ = (4, 5, 5, 5, 3)，22 个顶点。三色主特化有 31 个非零系数（次数 7 到 37），最大的是 819624，两边逐项相同；二色主特化 X¹⁰ + X¹² 对 2X¹¹。',
    en: 'j = 5: α₅ = (5, 5, 5, 4, 3), β₅ = (4, 5, 5, 5, 3), 22 vertices. The three-colour specialization has 31 nonzero coefficients (degrees 7 to 37), the largest 819624, equal term by term; the two-colour ones are X¹⁰ + X¹² against 2X¹¹.' }
};

/* =====================================================================
   4. The model
   ===================================================================== */
let MODEL = null, dirty = true, modelId = 0;
const sizeOf = (a) => a.reduce((s, v) => s + v, 0);
function currentPair() {
  if (S.mode === 'family') return [alpha(S.j), beta(S.j)];
  if (S.mode === 'fixed' && S.fixed) return S.fixed;
  const res = SEARCH.get(S.n); if (!res || !res.pairs.length) return null;
  return res.pairs[Math.min(S.pick, res.pairs.length - 1)];
}
function build() {
  S.j = Math.min(JMAX, Math.max(1, Math.round(S.j))); S.n = Math.min(NMAX, Math.max(NMIN, Math.round(S.n)));
  const pr = currentPair();
  if (!pr) { MODEL = { id: ++modelId, pair: null, n: S.n }; return; }
  const [a, b] = pr, p2a = ps(a, 2), p2b = ps(b, 2), p3a = ps(a, 3), p3b = ps(b, 3);
  const diff3 = psub(p3a, p3b).reduce((m, v) => Math.max(m, Math.abs(v)), 0);
  MODEL = { id: ++modelId, pair: [a.slice(), b.slice()], n: sizeOf(a), p2a, p2b, p3a, p3b, diff3, eq3: peq(p3a, p3b), eq2: peq(p2a, p2b), listed: listedAs([a, b]) };
}

/* =====================================================================
   5. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');

/* =====================================================================
   6. 3D scene: two caterpillars in front, the ps(·, 3) skyline behind, ps(·, 2) further back
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 6000, PTS_MAX = 600;
const CAMS = { iso: [0.55, 1.05, 21], front: [0.0001, 1.38, 20], top: [0.0001, 0.06, 22] };
const cam = { theta: 0.55, phi: 1.05, r: 21, tTheta: 0.55, tPhi: 1.05, tR: 21 };
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
  camera = new THREE.PerspectiveCamera(38, 1, 0.05, 120);
  const g = new THREE.BufferGeometry(); dyn(g, 'position', LINES_MAX, 3); dyn(g, 'color', LINES_MAX, 3);
  lines = new THREE.LineSegments(g, new THREE.LineBasicMaterial({ vertexColors: true, ...additive })); lines.frustumCulled = false; scene3.add(lines);
  const gp = new THREE.BufferGeometry(); dyn(gp, 'position', PTS_MAX, 3); dyn(gp, 'aColor', PTS_MAX, 3); dyn(gp, 'aAlpha', PTS_MAX, 1); dyn(gp, 'aSize', PTS_MAX, 1);
  pts = new THREE.Points(gp, new THREE.ShaderMaterial({ vertexShader: EVT_VS, fragmentShader: DOT_FS, uniforms: { uScale: { value: 60 } }, ...additive }));
  pts.frustumCulled = false; scene3.add(pts);
}
/* layout: caterpillar A at z = ZA, B at z = ZB (front); skyline of ps(·, 3) at z = Z3; ps(·, 2) at z = Z2; degrees along x */
const ZA = 4.6, ZB = 7.4, Z3 = -0.6, Z2 = 2.0, HL = 1.15;
function geom(M) {
  const deg = Math.max(M.p3a.length, M.p3b.length), DX = Math.min(0.5, 12 / deg), SP = Math.min(1.25, 11 / Math.max(M.pair[0].length, M.pair[1].length));
  return { DX, SP, xd: (d) => (d - (deg - 1) / 2) * DX, deg, spineX: (i, l) => (i - (l - 1) / 2) * SP };
}
function updateGL() {
  const M = MODEL;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, col, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = col[0] * k; Cc[3 * v + 1] = col[1] * k; Cc[3 * v + 2] = col[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, col, al, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = col[0]; PT.aColor.array[3 * np + 1] = col[1]; PT.aColor.array[3 * np + 2] = col[2]; PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  if (M.pair) {
    const G = geom(M);
    /* the two caterpillars: spine amber, leaves fanned behind (A, cyan) or in front (B, magenta) */
    M.pair.forEach((a, w) => {
      const z0 = w === 0 ? ZA : ZB, side = w === 0 ? -1 : 1, leafCol = w === 0 ? COL.cyan : COL.magenta;
      a.forEach((m, i) => {
        const x = G.spineX(i, a.length);
        if (i + 1 < a.length) seg([x, 0.02, z0], [G.spineX(i + 1, a.length), 0.02, z0], COL.amber, 0.95);
        dot([x, 0.02, z0], COL.amber, 1, 1.6);
        for (let r = 1; r < m; r++) {
          const ang = Math.PI * (r - 0.5) / (m - 1) - Math.PI / 2, L = 0.9;
          const q = [x + L * 0.55 * Math.sin(ang), 0.02, z0 + side * L * Math.cos(ang)];
          seg([x, 0.02, z0], q, leafCol, 0.7); dot(q, leafCol, 0.95, 1.0);
        }
      });
    });
    /* floor under the skylines */
    const x0 = G.xd(0) - 0.4, x1 = G.xd(G.deg - 1) + 0.4;
    for (const z of [Z3, Z2]) seg([x0, 0, z], [x1, 0, z], GREY, 0.35);
    for (let d = 0; d < G.deg; d += 5) seg([G.xd(d), 0, Z3 - 0.25], [G.xd(d), 0, Z3 + 0.25], GREY, 0.5);
    /* ps(·, 3): log₁₀(1 + coefficient), A cyan and B amber side by side */
    const h = (c) => HL * Math.log10(1 + Math.max(0, c));
    for (let d = 0; d < G.deg; d++) {
      const ca = M.p3a[d] || 0, cb = M.p3b[d] || 0, x = G.xd(d), bad = ca !== cb;
      if (ca > 0) { seg([x - 0.08, 0, Z3], [x - 0.08, h(ca), Z3], bad ? COL.magenta : COL.cyan, 1); dot([x - 0.08, h(ca), Z3], COL.cyan, 0.9, 1.0); }
      if (cb > 0) { seg([x + 0.08, 0, Z3], [x + 0.08, h(cb), Z3], bad ? COL.magenta : COL.amber, 1); dot([x + 0.08, h(cb), Z3], COL.amber, 0.9, 1.0); }
    }
    /* ps(·, 2): the two colourings of each tree, height = coefficient */
    const deg2 = Math.max(M.p2a.length, M.p2b.length);
    for (let d = 0; d < deg2; d++) {
      const ca = M.p2a[d] || 0, cb = M.p2b[d] || 0, x = G.xd(d);
      if (ca) { seg([x - 0.08, 0, Z2], [x - 0.08, 0.9 * ca, Z2], COL.cyan, 1); dot([x - 0.08, 0.9 * ca, Z2], COL.cyan, 1, 1.4); }
      if (cb) { seg([x + 0.08, 0, Z2], [x + 0.08, 0.9 * cb, Z2], VIO3, 1); dot([x + 0.08, 0.9 * cb, Z2], VIO3, 1, 1.4); }
    }
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
  const sp = Math.sin(cam.phi), r = cam.r * (camera.aspect < 1.2 ? 1.45 : 1), c = [0, 1.4, 2.4];
  camera.position.set(c[0] + r * sp * Math.sin(cam.theta), c[1] + r * Math.cos(cam.phi), c[2] + r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(c[0], c[1], c[2]);
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
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()]; drag.pinch = Math.hypot(p.x - q.x, p.y - q.y); }
});
stage.addEventListener('pointermove', (ev) => {
  if (!drag.pts.has(ev.pointerId)) return;
  drag.pts.set(ev.pointerId, { x: ev.clientX, y: ev.clientY });
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(50, Math.max(7, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(50, Math.max(7, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

/* =====================================================================
   8. Tags
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
  if (M.pair) {
    const G = geom(M), la = M.pair[0].length, lb = M.pair[1].length;
    put(`A = (${M.pair[0].join(', ')})`, [G.spineX(0, la) - 1.2, 0, ZA], 'cy');
    put(`B = (${M.pair[1].join(', ')})`, [G.spineX(0, lb) - 1.2, 0, ZB], 'mg');
    put(T('三色主特化 ps(·, 3)', 'three colours ps(·, 3)'), [G.xd(G.deg - 1) + 0.9, 0.3, Z3], 'hot');
    put(T('二色主特化 ps(·, 2)', 'two colours ps(·, 2)'), [G.xd(Math.max(M.p2a.length, M.p2b.length) - 1) + 0.4, 2.2, Z2], 'vi');
  } else put(T(`n = ${M.n}：没有这样的成对`, `n = ${M.n}: no such pair`), [0, 0.5, 2], 'gr');
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
/* ps(·, 3) upwards on a log scale (A filled, B outlined), ps(·, 2) downwards */
function drawMain() {
  const M = MODEL, F = frame2d(cv1, 40); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F;
  if (!M.pair) { lab(ctx, T('这个 n 上没有这样的成对', 'No such pair at this n'), pl + iw / 2, pt + ih / 2, 'center', 'middle'); $('c1Meta').innerHTML = ''; return; }
  const deg = Math.max(M.p3a.length, M.p3b.length), up = ih * 0.72, y0 = pt + up, down = ih - up;
  const top = Math.log10(1 + Math.max(...M.p3a, ...M.p3b)), bw = iw / deg, X = (d) => pl + bw * (d + 0.5);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, y0); ctx.lineTo(pl + iw, y0); ctx.stroke();
  for (const e of [0, Math.floor(top)]) lab(ctx, `10^${e}`, pl - 4 * dpr, y0 - up * Math.log10(1 + 10 ** e) / top, 'right', 'middle');
  lab(ctx, '2', pl - 4 * dpr, y0 + down * 0.9, 'right', 'middle', VIOLET);
  for (let d = 0; d < deg; d++) {
    const ca = M.p3a[d] || 0, cb = M.p3b[d] || 0, ha = up * Math.log10(1 + ca) / top, hb = up * Math.log10(1 + cb) / top;
    ctx.fillStyle = ca === cb ? CY : MG; ctx.globalAlpha = 0.75; ctx.fillRect(X(d) - bw * 0.35, y0 - ha, bw * 0.7, ha); ctx.globalAlpha = 1;
    ctx.strokeStyle = AM; ctx.lineWidth = 1.2 * dpr; ctx.strokeRect(X(d) - bw * 0.35, y0 - hb, bw * 0.7, hb);
    const pa = M.p2a[d] || 0, pb = M.p2b[d] || 0;
    if (pa) { ctx.fillStyle = CY; ctx.fillRect(X(d) - bw * 0.35, y0 + 1, bw * 0.32, down * 0.45 * pa); }
    if (pb) { ctx.fillStyle = VIOLET; ctx.fillRect(X(d) + bw * 0.03, y0 + 1, bw * 0.32, down * 0.45 * pb); }
  }
  const step = Math.max(1, Math.ceil(deg / 12));
  for (let d = 0; d < deg; d += step) lab(ctx, String(d), X(d), pt + ih + 4 * dpr, 'center', 'top');
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>ps(A, 3)</span><span class="it"><i class="sw" style="--c:${AM}"></i>ps(B, 3)</span><span class="it"><i class="sw" style="--c:${VIOLET}"></i>${T('下方：ps(·, 2)', 'below: ps(·, 2)')}</span>`;
}
/* pairs found at each n: listed (cyan) and unlisted (magenta) */
function drawSide() {
  const F = frame2d(cv2, 26); if (F.iw < 60 || F.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F, ns = NMAX - NMIN + 1, bw = iw / ns, X = (n) => pl + bw * (n - NMIN + 0.5);
  let top = 1; for (let n = NMIN; n <= NMAX; n++) if (SEARCH.has(n)) top = Math.max(top, SEARCH.get(n).pairs.length);
  const Y = (c) => pt + ih - ih * c / (top + 0.5);
  ctx.strokeStyle = FAINT; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(0)); ctx.lineTo(pl + iw, Y(0)); ctx.stroke();
  for (const c of [0, top]) lab(ctx, String(c), pl - 4 * dpr, Y(c), 'right', 'middle');
  for (let n = NMIN; n <= NMAX; n++) {
    const cur = S.mode !== 'family' && n === (MODEL.n || S.n);
    if (cur) { ctx.fillStyle = 'rgba(255,200,61,0.10)'; ctx.fillRect(X(n) - bw / 2, pt, bw, ih); }
    const res = SEARCH.get(n);
    if (res) {
      const li = res.pairs.filter((p) => p[2]).length, un = res.pairs.length - li;
      ctx.fillStyle = CY; ctx.fillRect(X(n) - bw * 0.3, Y(li), bw * 0.6, Y(0) - Y(li));
      ctx.fillStyle = MG; ctx.fillRect(X(n) - bw * 0.3, Y(li + un), bw * 0.6, Y(li) - Y(li + un));
      if (res.pairs.length) lab(ctx, String(res.pairs.length), X(n), Y(li + un) - 2 * dpr, 'center', 'bottom', INK);
    } else lab(ctx, '…', X(n), Y(0) - 2 * dpr, 'center', 'bottom');
    lab(ctx, String(n), X(n), pt + ih + 4 * dpr, 'center', 'top', cur ? AM : DIM);
  }
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('名单里', 'listed')}</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('名单外', 'unlisted')}</span>`;
}

/* =====================================================================
   10. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const SUP = '⁰¹²³⁴⁵⁶⁷⁸⁹';
const sup = (n) => String(n).split('').map((d) => SUP[+d]).join('');
function polyTxt(p) { const terms = []; p.forEach((c, d) => { if (!c) return; terms.push(`${c === 1 && d ? '' : c}${d ? 'X' + (d > 1 ? sup(d) : '') : ''}`); }); return terms.join(' + ') || '0'; }
const listedTxt = (l) => (l === 'base' ? T('名单里：基本对', 'listed: the base pair') : l ? T(`名单里：${l}`, `listed: ${l}`) : T('不在名单里', 'not listed'));
function readouts() {
  const M = MODEL, res = SEARCH.get(S.n);
  if (!M.pair) {
    pill('pillA', 'n', S.n); pill('pillB', 'ps₂', '—'); pill('pillC', 'ps₃', '—'); pill('pillD', T('名单', 'LIST'), '—');
    setRo([[T('成对', 'Pair'), T('这个 n 上没有', 'none at this n')], ['ps(·, 2)', '—'], ['ps(·, 3)', '—'], [T('名单', 'List'), '—'],
      [T(`搜索 n = ${S.n}：同构类 · 成对 · 名单外`, `Search at n = ${S.n}: classes · pairs · unlisted`), res ? `${res.classes} · ${res.pairs.length} · ${res.pairs.filter((p) => !p[2]).length}` : '…']]);
    $('roNote').innerHTML = T(`n = ${S.n} 时没有“二色不同、三色相同”的成对。`, `At n = ${S.n} no pair has different two-colour and equal three-colour specializations.`);
    return;
  }
  pill('pillA', 'n', M.n); pill('pillB', 'ps₂', M.eq2 ? T('相同', 'equal') : T('不同', 'differ')); pill('pillC', 'ps₃', M.eq3 ? T('相同', 'equal') : T('不同', 'differ')); pill('pillD', T('名单', 'LIST'), M.listed ? T('在', 'yes') : T('不在', 'no'));
  setRo([[T('成对 A · B（顶点数 n）', 'Pair A · B (n vertices)'), `(${M.pair[0].join(', ')}) · (${M.pair[1].join(', ')}) · n = ${M.n}`],
    [T('二色主特化 ps(A, 2) · ps(B, 2)', 'Two colours ps(A, 2) · ps(B, 2)'), `${polyTxt(M.p2a)} · ${polyTxt(M.p2b)}`],
    [T('三色主特化：次数范围 · 系数和 3·2ⁿ⁻¹ · 最大系数 · A 与 B 的最大差', 'Three colours: degrees · sum 3·2ⁿ⁻¹ · largest coefficient · largest difference between A and B'), `${M.p3a.findIndex((c) => c > 0)}–${M.p3a.length - 1} · ${M.p3a.reduce((s, v) => s + v, 0)} · ${Math.max(...M.p3a)} · ${M.diff3}`],
    [T('名单', 'List'), listedTxt(M.listed)],
    [T(`搜索 n = ${M.n}：同构类 · 成对 · 名单外`, `Search at n = ${M.n}: classes · pairs · unlisted`), SEARCH.has(M.n) ? `${SEARCH.get(M.n).classes} · ${SEARCH.get(M.n).pairs.length} · ${SEARCH.get(M.n).pairs.filter((p) => !p[2]).length}` : (M.n > NMAX ? T(`超出搜索范围（n ≤ ${NMAX}）`, `beyond the search (n ≤ ${NMAX})`) : '…')]]);
  $('roNote').innerHTML = !M.eq2 && M.eq3
    ? (M.listed ? T('二色分得开、三色分不开——名单里的成对，符合原文的猜测。', 'Two colours tell them apart, three do not — a listed pair, as the source expected.') : T('二色分得开、三色分不开，可它不在名单里：第二问的反例。', 'Two colours tell them apart, three do not, yet the pair is not listed: a counterexample to the second question.'))
    : T('这一对没有这个现象。', 'This pair does not show the phenomenon.');
}
const stateKey = () => `${S.mode}|${S.j}|${S.n}|${S.pick}|${S.fixed ? S.fixed.join(';') : ''}|${S.preset}|${searchNext}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; syncControls(); }
  const M = MODEL;
  if (!toasted && S.playing && railPos() >= railMax()) { toasted = true; toast(S.mode === 'family' ? T(`<b>j = 1 … ${JMAX}</b>：每个 j 上三色主特化都相同、二色都不同——与 Lean 对所有 j 的定理一致。`, `<b>j = 1 … ${JMAX}</b>: for every j the three-colour specializations agree and the two-colour ones differ — as Lean proves for all j.`) : T(`<b>n = ${NMIN} … ${NMAX}</b>：名单外的成对第一次出现在 n = 18，一共 ${SEARCH.has(18) ? SEARCH.get(18).pairs.filter((p) => !p[2]).length : '…'} 对。`, `<b>n = ${NMIN} … ${NMAX}</b>: unlisted pairs first appear at n = 18, ${SEARCH.has(18) ? SEARCH.get(18).pairs.filter((p) => !p[2]).length : '…'} of them.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts(); pairChips();
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('pairNote').innerHTML = S.mode === 'family' ? T(`α_${S.j} = (5, ${S.j}, ${S.j}, 4, 3)，β_${S.j} = (4, ${S.j}, ${S.j}, 5, 3)。`, `α_${S.j} = (5, ${S.j}, ${S.j}, 4, 3), β_${S.j} = (4, ${S.j}, ${S.j}, 5, 3).`)
    : S.mode === 'fixed' ? T('固定的成对；拖动时间轴就转到搜索结果。', 'A fixed pair; moving the rail switches to the search results.')
      : searchDone() ? T(`n = ${S.n} 上找到的成对（每对反转只列一个方向）：`, `Pairs found at n = ${S.n} (one direction of each reversal):`) : T(`正在搜索……已完成到 n = ${searchNext - 1}`, `Searching… done up to n = ${searchNext - 1}`);
  $('litNote').innerHTML = T('多项式与搜索都由页面算出；冻结的是整族对所有 j 成立，以及 18 个顶点的那一对是名单外的反例。', 'The polynomials and the search are computed on the page; what is frozen is that the family holds for every j and that the 18-vertex pair is an unlisted counterexample.');
  $('c1Title').textContent = T('系数：上方 ps(·, 3)（对数刻度），下方 ps(·, 2)', 'Coefficients: ps(·, 3) above (log scale), ps(·, 2) below');
  $('c2Title').textContent = T('每个 n 上“二色不同、三色相同”的成对数', 'Pairs with different ps(·, 2) and equal ps(·, 3) at each n');
  $('clock').innerHTML = S.mode === 'family' ? `j = ${S.j}` : `n = ${S.mode === 'fixed' && M.pair ? M.n : S.n}`;
  $('hudBig').textContent = M.pair ? `n = ${M.n} · ps₂ ${M.eq2 ? '=' : '≠'} · ps₃ ${M.eq3 ? '=' : '≠'} · ${listedTxt(M.listed)}` : T(`n = ${S.n} · 没有这样的成对`, `n = ${S.n} · no such pair`);
  $('hudSub').textContent = T('前两排：毛毛虫 A（叶子青）与 B（叶子品红），脊柱琥珀。后面：ps(·, 3) 的系数天际线，每个次数一对柱子（A 青、B 琥珀），高度 log₁₀(1 + 系数)，不等处变品红。最后一排：ps(·, 2)，A 青、B 紫', 'Front rows: caterpillar A (cyan leaves) and B (magenta leaves), spine amber. Behind: the coefficient skyline of ps(·, 3), one pair of bars per degree (A cyan, B amber), height log₁₀(1 + coefficient), magenta where they differ. Last row: ps(·, 2), A cyan, B violet');
}
function pairChips() {
  const box = $('pairChips'); if (S.mode !== 'search') { box.innerHTML = ''; return; }
  const res = SEARCH.get(S.n);
  if (!res) { box.innerHTML = '<span class="pairs-empty">…</span>'; return; }
  if (!res.pairs.length) { box.innerHTML = `<span class="pairs-empty">${T('没有', 'none')}</span>`; return; }
  box.innerHTML = res.pairs.map((p, i) => `<button class="chip" data-pick="${i}" aria-pressed="${i === Math.min(S.pick, res.pairs.length - 1)}">${p[0].join('')}/${p[1].join('')}${p[2] ? '' : ' ✱'}</button>`).join('');
  box.querySelectorAll('[data-pick]').forEach((b) => b.addEventListener('click', () => { S.pick = parseInt(b.dataset.pick, 10); S.preset = null; markPreset(); dirty = true; }));
}
function syncControls() {
  $('jIn').value = S.j; $('jOut').textContent = S.j;
  document.querySelectorAll('#modeChips [data-mode]').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.mode === (S.mode === 'fixed' ? '' : S.mode))));
  $('now').value = railPos() / railMax();
}
/* the rail: j ∈ [1, 12] in family mode, n ∈ [6, 18] otherwise; S.t is the continuous position */
const railMin = () => (S.mode === 'family' ? 1 : NMIN), railMax = () => (S.mode === 'family' ? JMAX : NMAX);
const railPos = () => (S.mode === 'family' ? S.j : (S.mode === 'fixed' && MODEL && MODEL.pair ? Math.min(NMAX, MODEL.n) : S.n));
function syncRail() {
  const key = `${S.mode === 'family' ? 'j' : 'n'}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = S.mode === 'family' ? [[0, 'j = 1'], [(7 - 1) / (JMAX - 1), T('j = 7（原文检查到此）', 'j = 7 (checked in the source)')], [1, `j = ${JMAX}`]]
    : [[0, `n = ${NMIN}`], [(16 - NMIN) / (NMAX - NMIN), T('16（原文搜到此）', '16 (searched in the source)')], [1, `n = ${NMAX}`]];
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(name) {
  const p = PRESETS[name]; if (!p) return;
  S.mode = p.mode; S.preset = name; S.pick = 0; S.hold = 0; toasted = false;
  if (p.mode === 'family') { S.j = p.j; S.t = p.j; }
  if (p.mode === 'fixed') { S.fixed = p.pair.map((a) => a.slice()); S.n = Math.min(NMAX, sizeOf(p.pair[0])); }
  if (p.mode === 'search') { S.n = p.n; S.t = p.n; if (p.pickPair) S.pickPair = p.pickPair; }
  markPreset(); dirty = true;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI();
  build(); dirty = true; setCamPreset('iso'); $('marks').dataset.key = '';
  TRV.glitch($('app'));
}
/* a preset may name a pair at its n; pick it once the search has reached that n */
function resolvePick() {
  if (!S.pickPair || S.mode !== 'search' || !SEARCH.has(S.n)) return;
  const i = SEARCH.get(S.n).pairs.findIndex((p) => samePair([p[0], p[1]], S.pickPair)); S.pickPair = null;
  if (i >= 0) { S.pick = i; dirty = true; }
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; $('marks').dataset.key = ''; };
document.querySelectorAll('#modeChips [data-mode]').forEach((b) => b.addEventListener('click', () => { S.mode = b.dataset.mode; S.pick = 0; custom(); }));
$('jIn').addEventListener('input', () => { S.mode = 'family'; S.j = parseInt($('jIn').value, 10); custom(); });
function setRail(v, user) {
  const lo = railMin(), hi = railMax(); v = Math.min(hi, Math.max(lo, v)); S.t = v;
  const k = Math.round(v);
  if (S.mode === 'family') { if (k !== S.j) { S.j = k; dirty = true; } }
  else { if (S.mode === 'fixed') { if (!user) return; S.mode = 'search'; dirty = true; } if (k !== S.n) { S.n = k; S.pick = 0; dirty = true; } }
  $('now').value = (v - lo) / (hi - lo);
  if (user) custom();
}
$('now').addEventListener('input', () => { setRail(railMin() + parseFloat($('now').value) * (railMax() - railMin()), true); S.hold = 0; });
let scrubbing = false;
$('now').addEventListener('pointerdown', () => { scrubbing = true; });
window.addEventListener('pointerup', () => { scrubbing = false; });
window.addEventListener('pointercancel', () => { scrubbing = false; });
function setPlayUI() { $('play').textContent = S.playing ? '❚❚' : '▶'; $('play').setAttribute('aria-pressed', String(S.playing)); $('rev').setAttribute('aria-pressed', String(S.dir < 0)); }
$('play').addEventListener('click', () => { if (S.mode === 'fixed') { S.mode = 'search'; S.t = S.n; dirty = true; } S.playing = !S.playing; S.hold = 0; setPlayUI(); });
$('rev').addEventListener('click', () => { S.dir = -S.dir; S.playing = true; S.hold = 0; setPlayUI(); });
document.querySelectorAll('#speedChips .chip').forEach((b) => b.addEventListener('click', () => {
  S.speed = parseFloat(b.dataset.speed);
  document.querySelectorAll('#speedChips .chip').forEach((c) => c.setAttribute('aria-pressed', String(c === b)));
}));
const drawer = TRV.drawer({ drawer: $('drawer'), open: $('infoBtn'), close: $('drawerClose') });
const jumpTo = (v) => { S.playing = false; setPlayUI(); setRail(v, true); };
document.addEventListener('keydown', (ev) => {
  if (ev.target && (ev.target.tagName === 'INPUT' && ev.target.type !== 'range')) return;
  if (drawer.isOpen()) return;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); jumpTo(Math.round(railPos()) + (ev.key === 'ArrowRight' ? 1 : -1)); }
  else if (ev.key === 'e' || ev.key === 'E') jumpTo(railMax());
});

/* =====================================================================
   11. Main loop
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
  if (!searchDone()) { searchN(searchNext); searchNext++; if (S.mode === 'search') dirty = true; }
  resolvePick();
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing && S.mode !== 'fixed') {
    const lo = railMin(), hi = railMax();
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setRail(S.dir > 0 ? lo : hi); toasted = false; } }
    else {
      setRail(S.t + S.dir * dtSec * S.speed * 1.1);
      if (S.t >= hi) S.hold = 2.4;
      if (S.t <= lo && S.dir < 0) S.hold = 1.2;
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
window.CP_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return M.pair ? { pair: M.pair, n: M.n, p2a: M.p2a, p2b: M.p2b, p3a: M.p3a, p3b: M.p3b, eq2: M.eq2, eq3: M.eq3, diff3: M.diff3, listed: M.listed } : { pair: null, n: M.n }; },
  searchDone,
  search: () => [...SEARCH.entries()].map(([n, r]) => ({ n, classes: r.classes, pairs: r.pairs.map((p) => ({ a: p[0], b: p[1], listed: p[2] })) })),
  ps: (a, k) => ps(a, k),
  setRail: (v) => setRail(v)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('witness'); S.playing = false; setPlayUI(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 18; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('family');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
