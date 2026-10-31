/* PERM//COMPLEMENT · at most 2^{v₂(n)} pairwise strongly complementary n × n permutation matrices
   Rajchel, Gąsiorowski and Życzkowski (2018) call permutation matrices P, Q complementary when P_ij = P_hk = Q_ik = 1 forces
   Q_hj = 1, and strongly complementary when moreover their supports are disjoint; disjoint supports give k ≤ n, and they ask
   how the largest family depends on n. Proved in trureturing (StronglyComplementaryPermutationMaximum.result): the maximum is
   2^{v₂(n)}. In permutation terms σ, τ are strongly complementary when σ⁻¹τ is a fixed-point-free involution; the translations
   of the first coordinate of (Z/2)^a × [m], n = 2^a m, attain the bound.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Permutations, the translation family and an exhaustive search
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.42, 0.5, 0.6], WHITE = [0.92, 0.95, 1];
const NMAX = 32, EXH = 10;
const v2 = (n) => { let a = 0; while (n % 2 === 0 && n > 0) { n /= 2; a++; } return a; };
const kOf = (n) => 2 ** v2(n);
/* i = x + 2^a·b with x ∈ (Z/2)^a written in binary and b ∈ [m]; σ_v translates x by v */
function family(n) { const K = kOf(n); return Array.from({ length: K }, (_, v) => Array.from({ length: n }, (_, i) => ((i % K) ^ v) + K * Math.floor(i / K))); }
const inv = (s) => { const r = new Array(s.length); s.forEach((x, i) => { r[x] = i; }); return r; };
const compose = (s, t) => t.map((x) => s[x]);              /* (s ∘ t)(i) = s(t(i)) */
const relative = (s, t) => compose(inv(s), t);              /* σ⁻¹τ */
const isFPFInvolution = (r) => r.every((x, i) => x !== i && r[x] === i);
/* every fixed-point-free involution of [n] (perfect matchings) */
function matchings(n) {
  const out = [], r = new Array(n).fill(-1);
  (function rec() { const i = r.indexOf(-1); if (i < 0) { out.push(r.slice()); return; } for (let j = i + 1; j < n; j++) if (r[j] < 0) { r[i] = j; r[j] = i; rec(); r[i] = r[j] = -1; } })();
  return out;
}
/* the largest family containing the identity: a largest clique among the matchings whose pairwise relatives are again
   fixed-point-free involutions (any family can be moved to contain the identity by relabelling) */
const EXHAUST = new Map();
function exhaustive(n) {
  if (EXHAUST.has(n)) return EXHAUST.get(n);
  let res;
  if (n % 2 || n === 0) res = { max: n ? 1 : 0, cand: 0 };
  else {
    const M = matchings(n), adj = M.map(() => []);
    for (let a = 0; a < M.length; a++) for (let b = a + 1; b < M.length; b++) if (isFPFInvolution(relative(M[a], M[b]))) { adj[a].push(b); adj[b].push(a); }
    let best = 0;
    const grow = (clique, cand) => { if (clique + cand.length <= best) return; if (!cand.length) { best = Math.max(best, clique); return; } for (let i = 0; i < cand.length; i++) { if (clique + cand.length - i <= best) return; const v = cand[i], nb = new Set(adj[v]); grow(clique + 1, cand.slice(i + 1).filter((w) => nb.has(w))); } };
    grow(0, M.map((_, i) => i));
    res = { max: best + 1, cand: M.length };
  }
  EXHAUST.set(n, res); return res;
}

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { n: 8, t: 1, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean' };
const PRESETS = {
  lean: { n: 8,
    zh: 'n = 8 = 2³：k(8) = 8。把 0 … 7 写成三位二进制，σ_v 是“异或 v”。八个置换矩阵的支撑互不相交，正好铺满 8 × 8 的格子——一个拉丁方（异或表）。任意两个的相对置换是“异或 u ⊕ v”，没有不动点、平方是恒等。',
    en: 'n = 8 = 2³: k(8) = 8. Write 0 … 7 in three binary digits; σ_v is “XOR with v”. The supports of the eight permutation matrices are disjoint and tile the whole 8 × 8 grid — a Latin square (the XOR table). The relative permutation of any two is “XOR with u ⊕ v”, which has no fixed point and squares to the identity.' },
  twelve: { n: 12,
    zh: 'n = 12 = 4 · 3：k(12) = 4，而不是支撑计数允许的 12。十二个点分成三块，每块四个点，σ_v 只在块内异或。页面的穷举对 n ≤ 10 进行；n = 12 的上界来自 Lean 的证明。',
    en: 'n = 12 = 4 · 3: k(12) = 4, not the 12 that counting supports would allow. The twelve points form three blocks of four, and σ_v XORs inside each block. The page’s exhaustive search covers n ≤ 10; the bound for n = 12 comes from Lean’s proof.' },
  six: { n: 6,
    zh: 'n = 6 = 2 · 3：k(6) = 2。页面穷举了 6 个点上全部 15 个无不动点的对合：没有两个能和恒等一起组成三元族（页面数值）。',
    en: 'n = 6 = 2 · 3: k(6) = 2. The page searches all 15 fixed-point-free involutions of 6 points: no two of them form a family of three with the identity (page numbers).' },
  odd: { n: 9,
    zh: 'n = 9 是奇数：k(9) = 1。两个强互补的置换，其相对置换必须是没有不动点的对合，即把 9 个点两两配对——奇数个点做不到。',
    en: 'n = 9 is odd: k(9) = 1. Two strongly complementary permutations need a relative permutation that is a fixed-point-free involution, pairing up the 9 points — impossible with an odd number of points.' },
  sixteen: { n: 16,
    zh: 'n = 16 = 2⁴：k(16) = 16，十六个置换铺满 16 × 16 的格子。只有 n 是 2 的幂时 k(n) = n。',
    en: 'n = 16 = 2⁴: k(16) = 16, and sixteen permutations tile the 16 × 16 grid. k(n) = n exactly when n is a power of two.' },
  mixed: { n: 24,
    zh: 'n = 24 = 8 · 3：k(24) = 8。奇数因子 3 让格子变大，却不增加族的大小：只用了 24 · 8 = 192 个格子，占 1/3。',
    en: 'n = 24 = 8 · 3: k(24) = 8. The odd factor 3 enlarges the grid without enlarging the family: only 24 · 8 = 192 cells are used, a third of them.' }
};
let MODEL = null, dirty = true, modelId = 0;
function build() {
  const n = S.n, F = family(n), K = F.length, j = Math.max(1, Math.round(S.t * K));
  const cur = F[j - 1], rel = relative(F[0], cur), m = n / K;
  MODEL = { id: ++modelId, n, a: v2(n), m, K, F, j, cur, rel, relFPF: isFPFInvolution(rel), cells: j * n, exh: n <= EXH ? exhaustive(n) : null };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');
const hueOf = (v, K) => { const h = v / Math.max(1, K), k = (n) => (n + h * 12) % 12, a = 0.85, l = 0.6; return [0, 8, 4].map((n) => l - a * Math.min(l, 1 - l) * Math.max(-1, Math.min(k(n) - 3, 9 - k(n), 1))); };
const css = (c) => `rgb(${c.map((x) => Math.round(255 * x)).join(',')})`;
const bits = (v, a) => (a ? v.toString(2).padStart(a, '0') : '∅');

/* =====================================================================
   4. 3D scene: the n × n grid, one layer per family member stacked above it, and the shadows of their supports
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const SIDE = 5.2, LAYER = 0.32, LINES_MAX = 6000, PTS_MAX = 2400;
/* the default view looks across the main diagonal, where the blocks of a family lie */
const CAMS = { iso: [-0.78, 0.95, 10.5], front: [0.0001, 1.45, 10], top: [0.0001, 0.05, 10.5] };
const cam = { theta: -0.78, phi: 0.95, r: 10.5, tTheta: -0.78, tPhi: 0.95, tR: 10.5 };
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
  float a = smoothstep(1.0, 0.7, r) * vA;
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
/* row i, column j of the grid; layer v floats above */
const cellPos = (M, i, j, y) => { const c = SIDE / M.n; return [-SIDE / 2 + c * (j + 0.5), y, -SIDE / 2 + c * (i + 0.5)]; };
const layerY = (M, v) => 0.35 + LAYER * v * Math.min(1, 16 / M.K);
function updateGL() {
  const M = MODEL, Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; for (let k = 0; k < 3; k++) { PT.position.array[3 * np + k] = p[k]; PT.aColor.array[3 * np + k] = c[k]; } PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const n = M.n, c = SIDE / n, ds = Math.min(2.6, 34 / n);
  /* the grid, with the blocks of 2^a points marked */
  for (let i = 0; i <= n; i++) { const edge = i % M.K === 0; seg([-SIDE / 2, 0, -SIDE / 2 + c * i], [SIDE / 2, 0, -SIDE / 2 + c * i], edge ? WHITE : GREY, edge ? 0.45 : 0.18); seg([-SIDE / 2 + c * i, 0, -SIDE / 2], [-SIDE / 2 + c * i, 0, SIDE / 2], edge ? WHITE : GREY, edge ? 0.45 : 0.18); }
  for (let w = 0; w < M.j; w++) {
    const col = hueOf(w, M.K), y = layerY(M, w), now = w === M.j - 1;
    M.F[w].forEach((jj, i) => {
      dot(cellPos(M, i, jj, y), col, now ? 1 : 0.75, ds);
      dot(cellPos(M, i, jj, 0.01), col, 0.55, ds * 0.9);
      if (now) seg(cellPos(M, i, jj, y), cellPos(M, i, jj, 0.01), col, 0.35);
    });
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
  camera.position.set(r * sp * Math.sin(cam.theta), r * Math.cos(cam.phi) + 1, r * sp * Math.cos(cam.theta));
  camera.up.set(0, 1, 0); camera.lookAt(0, 1, 0);
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
  if (drag.pts.size === 2) { const [p, q] = [...drag.pts.values()], d = Math.hypot(p.x - q.x, p.y - q.y); if (drag.pinch > 0) cam.tR = Math.min(26, Math.max(4, cam.tR * drag.pinch / d)); drag.pinch = d; return; }
  const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y; drag.x = ev.clientX; drag.y = ev.clientY;
  cam.tTheta -= dx * 0.006; cam.tPhi = Math.min(Math.PI - 0.06, Math.max(0.06, cam.tPhi - dy * 0.006));
  cam.theta = cam.tTheta; cam.phi = cam.tPhi;
  document.querySelectorAll('#camChips .chip').forEach((b) => b.setAttribute('aria-pressed', 'false'));
});
const endDrag = (ev) => { if (!drag.pts.has(ev.pointerId)) return; drag.pts.delete(ev.pointerId); if (drag.pts.size === 0) drag.pinch = 0; };
stage.addEventListener('pointerup', endDrag); stage.addEventListener('pointercancel', endDrag);
stage.addEventListener('wheel', (ev) => { ev.preventDefault(); cam.tR = Math.min(26, Math.max(4, cam.tR * Math.exp(ev.deltaY * 0.0012))); }, { passive: false });

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
  put(T(`σ_${bits(M.j - 1, M.a)}（第 ${M.j} 个）`, `σ_${bits(M.j - 1, M.a)} (member ${M.j})`), [SIDE / 2 + 0.5, layerY(M, M.j - 1), -SIDE / 2], 'am');
  put(T(`${M.n} × ${M.n} 格`, `${M.n} × ${M.n} grid`), [-SIDE / 2, 0, SIDE / 2 + 0.4], 't');
  put(T(`支撑已占 ${M.cells} / ${M.n * M.n}`, `supports cover ${M.cells} / ${M.n * M.n}`), [SIDE / 2, 0, SIDE / 2 + 0.4], 't');
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
/* k(n) = 2^{v₂(n)} for n = 1 … 32, the support bound n, and the page's exhaustive maxima for n ≤ 10 */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 34); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, bw = iw / NMAX, top = Math.log2(NMAX) + 0.4, Y = (y) => pt + ih * (1 - Math.log2(Math.max(1, y)) / top);
  ctx.strokeStyle = FAINT; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.beginPath(); for (let n = 1; n <= NMAX; n++) { const x = pl + (n - 0.5) * bw; n === 1 ? ctx.moveTo(x, Y(n)) : ctx.lineTo(x, Y(n)); } ctx.stroke(); ctx.setLineDash([]);
  for (let n = 1; n <= NMAX; n++) {
    const x = pl + (n - 1) * bw, k = kOf(n), sel = n === M.n;
    ctx.fillStyle = sel ? 'rgba(255,200,61,0.9)' : k === n ? 'rgba(25,240,255,0.7)' : 'rgba(212,239,255,0.4)';
    const h = Math.max(2 * dpr, Y(1) - Y(k)); ctx.fillRect(x + bw * 0.15, Y(1) - h, bw * 0.7, h);
    if (n <= EXH) { const e = exhaustive(n).max; ctx.strokeStyle = MG; ctx.lineWidth = 1.4 * dpr; ctx.beginPath(); ctx.moveTo(x + bw * 0.1, Y(e) - 3 * dpr); ctx.lineTo(x + bw * 0.9, Y(e) - 3 * dpr); ctx.stroke(); }
    if (n % 4 === 0 || n === 1) lab(ctx, String(n), x + bw / 2, pt + ih + 4 * dpr, 'center', 'top', sel ? AM : DIM);
  }
  [1, 2, 4, 8, 16, 32].forEach((v) => lab(ctx, String(v), pl - 4 * dpr, Y(v) - (v === 1 ? 2 * dpr : 0), 'right', 'middle'));
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('k(n) = n（2 的幂）', 'k(n) = n (powers of two)')}</span><span class="it"><i class="sw" style="--c:${INK}"></i>k(n) = 2^v₂(n)</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('穷举 n ≤ 10', 'exhaustive n ≤ 10')}</span><span class="it"><i class="sw" style="--c:${FAINT}"></i>k ≤ n</span>`;
}
/* the relative permutation σ₀⁻¹σ_j as arcs over the n points, which the blocks of 2^a points contain */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 16); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, n = M.n, X = (i) => pl + iw * (i + 0.5) / n, base = pt + ih * 0.78;
  for (let b = 0; b < M.m; b++) { ctx.fillStyle = b % 2 ? 'rgba(25,240,255,0.08)' : 'rgba(25,240,255,0.16)'; ctx.fillRect(pl + iw * b * M.K / n, base - 4 * dpr, iw * M.K / n, 8 * dpr); }
  const col = css(hueOf(M.j - 1, M.K));
  ctx.strokeStyle = col; ctx.lineWidth = 1.5 * dpr;
  for (let i = 0; i < n; i++) { const j = M.rel[i]; if (j <= i) continue; const x0 = X(i), x1 = X(j), r = (x1 - x0) / 2; ctx.beginPath(); ctx.ellipse((x0 + x1) / 2, base, r, Math.min(ih * 0.7, r * 0.9 + 4 * dpr), 0, Math.PI, 2 * Math.PI); ctx.stroke(); }
  for (let i = 0; i < n; i++) { ctx.fillStyle = M.rel[i] === i ? MG : INK; ctx.beginPath(); ctx.arc(X(i), base, 2.6 * dpr, 0, 2 * Math.PI); ctx.fill(); if (n <= 16 || i % 4 === 0) lab(ctx, String(i), X(i), base + 6 * dpr, 'center', 'top'); }
  $('c2Meta').innerHTML = M.j === 1 ? `<span class="it">${T('第一个成员是恒等置换：没有可比的一对', 'the first member is the identity: no pair to compare')}</span>` : `<span class="it"><i class="sw" style="--c:${col}"></i>σ₀⁻¹σ_${bits(M.j - 1, M.a)}</span><span class="it">· ${M.relFPF ? T('无不动点的对合', 'fixed-point-free involution') : T('不是无不动点的对合', 'not a fixed-point-free involution')}</span><span class="it">· ${T(`${M.m} 块，每块 ${M.K} 点`, `${M.m} blocks of ${M.K}`)}</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const oneLine = (s) => (s.length <= 16 ? s.join(' ') : s.slice(0, 16).join(' ') + ' …');
function readouts() {
  const M = MODEL;
  pill('pillA', 'n', String(M.n)); pill('pillB', 'v₂(n)', String(M.a)); pill('pillC', 'k(n)', String(M.K)); pill('pillD', T('成员', 'members'), `${M.j} / ${M.K}`);
  setRo([
    [T('n = 2^a · m（m 为奇数）· k(n) = 2^a · 支撑计数的上界 n', 'n = 2^a · m (m odd) · k(n) = 2^a · support bound n'), `${M.n} = ${M.K} · ${M.m} · ${M.K} · ${M.n}`],
    [T(`第 ${M.j} 个成员 σ_v，v = ${bits(M.j - 1, M.a)}：i ↦ σ(i)`, `Member ${M.j}, σ_v with v = ${bits(M.j - 1, M.a)}: i ↦ σ(i)`), oneLine(M.cur)],
    [T('相对置换 σ₀⁻¹σ_v：无不动点？对合？', 'Relative permutation σ₀⁻¹σ_v: no fixed point? involution?'), M.j === 1 ? T('（恒等，与自身不比较）', '(the identity; not compared with itself)') : `${oneLine(M.rel)} · ${M.relFPF ? T('是 · 是', 'yes · yes') : T('否', 'no')}`],
    [T('已用的格子 · 共', 'Cells used · of'), `${M.cells} · ${M.n * M.n}${M.j === M.K && M.K === M.n ? T('（铺满：拉丁方）', ' (all: a Latin square)') : ''}`],
    [T('页面穷举的最大值（n ≤ 10）· 候选的无不动点对合', 'Page’s exhaustive maximum (n ≤ 10) · candidate fixed-point-free involutions'), M.exh ? `${M.exh.max} · ${M.exh.cand}` : T('n > 10：不穷举', 'n > 10: not searched')]]);
  $('roNote').innerHTML = T(`Lean：对每个 n ≥ 1，两两强互补的 n × n 置换矩阵最多 2^v₂(n) 个，这里是 ${M.K}；平移族达到这个数。`, `Lean: for every n ≥ 1, at most 2^v₂(n) n × n permutation matrices are pairwise strongly complementary, here ${M.K}; the translation family attains it.`);
}
const stateKey = () => `${S.n}|${S.t}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; }
  const M = MODEL;
  if (!toasted && S.playing && M.j >= M.K) { toasted = true; toast(T(`<b>${M.K} 个</b>：k(${M.n}) = 2^${M.a}，再加一个就会与某个成员冲突。`, `<b>${M.K} members</b>: k(${M.n}) = 2^${M.a}; one more would clash with some member.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  $('nIn').value = String(S.n); $('nOut').textContent = String(S.n);
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('sysNote').innerHTML = T(`n = ${M.n} 个点写成 x + 2^a·b，x 是 a 位二进制、b < m；σ_v 把 x 换成 x ⊕ v。`, `The n = ${M.n} points are written x + 2^a·b with x an a-digit binary number and b < m; σ_v replaces x by x ⊕ v.`);
  $('litNote').innerHTML = T('Lean 证明的是每个 n ≥ 1；平移族的具体排列与 n ≤ 10 的穷举是页面计算。', 'Lean proves every n ≥ 1; the particular translation family and the exhaustive search for n ≤ 10 are page computations.');
  $('c1Title').textContent = T('最大族的大小 k(n)，对数刻度', 'Largest family size k(n), log scale');
  $('c2Title').textContent = T('相对置换：把 n 个点两两配对', 'The relative permutation pairs up the n points');
  $('clock').innerHTML = T(`${M.j} 个`, `${M.j} of ${M.K}`);
  $('hudBig').textContent = `n = ${M.n} · k = 2^${M.a} = ${M.K} · ${T('成员', 'members')} ${M.j}`;
  $('hudSub').textContent = T('每一层是族里的一个置换矩阵（n 个格子），从下往上一个个加入；地面上的投影互不重叠。白线把格子分成 2^a × 2^a 的块', 'Each layer is one permutation matrix of the family (n cells), added from the bottom up; their shadows on the floor never overlap. White lines cut the grid into 2^a × 2^a blocks');
}
function syncRail() {
  const M = MODEL, key = `${M.K}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = [[0, T('1 个', '1')], [1, T(`${M.K} 个 = k(n)`, `${M.K} = k(n)`)]];
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : 'last'}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { n: p.n, t: 0, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
const custom = () => { S.preset = null; markPreset(); dirty = true; toasted = false; };
$('nIn').addEventListener('input', () => { S.n = parseInt($('nIn').value, 10); custom(); });
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
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT')) { ev.preventDefault(); const K = MODEL.K; jumpTo((MODEL.j + (ev.key === 'ArrowRight' ? 1 : -1)) / K); }
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
/* one member every 0.7 s at 1×, at least 3 seconds per run */
const runSeconds = (K) => Math.max(3, 0.7 * K);
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  if (S.playing && !scrubbing) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : 1); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed / runSeconds(MODEL.K));
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
window.PC_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL; return { n: M.n, a: M.a, m: M.m, K: M.K, j: M.j, F: M.F.map((s) => s.slice()), cur: M.cur.slice(), rel: M.rel.slice(), relFPF: M.relFPF, cells: M.cells, exh: M.exh }; },
  family: (n) => family(n).map((s) => s.slice()),
  exhaustive: (n) => exhaustive(n),
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setT(1); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 9.6; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
