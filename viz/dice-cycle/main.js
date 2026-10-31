/* DICE//CYCLE · minimal-advantage dice cycles
   Easlick (2026, Conjecture 1): among n-sided dice with faces in 1 … n, cycles in which every die beats the next with the
   smallest probability above one half have maximum length exactly n only for n = 6. Proved in trureturing
   (EaslickSixBound.conjecture_one): S(6) holds and S(n) fails for every n ≥ 7. The page builds the minimal-advantage graph
   for n ≤ 7, finds its strongly connected components, and walks the seed cycles that Lean checks for n = 6 … 11.
   Depends on: assets/vendor/three.r128.min.js, assets/shell.js. */
(() => {
'use strict';

/* =====================================================================
   1. Dice, win counts and the seed cycles
   ===================================================================== */
const COL = TRV.rgb;
const reduceMotion = TRV.reduceMotion;
const { fitCanvas, L: T } = TRV;
const { ink: INK, dim: DIM, faint: FAINT, amber: AM, cyan: CY, magenta: MG } = TRV.palette;
const GREY = [0.5, 0.58, 0.68], WHITE = [0.92, 0.95, 1];
const NMIN = 3, NMAX = 11, NGRAPH = 7, NCHART = 16;
/* The seed cycles of EaslickCycleSeeds.sourceSeed, one die per string (faces 10 and 11 written a and b). The rows for
   n = 7 … 10 are Easlick's Appendices G–J (arXiv:2610.40321, CC BY 4.0); the n = 6 cycle is constructed in trureturing
   and the n = 11 cycle is derived from the n = 7 cycle. */
const SEEDS = {
  6: [
    '112555', '134444', '222366', '112556', '133444', '223336'],
  7: [
    '1113347', '2222226', '1113555', '1122444', '1133333', '1222256', '1114445', '1133334', '1222257', '1114446', '1133335',
    '1222267', '1113556', '2222344'],
  8: [
    '11124666', '11333335', '22222444', '11133378', '22222267', '11125556', '12333444', '22222366', '11125557', '12334444',
    '12223366', '11125555', '12344444', '12333346', '22222555', '11134488', '22222367', '11125558', '12444444', '11133677',
    '22222556', '11144467', '11333356', '22222458', '11133777', '22222268', '11135556', '13333444', '22233337'],
  9: [
    '111133337', '222222226', '111135555', '112224444', '111233338', '222222227', '111133666', '222222245', '111133459',
    '222222228'],
  10: [
    '1111244444', '1223333333', '1222222477', '1111333666', '1222222555', '1111244445', '1233333333', '1112226777', '1111245556',
    '1113333344', '2222222366', '1111255556', '1222224444', '1113333335', '2222222447', '1111333667', '2222222455', '1111333478',
    '2222222267', '1111344556', '1223333334', '1222222488', '1111333677', '2222222555', '1112244444', '1113333336', '2222222448',
    '1111333479', '2222222268', '1111255557', '1222234444', '1113333337', '1222222567', '1111344555', '2223333334', '1112226778',
    '1111345556', '1123333344', '2222222367', '1111255558', '1222244444', '111133347a', '2222222269', '1111345557', '1223333344',
    '1222222489', '1111333777', '1222222566', '1111444555', '1113333345', '2222222368', '1111255559', '1222334444', '1113333338',
    '1222222568', '1111444456', '1123333345', '1222222499', '1111333778', '1222222666', '111125555a', '1222344444', '1111333489',
    '2222222278', '1111246667', '1113333355', '122222249a', '1111333788', '222222226a', '1111345558', '1233333334', '1112226779',
    '1111355556', '1112244445', '1113333339', '1222222569', '1111444457', '1113333346', '2222222369', '1111255566', '1222444444',
    '111233348a', '2222222279', '1111246668', '1123333335', '12222224aa', '1111333779', '2222222456', '111133349a', '2222222289',
    '1111246678', '1133333335', '1222224445', '111333333a', '122222256a', '1111444458', '1113333347', '1222222667', '111133555a',
    '2222222449', '111133377a', '2222222466', '1111345559', '2223333344', '111222677a', '1111444556', '1113333348', '1222222578',
    '1111344467', '2222333335'],
  11: [
    '113335569bb', '224444448aa', '113335777bb', '223344666aa', '113355555bb', '223444478aa', '113336667bb', '223355556aa',
    '113444479bb', '223336668aa', '113355557bb', '223444489aa', '113335778bb', '224444566aa']
};
const decode = (s) => [...s].map((ch) => parseInt(ch, 36));
const name = (d) => d.map((x) => x.toString(36)).join('');
const threshold = (n) => Math.floor(n * n / 2) + 1;
const binom = (a, b) => { let r = 1; for (let i = 1; i <= b; i++) r = r * (a - b + i) / i; return Math.round(r); };
/* the least strict-win probability above 1/2, in lowest terms: 1/2 + 1/n² for even n, 1/2 + 1/(2n²) for odd n */
const probText = (n) => `${threshold(n)}/${n * n} = 1/2 + 1/${n % 2 ? 2 * n * n : n * n}`;
function winCount(d, e) { let w = 0; for (const x of d) for (const y of e) if (y < x) w++; return w; }
function duel(d, e) { let w = 0, t = 0; for (const x of d) for (const y of e) { if (y < x) w++; else if (y === x) t++; } return { win: w, tie: t, lose: d.length * e.length - w - t }; }
/* the attaining pair of EaslickMinimalAdvantage.threshold_attained: evenX/evenY for n = 2k, oddX/oddY for n = 2k + 1 */
function leanPair(n) {
  const k = Math.floor(n / 2), rep = (m, v) => Array(Math.max(0, m)).fill(v);
  return n % 2 === 0 ? [[...rep(k - 1, 1), 2, ...rep(k, 3)], [1, ...rep(2 * k - 1, 2)]] : [[...rep(k, 1), 2, ...rep(k, 3)], [...rep(k + 1, 1), ...rep(k, 2)]];
}
/* the longest cycle Lean exhibits for every n ≥ 6: the seeds up to 11, then padding (EaslickPaddedCycles.longer_cycle) */
const knownLength = (n) => (n < 6 ? null : SEEDS[n] ? SEEDS[n].length : n % 2 === 0 ? 6 * ((n - 6) / 2 + 1) : 14 * ((n - 7) / 2 + 1));

/* all dice with n faces, in lexicographic order */
function enumerate(n) {
  const out = [], cur = [];
  (function rec(lo) { if (cur.length === n) { out.push(cur.slice()); return; } for (let v = lo; v <= n; v++) { cur.push(v); rec(v); cur.pop(); } })(1);
  return out;
}
/* strongly connected components, iterative Tarjan */
function tarjan(N, adj) {
  const idx = new Int32Array(N).fill(-1), low = new Int32Array(N), on = new Uint8Array(N), comp = new Int32Array(N).fill(-1), st = [], comps = [];
  let c = 0;
  for (let s = 0; s < N; s++) {
    if (idx[s] >= 0) continue;
    const work = [[s, 0]]; idx[s] = low[s] = c++; st.push(s); on[s] = 1;
    while (work.length) {
      const top = work[work.length - 1], v = top[0];
      if (top[1] < adj[v].length) {
        const w = adj[v][top[1]++];
        if (idx[w] < 0) { idx[w] = low[w] = c++; st.push(w); on[w] = 1; work.push([w, 0]); }
        else if (on[w]) low[v] = Math.min(low[v], idx[w]);
      } else {
        work.pop(); if (work.length) { const u = work[work.length - 1][0]; low[u] = Math.min(low[u], low[v]); }
        if (low[v] === idx[v]) { const cc = []; let w; do { w = st.pop(); on[w] = 0; comp[w] = comps.length; cc.push(w); } while (w !== v); comps.push(cc); }
      }
    }
  }
  return { comp, comps };
}
/* the longest simple cycle inside a small component, by exhaustive search from its smallest vertex in each rotation */
function longestCycle(members, adj) {
  const S = new Set(members); let best = [];
  for (const s of members) {
    const path = [s], seen = new Set([s]);
    (function dfs(v) {
      for (const w of adj[v]) {
        if (w === s && path.length > best.length) best = path.slice();
        else if (S.has(w) && w > s && !seen.has(w)) { seen.add(w); path.push(w); dfs(w); path.pop(); seen.delete(w); }
      }
    })(s);
  }
  return best;
}
/* the minimal-advantage graph for n ≤ NGRAPH, with a layout: height = face sum, a ring per sum */
const GRAPHS = {};
function graph(n) {
  if (GRAPHS[n]) return GRAPHS[n];
  const dice = enumerate(n), N = dice.length, th = threshold(n);
  const below = dice.map((d) => { const c = new Int32Array(n + 2); for (let v = 1; v <= n + 1; v++) c[v] = d.filter((y) => y < v).length; return c; });
  const adj = dice.map(() => []); let E = 0, down = 0;
  const sums = dice.map((d) => d.reduce((a, b) => a + b, 0));
  for (let a = 0; a < N; a++) { const d = dice[a]; for (let b = 0; b < N; b++) { const cb = below[b]; let w = 0; for (let i = 0; i < n; i++) w += cb[d[i]]; if (w === th) { adj[a].push(b); E++; if (sums[a] > sums[b]) down++; } } }
  const { comp, comps } = tarjan(N, adj);
  const knots = comps.filter((c) => c.length > 1).sort((x, y) => y.length - x.length || Math.min(...x) - Math.min(...y));
  const longest = n <= 6 ? knots.map((c) => longestCycle(c, adj)) : null;
  const degree = new Int32Array(N); adj.forEach((l, a) => { degree[a] += l.length; l.forEach((b) => degree[b]++); });
  const lv = new Map(); sums.forEach((s, i) => { if (!lv.has(s)) lv.set(s, []); lv.get(s).push(i); });
  const maxCount = Math.max(...[...lv.values()].map((l) => l.length)), pos = new Array(N), H = 6;
  for (const [s, l] of lv) l.forEach((i, j) => {
    const a = 2 * Math.PI * (j + 0.5 * (s % 2)) / l.length, r = 2.2 * Math.sqrt(l.length / maxCount);
    pos[i] = [r * Math.cos(a), H * ((s - n) / (n * n - n) - 0.5), r * Math.sin(a)];
  });
  const key = new Map(dice.map((d, i) => [name(d), i]));
  return (GRAPHS[n] = { n, dice, N, adj, E, down, comp, knots, longest, degree, pos, key, isolated: [...degree].filter((x) => x === 0).length });
}

/* =====================================================================
   2. State, presets and the model
   ===================================================================== */
const S = { n: 6, which: 'seed', t: 0, playing: false, dir: 1, speed: 1, hold: 0, preset: 'lean', cut: false };
const PRESETS = {
  lean: { n: 6, which: 'seed', cut: false, t: 0, play: false,
    zh: 'Lean 里的六循环：112555 → 134444 → 222366 → 112556 → 133444 → 223336 → 112555。每一步都是 36 种掷法里赢 19 种，正好比一半多一点点。这 6 颗骰子都在同一个 7 颗骰子的结里，Lean 证明 n = 6 时没有更长的循环。',
    en: 'The six-cycle in Lean: 112555 → 134444 → 222366 → 112556 → 133444 → 223336 → 112555. Every step wins 19 of the 36 outcomes, just over one half. All six dice sit in the same knot of 7 dice, and Lean proves that no longer cycle exists for n = 6.' },
  cut: { n: 6, which: 'seed', cut: true, t: 5 / 6, play: false,
    zh: '第七颗为什么进不来：结里的 122366 与 223336 在结内都只能走向 112555。循环里每颗骰子的下一颗各不相同，所以这两颗不能同时在一个循环里——7 颗的结里最多用 6 颗。这是 Lean 的秩纤维检查器核对的“碰撞”（cuts6）。',
    en: 'Why the seventh die is left out: inside the knot, 122366 and 223336 can both only move to 112555. In a cycle every die has its own next die, so these two cannot both be on one cycle — a knot of 7 dice allows at most 6. This is the collision that Lean’s rank-fiber checker verifies (cuts6).' },
  mirror: { n: 6, which: 'knotB', cut: true, t: 0, play: false,
    zh: '另一个结：总点数在 21 到 23 之间的 7 颗骰子。页面在里面找到的最长循环也是 6，同样有两颗骰子（114555、114556）只能走向同一颗 333346。它是第一个结的镜像：把每个面 x 换成 7 − x，边的方向反过来，两个结互换（本页的论证，见右侧虚线框）。',
    en: 'The other knot: 7 dice with face sums between 21 and 23. The longest cycle the page finds in it is again 6, and again two dice (114555, 114556) can only move to the same die 333346. It mirrors the first knot: replacing every face x by 7 − x reverses the edges and swaps the two knots (the page’s argument, in the dashed box on the right).' },
  five: { n: 5, which: 'seed', cut: false, t: 0, play: false,
    zh: 'n = 5：126 颗骰子、620 条最小优势的边（赢 13/25），但整张图没有一个循环——沿边走永远回不到出发点。n = 3、4 也一样。图下是 Lean 用来证明最小值可以取到的那一对骰子。页面数值。',
    en: 'n = 5: 126 dice and 620 minimal-advantage edges (13 wins of 25), yet the graph has no cycle at all — no walk along the edges ever returns to where it started. The same holds for n = 3 and 4. The duel below is the pair Lean uses to show that the minimum is attained. Page numbers.' },
  seven: { n: 7, which: 'seed', cut: false, t: 0, play: true,
    zh: 'n = 7：1716 颗骰子之间有 89153 条边，其中 1081 颗落在同一个强连通分支里（页面数值）。Easlick 附录 G 的循环有 14 颗骰子，每一步赢 25/49；14 > 7，所以 S(7) 不成立。',
    en: 'n = 7: the 1716 dice carry 89153 edges, and 1081 of them lie in one strongly connected component (page numbers). The cycle from Easlick’s Appendix G has 14 dice, each step winning 25 of 49; 14 > 7, so S(7) fails.' },
  ten: { n: 10, which: 'seed', cut: false, t: 0, play: true,
    zh: 'n = 10：Easlick 附录 J 的循环有 110 颗骰子，每一步赢 51/100。页面不画 92378 颗骰子的整张图，只画这个循环：点的高度仍是总点数。',
    en: 'n = 10: the cycle from Easlick’s Appendix J has 110 dice, each step winning 51 of 100. The page does not draw the whole graph of 92378 dice, only this cycle, still raised to the face sums.' }
};
let MODEL = null, dirty = true, modelId = 0;
function build() {
  const n = S.n, G = n <= NGRAPH ? graph(n) : null, th = threshold(n);
  let cycle = [], knot = null, cut = null;
  if (n === 6 && S.which === 'knotB') {
    const kn = G.knots.find((c) => c.some((i) => name(G.dice[i]) === '114555')); knot = kn;
    cycle = G.longest[G.knots.indexOf(kn)].map((i) => G.dice[i]);
  } else if (SEEDS[n]) cycle = SEEDS[n].map(decode);
  if (G && n === 6 && !knot) knot = G.knots.find((c) => c.some((i) => name(G.dice[i]) === name(cycle[0])));
  if (G && knot) {
    /* dice of the knot whose only successor inside the knot is shared */
    const inside = new Set(knot), succ = knot.map((i) => [i, G.adj[i].filter((j) => inside.has(j))]);
    const single = succ.filter(([, l]) => l.length === 1), byT = new Map();
    single.forEach(([i, l]) => { if (!byT.has(l[0])) byT.set(l[0], []); byT.get(l[0]).push(i); });
    const pair = [...byT.entries()].find(([, l]) => l.length >= 2);
    if (pair) cut = { a: G.dice[pair[1][0]], b: G.dice[pair[1][1]], to: G.dice[pair[0]] };
  }
  const k = cycle.length, step = k ? Math.min(k - 1, Math.floor(S.t * k + 1e-9)) % k : 0, frac = k ? S.t * k - Math.floor(S.t * k + 1e-9) : 0;
  const cur = k ? cycle[step] : leanPair(n)[0], next = k ? cycle[(step + 1) % k] : leanPair(n)[1];
  const edgeOK = cycle.every((d, i) => winCount(d, cycle[(i + 1) % k]) === th);
  MODEL = { id: ++modelId, n, G, th, cycle, k, step, frac, cur, next, duel: duel(cur, next), cut, knot, edgeOK,
    count: binom(2 * n - 1, n), longest: G && G.longest ? Math.max(0, ...G.longest.map((c) => c.length)) : null };
}

/* =====================================================================
   3. DOM helpers
   ===================================================================== */
const $ = (id) => document.getElementById(id);
const stage = $('stage'), glCanvas = $('gl'), tagsBox = $('tags'), cv1 = $('c1'), cv2 = $('c2');

/* =====================================================================
   4. 3D scene: every die at the height of its face sum, edges, knots and the current cycle
   ===================================================================== */
let renderer = null, scene3, camera, glOK = false, lines, pts;
const LINES_MAX = 16000, PTS_MAX = 2200;
const CAMS = { iso: [0.7, 1.3, 11], front: [0.0001, 1.5708, 10.5], top: [0.0001, 0.06, 11] };
const cam = { theta: 0.7, phi: 1.3, r: 11, tTheta: 0.7, tPhi: 1.3, tR: 11 };
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
/* positions of the cycle's dice: the graph layout for n ≤ NGRAPH, otherwise a ring at the face-sum heights */
function cyclePos(M) {
  if (M.G) return M.cycle.map((d) => M.G.pos[M.G.key.get(name(d))]);
  const sums = M.cycle.map((d) => d.reduce((a, b) => a + b, 0)), lo = Math.min(...sums), hi = Math.max(...sums);
  return M.cycle.map((d, i) => { const a = 2 * Math.PI * i / M.k; return [2.4 * Math.cos(a), 2.2 * (sums[i] - (lo + hi) / 2) / Math.max(1, hi - lo), 2.4 * Math.sin(a)]; });
}
const posOf = (M, d) => (M.G ? M.G.pos[M.G.key.get(name(d))] : cyclePos(M)[M.cycle.findIndex((c) => name(c) === name(d))]);
function updateGL() {
  const M = MODEL, G = M.G;
  const Lb = lines.geometry.attributes, Pp = Lb.position.array, Cc = Lb.color.array; let v = 0;
  const seg = (p, q, c, k) => { if (v + 2 > LINES_MAX) return; for (const r of [p, q]) { Pp[3 * v] = r[0]; Pp[3 * v + 1] = r[1]; Pp[3 * v + 2] = r[2]; Cc[3 * v] = c[0] * k; Cc[3 * v + 1] = c[1] * k; Cc[3 * v + 2] = c[2] * k; v++; } };
  const PT = pts.geometry.attributes; let np = 0;
  const dot = (p, c, al, size) => { if (np >= PTS_MAX) return; PT.position.array[3 * np] = p[0]; PT.position.array[3 * np + 1] = p[1]; PT.position.array[3 * np + 2] = p[2]; PT.aColor.array[3 * np] = c[0]; PT.aColor.array[3 * np + 1] = c[1]; PT.aColor.array[3 * np + 2] = c[2]; PT.aAlpha.array[np] = al; PT.aSize.array[np] = size; np++; };
  const inKnot = new Set(); if (G) G.knots.forEach((c) => c.forEach((i) => inKnot.add(i)));
  if (G) {
    const faint = Math.min(0.25, 1.6 / Math.sqrt(Math.max(1, G.E)));
    if (G.n <= 6) G.adj.forEach((l, a) => l.forEach((b) => { const kn = inKnot.has(a) && inKnot.has(b) && G.comp[a] === G.comp[b]; seg(G.pos[a], G.pos[b], kn ? COL.amber : GREY, kn ? 0.75 : faint); }));
    G.dice.forEach((d, i) => dot(G.pos[i], inKnot.has(i) ? COL.amber : GREY, inKnot.has(i) ? (G.n <= 6 ? 0.9 : 0.35) : G.degree[i] ? 0.45 : 0.18, inKnot.has(i) && G.n <= 6 ? 1.5 : 0.9));
  }
  const cp = cyclePos(M);
  cp.forEach((p, i) => { seg(p, cp[(i + 1) % M.k], COL.cyan, 0.85); dot(p, COL.cyan, 1, M.k > 30 ? 1.2 : 1.7); });
  if (M.cut && S.cut) {
    const to = posOf(M, M.cut.to);
    for (const d of [M.cut.a, M.cut.b]) { const p = G.pos[G.key.get(name(d))]; seg(p, to, COL.magenta, 1); dot(p, COL.magenta, 1, 2); }
    dot(to, WHITE, 1, 2.2);
  }
  if (M.k) { const p = cp[M.step], q = cp[(M.step + 1) % M.k]; dot(p, WHITE, 1, 2.4); seg(p, q, WHITE, 0.9); }
  else if (G) { const p = G.pos[G.key.get(name(M.cur))], q = G.pos[G.key.get(name(M.next))]; dot(p, WHITE, 1, 2.2); dot(q, COL.cyan, 1, 2); seg(p, q, WHITE, 0.9); }
  lines.geometry.setDrawRange(0, v); Lb.position.needsUpdate = true; Lb.color.needsUpdate = true;
  for (let i = np; i < PTS_MAX; i++) PT.aAlpha.array[i] = 0;
  for (const a of [PT.position, PT.aColor, PT.aAlpha, PT.aSize]) a.needsUpdate = true;
  pts.material.uniforms.uScale.value = 60 * renderer.getPixelRatio() * (stage.clientHeight / 600);
}
/* a pulse runs along the current edge */
let pulseIdx = -1;
function updatePulse() {
  const M = MODEL; if (!M.k) return;
  const cp = cyclePos(M), p = cp[M.step], q = cp[(M.step + 1) % M.k], f = M.frac, PT = pts.geometry.attributes;
  const x = [p[0] + (q[0] - p[0]) * f, p[1] + (q[1] - p[1]) * f, p[2] + (q[2] - p[2]) * f];
  let i = pulseIdx; if (i < 0) return;
  PT.position.array[3 * i] = x[0]; PT.position.array[3 * i + 1] = x[1]; PT.position.array[3 * i + 2] = x[2]; PT.position.needsUpdate = true;
}
function addPulse() {
  const PT = pts.geometry.attributes; let i = 0; while (i < PTS_MAX && PT.aAlpha.array[i] > 0) i++;
  if (i >= PTS_MAX || !MODEL.k) { pulseIdx = -1; return; }
  pulseIdx = i; PT.aColor.array[3 * i] = COL.magenta[0]; PT.aColor.array[3 * i + 1] = COL.magenta[1]; PT.aColor.array[3 * i + 2] = COL.magenta[2]; PT.aAlpha.array[i] = 1; PT.aSize.array[i] = 1.8;
  PT.aColor.needsUpdate = true; PT.aAlpha.needsUpdate = true; PT.aSize.needsUpdate = true;
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
function tagAt(k, cls) { while (tagPool.length <= k) { const el = document.createElement('div'); el.className = 'tag raw dz'; tagsBox.appendChild(el); tagPool.push(el); } const el = tagPool[k]; el.className = 'tag raw dz ' + cls; return el; }
function placeTag(el, p, dy = -14) {
  if (!glOK) { el.style.display = 'none'; return; }
  const q = proj3(p); if (q.z > 1 || q.z < -1) { el.style.display = 'none'; return; }
  el.style.display = 'block';
  const w = el.offsetWidth, h = el.offsetHeight, Wd = stage.clientWidth, Hd = stage.clientHeight, hud = document.querySelector('.hud-tl'), top = hud.offsetTop + hud.offsetHeight + 4;
  el.style.left = Math.min(Wd - w / 2 - 6, Math.max(w / 2 + 6, q.x)) + 'px'; el.style.top = Math.min(Hd - h / 2 - 6, Math.max(top + h / 2, q.y + dy)) + 'px';
}
function updateTags() {
  const M = MODEL; let k = 0; const done = new Set();
  const put = (d, cls, dy) => { const nm = name(d); if (done.has(nm)) return; done.add(nm); const el = tagAt(k++, cls); el.textContent = nm; placeTag(el, posOf(M, d), dy); };
  put(M.cur, 'mg', -14); put(M.next, 'cy', 14);
  if (M.cut && S.cut) { put(M.cut.to, '', -14); put(M.cut.a, 'mg', 14); put(M.cut.b, 'mg', 14); }
  if (M.k && M.k <= 7) M.cycle.forEach((d) => put(d, 'cy', -14));
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
/* the n² outcomes of the current duel: rows are the faces of d, columns the faces of e */
function drawMain() {
  const M = MODEL, F2 = frame2d(cv1, 30); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, n = M.n, d = M.cur, e = M.next;
  const cell = Math.min(ih / n, (iw * (iw < 420 * dpr ? 0.5 : 0.62)) / n), x0 = pl, y0 = pt;
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
    const a = d[i], b = e[j];
    ctx.fillStyle = b < a ? 'rgba(25,240,255,0.75)' : b > a ? 'rgba(255,47,208,0.42)' : 'rgba(150,170,190,0.28)';
    ctx.fillRect(x0 + j * cell + 1, y0 + i * cell + 1, cell - 2, cell - 2);
  }
  ctx.font = `${Math.min(10.5, cell / dpr * 0.6) * dpr}px ${TRV.fonts.data}`;
  for (let i = 0; i < n; i++) { lab(ctx, d[i].toString(36), x0 - 4 * dpr, y0 + (i + 0.5) * cell, 'right', 'middle', INK); lab(ctx, e[i].toString(36), x0 + (i + 0.5) * cell, y0 + n * cell + 3 * dpr, 'center', 'top', INK); }
  const tx = x0 + n * cell + 14 * dpr, D2 = M.duel, fs = Math.min(12, Math.max(9, (F2.W - tx) / dpr / 13)), lh = fs * 1.6 * dpr; ctx.font = `${fs * dpr}px ${TRV.fonts.data}`;
  lab(ctx, `d = ${name(d)}`, tx, y0 + 2 * dpr, 'left', 'top', INK);
  lab(ctx, `e = ${name(e)}`, tx, y0 + 2 * dpr + lh, 'left', 'top', INK);
  lab(ctx, T(`赢 ${D2.win} · 平 ${D2.tie} · 输 ${D2.lose}`, `win ${D2.win} · tie ${D2.tie} · lose ${D2.lose}`), tx, y0 + 2 * dpr + 2.2 * lh, 'left', 'top', CY);
  lab(ctx, `P = ${D2.win}/${n * n}`, tx, y0 + 2 * dpr + 3.2 * lh, 'left', 'top', D2.win === M.th ? AM : MG);
  lab(ctx, D2.win === M.th ? T('= 最小优势', '= minimal advantage') : T('≠ 最小优势', '≠ minimal advantage'), tx, y0 + 2 * dpr + 4.2 * lh, 'left', 'top', D2.win === M.th ? AM : MG);
  $('c1Meta').innerHTML = `<span class="it"><i class="sw" style="--c:${CY}"></i>${T('d 赢', 'd wins')}</span><span class="it"><i class="sw" style="--c:${MG}"></i>${T('e 赢', 'e wins')}</span><span class="it"><i class="sw" style="--c:#8a9bb0"></i>${T('平', 'tie')}</span>`;
}
/* the longest cycle known for each n, against the line k = n, on a log scale */
function drawSide() {
  const M = MODEL, F2 = frame2d(cv2, 34); if (F2.iw < 60 || F2.ih < 40) return;
  const { ctx, dpr, pl, pt, iw, ih } = F2, ns = []; for (let n = NMIN; n <= NCHART; n++) ns.push(n);
  const bw = iw / ns.length, top = Math.log2(160), Y = (k) => pt + ih - ih * (k <= 0 ? 0 : (Math.log2(k) + 0.6) / (top + 0.6));
  for (const k of [1, 4, 16, 64]) { ctx.strokeStyle = 'rgba(120,140,160,0.18)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, Y(k)); ctx.lineTo(pl + iw, Y(k)); ctx.stroke(); lab(ctx, String(k), pl - 4 * dpr, Y(k), 'right', 'middle'); }
  lab(ctx, '0', pl - 4 * dpr, Y(0), 'right', 'middle');
  ctx.strokeStyle = AM; ctx.lineWidth = 1.2 * dpr; ctx.setLineDash([4 * dpr, 3 * dpr]); ctx.beginPath(); ns.forEach((n, i) => { const x = pl + (i + 0.5) * bw; if (i === 0) ctx.moveTo(x - bw / 2, Y(n)); ctx.lineTo(x, Y(n)); if (i === ns.length - 1) ctx.lineTo(x + bw / 2, Y(n)); }); ctx.stroke(); ctx.setLineDash([]);
  ns.forEach((n, i) => {
    const k = n < 6 ? 0 : knownLength(n), x = pl + i * bw + bw * 0.18, w = bw * 0.64, y = Y(k);
    ctx.fillStyle = n === M.n ? AM : n < 6 ? 'rgba(150,170,190,0.5)' : n === 6 ? 'rgba(70,255,178,0.8)' : 'rgba(25,240,255,0.7)';
    ctx.fillRect(x, Math.min(y, Y(0)) - (k ? 0 : 2 * dpr), w, Math.max(2 * dpr, Y(0) - y));
    lab(ctx, String(k), x + w / 2, y - 2 * dpr, 'center', 'bottom', n === M.n ? AM : DIM);
    lab(ctx, String(n), x + w / 2, pt + ih + 4 * dpr, 'center', 'top', n === M.n ? AM : DIM);
  });
  $('c2Meta').innerHTML = `<span class="it"><i class="sw" style="--c:#8a9bb0"></i>${T('无循环（页面）', 'no cycle (page)')}</span><span class="it"><i class="sw" style="--c:#46ffb2"></i>${T('最大值 6（Lean）', 'maximum 6 (Lean)')}</span><span class="it"><i class="sw" style="--c:${CY}"></i>${T('已知循环（Lean）', 'known cycle (Lean)')}</span><span class="it"><i class="sw" style="--c:${AM}"></i>k = n</span>`;
}

/* =====================================================================
   8. Readouts and controls
   ===================================================================== */
let syncedKey = '', toasted = false;
const toast = (html) => TRV.toast($('toast'), html);
function setRo(rows) { rows.forEach(([l, v], i) => { $(`ro${i + 1}L`).textContent = l; $(`ro${i + 1}`).textContent = v; }); }
function pill(id, label, value) { $(id).innerHTML = `${label} <strong>${value}</strong>`; }
const fmtInt = (x) => x.toLocaleString('en-US');
function readouts() {
  const M = MODEL, n = M.n, G = M.G, D2 = M.duel;
  pill('pillA', 'n', String(n)); pill('pillB', T('骰子', 'DICE'), fmtInt(M.count));
  pill('pillC', 'k', M.k ? `${M.k} ${M.k > n ? '>' : '='} n` : '—');
  pill('pillD', `S(${n})`, n === 6 ? '✓' : n >= 7 ? '✗' : '—');
  setRo([
    [T('骰子数 C(2n − 1, n) · 最小优势（n² 种掷法里赢 ⌊n²/2⌋ + 1 种）', 'Dice C(2n − 1, n) · minimal advantage (⌊n²/2⌋ + 1 wins of n²)'), `${fmtInt(M.count)} · ${probText(n)}`],
    G ? [T('最小优势的边 · 多于一颗骰子的强连通分支', 'Minimal-advantage edges · strongly connected components with more than one die'), `${fmtInt(G.E)} · ${G.knots.length ? G.knots.map((c) => c.length).join(', ') : T('无', 'none')}`]
      : [T('最小优势的边 · 强连通分支', 'Minimal-advantage edges · strongly connected components'), T('页面不枚举 n ≥ 8 的整张图', 'the page does not enumerate the whole graph for n ≥ 8')],
    [T('当前循环：长度 k 与 n', 'Current cycle: length k against n'), M.k ? `k = ${M.k} ${M.k > n ? '>' : '='} n = ${n}${M.edgeOK ? '' : ' !'}` : T('没有循环', 'no cycle')],
    [M.k ? T(`第 ${M.step + 1}/${M.k} 步 · 赢 · 平 · 输`, `Step ${M.step + 1}/${M.k} · win · tie · lose`) : T('Lean 取到最小值的那一对 · 赢 · 平 · 输', 'Lean’s attaining pair · win · tie · lose'), `${name(M.cur)} → ${name(M.next)} · ${D2.win} · ${D2.tie} · ${D2.lose}`],
    n === 6 && M.cut ? [T('最长循环（Lean：six_cycle_bound）· 结里的碰撞', 'Longest cycle (Lean: six_cycle_bound) · the collision in the knot'), `6 · ${name(M.cut.a)}, ${name(M.cut.b)} → ${name(M.cut.to)}`]
      : n < 6 ? [T('最长循环（页面枚举）', 'Longest cycle (page enumeration)'), `0`]
      : [T('最长循环', 'Longest cycle'), T(`≥ ${knownLength(n)}，最大值未知`, `≥ ${knownLength(n)}, maximum unknown`)]]);
  $('roNote').innerHTML = n === 6 ? T('n = 6：存在长度 6 的循环，没有更长的——S(6) 成立（Lean）。', 'n = 6: a cycle of length 6 exists and none is longer — S(6) holds (Lean).')
    : n >= 7 ? T(`n = ${n}：有长度 ${knownLength(n)} > ${n} 的循环，所以 S(${n}) 不成立（Lean）。`, `n = ${n}: a cycle of length ${knownLength(n)} > ${n} exists, so S(${n}) fails (Lean).`)
    : T(`n = ${n}：图里没有循环（页面枚举）；猜想不涉及 n ≤ 5。`, `n = ${n}: the graph has no cycle (page enumeration); the conjecture says nothing about n ≤ 5.`);
}
const stateKey = () => `${S.n}|${S.which}|${S.cut}|${MODEL ? MODEL.step : ''}|${S.preset}|${TRV.lang()}`;
function syncOutputs() {
  if (dirty) { build(); dirty = false; syncedKey = ''; glKey = ''; }
  const M = MODEL;
  if (!toasted && S.playing && M.k && S.t >= 1) { toasted = true; toast(T(`<b>走完一圈</b>：${M.k} 颗骰子，每一步都赢 ${M.th}/${M.n * M.n}，最后一颗又赢第一颗。`, `<b>Round trip</b>: ${M.k} dice, every step winning ${M.th} of ${M.n * M.n}, and the last die beats the first.`)); }
  const key = stateKey(); if (key === syncedKey) return; syncedKey = key;
  readouts();
  document.querySelectorAll('#nChips [data-n]').forEach((b) => b.setAttribute('aria-pressed', String(Number(b.dataset.n) === S.n)));
  $('presetNote').innerHTML = S.preset ? T(PRESETS[S.preset].zh, PRESETS[S.preset].en) : T('自定义设置：上面的卡带没有一个与当前设置完全一致。', 'Custom settings: none of the presets above matches the current settings exactly.');
  $('nNote').innerHTML = M.G ? T(`n = ${M.n}：页面枚举全部 ${fmtInt(M.count)} 颗骰子与 ${fmtInt(M.count * M.count)} 个有序对。`, `n = ${M.n}: the page enumerates all ${fmtInt(M.count)} dice and ${fmtInt(M.count * M.count)} ordered pairs.`) : T(`n = ${M.n}：${fmtInt(M.count)} 颗骰子太多，页面只画 Lean 核对过的种子循环。`, `n = ${M.n}: with ${fmtInt(M.count)} dice the page draws only the seed cycle that Lean checks.`);
  $('litNote').innerHTML = T('图里 n ≤ 5 的 0 与 n ≤ 7 的分支大小是页面枚举；n = 6 的最大值 6 与 n ≥ 7 的循环长度来自 Lean。', 'The zeros for n ≤ 5 and the component sizes for n ≤ 7 are page enumeration; the maximum 6 at n = 6 and the cycle lengths for n ≥ 7 come from Lean.');
  $('c1Title').textContent = M.k ? T('当前一步：两颗骰子对掷的 n² 种结果', 'Current step: the n² outcomes of the duel') : T('没有循环：Lean 取到最小优势的那一对', 'No cycle: the pair Lean uses to attain the minimum');
  $('c2Title').textContent = T('各个 n 的最长循环（已知）与 k = n', 'Longest known cycle for each n against k = n');
  $('clock').innerHTML = M.k ? `${M.step + 1}/${M.k}` : '—';
  $('hudBig').textContent = `n = ${M.n} · ${T(`${fmtInt(M.count)} 颗骰子`, `${fmtInt(M.count)} dice`)} · ${M.k ? `k = ${M.k}${M.k > M.n ? ' > n' : ' = n'}` : T('没有循环', 'no cycle')}`;
  $('hudSub').textContent = M.G ? T('每个点是一颗骰子，高度是总点数，同一高度排成一圈；灰线是最小优势的边（n ≤ 6），琥珀是强连通分支，青色是当前循环，白点是当前骰子，品红小点沿当前一步移动', 'Every point is a die, raised to its face sum, with each height laid out on a ring; grey lines are minimal-advantage edges (n ≤ 6), amber marks strongly connected components, cyan the current cycle, white the current die, and the small magenta dot moves along the current step')
    : T('只画种子循环：每个点是一颗骰子，高度是总点数，按循环顺序排成一圈', 'Only the seed cycle: every point is a die, raised to its face sum and placed around a ring in cycle order');
}
function syncRail() {
  const M = MODEL, key = `${M.k}|${TRV.lang()}`; if ($('marks').dataset.key === key) return; $('marks').dataset.key = key;
  const marks = M.k ? [[0, 'd₁'], [Math.floor(M.k / 2) / M.k, `d${sub(Math.floor(M.k / 2) + 1)}`], [1, T('回到 d₁', 'back to d₁')]] : [[0, T('没有循环', 'no cycle')]];
  $('marks').innerHTML = marks.map(([f, l], i) => `<i class="${i === 0 ? 'first' : i === marks.length - 1 ? 'last' : ''}" style="left:${(f * 100).toFixed(2)}%">${l}</i>`).join('');
}
const sub = (x) => String(x).replace(/\d/g, (c) => '₀₁₂₃₄₅₆₇₈₉'[c]);
function markPreset() { document.querySelectorAll('.preset').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.preset === S.preset))); }
document.querySelectorAll('#camChips .chip').forEach((b) => b.addEventListener('click', (ev) => { ev.stopPropagation(); setCamPreset(b.dataset.cam); }));
function applyPreset(nm) {
  const p = PRESETS[nm]; if (!p) return;
  Object.assign(S, { n: p.n, which: p.which, cut: p.cut, t: p.t, hold: 0 }); S.preset = nm; markPreset(); dirty = true; toasted = false;
  S.playing = !reduceMotion && p.play; S.dir = 1; setPlayUI(); $('now').value = S.t;
  build(); setCamPreset('iso');
  TRV.glitch($('app'));
}
document.querySelectorAll('.preset').forEach((b) => b.addEventListener('click', () => applyPreset(b.dataset.preset)));
document.querySelectorAll('#nChips [data-n]').forEach((b) => b.addEventListener('click', () => { S.n = Number(b.dataset.n); S.which = 'seed'; S.cut = false; S.t = 0; $('now').value = 0; S.preset = null; markPreset(); dirty = true; toasted = false; }));
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
  const k = MODEL ? MODEL.k : 0;
  if (ev.key === ' ' && !(ev.target && ev.target.tagName === 'BUTTON')) { ev.preventDefault(); S.playing = !S.playing; S.hold = 0; setPlayUI(); }
  else if ((ev.key === 'ArrowRight' || ev.key === 'ArrowLeft') && !(ev.target && ev.target.tagName === 'INPUT') && k) { ev.preventDefault(); const st = MODEL.step + (ev.key === 'ArrowRight' ? 1 : -1); jumpTo(((st % k) + k) % k / k); }
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
/* one step lasts STEP seconds at 1×, shortened so that a long cycle takes at most LOOP seconds */
const STEP = 1.4, LOOP = 40;
function frame(tms) {
  frameCount++;
  const dtSec = Math.min(0.1, (tms - lastT) / 1000); lastT = tms;
  if (dirty) syncOutputs();
  const k = MODEL.k;
  if (S.playing && !scrubbing && k) {
    if (S.hold > 0) { S.hold -= dtSec; if (S.hold <= 0) { setT(S.dir > 0 ? 0 : 1); toasted = false; } }
    else {
      setT(S.t + S.dir * dtSec * S.speed / Math.min(STEP * k, LOOP));
      if (S.t >= 1) S.hold = 2.4;
      if (S.t <= 0 && S.dir < 0) S.hold = 1.2;
    }
  }
  syncOutputs(); syncRail();
  if (glOK) {
    updateCamera(dtSec);
    if (glKey !== String(MODEL.id)) { updateGL(); addPulse(); glKey = String(MODEL.id); }
    updatePulse();
    renderer.render(scene3, camera); updateTags();
  }
  drawMain(); drawSide();
  requestAnimationFrame(frame);
}

TRV.onLang(() => { syncedKey = ''; syncOutputs(); $('marks').dataset.key = ''; });

/* read-only probe for automated browser tests */
window.DC_DEBUG = {
  pending: () => dirty || syncedKey !== stateKey(),
  frames: () => frameCount,
  state: () => JSON.parse(JSON.stringify(S)),
  info: () => { const M = MODEL, G = M.G; return { n: M.n, count: M.count, threshold: M.th, cycle: M.cycle.map(name), k: M.k, step: M.step, cur: name(M.cur), next: name(M.next), duel: { ...M.duel }, edgeOK: M.edgeOK,
    cut: M.cut ? { a: name(M.cut.a), b: name(M.cut.b), to: name(M.cut.to) } : null, knot: M.knot && G ? M.knot.map((i) => name(G.dice[i])).sort() : null,
    graph: G ? { N: G.N, E: G.E, down: G.down, isolated: G.isolated, knots: G.knots.map((c) => c.length), longest: G.longest ? G.longest.map((c) => c.length) : null } : null, known: M.n >= 6 ? knownLength(M.n) : 0 }; },
  edges: (n) => { const G = graph(n); const out = []; G.adj.forEach((l, a) => l.forEach((b) => out.push(name(G.dice[a]) + '>' + name(G.dice[b])))); return out; },
  known: (n) => knownLength(n),
  setT: (t) => setT(t)
};

/* cover state for scripts/thumbs.mjs */
window.TRV_THUMB = () => { applyPreset('lean'); S.playing = false; setPlayUI(); setCamPreset('iso'); cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR = 9; };

initGL();
if (glOK) { new ResizeObserver(resize).observe(stage); resize(); }
applyPreset('lean');
if (glOK) { cam.theta = cam.tTheta; cam.phi = cam.tPhi; cam.r = cam.tR; }
setPlayUI();
requestAnimationFrame(frame);
})();
