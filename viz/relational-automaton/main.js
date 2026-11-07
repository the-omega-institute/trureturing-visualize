(() => {
  'use strict';
  const $ = (id) => document.getElementById(id);
  const cv = $('view');
  const S = { step: 0, phase: 0, rate: 1, playing: false, t: 0 };
  const SQ = Math.SQRT1_2;
  TRV.startGlitch($('app'));
  const drawer = TRV.drawer({ drawer: $('drawer'), open: $('infoBtn'), close: $('drawerClose') });

  const cadd = (a,b) => [a[0]+b[0], a[1]+b[1]];
  const cmul = (a,b) => [a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]];
  const conj = (a) => [a[0], -a[1]];
  const stateAt = (step, phase) => {
    const z = phase * Math.PI / 180, e = [Math.cos(z), Math.sin(z)];
    if (step === 0) return [[1,0],[0,0]];
    if (step === 1) return [[SQ,0],[SQ,0]];
    const splitPhase = [[SQ,0], cmul([SQ,0], e)];
    if (step === 2) return splitPhase;
    return [[(splitPhase[0][0]+splitPhase[1][0])/SQ/2, (splitPhase[0][1]+splitPhase[1][1])/SQ/2],
      [(splitPhase[0][0]-splitPhase[1][0])/SQ/2, (splitPhase[0][1]-splitPhase[1][1])/SQ/2]];
  };
  const norm = (v) => v.reduce((s,a) => s + a[0]*a[0] + a[1]*a[1], 0);
  const bloch = (v) => {
    const ab = cmul(conj(v[0]), v[1]);
    return [2*ab[0], 2*ab[1], v[0][0]*v[0][0]+v[0][1]*v[0][1]-v[1][0]*v[1][0]-v[1][1]*v[1][1]];
  };
  const fmt = (x) => Math.abs(x) < 5e-4 ? '0' : x.toFixed(3);
  const ket = (v) => {
    const f = (a) => {
      const r = fmt(a[0]), i = fmt(a[1]);
      if (Math.abs(a[1]) < 5e-4) return r;
      return r + (a[1] >= 0 ? '+' : '') + i + 'i';
    };
    return f(v[0]) + ' |0⟩ + ' + f(v[1]) + ' |1⟩';
  };
  const relationEdges = (step) => step === 0 ? 0 : step === 1 ? 1 : step === 2 ? 3 : 6;
  const textFor = (step) => {
    const zh = ['恒等没有可区分的关系；系统只有一个稳定标签。','一次二元分叉产生两条可读分支；平方范数保持总量。','两条分支之间出现相对相位；三角闭包把关系的关系写出来。','重复门作用把局部三角复制成网络；可见读出来自边上的约束。'][step];
    const en = ['Identity has no distinguishable relation; the system carries one stable label.','A binary split creates two readable branches; the squared norm keeps the total.','A relative phase appears; triangle closure records a relation of relations.','Repeated gates copy local triangles into a network; visible readouts come from edge constraints.'][step];
    return TRV.L(zh, en);
  };
  function draw() {
    const v = stateAt(S.step, S.phase), b = bloch(v), n = norm(v);
    const dpr = TRV.fitCanvas(cv), W = cv.width, H = cv.height, ctx = cv.getContext('2d');
    ctx.clearRect(0,0,W,H);
    const cyan = '#19f0ff', mag = '#ff2fd0', amber = '#ffc857', dim = 'rgba(220,235,245,.52)', faint = 'rgba(220,235,245,.14)';
    const sx = W / 1000, sy = H / 620, sc = Math.min(sx,sy);
    ctx.save(); ctx.scale(sc,sc); const w = W/sc, h = H/sc;
    ctx.strokeStyle = faint; ctx.lineWidth = 1.2; ctx.setLineDash([4,6]);
    for (let y=92;y<h-54;y+=92) { ctx.beginPath(); ctx.moveTo(28,y); ctx.lineTo(w-28,y); ctx.stroke(); }
    ctx.setLineDash([]);
    const xs = [130, 350, 570, 790], y = 215;
    const labels = ['1','2','3','∞']; const colors = [dim,cyan,mag,amber];
    for (let i=0;i<3;i++) { ctx.strokeStyle = i < S.step ? colors[Math.min(i+1,3)] : faint; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(xs[i]+38,y); ctx.lineTo(xs[i+1]-38,y); ctx.stroke(); ctx.beginPath(); ctx.arc(xs[i+1]-45,y,6,0,Math.PI*2); ctx.fillStyle = ctx.strokeStyle; ctx.fill(); }
    for (let i=0;i<4;i++) { ctx.beginPath(); ctx.arc(xs[i],y,34,0,Math.PI*2); ctx.fillStyle = i <= S.step ? colors[i] : 'rgba(255,255,255,.08)'; ctx.globalAlpha = i <= S.step ? .95 : .45; ctx.fill(); ctx.globalAlpha=1; ctx.fillStyle='#071116'; ctx.font='700 22px Chakra Petch, sans-serif'; ctx.textAlign='center'; ctx.textBaseline='middle'; ctx.fillText(labels[i],xs[i],y); }
    ctx.fillStyle=dim; ctx.font='600 14px JetBrains Mono, monospace'; ctx.textAlign='center'; ctx.fillText(TRV.L('关系阶数','relation order'),xs[1],y+66);
    const cx = 270, cy = 447, r = 112;
    ctx.strokeStyle=faint; ctx.lineWidth=1; ctx.beginPath(); ctx.arc(cx,cy,r,0,Math.PI*2); ctx.stroke(); ctx.beginPath(); ctx.moveTo(cx-r-12,cy); ctx.lineTo(cx+r+12,cy); ctx.moveTo(cx,cy-r-12); ctx.lineTo(cx,cy+r+12); ctx.stroke();
    ctx.fillStyle=dim; ctx.font='12px JetBrains Mono, monospace'; ctx.fillText('x',cx+r+20,cy+4); ctx.fillText('z',cx+4,cy-r-18);
    const bx = cx + b[0]*r, by = cy - b[2]*r; ctx.strokeStyle=amber; ctx.lineWidth=5; ctx.beginPath(); ctx.moveTo(cx,cy); ctx.lineTo(bx,by); ctx.stroke(); ctx.fillStyle=amber; ctx.beginPath(); ctx.arc(bx,by,7,0,Math.PI*2); ctx.fill();
    ctx.fillStyle=dim; ctx.textAlign='left'; ctx.fillText(TRV.L('可见球面截面：Bloch 向量','visible sphere section: Bloch vector'),42,cy+r+38);
    const px=540, py=365, bw=265, bh=42; ctx.fillStyle=dim; ctx.textAlign='left'; ctx.fillText(TRV.L('Born 读出','Born readout'),px,py-18);
    const p0=v[0][0]*v[0][0]+v[0][1]*v[0][1], p1=1-p0;
    for (const [label,p,col,yy] of [['0',p0,cyan,py],['1',p1,mag,py+64]]) { ctx.fillStyle=faint; ctx.fillRect(px,yy,bw,bh); ctx.fillStyle=col; ctx.fillRect(px,yy,bw*p,bh); ctx.fillStyle='#eef8fb'; ctx.font='600 14px JetBrains Mono, monospace'; ctx.fillText(label+'   '+p.toFixed(3),px+10,yy+26); }
    ctx.fillStyle=dim; ctx.font='12px JetBrains Mono, monospace'; ctx.fillText('|a|² + |b|² = '+n.toFixed(6),px,py+150);
    ctx.restore();
  }
  function sync() {
    const v = stateAt(S.step,S.phase), n = norm(v), p0=v[0][0]*v[0][0]+v[0][1]*v[0][1], p1=1-p0;
    $('pillStep').innerHTML = 'STEP <strong>' + (S.step === 3 ? '∞' : S.step) + '</strong>';
    $('pillNorm').innerHTML = 'NORM <strong>' + n.toFixed(3) + '</strong>';
    $('oPhase').textContent = S.phase + '°'; $('oRate').textContent = S.rate + '×';
    $('roState').textContent = ket(v); $('roNorm').textContent = (n-1).toExponential(2); $('roEdges').textContent = String(relationEdges(S.step)); $('roBorn').textContent = p0.toFixed(3)+' · '+p1.toFixed(3);
    $('hudBig').textContent = (S.step === 0 ? '1' : S.step === 1 ? '1 → 2' : S.step === 2 ? '1 → 2 → 3' : '1 → 2 → 3 → ∞');
    $('hudSub').textContent = textFor(S.step); $('hudPhase').textContent = TRV.L('φ = '+S.phase+'°','φ = '+S.phase+'°');
    $('ruleText').textContent = textFor(S.step);
    $('formula').textContent = S.step < 2 ? '|a|² + |b|² = 1' : 'p(0) = |a|²,   p(1) = |b|²,   Δ = arg(b) − arg(a) = '+S.phase+'°';
    document.querySelectorAll('#stepChips .chip').forEach((b) => b.setAttribute('aria-pressed',String(+b.dataset.step === S.step)));
    $('modeNote').textContent = S.playing ? TRV.L('自动沿着闭包阶数运行。','Auto-running through the closure orders.') : TRV.L('选择一个阶数，或按播放观察闭包展开。','Choose an order, or play the closure expansion.');
    $('play').innerHTML = S.playing ? TRV.L('❚❚ 暂停','❚❚ Pause') : TRV.L('▶ 播放','▶ Play');
    $('play').setAttribute('aria-pressed',String(S.playing));
  }
  function setStep(k) { S.step = Math.max(0,Math.min(3,k|0)); sync(); draw(); }
  document.querySelectorAll('#stepChips .chip').forEach((b) => b.addEventListener('click',() => setStep(+b.dataset.step)));
  $('phase').addEventListener('input',(e) => { S.phase = +e.target.value; sync(); draw(); });
  $('rate').addEventListener('input',(e) => { S.rate = +e.target.value; sync(); });
  $('play').addEventListener('click',() => { S.playing=!S.playing; sync(); });
  $('reset').addEventListener('click',() => { S.step=0; S.phase=0; S.playing=false; $('phase').value=0; sync(); draw(); });
  const advance = (dt) => { if (!S.playing) return; S.t += dt*S.rate; if (S.t > 1.35) { S.t=0; setStep((S.step+1)%4); } };
  let last = performance.now();
  function frame(now) { advance(Math.min(.1,(now-last)/1000)); last=now; draw(); requestAnimationFrame(frame); }
  TRV.onLang(() => { sync(); draw(); });
  window.RQA_DEBUG = { frames: () => 1, state: () => ({...S}), info: () => { const v=stateAt(S.step,S.phase); return { step:S.step, phase:S.phase, state:v, norm:norm(v), born:[v[0][0]*v[0][0]+v[0][1]*v[0][1],v[1][0]*v[1][0]+v[1][1]*v[1][1]], edges:relationEdges(S.step), bloch:bloch(v) }; }, setStep, setPhase: (p) => { S.phase=+p; $('phase').value=S.phase; sync(); draw(); } };
  window.TRV_THUMB = () => { S.step=3; S.phase=90; S.playing=false; $('phase').value=90; sync(); draw(); };
  sync(); draw(); requestAnimationFrame(frame);
})();