(() => {
  'use strict';
  const $ = (id) => document.getElementById(id);
  const cv = $('view');
  const S = { step: 0, phase: 0, rate: 1, playing: false, t: 0, rule: 0, fault: false };
  const SQ = Math.SQRT1_2;
  const RULES = [
    { code:'R0', zh:'恒等与归一化', en:'Identity and normalization', need:0,
      conditionZh:'触发：存在恒等记录 Ω，闭包更新不改变总权重。',
      conditionEn:'Trigger: an identity record Ω preserves total weight under closure updates.',
      transitionZh:'证据：|a|² + |b|² = 1。',
      transitionEn:'Evidence: |a|² + |b|² = 1.',
      failureZh:'反例：总范数偏离 1，恒等记录不能保持闭包。',
      failureEn:'Counterexample: the norm leaves 1, so identity does not preserve closure.' },
    { code:'R1', zh:'二元区分', en:'Binary distinction', need:1,
      conditionZh:'触发：一个记录可以分成两个互补、可读的分支。',
      conditionEn:'Trigger: one record splits into two complementary readable branches.',
      transitionZh:'证据：分叉后 p(0)=p(1)=1/2，关系边数为 1。',
      transitionEn:'Evidence: after the split p(0)=p(1)=1/2 and one relation edge appears.',
      failureZh:'反例：两条分支不能同时归一化或无法区分。',
      failureEn:'Counterexample: the two branches cannot be normalized or distinguished.' },
    { code:'R2', zh:'有向三元闭包', en:'Oriented ternary closure', need:2,
      conditionZh:'触发：两条分支的关系也成为可测试记录，并保留定向相位。',
      conditionEn:'Trigger: the relation between the two branches becomes testable and keeps orientation.',
      transitionZh:'证据：三条关系边与有限相对相位 φ。',
      transitionEn:'Evidence: three relation edges and a finite relative phase φ.',
      failureZh:'反例：相位被抹掉，或者三角关系无法闭合。',
      failureEn:'Counterexample: phase is erased or the triangle cannot close.' },
    { code:'R3', zh:'后继一致性', en:'Successor consistency', need:3,
      conditionZh:'触发：相同当前记录的不同后继必须共享同一延续核。',
      conditionEn:'Trigger: continuations of the same current record share one continuation kernel.',
      transitionZh:'有限证书：网络步保持归一化并完成六条局部关系边。',
      transitionEn:'Finite certificate: the network step preserves normalization and closes six local edges.',
      failureZh:'反例：同一记录的后继给出不同核，更新不能下降为线性分支。',
      failureEn:'Counterexample: equal records yield different successor kernels, blocking linear branches.' },
    { code:'R4', zh:'完整正读出', en:'Complete positive readout', need:0,
      conditionZh:'触发：所有可读效应给出非负且可归一化的概率。',
      conditionEn:'Trigger: every readable effect gives a nonnegative normalized probability.',
      transitionZh:'证据：p(0)=|a|²，p(1)=|b|²，且 p(0)+p(1)=1。',
      transitionEn:'Evidence: p(0)=|a|², p(1)=|b|², and p(0)+p(1)=1.',
      failureZh:'反例：读出出现负值、总和不为一，或不再是二次形式。',
      failureEn:'Counterexample: a readout is negative, unnormalized, or ceases to be quadratic.' },
    { code:'R5', zh:'独立历史复合', en:'Independent-history composition', need:3,
      conditionZh:'触发：独立历史可以联合，且联合记录保留交叉关系。',
      conditionEn:'Trigger: independent histories compose while retaining cross-relations.',
      transitionZh:'证据：网络闭包把局部三角扩展为六条边的联合记录。',
      transitionEn:'Evidence: network closure expands local triangles into a six-edge joint record.',
      failureZh:'反例：只保留边缘分布，联合效应能检测到被删除的交叉关系。',
      failureEn:'Counterexample: marginals erase a cross-relation detected by a joint effect.' }
  ];
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
  const CLOSURE_TRACE = [
    { label:'S0', records:1, edges:0, passed:['R0','R4'] },
    { label:'S1', records:3, edges:1, passed:['R0','R1','R4'] },
    { label:'S2', records:5, edges:3, passed:['R0','R1','R2','R4'] },
    { label:'S3', records:6, edges:6, passed:['R0','R1','R2','R3','R4','R5'] }
  ];
  const ruleReport = () => {
    const v = stateAt(S.step, S.phase), n = norm(v);
    const p0 = v[0][0]*v[0][0] + v[0][1]*v[0][1], p1 = v[1][0]*v[1][0] + v[1][1]*v[1][1];
    const edges = relationEdges(S.step), finitePhase = Number.isFinite(S.phase);
    const evidence = [
      Math.abs(n - 1) < 1e-9,
      S.step >= 1 && Math.abs(p0 - .5) < 1e-9 && Math.abs(p1 - .5) < 1e-9,
      S.step >= 2 && edges >= 3 && finitePhase,
      S.step >= 3 && edges >= 6 && Math.abs(n - 1) < 1e-9,
      Math.abs(p0 + p1 - 1) < 1e-9,
      S.step >= 3 && edges === 6
    ];
    return RULES.map((r, i) => {
      const waiting = S.step < r.need;
      const failed = S.fault && S.rule === i;
      const status = failed ? 'FAIL' : waiting ? 'WAIT' : evidence[i] ? 'PASS' : 'FAIL';
      const reason = failed ? TRV.L(r.failureZh, r.failureEn)
        : waiting ? TRV.L('等待自动机到达第 '+r.need+' 阶。', 'Waiting for the automaton to reach step '+r.need+'.')
        : evidence[i] ? TRV.L('当前有限证据满足规则。', 'Current finite evidence satisfies the rule.')
        : TRV.L(r.failureZh, r.failureEn);
      return { code:r.code, status, reason, condition:TRV.L(r.conditionZh,r.conditionEn), transition:TRV.L(r.transitionZh,r.transitionEn) };
    });
  };
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
    const reports = ruleReport();
    const trace = CLOSURE_TRACE.map((item, index) => ({
      ...item,
      active: index <= S.step,
      fixed: index === 3 && S.step === 3 && !S.fault
    }));
    $('fixedPointBadge').textContent = S.step === 3 && !S.fault ? TRV.L('FIXED POINT','FIXED POINT') : TRV.L('OPEN','OPEN');
    $('fixedPointBadge').dataset.fixed = String(S.step === 3 && !S.fault);
    $('closureTrace').innerHTML = trace.map((item) => {
      const state = item.fixed ? 'fixed' : item.active ? 'closed' : 'waiting';
      return '<div class="closure-row '+state+'"><strong>'+item.label+'</strong><span>'+item.records+' '+TRV.L('记录','records')+'</span><span>'+item.edges+' '+TRV.L('边','edges')+'</span><span>'+item.passed.join(' ')+'</span></div>';
    }).join('');
    $('closureNote').textContent = S.step === 3 && !S.fault
      ? TRV.L('S3 = S4：本有限生成族没有新增记录。','S3 = S4: this finite generated family adds no new record.')
      : TRV.L('继续生成后继记录，直到下一轮不再增加。','Continue generating successors until the next round adds nothing.');
    document.querySelectorAll('.rule-tab').forEach((button) => {
      const i = +button.dataset.rule, report = reports[i];
      button.dataset.status = report.status;
      button.setAttribute('aria-selected', String(i === S.rule));
    });
    const active = reports[S.rule], rule = RULES[S.rule];
    $('ruleCode').textContent = rule.code;
    $('ruleName').textContent = TRV.L(rule.zh, rule.en);
    $('ruleStatus').textContent = active.status;
    $('ruleStatus').dataset.status = active.status;
    $('ruleCondition').textContent = active.condition;
    $('ruleTransition').textContent = active.transition + ' · ' + active.reason;
    $('ruleFailure').textContent = active.status === 'FAIL' ? active.reason : TRV.L('反例模式：点击按钮，使当前规则暂时失败。', 'Counterexample mode: click the button to fail this rule.');
    $('faultBtn').textContent = S.fault ? TRV.L('恢复规则', 'Restore rule') : TRV.L('注入反例', 'Inject counterexample');
    $('play').innerHTML = S.playing ? TRV.L('❚❚ 暂停','❚❚ Pause') : TRV.L('▶ 播放','▶ Play');
    $('play').setAttribute('aria-pressed',String(S.playing));
  }
  function setStep(k) { S.step = Math.max(0,Math.min(3,k|0)); sync(); draw(); }
  document.querySelectorAll('#stepChips .chip').forEach((b) => b.addEventListener('click',() => setStep(+b.dataset.step)));
  document.querySelectorAll('.rule-tab').forEach((b) => b.addEventListener('click',() => { S.rule=+b.dataset.rule; S.fault=false; sync(); draw(); }));
  $('faultBtn').addEventListener('click',() => { S.fault=!S.fault; sync(); draw(); });
  $('phase').addEventListener('input',(e) => { S.phase = +e.target.value; sync(); draw(); });
  $('rate').addEventListener('input',(e) => { S.rate = +e.target.value; sync(); });
  $('play').addEventListener('click',() => { S.playing=!S.playing; sync(); });
  $('reset').addEventListener('click',() => { S.step=0; S.phase=0; S.playing=false; S.rule=0; S.fault=false; $('phase').value=0; sync(); draw(); });
  const advance = (dt) => { if (!S.playing) return; S.t += dt*S.rate; if (S.t > 1.35) { S.t=0; setStep((S.step+1)%4); } };
  let last = performance.now();
  function frame(now) { advance(Math.min(.1,(now-last)/1000)); last=now; draw(); requestAnimationFrame(frame); }
  TRV.onLang(() => { sync(); draw(); });
  window.RQA_DEBUG = { frames: () => 1, state: () => ({...S}), info: () => { const v=stateAt(S.step,S.phase); return { step:S.step, phase:S.phase, state:v, norm:norm(v), born:[v[0][0]*v[0][0]+v[0][1]*v[0][1],v[1][0]*v[1][0]+v[1][1]*v[1][1]], edges:relationEdges(S.step), bloch:bloch(v), rules:ruleReport() }; }, setStep, setPhase: (p) => { S.phase=+p; $('phase').value=S.phase; sync(); draw(); }, setRule: (r) => { S.rule=+r; S.fault=false; sync(); draw(); }, injectFault: () => { S.fault=!S.fault; sync(); draw(); } };
  window.TRV_THUMB = () => { S.step=3; S.phase=90; S.playing=false; $('phase').value=90; sync(); draw(); };
  sync(); draw(); requestAnimationFrame(frame);
})();