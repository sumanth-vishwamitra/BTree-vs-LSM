/* UI wiring: configuration, frame loop, metrics, charts, log. */
(function () {
  'use strict';
  const SK = window.SK, C = window.SKC, fmtUs = window.fmtUs, fmtInt = window.fmtInt;
  const $ = id => document.getElementById(id);

  const PRESETS = {
    hdd: { storage: 'hdd', rate: 3000, wr: 100, dist: 'uniform', speed: 0.1 },
    ssd: { storage: 'ssd', rate: 25000, wr: 100, dist: 'uniform', speed: 0.02 },
    mixed: { storage: 'hdd', rate: 3000, wr: 50, dist: 'uniform', speed: 0.1 },
    zipf: { storage: 'hdd', rate: 3000, wr: 100, dist: 'zipf', speed: 0.1 },
    seq: { storage: 'hdd', rate: 3000, wr: 100, dist: 'seq', speed: 0.1 },
  };
  const STRUCTURAL = ['storage', 'pageSize', 'memBytes', 'cacheBytes', 'dataset', 'valueBytes', 'seed'];

  let sim, running = true, speed = 0.1, realTime = 0, ff = null, lastT = performance.now(), slow = false;
  let lastMetrics = 0, lastLogFlush = 0;
  const logLines = [], logQueue = [];
  const hist = { bt: [], lsm: [] };

  const panels = {
    bt: new window.Panel($('cvBT'), 'bt', onLog),
    lsm: new window.Panel($('cvLSM'), 'lsm', onLog),
  };

  /* -------------------------------------------------------------- metrics UI */
  const dash = '—';
  const spec = [
    ['thr', 'Throughput', 'hi', s => fmtInt(s.thr) + ' /s'],
    ['avg', 'Avg latency', 'hi', s => s.completed ? fmtUs(s.avg) : dash],
    ['p99', 'p99 latency', 'hi', s => s.completed ? fmtUs(s.p99) : dash],
    ['qd', 'Queue depth', 'hi', s => fmtInt(s.qd)],
    ['completed', 'Completed', 'hi', s => fmtInt(s.completed)],
    ['wa', 'Write amp.', 'hi', s => s.wa == null ? dash : s.wa.toFixed(1) + '×'],
    ['reads', 'Disk reads', 'disk', s => fmtInt(s.reads)],
    ['writes', 'Disk writes', 'disk', s => fmtInt(s.writes)],
    ['seeks', 'Disk seeks', 'disk', s => fmtInt(s.seeks)],
    ['iops', 'Disk IOPS', 'disk', s => fmtInt(s.iops)],
    ['mem', 'Memory writes', 'memc', s => fmtInt(s.memWrites)],
    ['wal', 'WAL appends', 'seqc', s => fmtInt(s.wal)],
    ['syncs', 'WAL fsyncs', 'seqc', s => fmtInt(s.syncs)],
    ['splits', 'Page splits', 'disk', (s, id) => id === 'bt' ? fmtInt(s.splits) : dash],
    ['flushes', 'Flushes', 'bgc', (s, id) => id === 'bt' ? fmtInt(s.flushes) + ' pages' : fmtInt(s.flushes) + ' tables'],
    ['comp', 'Compactions', 'bgc', (s, id) => id === 'lsm' ? fmtInt(s.compactions) : dash],
    ['hit', 'Cache hit', 'memc', s => s.hitPct == null ? dash : s.hitPct.toFixed(0) + '%'],
    ['busy', 'Disk busy', 'disk', s => s.busyPct.toFixed(0) + '%'],
    ['stall', 'Stalled', '', s => (s.stallUs / 1e6).toFixed(1) + ' s'],
  ];
  const cells = { bt: {}, lsm: {} };
  for (const id of ['bt', 'lsm']) {
    const host = $(id === 'bt' ? 'mBT' : 'mLSM');
    for (const [key, label, cls] of spec) {
      const d = document.createElement('div'); d.className = 'm ' + cls;
      d.innerHTML = '<span class="k">' + label + '</span><span class="v">—</span>';
      host.appendChild(d); cells[id][key] = d.lastChild;
    }
  }
  // B+ Tree "flushes" are dirty page write-backs; the label makes that explicit.
  cells.bt.flushes.previousSibling.textContent = 'Page flushes';
  cells.lsm.flushes.previousSibling.textContent = 'SSTable flushes';

  function updateMetrics() {
    const snaps = {};
    for (const e of sim.engines) {
      const s = snaps[e.id] = sim.snapshot(e);
      for (const [key, , , fn] of spec) cells[e.id][key].textContent = fn(s, e.id);
    }
    const b = snaps.bt, l = snaps.lsm, now = sim.sim.now;
    $('clock').textContent = (now / 1e6).toFixed(2) + ' s';
    $('realclock').textContent = realTime.toFixed(1);

    for (const id of ['bt', 'lsm']) {
      const s = snaps[id], h = hist[id]; h.push([now, s.qd]); while (h.length && now - h[0][0] > 3e6) h.shift();
      const grow = h.length > 1 && s.qd > h[0][1] + 5;
      const el = $(id === 'bt' ? 'badgeBT' : 'badgeLSM'), e = sim.engines[id === 'bt' ? 0 : 1];
      let cls = '', txt = '';
      if (s.qd > 300 && grow) { cls = 'sat'; txt = 'SATURATED · falling behind'; }
      else if (e.stall) { cls = 'warn'; txt = 'WRITE STALL'; }
      else if (s.completed > 50 && s.qd < 60) { cls = 'ok'; txt = 'KEEPING UP'; }
      el.className = 'badge ' + cls; el.textContent = txt;
    }

    // scoreboard
    const ratio = (a, bb) => bb > 0 ? a / bb : null;
    const fx = v => v >= 100 ? Math.round(v) : v >= 10 ? v.toFixed(0) : v.toFixed(1);
    const thrR = ratio(l.thr, b.thr);
    $('sThr').textContent = thrR && now > 2e6 ? fx(thrR) + '× faster' : dash;
    $('sThrSub').textContent = 'LSM ' + fmtInt(l.thr) + ' vs B+ ' + fmtInt(b.thr) + ' ops/s';
    const p99R = ratio(b.p99, l.p99);
    $('sP99').textContent = b.completed > 20 && l.completed > 20 && p99R ? fx(p99R) + '× lower' : dash;
    $('sP99Sub').textContent = 'LSM ' + (l.completed ? fmtUs(l.p99) : dash) + ' vs B+ ' + (b.completed ? fmtUs(b.p99) : dash);
    const bs = b.completed ? b.seeks / b.completed : 0, ls = l.completed ? l.seeks / l.completed : 0;
    $('sSeek').textContent = b.completed > 20 && l.completed > 20 ? (ls > 0 ? fx(bs / ls) + '× fewer' : (bs > 0 ? 'far fewer' : dash)) : dash;
    $('sSeekSub').textContent = 'seeks per op: LSM ' + ls.toFixed(3) + ' vs B+ ' + bs.toFixed(2);
    $('sWA').textContent = b.wa != null && l.wa != null ? 'B+ ' + b.wa.toFixed(1) + '× · LSM ' + l.wa.toFixed(1) + '×' : dash;
    $('sWASub').textContent = 'LSM rewrites more bytes, but in big sequential runs';

    if (now > 2e6 && b.thr > 0 && l.thr > 0) {
      const hdd = sim.cfg.storage === 'hdd';
      let v = 'On ' + (hdd ? 'an HDD' : 'an SSD') + ', the LSM Tree sustains <b>' + fmtInt(l.thr) + ' ops/s</b> while the B+ Tree manages <b>' + fmtInt(b.thr) + ' ops/s</b>';
      v += ' — ' + (hdd ? 'head seeks' : 'random-access latency') + ' eat <b>' + b.seekPct.toFixed(0) + '%</b> of the B+ Tree disk\'s time (disk ' + b.busyPct.toFixed(0) + '% busy) versus <b>' + l.seekPct.toFixed(0) + '%</b> for the LSM (' + l.busyPct.toFixed(0) + '% busy, mostly sequential).';
      if (b.qd > 100) v += ' B+ Tree queue: <b>' + fmtInt(b.qd) + '</b> requests waiting.';
      $('verdict').innerHTML = v;
    } else if (now > 2e6) $('verdict').textContent = 'Workload is light or read-heavy — both engines keep up. Raise the offered load or write ratio to expose the difference.';
  }

  /* ------------------------------------------------------------------ charts */
  const chartDefs = [
    { id: 'chThr', key: 'thr', log: false, fmt: v => fmtInt(v) },
    { id: 'chP99', key: 'p99', log: true, fmt: v => fmtUs(v) },
    { id: 'chQD', key: 'qd', log: false, fmt: v => fmtInt(v) },
  ];
  function drawChart(def) {
    const cv = $(def.id), dpr = window.devicePixelRatio || 1;
    const w = cv.clientWidth, h = cv.clientHeight;
    if (cv.width !== Math.round(w * dpr)) { cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr); }
    const ctx = cv.getContext('2d'); ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, w, h);
    const now = sim.sim.now / 1e6, span = 120, t0 = Math.max(0, now - span), padL = 46, padB = 16, padT = 6;
    const pw = w - padL - 6, ph = h - padB - padT;
    const sets = [['bt', '#ff8a5b'], ['lsm', '#34d399']];
    let max = 1, min = Infinity;
    for (const [id] of sets) {
      const s = sim[id].series;
      for (let i = 0; i < s.t.length; i++) if (s.t[i] >= t0) { const v = s[def.key][i]; if (v > max) max = v; if (v > 0 && v < min) min = v; }
    }
    let lo = 0, hi = max * 1.1;
    if (def.log) { lo = Math.log10(Math.max(50, Math.min(min, 1e5))) - 0.1; hi = Math.log10(max * 1.2); if (hi - lo < 1) hi = lo + 1; }
    const X = t => padL + (t - t0) / Math.max(1, now - t0 < 5 ? 5 : now - t0) * pw;
    const Y = v => padT + ph - (((def.log ? Math.log10(Math.max(v, 1)) : v) - lo) / (hi - lo)) * ph;
    ctx.font = '10px ui-monospace, Menlo, monospace'; ctx.textBaseline = 'middle'; ctx.textAlign = 'right';
    for (let i = 0; i <= 4; i++) {
      const frac = i / 4, y = padT + ph - frac * ph, val = def.log ? Math.pow(10, lo + frac * (hi - lo)) : lo + frac * (hi - lo);
      ctx.strokeStyle = 'rgba(120,140,210,.14)'; ctx.beginPath(); ctx.moveTo(padL, y); ctx.lineTo(w - 6, y); ctx.stroke();
      ctx.fillStyle = '#8b97b3'; ctx.fillText(def.fmt(val), padL - 5, y);
    }
    ctx.textAlign = 'center'; ctx.textBaseline = 'top';
    ctx.fillText('t = ' + t0.toFixed(0) + ' s', padL + 18, h - padB + 3); ctx.fillText(now.toFixed(0) + ' s', w - 20, h - padB + 3);
    for (const [id, col] of sets) {
      const s = sim[id].series; ctx.strokeStyle = col; ctx.lineWidth = 2; ctx.beginPath(); let started = false;
      for (let i = 0; i < s.t.length; i++) {
        if (s.t[i] < t0) continue;
        const v = s[def.key][i]; if (def.log && v <= 0) continue;
        const x = X(s.t[i]), y = Y(v); if (!started) { ctx.moveTo(x, y); started = true; } else ctx.lineTo(x, y);
      }
      ctx.stroke();
    }
  }
  function drawCharts() { for (const d of chartDefs) drawChart(d); }

  /* --------------------------------------------------------------------- log */
  function onLog(eng, e) { logQueue.push({ eng, t: e.t !== undefined ? e.t : sim.sim.now, cls: e.cls, text: e.text }); if (logQueue.length > 200) logQueue.splice(0, 100); }
  function flushLog() {
    if (!logQueue.length) return;
    const norm = s => s.replace(/[\d.,]+/g, '#');
    for (const q of logQueue.splice(0)) {
      const last = logLines.find(l => l.eng === q.eng);
      if (last && last === logLines[0] && norm(last.text) === norm(q.text)) { last.n++; last.text = q.text; last.t = q.t; }
      else logLines.unshift({ eng: q.eng, t: q.t, cls: q.cls, text: q.text, n: 1 });
    }
    logLines.length = Math.min(logLines.length, 70);
    $('log').innerHTML = logLines.map(l => '<div class="' + l.eng + '"><span class="t">' + (l.t / 1e6).toFixed(2) + 's</span><span class="tag">' + (l.eng === 'bt' ? 'B+' : 'LSM') + '</span><span class="' + l.cls + '">' + esc(l.text) + (l.n > 1 ? ' ×' + l.n : '') + '</span></div>').join('');
  }
  const esc = s => s.replace(/[&<>]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));

  /* ------------------------------------------------------------ config + reset */
  function readConfig() {
    return {
      storage: $('storage').value, dist: $('dist').value, rate: Math.round(Math.pow(10, +$('rate').value)),
      writeRatio: +$('wr').value / 100, pageSize: +$('pageSize').value, memBytes: +$('memBytes').value,
      cacheBytes: +$('cacheBytes').value, dataset: +$('dataset').value, valueBytes: +$('valueBytes').value, seed: +$('seed').value || 7,
    };
  }
  function build() {
    sim = new SK.Simulation(readConfig());
    for (const k of ['bt', 'lsm']) panels[k].setSim(sim);
    logLines.length = 0; logQueue.length = 0; hist.bt.length = hist.lsm.length = 0; ff = null; realTime = 0;
    $('log').innerHTML = '';
    for (const k in panels) panels[k].resize();
    tuneVis(); updateMetrics(); drawCharts();
  }
  function tuneVis() { if (sim) sim.visProb = Math.min(1, Math.max(0.0003, 5 / (sim.rate * speed))); }
  function readSpeed() { speed = Math.pow(10, +$('speed').value); const t = speed >= 1 ? speed.toFixed(speed >= 10 ? 0 : 1) : speed.toPrecision(2).replace(/0+$/, ''); $('speedVal').textContent = t + '×'; $('speedlabel').textContent = t + '×'; for (const k in panels) panels[k].speed = speed; tuneVis(); }
  function readLive() {
    const rate = Math.round(Math.pow(10, +$('rate').value));
    $('rateVal').textContent = fmtInt(rate) + ' ops/s'; $('wrVal').textContent = $('wr').value + '%';
    if (sim) { sim.rate = rate; sim.writeRatio = +$('wr').value / 100; sim.dist = $('dist').value; }
    tuneVis();
  }
  function markCustom() { const p = $('preset'); p.querySelector('[value=custom]').hidden = false; p.value = 'custom'; }
  function applyPreset(name) {
    const p = PRESETS[name]; if (!p) return;
    $('storage').value = p.storage; $('dist').value = p.dist; $('wr').value = p.wr; $('rate').value = Math.log10(p.rate).toFixed(3); $('speed').value = Math.log10(p.speed).toFixed(2);
    readSpeed(); readLive(); build();
  }
  let rebuildTimer = 0;
  for (const id of STRUCTURAL) $(id).addEventListener('change', () => { markCustom(); clearTimeout(rebuildTimer); rebuildTimer = setTimeout(() => { if (id === 'storage') { const ssd = $('storage').value === 'ssd'; $('rate').value = Math.log10(ssd ? 25000 : 3000).toFixed(3); $('speed').value = Math.log10(ssd ? 0.02 : 0.1).toFixed(2); readSpeed(); readLive(); } build(); }, 120); });
  $('dist').addEventListener('change', () => { markCustom(); readLive(); });
  $('rate').addEventListener('input', () => { markCustom(); readLive(); });
  $('wr').addEventListener('input', () => { markCustom(); readLive(); });
  $('speed').addEventListener('input', readSpeed);
  $('preset').addEventListener('change', e => applyPreset(e.target.value));
  $('btnReset').addEventListener('click', build);
  $('btnPlay').addEventListener('click', togglePlay);
  $('btnFF').addEventListener('click', () => { if (!ff) { ff = { target: sim.sim.now + 10e6 }; sim.visProb = 0; $('btnFF').textContent = '⏳ fast-forwarding…'; } });
  document.addEventListener('keydown', e => { if (e.code === 'Space' && !/INPUT|SELECT|TEXTAREA/.test(e.target.tagName)) { e.preventDefault(); togglePlay(); } });
  function togglePlay() { running = !running; $('btnPlay').textContent = running ? '⏸ Pause' : '▶ Play'; }
  window.addEventListener('resize', () => { for (const k in panels) panels[k].resize(); });

  /* ---------------------------------------------------------------- frame loop */
  function frame(nowMs) {
    const real = Math.min(0.05, Math.max(0, (nowMs - lastT) / 1000)); lastT = nowMs;
    if (ff) {
      sim.advance(ff.target, performance.now() + 14);
      sim.bus.length = 0;
      if (sim.sim.now >= ff.target - 1) {
        ff = null; $('btnFF').textContent = '⏩ +10 s'; tuneVis();
        for (const k in panels) { panels[k].tokens.clear(); panels[k].inspQ.length = 0; }
      }
    } else if (running) {
      realTime += real;
      const target = sim.sim.now + real * 1e6 * speed;
      slow = !sim.advance(target, performance.now() + 12);
      for (const k in panels) panels[k].consume(sim.bus);
      sim.bus.length = 0;
    }
    const dt = running && !ff ? real : 0;
    for (const k in panels) panels[k].draw(dt);
    if (nowMs - lastMetrics > 250) { lastMetrics = nowMs; updateMetrics(); drawCharts(); }
    if (nowMs - lastLogFlush > 400) { lastLogFlush = nowMs; flushLog(); }
    requestAnimationFrame(frame);
  }

  readSpeed(); build(); readLive();
  requestAnimationFrame(frame);
  window.__sim = () => sim;
  window.__panels = panels;
})();
