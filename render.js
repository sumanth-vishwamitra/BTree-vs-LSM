/*
 * Canvas renderer for one storage-engine panel. Reads live engine state each frame and layers
 * short-lived animations (tokens, particles, flashes) driven by the engine event bus.
 */
(function () {
  'use strict';
  const SK = window.SK;
  const W = 720, H = 792;

  const C = {
    mem: '#22d3ee', cpu: '#a78bfa', queue: '#fbbf24', rand: '#ff5d6c', seq: '#34d399', bg: '#f472b6',
    done: '#60a5fa', ink: '#e8edf8', mute: '#8b97b3', dim: '#1a2240', line: '#2b3760', dirty: '#fb923c',
    panel: '#0f1530', rot: '#fb923c', flush: '#2dd4bf',
  };
  const SANS = '-apple-system, "Segoe UI", Inter, Roboto, sans-serif';
  const MONO = 'ui-monospace, SFMono-Regular, Menlo, Consolas, monospace';

  const LY = {
    client: { x: 10, y: 22, w: 90, h: 58 }, queue: { x: 132, y: 22, w: 270, h: 58 },
    cpu: { x: 432, y: 22, w: 118, h: 58 }, done: { x: 600, y: 22, w: 110, h: 58 },
    mem: { x: 10, y: 108, w: 700, h: 244 }, disk: { x: 10, y: 364, w: 700, h: 420 },
    walBar: { x: 20, y: 424, w: 680, h: 11 },
    plot: { x: 20, y: 616, w: 680, h: 92 },
  };
  const BT = {
    gauge: { x: 20, y: 130, w: 450, h: 12 },
    root: { x: 225, y: 160, w: 40, h: 20 },
    inner: { x: 20, y: 200, w: 450, h: 20 },
    leaf: { x: 20, y: 246, w: 450, h: 18 },
    walBuf: { x: 490, y: 134, w: 210, h: 44 },
    insp: { x: 490, y: 184, w: 210, h: 164 },
    map: { x: 20, y: 462, w: 680, h: 16, rows: 5, cols: 120 },
  };
  const LS = {
    walBuf: { x: 20, y: 134, w: 150, h: 56 },
    mem: { x: 186, y: 134, w: 284, h: 126 },
    imm: { x: 490, y: 134, w: 210, h: 58 },
    cache: { x: 186, y: 276, w: 284, h: 62 },
    l0: { x: 20, y: 200, w: 150, h: 138 },
    bgt: { x: 490, y: 202, w: 210, h: 136 },
    lanes: { x: 62, y: 464, w: 638, h: 108 },
  };

  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
  const fmtInt = n => Math.round(n).toLocaleString('en-US');
  function fmtUs(us) {
    if (us < 1000) return us.toFixed(us < 10 ? 1 : 0) + ' µs';
    if (us < 1e6) return (us / 1000).toFixed(us < 1e4 ? 1 : 0) + ' ms';
    return (us / 1e6).toFixed(us < 1e7 ? 2 : 1) + ' s';
  }
  window.fmtUs = fmtUs; window.fmtInt = fmtInt;

  function rr(ctx, x, y, w, h, r) {
    r = Math.min(r, w / 2, h / 2);
    ctx.beginPath(); ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r); ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r); ctx.arcTo(x, y, x + w, y, r); ctx.closePath();
  }
  function box(ctx, b, o) {
    o = o || {};
    ctx.save();
    if (o.glow) { ctx.shadowColor = o.glow; ctx.shadowBlur = o.glowSize || 14; }
    rr(ctx, b.x, b.y, b.w, b.h, o.r === undefined ? 8 : o.r);
    if (o.fill) { ctx.fillStyle = o.fill; ctx.fill(); }
    ctx.shadowBlur = 0;
    if (o.stroke) { ctx.strokeStyle = o.stroke; ctx.lineWidth = o.lw || 1; if (o.dash) ctx.setLineDash(o.dash); ctx.stroke(); }
    ctx.restore();
  }
  function T(ctx, s, x, y, o) {
    o = o || {};
    ctx.font = (o.weight || '500') + ' ' + (o.size || 11) + 'px ' + (o.mono ? MONO : SANS);
    ctx.fillStyle = o.color || C.ink; ctx.textAlign = o.align || 'left'; ctx.textBaseline = o.base || 'middle';
    ctx.fillText(s, x, y);
  }
  function rgba(hex, a) {
    const n = parseInt(hex.slice(1), 16);
    return 'rgba(' + (n >> 16) + ',' + ((n >> 8) & 255) + ',' + (n & 255) + ',' + a + ')';
  }

  class Panel {
    constructor(canvas, kind, onLog) {
      this.canvas = canvas; this.ctx = canvas.getContext('2d'); this.kind = kind; this.onLog = onLog;
      this.scale = 1; this.dpr = window.devicePixelRatio || 1; this.speed = 0.1;
      this.cacheT = 0;
    }
    resize() {
      const w = this.canvas.parentElement.clientWidth;
      this.dpr = window.devicePixelRatio || 1; this.scale = w / W;
      this.canvas.style.width = w + 'px'; this.canvas.style.height = (H * this.scale) + 'px';
      this.canvas.width = Math.round(w * this.dpr); this.canvas.height = Math.round(H * this.scale * this.dpr);
    }
    setSim(sim) {
      this.sim = sim; this.eng = this.kind === 'bt' ? sim.bt : sim.lsm;
      this.act = { client: 0, queue: 0, cpu: 0, mem: 0, wal: 0, disk: 0, done: 0, walbar: 0 };
      this.tokens = new Map(); this.floats = []; this.parts = []; this.io = [];
      this.headY = 0.1; this.headTo = 0.1;
      this.fLeaf = new Float32Array(SK.BUCKETS_LEAF); this.fInner = new Float32Array(SK.BUCKETS_INT); this.fRoot = 0;
      this.fMapR = new Float32Array(600); this.fMapW = new Float32Array(600); this.mapHead = -1;
      this.fCell = new Float32Array(400); this.lastCell = 0;
      this.fFile = new Map(); this.insp = null; this.inspQ = []; this.splitFlash = 0; this.stallFlash = 0;
      this.t = 0; this.bucketT = -1; this.lastRot = 0;
      this.splitCount = 0; this.lastSplitToast = null;
    }

    /* ---------------------------------------------------------------- events */
    consume(evts) {
      const id = this.eng.id;
      for (const e of evts) {
        if (e.eng !== id) continue;
        switch (e.k) {
          case 'tok': this.onTok(e); break;
          case 'io': this.onIO(e.io); break;
          case 'modify': this.queueInsp({ type: 'modify', d: e }); break;
          case 'split': this.onSplit(e); break;
          case 'walflush': this.act.wal = 1; this.act.walbar = 1; break;
          case 'rotate': this.act.mem = 1; this.spawn(LS.mem.x + LS.mem.w / 2, LS.mem.y + LS.mem.h, LS.imm.x + 100, LS.imm.y + 50, C.mem, 12); break;
          case 'flush_start': break;
          case 'flush_done': this.fFile.set(e.id, 1); break;
          case 'comp_done': if (e.ids) for (const i of e.ids) this.fFile.set(i, 1); break;
          case 'log': this.onLog && this.onLog(this.eng.id, e); break;
        }
      }
    }
    onTok(e) {
      if (e.st === 'queue') {
        if (this.tokens.size >= 40) return;
        this.tokens.set(e.id, { id: e.id, x: LY.client.x + 45, y: LY.client.y + 29, wps: [{ st: 'queue' }], dwell: 0, op: e.op, key: e.key });
        this.act.client = 1; return;
      }
      const t = this.tokens.get(e.id);
      if (!t) return;
      t.wps.push(e);
      if (t.wps.length > 6) t.wps.splice(1, t.wps.length - 4);
    }
    onIO(io) {
      const y = this.eng.visY(io.addr);
      this.io.push({ y, kind: io.kind, tag: io.tag, seq: io.seq });
      if (this.io.length > 100) this.io.shift();
      this.headTo = y; this.act.disk = 1;
      if (io.tag === 'wal') this.act.walbar = 1;
      if (this.kind === 'bt') {
        const c = this.mapCell(io.addr);
        if (io.kind === 'r') this.fMapR[c] = 1; else this.fMapW[c] = 1;
        this.mapHead = c;
      }
    }
    mapCell(addr) {
      const n = BT.map.rows * BT.map.cols;
      return clamp(Math.floor((addr - SK.DATA_BASE) / this.eng.visExtent * n), 0, n - 1);
    }
    onSplit(e) {
      this.splitFlash = 1;
      this.fRoot = e.root ? 1 : this.fRoot;
      const b = e.leaf ? this.eng.bucketLeaf(e.key) : this.eng.bucketInt(e.key);
      (e.leaf ? this.fLeaf : this.fInner)[b] = 2;
      this.queueInsp({ type: 'split', d: e });
      this.onLog && this.onLog(this.eng.id, { cls: 'split', text: (e.root ? 'Root split → tree grows one level. ' : '') + (e.leaf ? 'Leaf' : 'Inner') + ' page #' + e.oldId + ' full → split into #' + e.oldId + ' + #' + e.newId + ' (' + e.leftN + '/' + e.rightN + ' keys). New page placed at end of file; parent updated.' });
    }
    queueInsp(x) {
      if (x.type === 'modify' && this.inspQ.length > 3) return;
      if (this.inspQ.length > 8) this.inspQ.shift();
      this.inspQ.push(x);
    }
    spawn(x0, y0, x1, y1, color, n, dur) {
      for (let i = 0; i < n && this.parts.length < 160; i++)
        this.parts.push({ x0: x0 + (Math.random() - 0.5) * 16, y0: y0 + (Math.random() - 0.5) * 8, x1: x1 + (Math.random() - 0.5) * 16, y1: y1 + (Math.random() - 0.5) * 8, t0: -Math.random() * 0.35, dur: dur || 0.7, color, r: 2 + Math.random() * 1.6 });
    }

    /* ------------------------------------------------------------ waypoints */
    cellCenter(grid, i, cols) {
      return { x: grid.x + (i % cols + 0.5) * grid.cw, y: grid.y + (Math.floor(i / cols) + 0.5) * grid.ch };
    }
    resolve(wp, t) {
      const e = this.eng;
      switch (wp.st) {
        case 'queue': {
          const idx = clamp(wp.id !== undefined ? 0 : t.id - e.qHeadId(), 0, 38);
          return { x: LY.queue.x + LY.queue.w - 12 - idx * 6.6, y: LY.queue.y + 36 + ((t.id * 7) % 5 - 2) * 2.5, c: C.queue };
        }
        case 'cpu': return { x: LY.cpu.x + LY.cpu.w / 2, y: LY.cpu.y + 47, c: C.cpu };
        case 'mem':
          if (this.kind === 'bt') {
            if (wp.lv === 0) return { x: BT.root.x + BT.root.w / 2, y: BT.root.y + 10, c: C.mem };
            if (wp.leaf) { const b = wp.bucket, cw = BT.leaf.w / 32; return { x: BT.leaf.x + (b % 32 + 0.5) * cw, y: BT.leaf.y + (b >> 5) * 22 + 9, c: C.mem }; }
            return { x: BT.inner.x + (wp.bucket + 0.5) * BT.inner.w / SK.BUCKETS_INT, y: BT.inner.y + 10, c: C.mem };
          } else {
            const cells = 28 * 7, i = Math.floor(clamp(wp.fill || 0, 0, 0.999) * cells);
            return { x: LS.mem.x + 12 + (i % 28 + 0.5) * 9.4, y: LS.mem.y + 30 + (Math.floor(i / 28) + 0.5) * 14, c: C.mem };
          }
        case 'disk':
          if (this.kind === 'bt') {
            const c = this.mapCell(wp.addr), m = BT.map, cw = m.w / m.cols;
            return { x: m.x + (c % m.cols + 0.5) * cw, y: m.y + Math.floor(c / m.cols) * (m.h + 2) + m.h / 2, c: C.rand };
          } else {
            const row = this.laneRow(wp.level || 0);
            return { x: LS.lanes.x + LS.lanes.w * 0.5, y: row.y + row.h / 2, c: C.rand };
          }
        case 'wal': { const wb = this.kind === 'bt' ? BT.walBuf : LS.walBuf; return { x: wb.x + wb.w / 2 + ((t.id * 13) % 9 - 4) * (wb.w / 14), y: wb.y + (this.kind === 'bt' ? 27 : 28), c: C.mem }; }
        case 'walsync': return { x: LY.walBar.x + 20 + (wp.off || 0) * 40, y: LY.walBar.y + 5, c: C.seq };
        case 'done': return { x: LY.done.x + LY.done.w / 2, y: LY.done.y + 38, c: C.done };
      }
      return { x: 0, y: 0, c: C.ink };
    }
    laneRow(L) {
      const rows = this.laneRows(), r = Math.min(L, rows - 1), h = LS.lanes.h / rows;
      return { y: LS.lanes.y + r * h, h: h - 3 };
    }
    laneRows() { return clamp(this.eng.maxLevelUsed() + 1, 4, 6); }

    /* ----------------------------------------------------------------- frame */
    draw(dt) {
      const ctx = this.ctx, e = this.eng;
      ctx.setTransform(this.dpr * this.scale, 0, 0, this.dpr * this.scale, 0, 0);
      ctx.clearRect(0, 0, W, H);
      this.t += dt;
      for (const k in this.act) this.act[k] = Math.max(0, this.act[k] - dt * 2.6);
      this.splitFlash = Math.max(0, this.splitFlash - dt * 1.2);
      this.fRoot = Math.max(0, this.fRoot - dt * 1.2);
      for (let i = 0; i < this.fLeaf.length; i++) this.fLeaf[i] = Math.max(0, this.fLeaf[i] - dt * 1.4);
      for (let i = 0; i < this.fInner.length; i++) this.fInner[i] = Math.max(0, this.fInner[i] - dt * 1.4);
      for (let i = 0; i < 600; i++) { if (this.fMapR[i] > 0) this.fMapR[i] = Math.max(0, this.fMapR[i] - dt * 0.9); if (this.fMapW[i] > 0) this.fMapW[i] = Math.max(0, this.fMapW[i] - dt * 0.9); }
      for (const [k, v] of this.fFile) { if (v - dt * 0.6 <= 0) this.fFile.delete(k); else this.fFile.set(k, v - dt * 0.6); }
      this.headY += (this.headTo - this.headY) * (1 - Math.exp(-dt * 7));

      this.drawFlow(ctx, e);
      if (this.kind === 'bt') this.drawBTMemory(ctx, e, dt); else this.drawLSMMemory(ctx, e);
      this.drawDisk(ctx, e);
      if (this.kind === 'bt') this.drawBTDiskMap(ctx, e); else this.drawLSMLanes(ctx, e, dt);
      this.drawPlot(ctx, e);
      this.drawBreakdown(ctx, e);
      this.drawParts(ctx, dt);
      this.drawTokens(ctx, dt);
    }

    /* ---------------------------------------------------------- request flow */
    drawFlow(ctx, e) {
      const a = this.act, sim = this.sim, depth = e.qLen();
      // arrows
      ctx.strokeStyle = C.line; ctx.lineWidth = 2; ctx.fillStyle = C.line;
      for (const [x0, x1] of [[100, 132], [402, 432], [550, 600]]) {
        ctx.beginPath(); ctx.moveTo(x0 + 2, 51); ctx.lineTo(x1 - 6, 51); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(x1 - 2, 51); ctx.lineTo(x1 - 8, 47); ctx.lineTo(x1 - 8, 55); ctx.fill();
      }
      box(ctx, LY.client, { fill: '#121a38', stroke: rgba(C.queue, 0.35 + a.client * 0.6), glow: a.client > 0.1 ? C.queue : null });
      T(ctx, 'CLIENTS', 55, 38, { size: 10, weight: '700', color: C.mute, align: 'center' });
      T(ctx, fmtInt(e.metrics.arrived), 55, 58, { size: 13, weight: '700', align: 'center', mono: true, color: C.queue });
      T(ctx, 'arrived', 55, 71, { size: 8.5, align: 'center', color: C.mute });

      const over = depth > 300;
      box(ctx, LY.queue, { fill: '#121a38', stroke: over ? rgba(C.rand, 0.5 + 0.4 * Math.sin(this.t * 6)) : rgba(C.queue, 0.4), lw: over ? 1.6 : 1 });
      T(ctx, 'REQUEST QUEUE', LY.queue.x + 10, LY.queue.y + 11, { size: 10, weight: '700', color: C.mute });
      T(ctx, 'depth ' + fmtInt(depth), LY.queue.x + LY.queue.w - 10, LY.queue.y + 11, { size: 11, weight: '700', align: 'right', mono: true, color: over ? C.rand : C.queue });
      const n = Math.min(depth, 39);
      for (let i = 0; i < n; i++) {
        ctx.fillStyle = rgba(C.queue, 0.35 + 0.5 * (1 - i / 39));
        ctx.beginPath(); ctx.arc(LY.queue.x + LY.queue.w - 12 - i * 6.6, LY.queue.y + 36, 2.6, 0, 6.3); ctx.fill();
      }
      if (depth > 39) T(ctx, '+' + fmtInt(depth - 39) + ' waiting', LY.queue.x + 12, LY.queue.y + 46, { size: 10, color: over ? C.rand : C.mute, weight: '600' });

      const col = { idle: '#3a4670', cpu: C.cpu, mem: C.mem, disk: C.rand, stall: C.queue }[e.mode] || C.cpu;
      const busy = e.mode !== 'idle';
      box(ctx, LY.cpu, { fill: rgba(col, busy ? 0.14 : 0.05), stroke: rgba(col, busy ? 0.9 : 0.4), glow: busy ? col : null, glowSize: 10 });
      T(ctx, 'WORKER THREAD', LY.cpu.x + LY.cpu.w / 2, LY.cpu.y + 11, { size: 9.5, weight: '700', color: C.mute, align: 'center' });
      this.wrapText(ctx, e.modeText, LY.cpu.x + LY.cpu.w / 2, LY.cpu.y + 25, LY.cpu.w - 10, 9.5, busy ? col : C.mute, 2);
      if (busy && e.mode !== 'stall') {
        ctx.strokeStyle = col; ctx.lineWidth = 2; ctx.beginPath();
        ctx.arc(LY.cpu.x + 12, LY.cpu.y + 11, 4, this.t * 8, this.t * 8 + 4); ctx.stroke();
      }

      box(ctx, LY.done, { fill: '#121a38', stroke: rgba(C.done, 0.35 + a.done * 0.6), glow: a.done > 0.1 ? C.done : null });
      T(ctx, 'COMPLETED', 655, 38, { size: 10, weight: '700', color: C.mute, align: 'center' });
      T(ctx, fmtInt(e.metrics.completed), 655, 58, { size: 13, weight: '700', align: 'center', mono: true, color: C.done });
      T(ctx, 'durable ✓', 655, 71, { size: 8.5, align: 'center', color: C.mute });
      const cur = e.curReq;
      T(ctx, cur ? 'serving request #' + fmtInt(cur.id) + ' · ' + fmtInt(Math.max(0, sim.nextId - 1 - cur.id)) + ' behind' : '', 20, 98, { size: 9.5, color: C.mute, mono: true });
      if (e.stall) T(ctx, '⚠ ' + e.stall, 290, 98, { size: 10, weight: '700', color: C.queue });
    }
    wrapText(ctx, s, x, y, maxW, size, color, maxLines) {
      ctx.font = '500 ' + size + 'px ' + SANS;
      const words = s.split(' '); const lines = []; let cur = '';
      for (const w of words) {
        const t = cur ? cur + ' ' + w : w;
        if (ctx.measureText(t).width > maxW && cur) { lines.push(cur); cur = w; } else cur = t;
      }
      lines.push(cur);
      if (lines.length > maxLines) { lines.length = maxLines; lines[maxLines - 1] += '…'; }
      lines.forEach((l, i) => T(ctx, l, x, y + i * (size + 2), { size, color, align: 'center' }));
    }
    zone(ctx, b, color, title, sub) {
      box(ctx, b, { fill: rgba(color, 0.045), stroke: rgba(color, 0.4), r: 12 });
      T(ctx, title, b.x + 12, b.y + 12, { size: 10.5, weight: '800', color });
      if (sub) T(ctx, sub, b.x + b.w - 12, b.y + 12, { size: 10, color: C.mute, align: 'right' });
    }

    /* ----------------------------------------------------------- B+ tree RAM */
    drawBTMemory(ctx, e, dt) {
      const a = this.act;
      this.zone(ctx, LY.mem, C.mem, 'MEMORY · buffer pool', 'every access costs ~µs');
      if (this.t - this.bucketT > 0.18) { e.refreshBuckets(); this.bucketT = this.t; }
      const used = e.pool.size, cap = e.poolCap, dirty = e.flushList.size, g = BT.gauge;
      box(ctx, g, { fill: '#0b1126', stroke: C.line, r: 4 });
      ctx.fillStyle = rgba(C.mem, 0.55); rr(ctx, g.x, g.y, g.w * (used - dirty) / cap, g.h, 4); ctx.fill();
      ctx.fillStyle = C.dirty; rr(ctx, g.x + g.w * (used - dirty) / cap, g.y, Math.max(0, g.w * dirty / cap), g.h, 3); ctx.fill();
      const hit = e.stats.hits + e.stats.misses ? e.stats.hits / (e.stats.hits + e.stats.misses) * 100 : 0;
      T(ctx, fmtInt(used) + ' / ' + fmtInt(cap) + ' pages cached · ' + fmtInt(dirty) + ' dirty · ' + hit.toFixed(0) + '% hit', g.x + 2, g.y + 24, { size: 9.5, color: C.mute, mono: true });

      // tree
      const t = e.tree, root = BT.root, inn = BT.inner, lf = BT.leaf, ci = inn.w / SK.BUCKETS_INT, cl = lf.w / 32;
      ctx.strokeStyle = rgba(C.mem, 0.14); ctx.lineWidth = 1;
      for (let i = 0; i < SK.BUCKETS_INT; i++) {
        ctx.beginPath(); ctx.moveTo(root.x + 20, root.y + 20); ctx.lineTo(inn.x + (i + 0.5) * ci, inn.y); ctx.stroke();
        const b0 = Math.floor(i * SK.BUCKETS_LEAF / SK.BUCKETS_INT), b1 = Math.floor((i + 1) * SK.BUCKETS_LEAF / SK.BUCKETS_INT) - 1;
        for (const b of [b0, b1]) { ctx.beginPath(); ctx.moveTo(inn.x + (i + 0.5) * ci, inn.y + inn.h); ctx.lineTo(lf.x + (b % 32 + 0.5) * cl, lf.y + (b >> 5) * 22); ctx.stroke(); }
      }
      const cell = (x, y, w, h, tot, cache, dr, flash) => {
        if (!tot) { box(ctx, { x, y, w, h }, { stroke: rgba(C.line, 0.6), r: 2 }); return; }
        const cf = cache / tot, df = dr / tot;
        ctx.fillStyle = rgba(C.mem, 0.08 + 0.62 * cf); rr(ctx, x, y, w, h, 2); ctx.fill();
        if (df > 0) { ctx.fillStyle = rgba(C.dirty, 0.25 + 0.7 * Math.min(1, df * 3)); rr(ctx, x, y + h * (1 - Math.min(1, df * 2)), w, h * Math.min(1, df * 2), 2); ctx.fill(); }
        ctx.strokeStyle = rgba(C.mem, 0.25 + 0.4 * cf); ctx.lineWidth = 0.8; rr(ctx, x, y, w, h, 2); ctx.stroke();
        if (flash > 0) { ctx.save(); ctx.shadowColor = flash > 1 ? '#facc15' : '#ffffff'; ctx.shadowBlur = 10; ctx.strokeStyle = flash > 1 ? '#facc15' : '#ffffff'; ctx.lineWidth = 1.6; rr(ctx, x - 1, y - 1, w + 2, h + 2, 3); ctx.stroke(); ctx.restore(); }
      };
      cell(root.x, root.y, root.w, root.h, 1, 1, 0, this.fRoot * 2);
      T(ctx, 'root', root.x + 20, root.y + 10, { size: 9, weight: '700', color: '#06222a', align: 'center' });
      const hasInner = t.height > 2;
      for (let i = 0; i < SK.BUCKETS_INT; i++) cell(inn.x + i * ci + 1, inn.y, ci - 2, inn.h, hasInner ? e.bI.tot[i] : 0, e.bI.cache[i], e.bI.dirty[i], this.fInner[i]);
      for (let b = 0; b < SK.BUCKETS_LEAF; b++) cell(lf.x + (b % 32) * cl + 1, lf.y + (b >> 5) * 22, cl - 2, lf.h, e.bL.tot[b], e.bL.cache[b], e.bL.dirty[b], this.fLeaf[b]);
      T(ctx, 'Root', 20, root.y + 10, { size: 9, color: C.mute });
      T(ctx, 'Inner pages' + (hasInner ? '' : ' (none yet)'), 20, inn.y - 8, { size: 9, color: C.mute });
      T(ctx, 'Leaf pages — key range grouped into 64 cells, left → right', 20, lf.y - 8, { size: 9, color: C.mute });
      T(ctx, 'height ' + t.height + ' · ' + fmtInt(t.leaves) + ' leaf pages · ' + fmtInt(t.internals) + ' inner · ' + (e.pageSize / 1024) + ' KB pages (≈' + e.leafCap + ' keys/leaf)', 20, 318, { size: 9.5, color: C.mute, mono: true });
      // legend
      let lx = 20; const ly = 334;
      for (const [col, txt, al] of [[C.mem, 'cached', 0.6], ['#1a2240', 'on disk only', 1], [C.dirty, 'dirty (modified in RAM)', 1], ['#facc15', 'just split', 1]]) {
        ctx.fillStyle = rgba(col.length === 7 ? col : '#1a2240', al); rr(ctx, lx, ly - 4, 10, 8, 2); ctx.fill();
        T(ctx, txt, lx + 14, ly, { size: 9, color: C.mute }); lx += 22 + txt.length * 4.9;
      }

      // WAL buffer
      const wb = BT.walBuf, pend = e.wal.pending.length;
      box(ctx, wb, { fill: rgba(C.mem, 0.08 + a.wal * 0.2), stroke: rgba(C.mem, 0.5 + a.wal * 0.5), glow: a.wal > 0.2 ? C.mem : null, glowSize: 8 });
      T(ctx, 'WAL BUFFER (RAM)', wb.x + 8, wb.y + 11, { size: 9.5, weight: '700', color: C.mem });
      ctx.fillStyle = '#0b1126'; rr(ctx, wb.x + 8, wb.y + 22, wb.w - 16, 8, 3); ctx.fill();
      ctx.fillStyle = C.mem; rr(ctx, wb.x + 8, wb.y + 22, (wb.w - 16) * clamp(pend / 48, 0, 1), 8, 3); ctx.fill();
      T(ctx, pend + ' rec', wb.x + wb.w - 8, wb.y + 11, { size: 9, color: C.mute, align: 'right', mono: true });
      T(ctx, e.wal.flushing ? 'fsync in flight → disk' : 'waiting for next group commit', wb.x + 8, wb.y + 37, { size: 8.5, color: e.wal.flushing ? C.seq : C.mute });
      this.drawInspector(ctx, e, dt);
    }
    drawInspector(ctx, e, dt) {
      const b = BT.insp, now = this.t;
      box(ctx, b, { fill: '#0b1126', stroke: rgba(C.mem, 0.35), r: 8 });
      T(ctx, 'PAGE INSPECTOR', b.x + 10, b.y + 12, { size: 9.5, weight: '800', color: C.mem });
      if (!this.insp || now - this.insp.t0 > this.insp.dur) {
        const nx = this.inspQ.shift();
        if (nx) this.insp = { type: nx.type, d: nx.d, t0: now, dur: nx.type === 'split' ? 2.2 : 0.9 };
      } else if (this.inspQ.length > 4 && this.insp.type === 'modify') this.insp.dur = 0;
      const s = this.insp;
      if (!s) { T(ctx, 'waiting for a sampled write…', b.x + b.w / 2, b.y + 80, { size: 10, color: C.mute, align: 'center' }); return; }
      const d = s.d, el = now - s.t0;
      const grid = (x, y, w, h, cap, fill, hl, col) => {
        const cols = clamp(Math.round(Math.sqrt(cap * w / h)), 1, cap), rows = Math.ceil(cap / cols), cw = w / cols, ch = Math.min(h / rows, cw * 1.3);
        for (let i = 0; i < cap; i++) {
          const cx = x + (i % cols) * cw, cy = y + Math.floor(i / cols) * ch;
          ctx.fillStyle = i < fill ? rgba(col, 0.75) : 'rgba(40,52,95,0.7)';
          if (i === hl) { ctx.fillStyle = '#ffffff'; }
          ctx.fillRect(cx + 0.6, cy + 0.6, cw - 1.2, ch - 1.2);
        }
      };
      if (s.type === 'modify') {
        T(ctx, 'leaf #' + d.id + ' · slot ' + (d.isNew ? 'insert' : 'overwrite'), b.x + 10, b.y + 28, { size: 9.5, color: C.ink, mono: true });
        const fillShown = d.isNew ? (el < 0.3 ? d.count - 1 : d.count) : d.count;
        grid(b.x + 10, b.y + 38, b.w - 20, 56, d.cap, fillShown, el < 0.6 ? d.slot : -1, C.mem);
        T(ctx, d.count + ' / ' + d.cap + ' entries', b.x + 10, b.y + 108, { size: 10, weight: '700', mono: true });
        T(ctx, 'page now DIRTY in RAM', b.x + 10, b.y + 123, { size: 9.5, color: C.dirty, weight: '700' });
        T(ctx, 'later: whole ' + (e.pageSize / 1024) + ' KB page → random write', b.x + 10, b.y + 137, { size: 9, color: C.mute });
        T(ctx, 'disk addr ' + (d.addr / 1048576).toFixed(1) + ' MB', b.x + 10, b.y + 151, { size: 9, color: C.mute, mono: true });
      } else {
        const shake = el < 0.6 ? Math.sin(el * 60) * 2 : 0;
        T(ctx, (d.root ? 'ROOT SPLIT' : (d.leaf ? 'LEAF SPLIT' : 'INNER SPLIT')) + ' #' + d.oldId, b.x + 10, b.y + 28, { size: 10, weight: '800', color: '#facc15' });
        if (el < 0.7) grid(b.x + 10 + shake + 40, b.y + 40, 110, 50, d.cap, d.cap, -1, C.rand);
        else {
          const k = clamp((el - 0.7) / 0.5, 0, 1), off = 36 * k;
          grid(b.x + 12 - 0 + 40 - off, b.y + 40, 52, 50, d.cap, d.leftN, -1, C.mem);
          grid(b.x + 12 + 40 + 58 + off - 36 + 36 * 0, b.y + 40, 52, 50, d.cap, d.rightN, -1, '#facc15');
          T(ctx, '#' + d.oldId, b.x + 50 - off + 26, b.y + 98, { size: 9, align: 'center', color: C.mute, mono: true });
          T(ctx, '#' + d.newId, b.x + 110 + 26 + off - 36 + 36, b.y + 98, { size: 9, align: 'center', color: '#facc15', mono: true });
        }
        T(ctx, d.leftN + ' + ' + d.rightN + ' entries · separator key ' + d.key, b.x + 10, b.y + 115, { size: 9.5, mono: true });
        T(ctx, 'new page appended at end of file', b.x + 10, b.y + 130, { size: 9, color: C.mute });
        T(ctx, 'old + new + parent → 3 dirty pages', b.x + 10, b.y + 144, { size: 9, color: C.dirty });
        T(ctx, 'split also logged in WAL (~' + (e.pageSize / 2048).toFixed(0) + ' KB)', b.x + 10, b.y + 158, { size: 9, color: C.mute });
      }
    }

    /* ------------------------------------------------------------- LSM RAM */
    drawLSMMemory(ctx, e) {
      const a = this.act;
      this.zone(ctx, LY.mem, C.mem, 'MEMORY · MemTable', 'every access costs ~µs');
      const wb = LS.walBuf, pend = e.wal.pending.length;
      box(ctx, wb, { fill: rgba(C.mem, 0.08 + a.wal * 0.2), stroke: rgba(C.mem, 0.5 + a.wal * 0.5), glow: a.wal > 0.2 ? C.mem : null, glowSize: 8 });
      T(ctx, 'WAL BUFFER (RAM)', wb.x + 8, wb.y + 12, { size: 9.5, weight: '700', color: C.mem });
      ctx.fillStyle = '#0b1126'; rr(ctx, wb.x + 8, wb.y + 24, wb.w - 16, 8, 3); ctx.fill();
      ctx.fillStyle = C.mem; rr(ctx, wb.x + 8, wb.y + 24, (wb.w - 16) * clamp(pend / 48, 0, 1), 8, 3); ctx.fill();
      T(ctx, pend + ' records buffered', wb.x + 8, wb.y + 41, { size: 9, color: C.mute, mono: true });
      T(ctx, e.wal.flushing ? 'fsync →' : '', wb.x + wb.w - 8, wb.y + 41, { size: 9, color: C.seq, align: 'right' });

      const m = LS.mem, fill = clamp(e.mem.bytes / e.memBytes, 0, 1);
      box(ctx, m, { fill: '#0b1126', stroke: rgba(C.mem, 0.45 + a.mem * 0.5), glow: a.mem > 0.2 ? C.mem : null, glowSize: 8 });
      T(ctx, 'MEMTABLE', m.x + 12, m.y + 13, { size: 9.5, weight: '700', color: C.mem });
      T(ctx, fmtInt(e.mem.set.size) + ' keys · ' + (fill * 100).toFixed(0) + '% of ' + SK.fmtBytes(e.memBytes), m.x + m.w - 12, m.y + 13, { size: 9.5, color: C.mute, align: 'right', mono: true });
      const cols = 28, rows = 7, cells = cols * rows, lit = Math.floor(fill * cells);
      for (let i = 0; i < cells; i++) {
        const cx = m.x + 12 + (i % cols) * 9.4, cy = m.y + 26 + Math.floor(i / cols) * 14;
        ctx.fillStyle = i < lit ? rgba(C.mem, 0.35 + 0.55 * (i / cells)) : 'rgba(40,52,95,0.55)';
        ctx.fillRect(cx, cy, 8.2, 12);
      }
      T(ctx, 'inserts: O(log n) in RAM — no disk I/O, ordered by key', m.x + 12, m.y + m.h - 8, { size: 9, color: C.mute });

      const im = LS.imm, imm = e.imm, fl = e.flushing;
      box(ctx, im, { fill: imm ? rgba(C.bg, 0.07) : '#0b1126', stroke: imm ? rgba(C.bg, 0.8) : C.line, glow: imm ? C.bg : null, glowSize: 8 });
      T(ctx, 'IMMUTABLE MEMTABLE', im.x + 10, im.y + 12, { size: 9.5, weight: '700', color: imm ? C.bg : C.mute });
      if (imm) {
        const p = fl ? fl.written / fl.bytes : 0;
        for (let i = 0; i < 30; i++) { ctx.fillStyle = i / 30 < 1 - p ? rgba(C.mem, 0.7) : 'rgba(40,52,95,0.55)'; ctx.fillRect(im.x + 10 + i * 6.3, im.y + 24, 5.2, 10); }
        T(ctx, 'flushing → L0 SSTable (sequential)', im.x + 10, im.y + 46, { size: 9, color: C.bg });
      } else T(ctx, 'empty — ready for next rotation', im.x + 10, im.y + 36, { size: 9, color: C.mute });

      const l = LS.l0, l0 = e.levels[0].length;
      box(ctx, l, { fill: '#0b1126', stroke: C.line });
      T(ctx, 'L0 PRESSURE', l.x + 10, l.y + 12, { size: 9.5, weight: '700', color: C.mute });
      for (let i = 0; i < 12; i++) {
        const col = i < 4 ? C.seq : i < 8 ? C.queue : C.rand, y = l.y + l.h - 14 - i * 9.4;
        ctx.fillStyle = i < l0 ? col : 'rgba(40,52,95,0.55)'; ctx.fillRect(l.x + 12, y, 38, 7.6);
      }
      T(ctx, l0 + ' L0 files', l.x + 60, l.y + 36, { size: 10, weight: '700', mono: true });
      T(ctx, '≥4 compact', l.x + 60, l.y + 62, { size: 9, color: C.seq }); T(ctx, '≥8 slow writes', l.x + 60, l.y + 80, { size: 9, color: C.queue }); T(ctx, '≥12 stop writes', l.x + 60, l.y + 98, { size: 9, color: C.rand });

      const c = LS.cache, hit = e.stats.hits + e.stats.misses ? e.stats.hits / (e.stats.hits + e.stats.misses) * 100 : 0;
      box(ctx, c, { fill: '#0b1126', stroke: C.line });
      T(ctx, 'BLOCK CACHE (reads)', c.x + 10, c.y + 12, { size: 9.5, weight: '700', color: C.mem });
      ctx.fillStyle = '#121a38'; rr(ctx, c.x + 10, c.y + 24, c.w - 20, 9, 3); ctx.fill();
      ctx.fillStyle = rgba(C.mem, 0.6); rr(ctx, c.x + 10, c.y + 24, (c.w - 20) * clamp(e.cache.size / e.cacheCap, 0, 1), 9, 3); ctx.fill();
      T(ctx, fmtInt(e.cache.size) + ' / ' + fmtInt(e.cacheCap) + ' blocks · ' + (e.metrics.reads ? hit.toFixed(0) + '% hit' : 'no reads in workload'), c.x + 10, c.y + 46, { size: 9, color: C.mute, mono: true });

      const g = LS.bgt;
      box(ctx, g, { fill: '#0b1126', stroke: C.line });
      T(ctx, 'BACKGROUND THREADS', g.x + 10, g.y + 12, { size: 9.5, weight: '700', color: C.bg });
      const bar = (y, label, p, active, col) => {
        T(ctx, label, g.x + 10, y, { size: 9, color: active ? col : C.mute, weight: '600' });
        ctx.fillStyle = '#121a38'; rr(ctx, g.x + 10, y + 8, g.w - 20, 8, 3); ctx.fill();
        if (active) { ctx.fillStyle = col; rr(ctx, g.x + 10, y + 8, Math.max(4, (g.w - 20) * p), 8, 3); ctx.fill(); }
      };
      bar(g.y + 30, e.flushing ? 'Flush · MemTable → L0 ' + (100 * e.flushing.written / e.flushing.bytes).toFixed(0) + '%' : 'Flush thread · idle', e.flushing ? e.flushing.written / e.flushing.bytes : 0, !!e.flushing, C.seq);
      const cp = e.comp;
      let lab = 'Compaction thread · idle', p = 0;
      if (cp) {
        lab = 'Compact L' + cp.level + '→L' + cp.to + ' · ' + { read: 'reading', merge: 'merging', write: 'writing' }[cp.phase];
        p = cp.phase === 'read' ? cp.p * 0.45 : cp.phase === 'merge' ? 0.45 + cp.p * 0.1 : 0.55 + cp.p * 0.45;
      }
      bar(g.y + 66, lab, p, !!cp, C.bg);
      T(ctx, cp ? SK.fmtBytes(cp.bytesIn) + ' input · all I/O is sequential runs' : 'wakes when a level exceeds its size limit', g.x + 10, g.y + 104, { size: 9, color: C.mute });
      T(ctx, 'completed: ' + e.stats.flushes + ' flushes · ' + e.stats.compactions + ' compactions', g.x + 10, g.y + 124, { size: 9, color: C.mute, mono: true });
    }

    /* ------------------------------------------------------------------ disk */
    drawDisk(ctx, e) {
      const a = this.act, d = e.disk, cur = d.cur, st = SK.STORAGE[e.cfg.storage];
      this.zone(ctx, LY.disk, C.rand, 'DISK · ' + st.label, st.kind === 'hdd' ? 'random seek ≈ 5-10 ms' : 'random 4K ≈ 0.1 ms');
      let txt = 'idle', col = C.mute;
      if (cur) {
        const now = this.sim.sim.now, inPos = now - cur.start < cur.pos;
        const kind = (cur.kind === 'r' ? 'READ ' : 'WRITE ') + (cur.bytes >= 1048576 ? (cur.bytes / 1048576).toFixed(1) + ' MB' : (cur.bytes / 1024).toFixed(cur.bytes < 10240 ? 1 : 0) + ' KB');
        const how = cur.seq ? 'sequential' : 'RANDOM';
        txt = kind + ' · ' + how + ' · ' + cur.tag + ' · ' + (inPos ? (st.kind === 'hdd' ? (cur.seq ? 'waiting for platter rotation…' : 'seek + rotate…') : 'flash access…') : 'transferring') + ' (' + fmtUs(cur.pos) + ' + ' + fmtUs(cur.xfer) + ')';
        col = cur.seq ? C.seq : C.rand;
      }
      T(ctx, txt, 20, 396, { size: 10, weight: '700', color: col, mono: true });
      T(ctx, 'queued I/Os: ' + Math.max(0, d.pending() - (cur ? 1 : 0)), 700, 408, { size: 9.5, color: C.mute, align: 'right', mono: true });
      // WAL bar
      const w = LY.walBar, wal = e.wal;
      box(ctx, w, { fill: '#0b1126', stroke: rgba(C.seq, 0.4 + a.walbar * 0.6), r: 3, glow: a.walbar > 0.3 ? C.seq : null, glowSize: 8 });
      const fillW = Math.max(3, w.w * (wal.off / SK.WAL_SIZE));
      ctx.fillStyle = rgba(C.seq, 0.55 + a.walbar * 0.4); rr(ctx, w.x, w.y, Math.min(w.w, fillW + 14), w.h, 3); ctx.fill();
      T(ctx, 'WAL — append-only log, always sequential (' + fmtInt(wal.syncs) + ' group fsyncs · avg batch ' + (wal.syncs ? (wal.appends / wal.syncs).toFixed(1) : '–') + ' records)', w.x, w.y - 5, { size: 9, color: C.seq, weight: '600' });
    }
    drawBTDiskMap(ctx, e) {
      const m = BT.map, cw = m.w / m.cols, n = m.rows * m.cols;
      const used = Math.ceil(e.tree.nodes.length * e.pageSize / e.visExtent * n);
      T(ctx, 'B+ Tree data file — each cell = a slice of the page file (original pages, then split pages appended at the end)', m.x, m.y - 8, { size: 9, color: C.mute });
      for (let i = 0; i < n; i++) {
        const x = m.x + (i % m.cols) * cw, y = m.y + Math.floor(i / m.cols) * (m.h + 2);
        ctx.fillStyle = i < used ? '#27345f' : '#141c3a';
        ctx.fillRect(x + 0.5, y, cw - 1, m.h);
        const r = this.fMapR[i], w = this.fMapW[i];
        if (r > 0) { ctx.fillStyle = rgba('#ff9f5b', r); ctx.fillRect(x + 0.5, y, cw - 1, m.h); }
        if (w > 0) { ctx.fillStyle = rgba(C.rand, Math.min(1, w * 1.2)); ctx.fillRect(x + 0.5, y, cw - 1, m.h); }
      }
      if (this.mapHead >= 0) {
        const i = this.mapHead, x = m.x + (i % m.cols) * cw, y = m.y + Math.floor(i / m.cols) * (m.h + 2);
        ctx.save(); ctx.strokeStyle = '#fff'; ctx.shadowColor = '#fff'; ctx.shadowBlur = 8; ctx.lineWidth = 1.5; ctx.strokeRect(x - 1, y - 1, cw + 1, m.h + 2); ctx.restore();
      }
      const ly = m.y + m.rows * (m.h + 2) + 8;
      let lx = m.x;
      for (const [col, txt] of [['#ff9f5b', 'random page READ (cache miss)'], [C.rand, 'random page WRITE (eviction / cleaner)'], ['#ffffff', 'head position']]) {
        ctx.fillStyle = col; ctx.fillRect(lx, ly - 4, 9, 8); T(ctx, txt, lx + 13, ly, { size: 9, color: C.mute }); lx += 30 + txt.length * 4.7;
      }
    }
    drawLSMLanes(ctx, e, dt) {
      const L = LS.lanes, rows = this.laneRows(), rowH = L.h / rows, cp = e.comp, fl = e.flushing;
      T(ctx, 'SSTables by level — immutable sorted files, written once in one sequential stream', L.x - 42, L.y - 10, { size: 9, color: C.mute });
      const inSet = new Set(cp ? cp.in0.concat(cp.in1) : []);
      const laneCap = lv => lv === 0 ? e.l0Stop * e.F : Math.max(e.maxBytes(lv), e.levelBytes[lv] * 1.05, e.F);
      for (let lv = 0; lv < rows; lv++) {
        const y = L.y + lv * rowH, h = rowH - 3, cap = laneCap(lv), files = e.levels[lv];
        T(ctx, 'L' + lv, L.x - 8, y + h / 2, { size: 10, weight: '800', color: C.mute, align: 'right' });
        box(ctx, { x: L.x, y, w: L.w, h }, { fill: '#0b1126', stroke: lv === 0 ? rgba(C.seq, 0.3) : C.line, r: 4 });
        let x = L.x;
        for (const f of files) {
          const fw = Math.max(1.5, f.bytes / cap * L.w);
          if (lv === 0) { /* overlapping files drawn side by side in arrival order */ }
          const fx = x; x += fw;
          const fl2 = this.fFile.get(f.id) || 0, busy = inSet.has(f.id);
          ctx.fillStyle = busy ? rgba(C.bg, 0.55 + 0.3 * Math.sin(this.t * 8)) : lv === 0 ? rgba(C.seq, 0.7) : rgba('#6366f1', 0.45 + 0.1 * lv);
          ctx.fillRect(fx + 0.4, y + 1.5, Math.max(0.8, fw - 0.8), h - 3);
          if (fl2 > 0) { ctx.fillStyle = rgba('#ffffff', fl2 * 0.8); ctx.fillRect(fx + 0.4, y + 1.5, Math.max(0.8, fw - 0.8), h - 3); }
        }
        // ghost for the file being flushed / compaction output being written
        if (lv === 0 && fl) {
          const gw = Math.max(2, fl.bytes / cap * L.w * (fl.written / fl.bytes));
          ctx.fillStyle = rgba(C.seq, 0.9); ctx.fillRect(x + 0.4, y + 1.5, gw, h - 3);
          ctx.strokeStyle = C.seq; ctx.strokeRect(x + 0.4, y + 1.5, Math.max(4, fl.bytes / cap * L.w), h - 3);
        }
        if (cp && cp.to === lv && cp.phase === 'write') {
          let ox = x;
          for (const o of cp.out) {
            const ow = Math.max(1.5, o.bytes / cap * L.w);
            ctx.fillStyle = rgba(C.bg, 0.85); ctx.fillRect(ox + 0.4, y + 1.5, Math.max(0.8, ow * (o.written / o.bytes)), h - 3);
            ox += ow;
          }
        }
        const tot = e.levelBytes[lv];
        T(ctx, files.length + ' files · ' + SK.fmtBytes(tot) + (lv === 0 ? '' : ' / ' + SK.fmtBytes(e.maxBytes(lv))), L.x + L.w - 6, y + h / 2, { size: 8.5, color: 'rgba(232,237,248,0.75)', align: 'right', mono: true });
      }
      // flow particles while background work is running
      if (fl && Math.random() < dt * 22) { const r = this.laneRow(0); this.spawn(LS.imm.x + 100, LS.imm.y + 58, L.x + 80, r.y + r.h / 2, C.seq, 1, 0.9); }
      if (cp && Math.random() < dt * 24) {
        const a = this.laneRow(cp.level), b = this.laneRow(cp.to);
        if (cp.phase === 'write') this.spawn(L.x + L.w * 0.55, (a.y + b.y) / 2 + 8, L.x + L.w * 0.35 + Math.random() * 200, b.y + b.h / 2, C.bg, 1, 0.6);
        else this.spawn(L.x + Math.random() * L.w, (cp.phase === 'read' ? a.y : b.y) + 6, L.x + L.w * 0.5, (a.y + b.y) / 2, C.bg, 1, 0.6);
      }
      const ly = L.y + L.h + 14; let lx = L.x - 42;
      for (const [col, txt] of [[C.seq, 'flushed L0 file'], ['#6366f1', 'sorted run (L1+)'], [C.bg, 'compaction in progress'], ['#ffffff', 'new']]) {
        ctx.fillStyle = col; ctx.fillRect(lx, ly - 4, 9, 8); T(ctx, txt, lx + 13, ly, { size: 9, color: C.mute }); lx += 30 + txt.length * 4.8;
      }
    }

    /* ---------------------------------------------- access pattern + breakdown */
    drawPlot(ctx, e) {
      const p = LY.plot, io = this.io, st = this.sim.cfg.storage;
      T(ctx, 'DISK ACCESS PATTERN — last 100 I/Os (y = disk address, line = head movement)', p.x, p.y - 12, { size: 9.5, weight: '700', color: C.ink });
      box(ctx, p, { fill: '#0b1126', stroke: C.line, r: 6 });
      ctx.save(); rr(ctx, p.x, p.y, p.w, p.h, 6); ctx.clip();
      ctx.strokeStyle = 'rgba(80,100,170,0.15)'; ctx.lineWidth = 1;
      const yOf = v => p.y + p.h - 6 - v * (p.h - 12);
      for (const v of [0.16, 0.57, 0.98]) { ctx.beginPath(); ctx.moveTo(p.x, yOf(v)); ctx.lineTo(p.x + p.w, yOf(v)); ctx.stroke(); }
      T(ctx, 'WAL region', p.x + 6, yOf(0.055) - 6, { size: 8.5, color: rgba(C.seq, 0.7) });
      T(ctx, 'data region ↑', p.x + 6, yOf(0.5), { size: 8.5, color: C.mute });
      const dx = (p.w - 40) / 99, xs = i => p.x + 14 + i * dx;
      for (let i = 1; i < io.length; i++) {
        const a = io[i - 1], b = io[i], jump = Math.abs(b.y - a.y);
        ctx.strokeStyle = b.seq ? rgba(C.seq, 0.8) : rgba(C.rand, 0.25 + Math.min(0.55, jump * 1.2));
        ctx.lineWidth = b.seq ? 1.6 : 1 + jump * 1.6;
        ctx.beginPath(); ctx.moveTo(xs(i - 1 + 100 - io.length), yOf(a.y)); ctx.lineTo(xs(i + 100 - io.length), yOf(b.y)); ctx.stroke();
      }
      for (let i = 0; i < io.length; i++) {
        const o = io[i], x = xs(i + 100 - io.length), y = yOf(o.y);
        const tag = o.tag;
        const col = tag === 'wal' ? C.seq : tag === 'flush' ? C.flush : tag.startsWith('compact') ? C.bg : C.rand;
        ctx.beginPath(); ctx.arc(x, y, i === io.length - 1 ? 3.6 : 2.4, 0, 6.3);
        if (o.kind === 'r') { ctx.strokeStyle = col; ctx.lineWidth = 1.3; ctx.stroke(); } else { ctx.fillStyle = col; ctx.fill(); }
      }
      ctx.restore();
      // head marker
      const hy = yOf(this.headY), cur = e.disk.cur, seeking = cur && !cur.seq && this.sim.sim.now - cur.start < cur.pos;
      ctx.fillStyle = seeking ? C.rand : (cur ? C.seq : C.mute);
      ctx.beginPath(); ctx.moveTo(p.x + p.w - 3, hy); ctx.lineTo(p.x + p.w - 13, hy - 5); ctx.lineTo(p.x + p.w - 13, hy + 5); ctx.fill();
      if (seeking) T(ctx, st === 'hdd' ? 'SEEK' : 'RANDOM', p.x + p.w - 18, hy, { size: 9, weight: '800', color: C.rand, align: 'right' });
      let lx = p.x; const ly = p.y + p.h + 12;
      for (const [col, txt, hollow] of [[C.rand, 'random page I/O', false], [C.seq, 'WAL / sequential', false], [C.flush, 'SSTable flush', false], [C.bg, 'compaction', false], [C.mute, '○ read  ● write', true]]) {
        if (!hollow) { ctx.fillStyle = col; ctx.beginPath(); ctx.arc(lx + 4, ly, 3, 0, 6.3); ctx.fill(); }
        T(ctx, txt, lx + (hollow ? 0 : 11), ly, { size: 9, color: C.mute }); lx += 22 + txt.length * 4.9;
      }
    }
    drawBreakdown(ctx, e) {
      const x = 20, y = 758, w = 680, h = 12, now = Math.max(1, this.sim.sim.now), s = e.disk.s;
      const hdd = this.sim.cfg.storage === 'hdd';
      const seek = clamp(s.seekUs / now, 0, 1), rot = clamp(s.rotUs / now, 0, 1), xf = clamp(s.xferUs / now, 0, 1);
      const idle = Math.max(0, 1 - seek - rot - xf);
      T(ctx, 'WHERE DISK TIME GOES (simulated time so far)', x, y - 9, { size: 9.5, weight: '700' });
      ctx.fillStyle = '#0b1126'; rr(ctx, x, y, w, h, 4); ctx.fill();
      let cx = x;
      for (const [v, col] of [[seek, C.rand], [rot, C.rot], [xf, C.seq], [idle, '#1c2547']]) {
        ctx.fillStyle = col; ctx.fillRect(cx, y, w * v, h); cx += w * v;
      }
      const f = v => (v * 100).toFixed(0) + '%';
      let lx = x; const ly = y + 22;
      for (const [col, txt] of [[C.rand, (hdd ? 'seek ' : 'access latency ') + f(seek)], [C.rot, 'rotational wait ' + f(rot)], [C.seq, 'useful data transfer ' + f(xf)], ['#2b3760', 'idle ' + f(idle)]]) {
        ctx.fillStyle = col; ctx.fillRect(lx, ly - 4, 9, 8); T(ctx, txt, lx + 13, ly, { size: 9, color: C.mute }); lx += 30 + txt.length * 4.9;
      }
    }

    /* ----------------------------------------------------- tokens & particles */
    drawTokens(ctx, dt) {
      const dwellBase = this.speed > 1 ? 0.03 : this.speed > 0.3 ? 0.07 : 0.12;
      const k = 1 - Math.exp(-dt * 9);
      for (const [id, t] of this.tokens) {
        const wp = t.wps[0], tg = this.resolve(wp, t);
        t.x += (tg.x - t.x) * k; t.y += (tg.y - t.y) * k; t.c = tg.c;
        const near = Math.hypot(tg.x - t.x, tg.y - t.y) < 6;
        if (near) {
          if (wp.st === 'done') {
            this.floats.push({ x: LY.done.x + LY.done.w / 2, y: 94, t0: this.t, text: fmtUs(wp.lat), c: C.done });
            this.act.done = 1; this.tokens.delete(id); continue;
          }
          if (t.wps.length > 1) {
            t.dwell += dt;
            if (t.dwell >= (t.wps.length > 3 ? dwellBase * 0.25 : dwellBase)) { t.wps.shift(); t.dwell = 0; }
          }
        }
        if (wp.st === 'cpu') this.act.cpu = 1;
        ctx.save();
        ctx.shadowColor = t.c; ctx.shadowBlur = 10;
        ctx.fillStyle = t.c; ctx.beginPath(); ctx.arc(t.x, t.y, t.op === 'w' ? 5 : 5, 0, 6.3); ctx.fill();
        ctx.restore();
        ctx.strokeStyle = '#0b1126'; ctx.lineWidth = 1.5; ctx.beginPath(); ctx.arc(t.x, t.y, t.op === 'w' ? 5 : 5, 0, 6.3); ctx.stroke();
        if (t.op === 'r') { ctx.fillStyle = '#0b1126'; ctx.beginPath(); ctx.arc(t.x, t.y, 2, 0, 6.3); ctx.fill(); }
        if (!(wp.st === 'wal' || wp.st === 'walsync' || (wp.st === 'queue' && t.id - this.eng.qHeadId() >= 38))) T(ctx, '#' + t.id, t.x, t.y - 11, { size: 8.5, color: '#fff', align: 'center', mono: true, weight: '700' });
      }
      this.floats = this.floats.filter(f => this.t - f.t0 < 1.4);
      for (const f of this.floats) {
        const a = 1 - (this.t - f.t0) / 1.4;
        ctx.globalAlpha = a; T(ctx, f.text, f.x, f.y - (1 - a) * 22, { size: 10, weight: '800', color: f.c, align: 'center', mono: true }); ctx.globalAlpha = 1;
      }
    }
    drawParts(ctx, dt) {
      for (const p of this.parts) p.t0 += dt;
      this.parts = this.parts.filter(p => p.t0 < p.dur);
      for (const p of this.parts) {
        if (p.t0 < 0) continue;
        const u = p.t0 / p.dur, e = u * u * (3 - 2 * u);
        ctx.globalAlpha = Math.sin(u * Math.PI) * 0.9;
        ctx.fillStyle = p.color; ctx.beginPath(); ctx.arc(p.x0 + (p.x1 - p.x0) * e, p.y0 + (p.y1 - p.y0) * e, p.r, 0, 6.3); ctx.fill();
      }
      ctx.globalAlpha = 1;
    }
  }

  window.Panel = Panel;
  window.SKC = C;
})();
