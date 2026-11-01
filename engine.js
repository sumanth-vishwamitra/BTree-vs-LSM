/*
 * Discrete-event model of a B+ Tree storage engine and an LSM Tree storage engine
 * (LevelDB-style leveled compaction) running the same write workload on one disk each.
 *
 * Time unit: microseconds of *simulated* time. Nothing here touches the DOM; the renderer
 * only reads engine state and consumes the event bus.
 */
(function (root) {
  'use strict';

  const KB = 1024, MB = 1024 * 1024;
  const KEY_BYTES = 16;
  const WAL_BASE = 0, WAL_SIZE = 64 * MB, DATA_BASE = 128 * MB, SPAN = 1024 * MB;
  const BUCKETS_LEAF = 64, BUCKETS_INT = 24;
  const MAX_LEVELS = 7;
  const MAX_IO = 1 * MB;

  // CPU / memory costs in microseconds.
  const COST = {
    parse: 3, search: 0.5, memAccess: 0.15, leafInsert: 1.8, split: 14, walBuf: 0.6,
    memInsert: 2.6, bloom: 0.3, mergePerKey: 0.12, flushPerKey: 0.1,
  };

  // Storage profiles. HDD: positioning = seek (distance-dependent) + rotational latency.
  const STORAGE = {
    hdd: { kind: 'hdd', label: 'HDD · 7200 RPM', rot: 8333, seekMin: 700, seekVar: 8500, bw: 160e6, cmd: 150 },
    ssd: { kind: 'ssd', label: 'SATA SSD', readUs: 90, writeUs: 110, seqUs: 22, flushUs: 90, bw: 520e6 },
  };

  const DEFAULTS = {
    storage: 'hdd', rate: 3000, writeRatio: 1, dist: 'uniform', valueBytes: 100,
    pageSize: 4096, memBytes: 256 * KB, cacheBytes: 4 * MB, dataset: 100000, seed: 7,
  };

  /* ----------------------------------------------------------------- utilities */
  class RNG {
    constructor(seed) { this.s = (seed >>> 0) || 1; }
    float() {
      let t = (this.s += 0x6D2B79F5);
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    }
    int(n) { return Math.floor(this.float() * n); }
  }

  function lowerBound(a, x) {
    let lo = 0, hi = a.length;
    while (lo < hi) { const m = (lo + hi) >> 1; if (a[m] < x) lo = m + 1; else hi = m; }
    return lo;
  }
  function upperBound(a, x) {
    let lo = 0, hi = a.length;
    while (lo < hi) { const m = (lo + hi) >> 1; if (a[m] <= x) lo = m + 1; else hi = m; }
    return lo;
  }

  class Zipf {
    constructor(n, theta, rng) {
      this.n = n; this.theta = theta; this.rng = rng;
      let z = 0;
      for (let i = 1; i <= n; i++) z += 1 / Math.pow(i, theta);
      this.zetan = z;
      this.alpha = 1 / (1 - theta);
      const z2 = 1 + 1 / Math.pow(2, theta);
      this.eta = (1 - Math.pow(2 / n, 1 - theta)) / (1 - z2 / z);
    }
    next() {
      const u = this.rng.float(), uz = u * this.zetan;
      if (uz < 1) return 0;
      if (uz < 1 + Math.pow(0.5, this.theta)) return 1;
      return Math.min(this.n - 1, Math.floor(this.n * Math.pow(this.eta * u - this.eta + 1, this.alpha)));
    }
  }

  const LOG_G = Math.log(1.04);
  class Hist {
    constructor() { this.c = new Uint32Array(520); this.n = 0; }
    add(us) {
      const i = us <= 1 ? 0 : Math.min(519, Math.floor(Math.log(us) / LOG_G));
      this.c[i]++; this.n++;
    }
    q(p) {
      if (!this.n) return 0;
      const target = Math.ceil(this.n * p);
      let acc = 0;
      for (let i = 0; i < 520; i++) { acc += this.c[i]; if (acc >= target) return Math.exp((i + 1) * LOG_G); }
      return Math.exp(520 * LOG_G);
    }
    reset() { this.c.fill(0); this.n = 0; }
  }

  // Sliding rate over the last second of simulated time (10 x 100 ms buckets).
  class RateWindow {
    constructor() { this.bu = 100000; this.n = 10; this.c = new Float64Array(10); this.last = 0; }
    roll(now) {
      const b = Math.floor(now / this.bu);
      if (b - this.last > this.n) { this.c.fill(0); this.last = b; return; }
      while (this.last < b) { this.last++; this.c[this.last % this.n] = 0; }
    }
    add(now, v) { this.roll(now); this.c[this.last % this.n] += v; }
    rate(now) {
      this.roll(now);
      let s = 0;
      for (let i = 0; i < this.n; i++) s += this.c[i];
      const cur = (now - this.last * this.bu) / this.bu;
      const span = Math.min((this.n - 1 + cur) * this.bu, Math.max(now, 1)) / 1e6;
      return s / Math.max(span, 0.05);
    }
  }

  /* -------------------------------------------------------------- event kernel */
  const less = (a, b) => a.t < b.t || (a.t === b.t && a.s < b.s);

  class Sim {
    constructor() { this.now = 0; this.h = []; this.seq = 0; }
    at(t, fn) {
      const e = { t, s: this.seq++, fn }, h = this.h;
      let i = h.length; h.push(e);
      while (i > 0) { const p = (i - 1) >> 1; if (less(h[p], e)) break; h[i] = h[p]; i = p; }
      h[i] = e;
    }
    pop() {
      const h = this.h, top = h[0], last = h.pop();
      if (h.length) {
        let i = 0; const n = h.length;
        for (;;) {
          const l = 2 * i + 1; if (l >= n) break;
          const r = l + 1, c = (r < n && less(h[r], h[l])) ? r : l;
          if (less(h[c], last)) { h[i] = h[c]; i = c; } else break;
        }
        h[i] = last;
      }
      return top;
    }
    // Returns true when the clock reached `target`, false if the wall-clock budget ran out first.
    run(target, deadline) {
      let n = 0;
      while (this.h.length && this.h[0].t <= target) {
        const e = this.pop(); this.now = e.t; e.fn();
        if ((++n & 127) === 0 && performance.now() > deadline) return false;
      }
      this.now = target;
      return true;
    }
    // Cooperative "process": generators yield {d: delay} | {io:{disk,req}} | {w: Signal}.
    spawn(gen) {
      const step = () => {
        let r;
        try { r = gen.next(); } catch (err) { console.error(err); return; }
        if (r.done) return;
        const y = r.value;
        if (y.d !== undefined) this.at(this.now + Math.max(0, y.d), step);
        else if (y.io) y.io.disk.submit(y.io.req, step);
        else if (y.w) y.w.wait(step);
      };
      step();
    }
  }

  class Signal {
    constructor(sim) { this.sim = sim; this.w = []; }
    wait(f) { this.w.push(f); }
    fire() { const w = this.w; if (!w.length) return; this.w = []; for (const f of w) this.sim.at(this.sim.now, f); }
  }

  /* --------------------------------------------------------------------- disk */
  class Disk {
    constructor(engine, prof, rng) {
      this.eng = engine; this.sim = engine.sim; this.p = prof; this.rng = rng;
      this.q = [[], []]; this.busy = false; this.head = DATA_BASE; this.lastEnd = 0; this.streak = 0;
      this.cur = null;
      this.iops = new RateWindow();
      this.s = { reads: 0, writes: 0, seeks: 0, seqIOs: 0, bytesR: 0, bytesW: 0, busyUs: 0, posUs: 0, seekUs: 0, rotUs: 0, xferUs: 0 };
    }
    submit(io, cb) {
      io.cb = cb;
      this.q[io.prio ? 1 : 0].push(io);
      this.pump();
    }
    pump() {
      if (this.busy) return;
      const q0 = this.q[0], q1 = this.q[1];
      let io;
      if (q0.length && !(q1.length && this.streak >= 2)) { io = q0.shift(); this.streak++; }
      else if (q1.length) { io = q1.shift(); this.streak = 0; }
      else return;
      this.start(io);
    }
    start(io) {
      const p = this.p, now = this.sim.now, seq = io.addr === this.head;
      let seekT = 0, rotT = 0;
      if (p.kind === 'hdd') {
        if (seq) {
          let gap = now - this.lastEnd;
          if (io.sync) gap += p.cmd;
          // The platter kept turning while we were idle: wait for the sector to come around again.
          if (gap > 3) rotT = (p.rot - (gap % p.rot)) % p.rot;
        } else {
          const dist = Math.abs(io.addr - this.head);
          seekT = p.seekMin + p.seekVar * Math.sqrt(Math.min(1, dist / SPAN));
          rotT = this.rng.float() * p.rot;
        }
      } else {
        seekT = (io.kind === 'r' ? (seq ? p.seqUs : p.readUs) : (seq ? p.seqUs : p.writeUs)) + (io.sync ? p.flushUs : 0);
      }
      const pos = seekT + rotT;
      const xfer = io.bytes / p.bw * 1e6;
      io.start = now; io.seekT = seekT; io.rotT = rotT; io.pos = pos; io.xfer = xfer; io.seq = seq; io.end = now + pos + xfer;
      this.busy = true; this.cur = io;
      this.eng.emit({ k: 'io', io: { addr: io.addr, bytes: io.bytes, kind: io.kind, tag: io.tag, seq, pos, xfer, prio: io.prio } });
      this.sim.at(io.end, () => this.finish(io));
    }
    finish(io) {
      const s = this.s;
      if (io.kind === 'r') { s.reads++; s.bytesR += io.bytes; } else { s.writes++; s.bytesW += io.bytes; }
      if (io.seq) s.seqIOs++; else s.seeks++;
      s.busyUs += io.pos + io.xfer; s.posUs += io.pos; s.seekUs += io.seekT; s.rotUs += io.rotT; s.xferUs += io.xfer;
      this.head = io.addr + io.bytes; this.lastEnd = this.sim.now;
      this.busy = false; this.cur = null;
      this.iops.add(this.sim.now, 1);
      io.cb();
      this.pump();
    }
    pending() { return this.q[0].length + this.q[1].length + (this.busy ? 1 : 0); }
  }

  /* ---------------------------------------------------------------------- WAL */
  // Group commit: while one sync is in flight, new records accumulate and ride the next sync.
  class WAL {
    constructor(engine) {
      this.eng = engine; this.pending = []; this.pendBytes = 0; this.flushing = false; this.off = 0;
      this.appends = 0; this.syncs = 0; this.bytes = 0; this.lastBatch = 0;
    }
    append(req, bytes, records) {
      this.pending.push(req); this.pendBytes += bytes; this.appends += records;
      this.kick();
    }
    kick() {
      if (this.flushing || !this.pending.length) return;
      const batch = this.pending, eng = this.eng;
      const bytes = Math.max(512, Math.ceil(this.pendBytes / 512) * 512);
      this.pending = []; this.pendBytes = 0; this.flushing = true;
      if (this.off + bytes > WAL_SIZE) this.off = 0;
      const addr = WAL_BASE + this.off;
      this.off += bytes; this.lastBatch = batch.length;
      for (const r of batch) eng.mark(r, 'walsync', { off: this.off / WAL_SIZE });
      eng.emit({ k: 'walflush', n: batch.length, bytes });
      eng.disk.submit({ kind: 'w', addr, bytes, prio: 0, sync: true, tag: 'wal' }, () => {
        this.flushing = false; this.syncs++; this.bytes += bytes;
        for (const r of batch) eng.complete(r);
        this.kick();
      });
    }
  }

  /* ------------------------------------------------------------------ metrics */
  class Metrics {
    constructor() {
      this.arrived = 0; this.completed = 0; this.writes = 0; this.reads = 0; this.latSum = 0;
      this.hist = new Hist(); this.win = new Hist(); this.rate = new RateWindow(); this.userBytes = 0;
    }
    record(lat, isWrite, bytes, now) {
      this.completed++; this.latSum += lat; this.hist.add(lat); this.win.add(lat);
      if (isWrite) { this.writes++; this.userBytes += bytes; } else this.reads++;
      this.rate.add(now, 1);
    }
  }

  /* --------------------------------------------------------------- engine base */
  class EngineBase {
    constructor(host, id) {
      this.host = host; this.sim = host.sim; this.cfg = host.cfg; this.id = id; this.bus = host.bus;
      this.q = []; this.qh = 0; this.qTok = 0; this.idle = true;
      this.metrics = new Metrics(); this.workSig = new Signal(this.sim);
      this.mode = 'idle'; this.modeText = 'idle'; this.stall = null; this.stallStart = 0;
      this.stats = { memWrites: 0, memReads: 0, splits: 0, flushes: 0, compactions: 0, stallUs: 0, hits: 0, misses: 0 };
      this.series = { t: [], thr: [], p99: [], qd: [] };
      this.entryBytes = KEY_BYTES + this.cfg.valueBytes + 8;
      this.recBytes = KEY_BYTES + this.cfg.valueBytes + 16;
      this.userRec = KEY_BYTES + this.cfg.valueBytes;
      this.disk = new Disk(this, STORAGE[this.cfg.storage], new RNG(this.cfg.seed * 31 + (id === 'bt' ? 11 : 23)));
      this.wal = new WAL(this);
    }
    qLen() { return this.q.length - this.qh; }
    qHeadId() { return this.qh < this.q.length ? this.q[this.qh].id : this.host.nextId; }
    emit(e) { e.eng = this.id; if (this.bus.length < 6000) this.bus.push(e); }
    mark(req, st, x) {
      if (!req.vis) return;
      const e = x || {}; e.k = 'tok'; e.id = req.id; e.st = st; e.key = req.key; e.op = req.op;
      this.emit(e);
    }
    log(cls, text) { this.emit({ k: 'log', cls, text, t: this.sim.now }); }
    setMode(m, t) { this.mode = m; this.modeText = t; }
    beginStall(text) {
      if (this.stall === null) this.stallStart = this.sim.now;
      if (this.stall !== text) this.log('stall', text);
      this.stall = text; this.setMode('stall', text);
    }
    endStall() {
      if (this.stall !== null) { this.stats.stallUs += this.sim.now - this.stallStart; this.stall = null; }
    }
    arrive(req) {
      this.metrics.arrived++;
      if (req.vis) { if (this.qTok >= 10) req.vis = false; else this.qTok++; }
      this.q.push(req);
      this.mark(req, 'queue');
      if (this.idle) { this.idle = false; this.workSig.fire(); }
    }
    *worker() {
      for (;;) {
        if (this.qLen() === 0) {
          if (this.qh > 0) { this.q = []; this.qh = 0; }
          this.idle = true; this.setMode('idle', 'idle · waiting for requests');
          this.onIdle();
          yield { w: this.workSig };
          continue;
        }
        const r = this.q[this.qh++];
        if (this.qh > 4096 && this.qh * 2 > this.q.length) { this.q = this.q.slice(this.qh); this.qh = 0; }
        if (r.vis) this.qTok--;
        this.curReq = r;
        yield* this.process(r);
      }
    }
    onIdle() {}
    complete(req) {
      const now = this.sim.now, lat = now - req.t;
      this.metrics.record(lat, req.op === 'w', this.userRec, now);
      this.mark(req, 'done', { lat });
    }
    start() { this.sim.spawn(this.worker()); }
    writeAmp() {
      const m = this.metrics;
      if (m.writes < 30) return null;
      return (this.disk.s.bytesW + this.wal.pendBytes) / m.userBytes;
    }
    sample(now) {
      const m = this.metrics, s = this.series;
      s.t.push(now / 1e6); s.thr.push(m.rate.rate(now));
      const prev = s.p99.length ? s.p99[s.p99.length - 1] : 0;
      s.p99.push(m.win.n ? m.win.q(0.99) : prev); m.win.reset();
      s.qd.push(this.qLen());
      if (s.t.length > 6000) for (const k in s) s[k] = s[k].filter((_, i) => i % 2 === 0);
    }
  }

  /* ----------------------------------------------------------------- B+ tree */
  class BTree {
    constructor(leafCap, intCap) {
      this.leafCap = leafCap; this.intCap = intCap; this.nodes = []; this.root = -1; this.height = 0;
      this.leaves = 0; this.internals = 0;
    }
    newNode(leaf) {
      const n = { id: this.nodes.length, leaf, keys: [], kids: leaf ? null : [] };
      this.nodes.push(n); if (leaf) this.leaves++; else this.internals++;
      return n;
    }
    minKey(n) { while (!n.leaf) n = this.nodes[n.kids[0]]; return n.keys[0]; }
    // Pre-aged tree: node fill factors are spread between 50% and 100%, like a tree built by random inserts.
    bulkLoad(keys, rng) {
      const pick = cap => Math.max(2, Math.floor(cap * (0.5 + 0.5 * rng.float())));
      let level = [];
      for (let i = 0; i < keys.length;) {
        const per = pick(this.leafCap), n = this.newNode(true);
        n.keys = Array.from(keys.subarray(i, Math.min(keys.length, i + per)));
        level.push(n); i += per;
      }
      this.height = 1;
      while (level.length > 1) {
        const groups = [];
        for (let i = 0; i < level.length;) {
          const per = Math.max(3, pick(this.intCap + 1));
          groups.push(level.slice(i, i + per)); i += per;
        }
        if (groups.length > 1 && groups[groups.length - 1].length === 1) {
          const lone = groups.pop()[0]; groups[groups.length - 1].push(lone);
        }
        const up = [];
        for (const g of groups) {
          const n = this.newNode(false);
          n.kids = g.map(x => x.id);
          n.keys = g.slice(1).map(x => this.minKey(x));
          up.push(n);
        }
        level = up; this.height++;
      }
      this.root = level[0].id;
    }
    path(key) {
      const p = []; let id = this.root;
      for (;;) {
        p.push(id);
        const n = this.nodes[id];
        if (n.leaf) return p;
        id = n.kids[upperBound(n.keys, key)];
      }
    }
    insertAt(key, path) {
      const leaf = this.nodes[path[path.length - 1]];
      const i = lowerBound(leaf.keys, key);
      const info = { isNew: false, leafId: leaf.id, slot: i, splits: [] };
      if (leaf.keys[i] === key) { info.count = leaf.keys.length; return info; }
      leaf.keys.splice(i, 0, key);
      info.isNew = true; info.count = leaf.keys.length;
      let node = leaf, depth = path.length - 1, level = 0;
      for (;;) {
        const cap = node.leaf ? this.leafCap : this.intCap;
        if (node.keys.length <= cap) break;
        const right = this.newNode(node.leaf), mid = node.keys.length >> 1;
        let sep;
        if (node.leaf) { right.keys = node.keys.splice(mid); sep = right.keys[0]; }
        else {
          sep = node.keys[mid];
          right.keys = node.keys.splice(mid + 1); node.keys.pop();
          right.kids = node.kids.splice(mid + 1);
        }
        const sp = { oldId: node.id, newId: right.id, leaf: node.leaf, level, sep, leftN: node.keys.length, rightN: right.keys.length, parentId: -1, newRootId: -1 };
        info.splits.push(sp);
        if (depth === 0) {
          const nr = this.newNode(false);
          nr.keys = [sep]; nr.kids = [node.id, right.id]; this.root = nr.id; this.height++;
          sp.parentId = nr.id; sp.newRootId = nr.id;
          break;
        }
        const parent = this.nodes[path[depth - 1]], idx = parent.kids.indexOf(node.id);
        parent.keys.splice(idx, 0, sep); parent.kids.splice(idx + 1, 0, right.id);
        sp.parentId = parent.id;
        node = parent; depth--; level++;
      }
      return info;
    }
  }

  class BTreeEngine extends EngineBase {
    constructor(host) {
      super(host, 'bt');
      const c = this.cfg;
      this.pageSize = c.pageSize;
      this.leafCap = Math.max(4, Math.floor((c.pageSize - 64) / this.entryBytes));
      this.intCap = Math.max(4, Math.floor((c.pageSize - 64) / (KEY_BYTES + 8)));
      this.tree = new BTree(this.leafCap, this.intCap);
      this.tree.bulkLoad(host.keys, new RNG(c.seed + 3));
      this.poolCap = Math.max(16, Math.floor(c.cacheBytes / c.pageSize));
      this.pool = new Map();
      this.flushList = new Map();
      this.pins = [];
      this.cleanSig = new Signal(this.sim); this.cleanDone = new Signal(this.sim);
      this.cleanerWaiting = false;
      this.dirtyWritebacks = 0; this.evictWrites = 0;
      this.visExtent = Math.max(this.tree.nodes.length * c.pageSize * 1.8, 16 * MB);
      this.bL = { tot: new Uint16Array(BUCKETS_LEAF), cache: new Uint16Array(BUCKETS_LEAF), dirty: new Uint16Array(BUCKETS_LEAF) };
      this.bI = { tot: new Uint16Array(BUCKETS_INT), cache: new Uint16Array(BUCKETS_INT), dirty: new Uint16Array(BUCKETS_INT) };
      this.warm();
    }
    warm() {
      const nodes = this.tree.nodes, leaves = [];
      for (const n of nodes) {
        if (!n.leaf) { if (this.pool.size < this.poolCap) this.pool.set(n.id, { dirty: false, ver: 0, flushing: false }); }
        else leaves.push(n.id);
      }
      const rng = new RNG(this.cfg.seed + 99);
      for (let i = leaves.length - 1; i > 0; i--) { const j = rng.int(i + 1), t = leaves[i]; leaves[i] = leaves[j]; leaves[j] = t; }
      for (let i = 0; i < leaves.length && this.pool.size < this.poolCap; i++) this.pool.set(leaves[i], { dirty: false, ver: 0, flushing: false });
    }
    start() { super.start(); this.sim.spawn(this.cleaner()); }
    addrOf(id) { return DATA_BASE + id * this.pageSize; }
    visY(addr) {
      if (addr < DATA_BASE) return 0.02 + 0.07 * (addr / WAL_SIZE);
      return 0.16 + 0.82 * Math.min(1, (addr - DATA_BASE) / this.visExtent);
    }
    bucketLeaf(key) { return Math.max(0, Math.min(BUCKETS_LEAF - 1, Math.floor(key / this.host.keyspace * BUCKETS_LEAF))); }
    bucketInt(key) { return Math.max(0, Math.min(BUCKETS_INT - 1, Math.floor(key / this.host.keyspace * BUCKETS_INT))); }
    refreshBuckets() {
      const L = this.bL, I = this.bI;
      for (const o of [L, I]) { o.tot.fill(0); o.cache.fill(0); o.dirty.fill(0); }
      const root = this.tree.root;
      for (const n of this.tree.nodes) {
        if (n.id === root) continue;
        const o = n.leaf ? L : I, b = n.leaf ? this.bucketLeaf(n.keys[0] || 0) : this.bucketInt(n.keys[0] || 0);
        o.tot[b]++;
        const e = this.pool.get(n.id);
        if (e) { o.cache[b]++; if (e.dirty) o.dirty[b]++; }
      }
    }
    touchDirty(id) {
      const e = this.pool.get(id);
      if (!e) return;
      e.dirty = true; e.ver++;
      if (!this.flushList.has(id)) this.flushList.set(id, true);
      this.stats.memWrites++;
      if (this.cleanerWaiting) this.cleanSig.fire();
    }
    lruVictim() {
      for (const id of this.pool.keys()) {
        if (this.pins.indexOf(id) >= 0) continue;
        if (this.pool.get(id).flushing) continue;
        return id;
      }
      return -1;
    }
    *makeRoom(req) {
      while (this.pool.size >= this.poolCap) {
        const vid = this.lruVictim();
        if (vid < 0) { yield { w: this.cleanDone }; continue; }
        const e = this.pool.get(vid);
        if (e.dirty) {
          e.flushing = true;
          this.setMode('disk', 'evicting dirty page #' + vid + ' → random write');
          if (req) this.mark(req, 'disk', { addr: this.addrOf(vid), evict: true });
          yield { io: { disk: this.disk, req: { kind: 'w', addr: this.addrOf(vid), bytes: this.pageSize, prio: 0, tag: 'evict_write' } } };
          e.flushing = false; this.dirtyWritebacks++; this.evictWrites++; this.stats.flushes++;
          this.flushList.delete(vid);
        }
        this.pool.delete(vid);
      }
    }
    *fetch(id, req, lv, plen, key) {
      const leaf = lv === plen - 1;
      const bucket = leaf ? this.bucketLeaf(key) : this.bucketInt(key);
      const e = this.pool.get(id);
      if (e) {
        this.pool.delete(id); this.pool.set(id, e);
        this.stats.hits++; this.stats.memReads++;
        this.mark(req, 'mem', { lv, plen, leaf, bucket });
        this.setMode('mem', 'buffer-pool hit · page #' + id);
        yield { d: COST.memAccess };
        return;
      }
      this.stats.misses++;
      this.mark(req, 'disk', { lv, plen, leaf, bucket, addr: this.addrOf(id) });
      yield* this.makeRoom(req);
      this.setMode('disk', 'buffer-pool miss · random read page #' + id);
      yield { io: { disk: this.disk, req: { kind: 'r', addr: this.addrOf(id), bytes: this.pageSize, prio: 0, tag: 'page_read' } } };
      this.pool.set(id, { dirty: false, ver: 0, flushing: false });
      this.mark(req, 'mem', { lv, plen, leaf, bucket });
    }
    *allocPage(id, req) {
      yield* this.makeRoom(req);
      this.pool.set(id, { dirty: false, ver: 0, flushing: false });
    }
    *process(req) {
      const key = req.key, isWrite = req.op === 'w';
      this.setMode('cpu', 'parse request · acquire latch');
      this.mark(req, 'cpu');
      yield { d: COST.parse };
      const path = this.tree.path(key);
      this.pins = path;
      for (let lv = 0; lv < path.length; lv++) {
        yield* this.fetch(path[lv], req, lv, path.length, key);
        this.setMode('cpu', 'binary search in page #' + path[lv]);
        yield { d: COST.search };
      }
      if (!isWrite) { this.pins = []; this.complete(req); return; }

      const info = this.tree.insertAt(key, path);
      const leafId = info.leafId, plen = path.length;
      this.setMode('mem', 'modify leaf page #' + leafId + ' in buffer pool');
      yield { d: COST.leafInsert };
      this.touchDirty(leafId);
      if (req.vis) this.emit({ k: 'modify', id: leafId, count: info.count, cap: this.leafCap, slot: info.slot, isNew: info.isNew, addr: this.addrOf(leafId) });
      let walBytes = this.recBytes, recs = 1;
      for (const sp of info.splits) {
        this.setMode('cpu', 'page split #' + sp.oldId + ' → #' + sp.newId);
        yield* this.allocPage(sp.newId, req);
        if (sp.newRootId >= 0) yield* this.allocPage(sp.newRootId, req);
        yield { d: COST.split };
        this.touchDirty(sp.oldId); this.touchDirty(sp.newId); this.stats.memWrites++;
        if (sp.parentId >= 0) this.touchDirty(sp.parentId);
        this.stats.splits++;
        walBytes += this.pageSize / 2; recs++;
        this.emit({ k: 'split', leaf: sp.leaf, level: sp.level, oldId: sp.oldId, newId: sp.newId, leftN: sp.leftN, rightN: sp.rightN, cap: sp.leaf ? this.leafCap : this.intCap, addrOld: this.addrOf(sp.oldId), addrNew: this.addrOf(sp.newId), root: sp.newRootId >= 0, key: sp.sep });
      }
      this.pins = [];
      this.setMode('mem', 'append redo record to WAL buffer');
      yield { d: COST.walBuf };
      this.stats.memWrites++;
      this.mark(req, 'wal');
      this.wal.append(req, walBytes, recs);
    }
    onIdle() { if (this.cleanerWaiting) this.cleanSig.fire(); }
    // Background page cleaner: writes the oldest dirty pages back at low priority.
    *cleaner() {
      for (;;) {
        const want = () => this.flushList.size > 0 && (this.flushList.size > Math.max(4, this.poolCap * 0.1) || this.idle);
        while (!want()) { this.cleanerWaiting = true; yield { w: this.cleanSig }; this.cleanerWaiting = false; }
        this.cleanerWaiting = false;
        let id = -1;
        for (const k of this.flushList.keys()) {
          const e = this.pool.get(k);
          if (!e) { this.flushList.delete(k); continue; }
          if (!e.flushing) { id = k; break; }
        }
        if (id < 0) { this.cleanerWaiting = true; yield { w: this.cleanDone }; this.cleanerWaiting = false; continue; }
        const e = this.pool.get(id), ver = e.ver;
        e.flushing = true;
        yield { io: { disk: this.disk, req: { kind: 'w', addr: this.addrOf(id), bytes: this.pageSize, prio: 1, tag: 'page_flush' } } };
        e.flushing = false; this.dirtyWritebacks++; this.stats.flushes++;
        if (this.pool.get(id) === e && e.ver === ver) { e.dirty = false; this.flushList.delete(id); }
        this.cleanDone.fire();
      }
    }
  }

  /* ---------------------------------------------------------------- LSM tree */
  class LSMEngine extends EngineBase {
    constructor(host) {
      super(host, 'lsm');
      const c = this.cfg;
      this.pageSize = c.pageSize; this.memBytes = c.memBytes;
      this.F = Math.max(32 * KB, Math.floor(c.memBytes / 2));
      this.l0Trigger = 4; this.l0Slow = 8; this.l0Stop = 12; this.mult = 10;
      this.l1Max = 5 * this.F;
      this.perFile = Math.max(1, Math.floor(this.F / this.entryBytes));
      this.levels = []; this.levelBytes = new Float64Array(MAX_LEVELS); this.cptr = new Array(MAX_LEVELS).fill(-1);
      for (let i = 0; i < MAX_LEVELS; i++) this.levels.push([]);
      this.mem = { set: new Set(), bytes: 0 }; this.imm = null; this.walSeg = 1;
      this.nextFileId = 1; this.flushing = null; this.comp = null;
      this.flushSig = new Signal(this.sim); this.compSig = new Signal(this.sim); this.stallSig = new Signal(this.sim);
      this.cacheCap = Math.max(4, Math.floor(Math.max(0, c.cacheBytes - 2 * c.memBytes) / c.pageSize));
      this.cache = new Map();
      this.bloomFP = 0.01;
      this.rng = new RNG(c.seed + 5);
      this.bulkLoad(host.keys);
    }
    maxBytes(L) { return this.l1Max * Math.pow(this.mult, L - 1); }
    bulkLoad(keys) {
      const total = keys.length * this.entryBytes;
      let L = 2;
      while (L < MAX_LEVELS - 1 && this.maxBytes(L) < total) L++;
      this.bottom = L;
      this.dataExtent = Math.max(3 * total, 48 * MB);
      this.allocPtr = DATA_BASE;
      for (let i = 0; i < keys.length; i += this.perFile) {
        this.addFile(L, keys.slice(i, Math.min(keys.length, i + this.perFile)), this.alloc(this.fileBytes(Math.min(this.perFile, keys.length - i))));
      }
    }
    fileBytes(n) { return Math.ceil((n * this.entryBytes + 1024) / 4096) * 4096; }
    alloc(bytes) {
      if (this.allocPtr + bytes > DATA_BASE + this.dataExtent) this.allocPtr = DATA_BASE;
      const a = this.allocPtr; this.allocPtr += bytes; return a;
    }
    addFile(L, keys, addr) {
      const f = { id: this.nextFileId++, level: L, keys, min: keys[0], max: keys[keys.length - 1], bytes: this.fileBytes(keys.length), addr };
      const arr = this.levels[L];
      if (L === 0) arr.push(f);
      else if (!arr.length || arr[arr.length - 1].min < f.min) arr.push(f);
      else { let i = 0; while (i < arr.length && arr[i].min < f.min) i++; arr.splice(i, 0, f); }
      this.levelBytes[L] += f.bytes;
      return f;
    }
    removeFiles(set) {
      for (let L = 0; L < MAX_LEVELS; L++) {
        const arr = this.levels[L]; let removed = 0;
        for (let i = arr.length - 1; i >= 0; i--) if (set.has(arr[i].id)) { removed += arr[i].bytes; arr.splice(i, 1); }
        this.levelBytes[L] -= removed;
      }
    }
    visY(addr) {
      if (addr < DATA_BASE) return 0.02 + 0.07 * (addr / WAL_SIZE);
      return 0.16 + 0.82 * Math.min(1, (addr - DATA_BASE) / this.dataExtent);
    }
    maxLevelUsed() { let m = 0; for (let L = 0; L < MAX_LEVELS; L++) if (this.levels[L].length) m = L; return m; }
    start() {
      super.start();
      this.sim.spawn(this.flusher());
      this.sim.spawn(this.compactor());
    }

    rotate() {
      this.imm = this.mem; this.mem = { set: new Set(), bytes: 0 }; this.walSeg++;
      this.log('flush', 'MemTable full (' + this.imm.set.size.toLocaleString() + ' keys) → immutable; new WAL segment #' + this.walSeg);
      this.emit({ k: 'rotate' });
      this.flushSig.fire();
    }
    *makeRoom() {
      let slowed = false;
      for (;;) {
        const l0 = this.levels[0].length;
        if (l0 >= this.l0Stop) { this.beginStall('STALL · L0 has ' + l0 + ' files — writes stopped until compaction catches up'); yield { w: this.stallSig }; continue; }
        if (this.mem.bytes >= this.memBytes) {
          if (this.imm) { this.beginStall('STALL · MemTable full, previous flush still running'); yield { w: this.stallSig }; continue; }
          this.rotate(); continue;
        }
        if (!slowed && l0 >= this.l0Slow) { slowed = true; this.beginStall('SLOWDOWN · L0 has ' + l0 + ' files — 1 ms delay per write'); yield { d: 1000 }; continue; }
        break;
      }
      this.endStall();
    }
    *process(req) {
      this.setMode('cpu', 'parse request');
      this.mark(req, 'cpu');
      yield { d: COST.parse };
      if (req.op === 'r') { yield* this.get(req); return; }
      yield* this.makeRoom();
      this.setMode('mem', 'append record to WAL buffer');
      this.mark(req, 'wal');
      yield { d: COST.walBuf };
      this.stats.memWrites++;
      this.wal.append(req, this.recBytes, 1);
      this.setMode('mem', 'insert into MemTable (skip list)');
      this.mark(req, 'mem', { fill: this.mem.bytes / this.memBytes });
      yield { d: COST.memInsert };
      this.mem.set.add(req.key); this.mem.bytes += this.entryBytes + 24;
      this.stats.memWrites++;
    }
    *get(req) {
      const key = req.key;
      this.setMode('mem', 'lookup in MemTable / immutable MemTable');
      this.mark(req, 'mem', { fill: this.mem.bytes / this.memBytes });
      this.stats.memReads++;
      yield { d: COST.memInsert * 0.6 };
      if (this.mem.set.has(key) || (this.imm && this.imm.set.has(key))) { this.complete(req); return; }
      let found = false;
      const l0 = this.levels[0];
      for (let i = l0.length - 1; i >= 0 && !found; i--) {
        const f = l0[i];
        if (key < f.min || key > f.max) continue;
        found = yield* this.probe(f, req, key);
      }
      for (let L = 1; L < MAX_LEVELS && !found; L++) {
        const arr = this.levels[L]; if (!arr.length) continue;
        let lo = 0, hi = arr.length;
        while (lo < hi) { const m = (lo + hi) >> 1; if (arr[m].max < key) lo = m + 1; else hi = m; }
        const f = arr[lo];
        if (!f || key < f.min) continue;
        found = yield* this.probe(f, req, key);
      }
      this.complete(req);
    }
    *probe(f, req, key) {
      this.setMode('mem', 'bloom filter check · SSTable #' + f.id);
      this.stats.memReads++;
      yield { d: COST.bloom };
      const pos = lowerBound(f.keys, key), present = f.keys[pos] === key;
      if (!present && this.rng.float() >= this.bloomFP) return false;
      const bi = Math.floor(pos * this.entryBytes / this.pageSize), ck = f.id * 8192 + bi;
      if (this.cache.has(ck)) {
        const v = this.cache.get(ck); this.cache.delete(ck); this.cache.set(ck, v);
        this.stats.hits++; this.stats.memReads++;
        yield { d: COST.memAccess }; return present;
      }
      this.stats.misses++;
      const addr = f.addr + Math.min(bi * this.pageSize, f.bytes - this.pageSize);
      this.mark(req, 'disk', { level: f.level, addr });
      this.setMode('disk', 'block cache miss · random read from L' + f.level);
      yield { io: { disk: this.disk, req: { kind: 'r', addr, bytes: this.pageSize, prio: 0, tag: 'block_read' } } };
      this.cache.set(ck, true);
      if (this.cache.size > this.cacheCap) this.cache.delete(this.cache.keys().next().value);
      return present;
    }

    *flusher() {
      for (;;) {
        while (!this.imm) yield { w: this.flushSig };
        const imm = this.imm, keys = Int32Array.from(imm.set).sort();
        const bytes = this.fileBytes(keys.length), addr = this.alloc(bytes);
        this.flushing = { bytes, written: 0, addr, n: keys.length };
        this.emit({ k: 'flush_start', bytes });
        yield { d: keys.length * COST.flushPerKey };
        for (let off = 0; off < bytes; off += MAX_IO) {
          const n = Math.min(MAX_IO, bytes - off);
          yield { io: { disk: this.disk, req: { kind: 'w', addr: addr + off, bytes: n, prio: 1, tag: 'flush' } } };
          this.flushing.written = off + n;
        }
        const f = this.addFile(0, keys, addr);
        this.imm = null; this.flushing = null; this.stats.flushes++;
        this.log('flush', 'Flushed MemTable → SSTable #' + f.id + ' in L0 (' + fmtBytes(f.bytes) + ', ' + keys.length.toLocaleString() + ' keys, sequential write). L0 files: ' + this.levels[0].length);
        this.emit({ k: 'flush_done', id: f.id });
        this.stallSig.fire(); this.compSig.fire();
      }
    }

    pickCompaction() {
      let best = -1, bestScore = 1;
      const s0 = this.levels[0].length / this.l0Trigger;
      if (s0 >= 1) { best = 0; bestScore = s0; }
      for (let L = 1; L < MAX_LEVELS - 1; L++) {
        const score = this.levelBytes[L] / this.maxBytes(L);
        if (score > bestScore) { best = L; bestScore = score; }
      }
      if (best < 0) return null;
      const overlap = (arr, lo, hi) => arr.filter(f => f.max >= lo && f.min <= hi);
      let in0, in1;
      if (best === 0) {
        in0 = this.levels[0].slice();
        let lo = Infinity, hi = -Infinity;
        for (const f of in0) { if (f.min < lo) lo = f.min; if (f.max > hi) hi = f.max; }
        in1 = overlap(this.levels[1], lo, hi);
      } else {
        const files = this.levels[best];
        const f = files.find(x => x.min > this.cptr[best]) || files[0];
        this.cptr[best] = f.max;
        in0 = [f]; in1 = overlap(this.levels[best + 1], f.min, f.max);
      }
      return { level: best, in0, in1, trivial: best > 0 && in1.length === 0 };
    }
    *compactor() {
      for (;;) {
        const job = this.pickCompaction();
        if (!job) { yield { w: this.compSig }; continue; }
        yield* this.runCompaction(job);
      }
    }
    *runCompaction(job) {
      const inputs = job.in0.concat(job.in1), to = job.level + 1;
      const idSet = new Set(inputs.map(f => f.id));
      const bytesIn = inputs.reduce((s, f) => s + f.bytes, 0);
      const comp = this.comp = { level: job.level, to, in0: job.in0.map(f => f.id), in1: job.in1.map(f => f.id), phase: 'read', p: 0, out: [], bytesIn };
      this.emit({ k: 'comp_start', level: job.level, to });
      this.log('compact', 'Compaction L' + job.level + ' → L' + to + ': ' + job.in0.length + ' file(s) + ' + job.in1.length + ' overlapping in L' + to + ' (' + fmtBytes(bytesIn) + ' to read & merge)' + (job.trivial ? ' — trivial move, no I/O' : ''));
      if (job.trivial) {
        const f = job.in0[0];
        this.removeFiles(idSet);
        this.addFile(to, f.keys, f.addr);
        this.stats.compactions++; this.comp = null;
        this.emit({ k: 'comp_done', level: job.level, to });
        this.stallSig.fire(); return;
      }
      // Adjacent input files are read as one streaming run (readahead), like a real compaction iterator.
      const runs = [];
      for (const f of inputs.slice().sort((a, b) => a.addr - b.addr)) {
        const last = runs[runs.length - 1];
        if (last && last.addr + last.bytes === f.addr) last.bytes += f.bytes; else runs.push({ addr: f.addr, bytes: f.bytes });
      }
      let done = 0;
      for (const r of runs) {
        for (let off = 0; off < r.bytes; off += MAX_IO) {
          const n = Math.min(MAX_IO, r.bytes - off);
          yield { io: { disk: this.disk, req: { kind: 'r', addr: r.addr + off, bytes: n, prio: 1, tag: 'compact_read' } } };
          done += n; comp.p = done / bytesIn;
        }
      }
      comp.phase = 'merge'; comp.p = 0;
      let total = 0;
      for (const f of inputs) total += f.keys.length;
      const all = new Int32Array(total);
      let pos = 0;
      for (const f of inputs) { all.set(f.keys, pos); pos += f.keys.length; }
      all.sort();
      let u = 0;
      for (let i = 0; i < all.length; i++) if (i === 0 || all[i] !== all[i - 1]) all[u++] = all[i];
      const merged = all.subarray(0, u);
      for (let s = 0; s < 4; s++) { yield { d: total * COST.mergePerKey / 4 }; comp.p = (s + 1) / 4; }
      comp.phase = 'write'; comp.p = 0;
      const outs = [];
      for (let i = 0; i < merged.length; i += this.perFile) {
        const keys = merged.slice(i, Math.min(merged.length, i + this.perFile));
        const bytes = this.fileBytes(keys.length);
        outs.push({ keys, bytes, addr: this.alloc(bytes), written: 0 });
      }
      comp.out = outs;
      let totalOut = 0;
      const wruns = [];
      for (const o of outs) {
        o.base = totalOut; totalOut += o.bytes;
        const last = wruns[wruns.length - 1];
        if (last && last.addr + last.bytes === o.addr) last.bytes += o.bytes; else wruns.push({ addr: o.addr, bytes: o.bytes });
      }
      let wr = 0;
      for (const r of wruns) {
        for (let off = 0; off < r.bytes; off += MAX_IO) {
          const n = Math.min(MAX_IO, r.bytes - off);
          yield { io: { disk: this.disk, req: { kind: 'w', addr: r.addr + off, bytes: n, prio: 1, tag: 'compact_write' } } };
          wr += n; comp.p = wr / totalOut;
          for (const o of outs) o.written = Math.max(0, Math.min(o.bytes, wr - o.base));
        }
      }
      this.removeFiles(idSet);
      const newIds = [];
      for (const o of outs) newIds.push(this.addFile(to, o.keys, o.addr).id);
      this.stats.compactions++; this.comp = null;
      this.log('compact', 'Compaction L' + job.level + ' → L' + to + ' finished: ' + fmtBytes(bytesIn) + ' read, ' + fmtBytes(totalOut) + ' written sequentially → ' + outs.length + ' new SSTables (' + (total - u).toLocaleString() + ' obsolete versions dropped)');
      this.emit({ k: 'comp_done', level: job.level, to, ids: newIds });
      this.stallSig.fire(); this.compSig.fire();
    }
  }

  function fmtBytes(b) {
    if (b >= MB) return (b / MB).toFixed(b >= 10 * MB ? 0 : 1) + ' MB';
    if (b >= KB) return (b / KB).toFixed(0) + ' KB';
    return b + ' B';
  }

  /* ------------------------------------------------------------- simulation */
  class Simulation {
    constructor(cfg) {
      this.cfg = Object.assign({}, DEFAULTS, cfg);
      const c = this.cfg;
      this.sim = new Sim(); this.bus = [];
      this.rng = new RNG(c.seed); this.wrng = new RNG(c.seed * 7919 + 13);
      this.keyspace = c.dataset * 2;
      const tmp = new Int32Array(this.keyspace); let n = 0;
      for (let k = 0; k < this.keyspace; k++) if (this.rng.float() < 0.5) tmp[n++] = k;
      this.keys = tmp.slice(0, n);
      this.zipf = c.dist === 'zipf' ? new Zipf(this.keyspace, 0.99, this.wrng) : null;
      this.seqNext = 0;
      this.rate = c.rate; this.writeRatio = c.writeRatio; this.dist = c.dist; this.visProb = 0.02;
      this.nextId = 1;
      this.bt = new BTreeEngine(this); this.lsm = new LSMEngine(this);
      this.engines = [this.bt, this.lsm];
      for (const e of this.engines) e.start();
      this.sim.at(0, () => this.arrival());
      this.sim.at(250000, () => this.sampler());
    }
    get now() { return this.sim.now; }
    nextKey() {
      const ks = this.keyspace;
      if (this.dist === 'seq') return ks + this.seqNext++;
      if (this.dist === 'zipf') {
        if (!this.zipf) this.zipf = new Zipf(ks, 0.99, this.wrng);
        return (Math.imul(this.zipf.next(), 2654435761) >>> 0) % ks;
      }
      return this.wrng.int(ks);
    }
    arrival() {
      const id = this.nextId++, isW = this.wrng.float() < this.writeRatio, key = this.nextKey();
      const vis = Math.random() < this.visProb, t = this.sim.now;
      for (const e of this.engines) e.arrive({ id, t, key, op: isW ? 'w' : 'r', vis });
      const gap = -Math.log(1 - this.wrng.float()) / this.rate * 1e6;
      this.sim.at(t + gap, () => this.arrival());
    }
    sampler() {
      for (const e of this.engines) e.sample(this.sim.now);
      this.sim.at(this.sim.now + 250000, () => this.sampler());
    }
    advance(target, deadline) { return this.sim.run(target, deadline); }
    snapshot(e) {
      const now = this.sim.now, m = e.metrics, d = e.disk, s = d.s;
      const busy = s.busyUs;
      const out = {
        thr: m.rate.rate(now), avg: m.completed ? m.latSum / m.completed : 0, p99: m.hist.q(0.99),
        qd: e.qLen(), reads: s.reads, writes: s.writes, seeks: s.seeks, memWrites: e.stats.memWrites,
        memReads: e.stats.memReads, wal: e.wal.appends, syncs: e.wal.syncs, splits: e.stats.splits,
        flushes: e.stats.flushes, compactions: e.stats.compactions, wa: e.writeAmp(), iops: d.iops.rate(now),
        completed: m.completed, arrived: m.arrived, bytesW: s.bytesW, bytesR: s.bytesR,
        busyPct: now > 0 ? Math.min(100, busy / now * 100) : 0, posPct: busy > 0 ? s.posUs / busy * 100 : 0,
        seekPct: now > 0 ? s.seekUs / now * 100 : 0, rotPct: now > 0 ? s.rotUs / now * 100 : 0, xferPct: now > 0 ? s.xferUs / now * 100 : 0,
        hitPct: (e.stats.hits + e.stats.misses) ? e.stats.hits / (e.stats.hits + e.stats.misses) * 100 : null,
        stallUs: e.stats.stallUs + (e.stall !== null ? now - e.stallStart : 0),
      };
      return out;
    }
  }

  const API = { Simulation, DEFAULTS, STORAGE, COST, KB, MB, KEY_BYTES, WAL_BASE, WAL_SIZE, DATA_BASE, BUCKETS_LEAF, BUCKETS_INT, MAX_LEVELS, fmtBytes };
  if (typeof module !== 'undefined' && module.exports) module.exports = API;
  else root.SK = API;
})(typeof window !== 'undefined' ? window : globalThis);
