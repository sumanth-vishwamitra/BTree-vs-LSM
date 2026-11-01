# B+ Tree vs LSM Tree — write-path simulator

Open `index.html` in a browser (no build step, works from `file://`).

| File | Role |
|---|---|
| `engine.js` | Headless discrete-event model (µs clock): real B+ Tree with splits and an LRU buffer pool + page cleaner; leveled LSM with MemTable, flush, compaction, L0 slowdown/stop, bloom filters and block cache; single-queue HDD/SSD model (seek + rotation + transfer); WAL with group commit. Also usable from Node (`require('./engine.js')`). |
| `render.js` | Canvas renderer for one engine panel (request pipeline, memory, disk, access-pattern plot, disk-time breakdown). |
| `app.js` | Controls, presets, frame loop, metrics, charts, event log. |

Both engines receive the identical Poisson stream of requests (same id, time, key, op). Only a sample of requests is drawn as tokens; every request is simulated and counted.
Structural settings (storage, page size, MemTable, cache, dataset, value size, seed) rebuild the engines; speed, offered load, write ratio and key pattern are live.
Latencies are relative, not product benchmarks. On an HDD every WAL group commit waits about one platter rotation, so both engines are bounded near ~100 commits/s and rely on batching.
