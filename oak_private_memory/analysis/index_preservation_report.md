# Index Preservation Analysis Report

**Date**: 2026-04-20 **Configuration**: 768-dimension embeddings, 5 iterations
per data point

## Executive Summary

This analysis compares two cold-start initialization strategies for the Icing
metadata database:

1. **Ground truth only** (current): Persist schema + document log only. Icing
   rebuilds the index from scratch on every `initialize()`.
2. **Full directory copy** (proposed): Persist the entire Icing directory,
   including pre-built index files. Icing skips index rebuild on `initialize()`.

**Key Finding: Preserving index files eliminates 99% of cold-start latency.**

| Scale | Current (rebuild) | Proposed (full copy) | Savings   | Speedup   |
| ----- | ----------------- | -------------------- | --------- | --------- |
| 1k    | 422 ms            | 13 ms                | 409 ms    | **31.7x** |
| 8k    | 3,503 ms          | 58 ms                | 3,445 ms  | **60.5x** |
| 64k   | 32,667 ms         | 386 ms               | 32,281 ms | **84.6x** |

---

## Full Results

| Embeddings | GT Size   | Total Size | GT Rebuild (ms) | Full Copy (ms) | Init Only (ms) | Savings (ms) | Speedup |
| ---------- | --------- | ---------- | --------------- | -------------- | -------------- | ------------ | ------- |
| 1,000      | 2.93 MB   | 8.11 MB    | 422.4           | 13.3           | 7.1            | 409.1        | 31.7x   |
| 2,000      | 5.85 MB   | 14.17 MB   | 841.5           | 19.5           | 10.9           | 822.1        | 43.3x   |
| 4,000      | 11.71 MB  | 26.16 MB   | 1,705.5         | 32.7           | 19.3           | 1,672.8      | 52.1x   |
| 8,000      | 23.42 MB  | 50.34 MB   | 3,502.9         | 57.9           | 34.1           | 3,445.0      | 60.5x   |
| 16,000     | 46.87 MB  | 100.10 MB  | 8,046.2         | 106.1          | 63.2           | 7,940.0      | 75.8x   |
| 32,000     | 93.76 MB  | 197.72 MB  | 16,207.9        | 203.7          | 123.3          | 16,004.1     | 79.6x   |
| 64,000     | 187.56 MB | 392.84 MB  | 32,666.8        | 385.9          | 238.3          | 32,280.8     | 84.6x   |

- **GT Rebuild (ms)**: Current approach — migrate ground truth, then
  `initialize()` which rebuilds the index.
- **Full Copy (ms)**: Proposed approach — copy entire directory (including
  index) + `initialize()`.
- **Init Only (ms)**: Just the `initialize()` call after full copy (no rebuild
  needed). This isolates the I/O cost from the computation cost.

---

## Analysis

### Why the speedup increases with scale

The rebuild cost scales linearly at ~0.51 ms/embedding (index construction is
O(n)). The full-copy cost scales linearly at ~0.006 ms/embedding (pure I/O,
dominated by `memcpy`-class operations). As n grows, the ratio diverges:

```text
Speedup
      |
  85x |                                              *
      |                                   *
  80x |
      |
  75x |
      |                        *
  60x |             *
      |
  50x |       *
      |
  40x |   *
  30x | *
      +----+----+----+----+----+----+----+
      0   8k  16k  24k  32k  48k  56k  64k
                   Embeddings
```

### Storage trade-off

Preserving the index doubles the blob size stored in the external database:

| Embeddings | Ground Truth Only | Full Directory | Overhead |
| ---------- | ----------------- | -------------- | -------- |
| 1,000      | 2.93 MB           | 8.11 MB        | +177%    |
| 8,000      | 23.42 MB          | 50.34 MB       | +115%    |
| 64,000     | 187.56 MB         | 392.84 MB      | +109%    |

The index overhead stabilizes at ~2.1x of the ground truth size. For 768D
embeddings, each embedding costs:

- Ground truth only: ~2.93 KB/embedding
- With index: ~6.14 KB/embedding (+3.21 KB for index data)

### Time breakdown at 64k embeddings

| Component             | Time (ms)    | % of full copy |
| --------------------- | ------------ | -------------- |
| Directory copy (I/O)  | 147.6        | 38%            |
| Icing initialize()    | 238.3        | 62%            |
| **Total (full copy)** | **385.9**    | 100%           |
| **Index rebuild**     | **32,666.8** | (current)      |

Even with the file copy overhead, the full-copy approach is **84.6x faster**
than rebuilding.

---

## Implications

### For the current architecture

The metadata blob stored in the external database (`EncryptedUserInfo.icing_db`)
currently contains only `IcingGroundTruthFiles` (schema + document log). The
proposed change would expand this to include the full directory contents.

### Storage cost vs latency trade-off

| Scenario               | Storage (64k) | Cold start |
| ---------------------- | ------------- | ---------- |
| Current (GT only)      | 187.56 MB     | 32.7 s     |
| Proposed (full dir)    | 392.84 MB     | 0.39 s     |
| Projected (100k, GT)   | ~293 MB       | ~51 s      |
| Projected (100k, full) | ~614 MB       | ~0.60 s    |

### Recommendation

**Strongly recommended.** The 2x storage increase is a small price for
eliminating 30+ seconds of cold-start latency. The improvement becomes more
impactful at scale.

### Implementation path

1. Extend `IcingGroundTruthFiles` proto (or create a new proto) to include the
   full directory contents (index files, embedding index, integer index, etc.).
2. Update `export()` to serialize the full directory.
3. Update `import()` / `migrate()` to restore the full directory.
4. Verify that Icing correctly detects the pre-built index and skips rebuild on
   `initialize()`.

---

## Methodology

1. Populate a fresh Icing database with N embeddings (768D, random values)
2. Call `optimize()` to compact the database
3. **Strategy A** (ground truth rebuild): Export ground truth files → migrate to
   new temp dir → `initialize()` (rebuilds index). Repeat 5 times.
4. **Strategy B** (full directory copy): Recursively copy entire icing directory
   → `initialize()` (no rebuild). Repeat 5 times.
5. Report average timings across iterations.

Benchmark source:
[index_preservation_benchmark.rs](file:///usr/local/google/home/yongheng/oak/oak_private_memory/analysis/index_preservation_benchmark.rs)
