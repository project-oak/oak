# Icing Index Rebuild Benchmark Report

**Date**: 2026-02-10  
**Configuration**: 768-dimension embeddings, 5 rebuild iterations per data point

## Executive Summary

This benchmark measures the time required to rebuild the Icing search index from
ground truth files. This simulates the cold-start initialization scenario when a
new session starts with pre-existing data.

**Key Findings:**

- At 64k embeddings: **~30 seconds** to rebuild index from ~185 MB ground truth
- Rebuild time scales **linearly** with embedding count (~0.46 ms/embedding)
- External timing matches Icing's internal reporting (< 1ms variance)

---

## Results

| Embeddings | Ground Truth | Index Files | Total Size | Rebuild Avg (ms) | Per-Embedding (ms) |
| ---------- | ------------ | ----------- | ---------- | ---------------- | ------------------ |
| 1,000      | 2.89 MB      | 4.99 MB     | 7.88 MB    | 372.2            | 0.37               |
| 2,000      | 5.78 MB      | 8.10 MB     | 13.88 MB   | 749.9            | 0.37               |
| 4,000      | 11.56 MB     | 14.05 MB    | 25.61 MB   | 1,516.5          | 0.38               |
| 8,000      | 23.12 MB     | 26.43 MB    | 49.55 MB   | 3,109.2          | 0.39               |
| 16,000     | 46.25 MB     | 52.77 MB    | 99.02 MB   | 7,330.5          | 0.46               |
| 32,000     | 92.53 MB     | 103.26 MB   | 195.79 MB  | 14,755.2         | 0.46               |
| 64,000     | 185.09 MB    | 204.12 MB   | 389.21 MB  | 29,673.8         | 0.46               |

---

## Timing Validation

External wall-clock measurements were validated against Icing's internal
`InitializeStatsProto.latency_ms`:

| Embeddings | Ext Avg (ms) | Icing Internal (ms) | Difference |
| ---------- | ------------ | ------------------- | ---------- |
| 1,000      | 372.2        | 371.6               | 0.6 ms     |
| 2,000      | 749.9        | 749.4               | 0.5 ms     |
| 4,000      | 1,516.5      | 1,516.0             | 0.5 ms     |
| 8,000      | 3,109.2      | 3,108.6             | 0.6 ms     |
| 16,000     | 7,330.5      | 7,330.0             | 0.5 ms     |
| 32,000     | 14,755.2     | 14,754.6            | 0.6 ms     |
| 64,000     | 29,673.8     | 29,673.2            | 0.6 ms     |

The close alignment (< 1ms difference) confirms the external measurement
methodology is accurate.

---

## Storage Analysis

- **Ground Truth** files (schema + document log): ~2.9 KB per embedding
- **Index Files** (generated during rebuild): ~3.2 KB per embedding
- **Total Storage**: ~6.1 KB per embedding (768D vectors)

---

## Scaling Characteristics

```text
Rebuild Time (seconds)
     |
 30s |                                              *
     |
 25s |
     |
 20s |
     |                            *
 15s |
     |                     *
 10s |
     |              *
  5s |        *
     |   * *
  0s +----+----+----+----+----+----+----+
     0   8k  16k  24k  32k  48k  56k  64k
                  Embeddings
```

**Scaling**: Linear O(n) with embedding count

---

## Methodology

1. Store N embeddings in fresh Icing database
2. Export ground truth files (schema + document log)
3. For each iteration:
   - Migrate ground truth to new temp directory
   - Initialize Icing search engine (triggers index rebuild)
   - Record both external wall-clock time and Icing's internal latency_ms
4. Report min/avg/max across iterations

---

## Implications

- **Cold start for 64k memories**: ~30 second initialization overhead
- **Estimated for 100k memories**: ~46 seconds (extrapolated)
- **Index rebuild dominates startup time** - consider caching or lazy
  initialization strategies
