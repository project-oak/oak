# Eigen Embedding Search Benchmark Report

**Date**: 2026-04-21 **Configuration**: 768-dimension embeddings, 20 iterations
per data point

## Executive Summary

This benchmark evaluates the impact of enabling the
[Eigen](https://eigen.tuxfamily.org/) linear algebra library for Icing's
embedding scorer. Eigen provides SIMD-optimized implementations of vector dot
product, cosine similarity, and euclidean distance — the core operations in
embedding search.

**Key Finding: Eigen provides a ~1.9x speedup for embedding search with
optimized builds (`-c opt`).**

| Scale | Without Eigen | With Eigen | Speedup  |
| ----- | ------------- | ---------- | -------- |
| 1k    | 1.12 ms       | 0.34 ms    | **3.3x** |
| 8k    | 9.49 ms       | 3.15 ms    | **3.0x** |
| 64k   | 79.46 ms      | 41.59 ms   | **1.9x** |

> [!WARNING] **Optimization level matters.** Without `-c opt`, Eigen is actually
> _slower_ than the scalar fallback due to template instantiation overhead.
> Always use `-c opt` (or equivalent) for production builds.

---

## Full Results (with `-c opt`)

### With Eigen Enabled

| Embeddings | Min (ms) | Avg (ms) | Max (ms) |
| ---------- | -------- | -------- | -------- |
| 1,000      | 0.33     | 0.34     | 0.38     |
| 2,000      | 0.66     | 0.68     | 0.77     |
| 4,000      | 1.28     | 1.32     | 1.54     |
| 8,000      | 2.94     | 3.15     | 3.95     |
| 16,000     | 8.08     | 8.42     | 8.78     |
| 32,000     | 17.26    | 17.53    | 17.96    |
| 64,000     | 40.69    | 41.59    | 42.53    |

### Without Eigen (Scalar Fallback)

| Embeddings | Min (ms) | Avg (ms) | Max (ms) |
| ---------- | -------- | -------- | -------- |
| 1,000      | 1.11     | 1.12     | 1.15     |
| 2,000      | 2.24     | 2.27     | 2.34     |
| 4,000      | 4.51     | 4.54     | 4.68     |
| 8,000      | 9.27     | 9.49     | 9.73     |
| 16,000     | 19.63    | 19.72    | 19.95    |
| 32,000     | 39.35    | 39.55    | 39.94    |
| 64,000     | 79.13    | 79.46    | 80.13    |

### Side-by-side Comparison (`-c opt`)

| Embeddings | No Eigen (ms) | Eigen (ms) | Savings (ms) | Speedup |
| ---------- | ------------- | ---------- | ------------ | ------- |
| 1,000      | 1.12          | 0.34       | 0.78         | 3.3x    |
| 2,000      | 2.27          | 0.68       | 1.59         | 3.3x    |
| 4,000      | 4.54          | 1.32       | 3.22         | 3.4x    |
| 8,000      | 9.49          | 3.15       | 6.34         | 3.0x    |
| 16,000     | 19.72         | 8.42       | 11.30        | 2.3x    |
| 32,000     | 39.55         | 17.53      | 22.02        | 2.3x    |
| 64,000     | 79.46         | 41.59      | 37.87        | 1.9x    |

---

## Impact of Optimization Level

> [!IMPORTANT] Without compiler optimization, Eigen's template-heavy code incurs
> overhead that dominates the SIMD benefits.

| Config              | 64k Avg (ms) | vs Eigen+opt |
| ------------------- | ------------ | ------------ |
| No Eigen, fastbuild | 299.63       | 7.2x slower  |
| Eigen, fastbuild    | 408.32       | 9.8x slower  |
| No Eigen, `-c opt`  | 79.46        | 1.9x slower  |
| **Eigen, `-c opt`** | **41.59**    | **baseline** |

The full matrix shows that `-c opt` provides a ~7-10x improvement regardless of
Eigen, and Eigen adds an additional ~1.9x on top.

---

## Analysis

### Why the speedup decreases at scale

At smaller scales (1k-4k), Eigen's SIMD vectorization delivers ~3.3x speedup
because the scoring computation dominates. At larger scales (32k-64k),
non-scoring overhead (index traversal, result aggregation, memory access)
becomes a larger fraction of total time, diluting the scoring speedup to ~1.9x.

### Per-embedding scoring cost

| Config    | µs/embedding (64k) |
| --------- | ------------------ |
| No Eigen  | 1.24               |
| Eigen     | 0.65               |
| **Ratio** | **1.9x**           |

### What Eigen optimizes

Icing's `embedding-scorer.cc` has two code paths:

- **Scalar** (`ICING_DISABLE_EIGEN`): Simple `for` loop computing dot product
  element-by-element
- **Eigen**: Uses `Eigen::Map<VectorXf>` with hardware SIMD (SSE/AVX on x86) for
  vectorized `.dot()` and `.norm()` operations

---

## Changes Made

1. **Added Eigen dependency**: `git_repository` in `MODULE.bazel` from Android's
   mirror (`https://android.googlesource.com/platform/external/eigen/`)
2. **Removed `-DICING_DISABLE_EIGEN`** from `third_party/icing/BUILD.bazel`
3. **Added `@eigen` to Icing deps**
4. **Enabled runtime flag**: Set `enable_eigen_embedding_scoring = true` in
   `IcingSearchEngineOptions`

## Recommendation

**Enable Eigen.** The ~1.9x embedding search speedup at 64k embeddings (79ms →
42ms) is a meaningful improvement with no functional cost. The Eigen library is
header-only, adds zero runtime dependencies, and is already used by Android's
Icing in production.

Ensure production builds use `-c opt` or equivalent optimization flags.

---

## Methodology

1. Populate Icing database with N embeddings (768D, random values)
2. Call `optimize()` to compact the database
3. Warmup: Run one search query (discarded)
4. Measure: Run 20 embedding search queries, recording wall-clock time
5. Report min/avg/max across iterations
6. Repeat with Eigen enabled vs disabled (compile-time toggle via
   `ICING_DISABLE_EIGEN`)
7. All comparison runs use `bazel run -c opt` for production-realistic
   optimization

Benchmark source:
[eigen_benchmark.rs](file:///usr/local/google/home/yongheng/oak/oak_private_memory/analysis/eigen_benchmark.rs)
