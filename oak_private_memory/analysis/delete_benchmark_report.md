# Batch Delete Benchmark Report

Measures the latency and scaling behaviour of
[`IcingMetaDatabase::delete_memories`](../database/icing.rs) (reached via
[`Database::delete_memories`](../database/database.rs)).

Reproduce with:

```bash
nix develop --command bazel run -c opt //analysis:delete_benchmark
```

Config: `repetitions=3`, `embedding_size=8`, one LLM view per memory, all
memories seeded with a far-future expiration (i.e. all "non-expired", matching a
load test). Database is `optimize()`d after seeding so each run starts from a
compacted state. Machine: local dev workstation, `-c opt` build.

## Experiment A — delete ALL N in a single call

|    N | mean (ms) | per-mem (µs) | ratio vs prev | mem/sec |
| ---: | --------: | -----------: | ------------: | ------: |
|  100 |      9.98 |         99.8 |             – |   10019 |
|  200 |     23.46 |        117.3 |         2.35× |    8525 |
|  400 |     58.88 |        147.2 |         2.51× |    6793 |
|  800 |    160.02 |        200.0 |         2.72× |    4999 |
| 1600 |    481.72 |        301.1 |         3.01× |    3321 |

The doubling ratio climbs from 2.35× toward 4× and the **per-memory cost
triples** (100 → 301 µs) as N grows. That is **super-linear**, sitting between
O(N) and O(N²).

A least-squares fit of the total time is:

```text
total(N) ≈ 86 µs · N  +  0.134 µs · N²
```

The quadratic term overtakes the linear term at **N ≈ 650**, so above a few
hundred memories the operation is effectively quadratic. Throughput collapses
from ~10k memories/s at N=100 to ~3.3k at N=1600.

## Experiment B — delete a FIXED 50 from a corpus of size N (decisive test)

|    N | mean (ms) | per-delete (µs) | ratio vs prev |
| ---: | --------: | --------------: | ------------: |
|  100 |     5.132 |           102.6 |             – |
|  200 |     6.177 |           123.5 |         1.20× |
|  400 |     8.029 |           160.6 |         1.30× |
|  800 |    11.501 |           230.0 |         1.43× |
| 1600 |    18.563 |           371.3 |         1.61× |

Deleting the **same 50 memories** costs **3.6× more** on a 1600-doc corpus than
on a 100-doc corpus. Fit:

```text
per-delete(N) ≈ 85 µs  +  0.18 µs · N
```

Each individual delete is **O(N) in the resident corpus size**. Since delete-all
performs N such deletes, delete-all is **O(N²)** — exactly the shape seen in
Experiment A.

## Interpretation

- **The `delete_memories` batch API is not batched internally.** It loops
  per-id, and each id triggers two Icing searches
  ([`get_blob_id_by_memory_id`](../database/icing.rs) and
  [`get_view_ids_by_memory_id`](../database/icing.rs)) plus (V+1) soft-deletes.
  A single call with N ids costs the same as N single-id calls.

- **The O(N) per-delete cost is caused by the lookup searches, not by
  soft-delete accumulation.** In Experiment B the corpus is freshly
  `optimize()`d and only ~50 documents are soft-deleted during the run (a tiny,
  constant fraction of N), yet per-delete cost still grows linearly with N. The
  variable that drives cost is the number of **live** documents, which is
  consistent with each lookup search scanning the whole corpus. This supports
  the hypothesis that the `expiration_timestamp > now` numeric-range clause in
  [`build_non_expired_query_str`](../database/icing.rs) expands to a candidate
  set of every non-expired document per lookup, and argues against soft-delete
  accumulation being the primary cause.

- **The ~85 µs constant** is the fixed per-op overhead (two searches + the
  DocumentStore deletes) at small corpus size.

## Results after Fix 1 (validated)

Fix 1 was implemented: the delete path now resolves `blob_id` with a query that
omits the `expiration_timestamp` numeric-range clause (a memory id is unique, so
the `__memory_id` term alone identifies the document, and deletion should
proceed regardless of expiry). Read/upsert paths keep the expiration filter.

Re-running the same benchmark:

Experiment A (delete all N):

|    N | before mean (ms) | after mean (ms) | speedup | after per-mem (µs) | after ratio |
| ---: | ---------------: | --------------: | ------: | -----------------: | ----------: |
|  100 |             9.98 |            6.79 |    1.5× |               67.9 |           – |
|  200 |            23.46 |           13.66 |    1.7× |               68.3 |       2.01× |
|  400 |            58.88 |           28.42 |    2.1× |               71.1 |       2.08× |
|  800 |           160.02 |           56.20 |    2.8× |               70.3 |       1.98× |
| 1600 |           481.72 |          110.30 |    4.4× |               68.9 |       1.96× |

Experiment B (delete a fixed 50 from a corpus of size N):

|    N | before per-delete (µs) | after per-delete (µs) | speedup |
| ---: | ---------------------: | --------------------: | ------: |
|  100 |                  102.6 |                  68.7 |    1.5× |
|  200 |                  123.5 |                  70.8 |    1.7× |
|  400 |                  160.6 |                  73.3 |    2.2× |
|  800 |                  230.0 |                  72.6 |    3.2× |
| 1600 |                  371.3 |                  71.0 |    5.2× |

This **confirmed the root cause**: the expiration numeric-range clause was the
source of the O(N) per-lookup scan. Fix 1 was a diagnostic step; the shipped
delete path instead uses Fix 2 below (a point lookup), which subsumes it and is
also O(1) in corpus size.

## Results after Fix 2 (shipped)

Fix 2 binds Icing's `Get` in the FFI layer (`src/icing`) and resolves `blob_id`
on the delete path with a direct `Get(NAMESPACE_NAME, memory_id)` point lookup
(`IcingMetaDatabase::get_blob_id_by_memory_id_point_lookup`). This avoids a
query entirely for the blob-id resolution — O(1) in corpus size and cheaper than
the Fix 1 term search.

Three-way comparison at the extremes:

Experiment A (delete all N), per-memory latency (µs):

|    N | baseline | Fix 1 | Fix 2 |
| ---: | -------: | ----: | ----: |
|  100 |     99.8 |  67.9 |  51.2 |
| 1600 |    301.1 |  68.9 |  50.4 |

Experiment A (delete all N), total latency and throughput:

|    N | baseline (ms) | Fix 2 (ms) | total speedup | Fix 2 mem/sec |
| ---: | ------------: | ---------: | ------------: | ------------: |
|  100 |          9.98 |       5.12 |          1.9× |         19520 |
| 1600 |        481.72 |      80.60 |          6.0× |         19851 |

Experiment B (delete a fixed 50 from a corpus of size N), per-delete (µs):

|    N | baseline | Fix 1 | Fix 2 |
| ---: | -------: | ----: | ----: |
|  100 |    102.6 |  68.7 |  52.0 |
| 1600 |    371.3 |  71.0 |  53.5 |

- Both experiments stay **linear / flat** and Fix 2 lowers the per-delete
  constant by a further ~26% vs Fix 1 (~51 µs vs ~69 µs) by replacing one of the
  two per-delete searches with an O(1) point lookup.
- End to end at N=1600, delete-all is **6.0× faster** than baseline (481.7 ms →
  80.6 ms) and throughput rises from ~3.3k to ~19.9k memories/s.
- The residual ~51 µs per delete is now dominated by the view-id lookup search
  plus the (V+1) DocumentStore deletes — the target of Fix 3.

## Remaining fixes (in expected impact order)

1. ✅ **Done (diagnostic) — drop the expiration clause from the delete-lookup
   query.** Confirmed the O(N) term came from the `expiration_timestamp`
   numeric-range predicate. Superseded on the delete path by Fix 2.
2. ✅ **Done (shipped) — resolve `blob_id` with a point lookup.** Bound Icing's
   `Get` in the FFI bridge and used it in
   `get_blob_id_by_memory_id_point_lookup`. O(1) in corpus size; removes a
   search from every delete.
3. **Batch the view lookup / deletes** rather than one search per id. Would cut
   into the remaining ~51 µs constant.
4. **`optimize()` periodically** for very large delete batches so soft-deleted
   docs stop inflating later work (secondary effect at these scales).
