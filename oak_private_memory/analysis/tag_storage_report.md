# Icing Database Tag Storage Analysis

This report analyzes the storage impact of saving tags within the Icing search
database, specifically focusing on the overhead of individual tags, the effect
of tag deduplication (reused vs. unique tags), and how tag length influences
overall database size.

## 1. Storage Overhead of a Single Tag

When adding tags to a single memory, we observe a small, relatively fixed
overhead per tag assignment.

- **0 Tags:** ~135 bytes overhead per memory.
- **1 Tag (Length 10):** ~143 bytes overhead per memory.

**Conclusion:** A single short tag adds roughly **~8 bytes** of storage overhead
to a memory.

## 2. Impact of Tag Reuse (Unique vs. Identical Tags)

To understand if Icing deduplicates tags across different memories, we analyzed
the storage impact across 10 memories, comparing completely unique tags against
identical (reused) tags.

- **0 Tags:** 1,325 bytes (Baseline for 10 memories)
- **10 Unique Tags per memory (Length 10):** 1,848 bytes (+523 bytes over
  baseline)
- **10 Identical Tags per memory (Length 10):** 1,685 bytes (+360 bytes over
  baseline)

**Conclusion:** Storing the **same tags** across multiple memories is somewhat
more storage-efficient than storing completely unique tags. This suggests that
while Icing's search index (lexicon) benefits from deduplication, the underlying
document store still retains individual copies of the tags.

## 3. Relationship Between Tag Length and Storage Size

To determine how the length of the tag string impacts storage, we tested various
tag lengths using high-entropy (random hex) strings to prevent unrealistic
compression ratios.

The following data represents **10 Memories** with **10 Tags per memory** (100
total tag assignments):

| Tag Length (Characters) | Total Database Increase | Storage Cost for 100 Tags | Average Storage per Tag |
| :---------------------- | :---------------------- | :------------------------ | :---------------------- |
| **0** (Baseline)        | 1,325 bytes             | 0 bytes                   | 0 bytes                 |
| **10**                  | 1,848 bytes             | 523 bytes                 | ~5.2 bytes              |
| **50**                  | 4,169 bytes             | 2,844 bytes               | ~28.4 bytes             |
| **100**                 | 6,974 bytes             | 5,649 bytes               | ~56.5 bytes             |
| **500**                 | 30,378 bytes            | 29,053 bytes              | ~290.5 bytes            |
| **1000**                | 60,127 bytes            | 58,802 bytes              | ~588.0 bytes            |

**Conclusion:** The relationship between tag length and storage size is **highly
linear**.

## 4. Real-World Simulation: Pooled Tags

In a realistic scenario, a user might have a fixed pool of tags (e.g., 20 unique
tags) and apply a subset of them (e.g., 10 tags) to many different memories
(e.g., 100 memories).

This results in exactly 1,000 tag assignments, heavily reusing the 20 unique
strings.

| Tag Length             | Total DB Size Increase | Tag Storage Overhead | Overhead per Memory | Overhead per Tag Assignment |
| :--------------------- | :--------------------- | :------------------- | :------------------ | :-------------------------- |
| **0 chars (Baseline)** | 13,293 bytes           | 0 bytes              | 0 bytes             | 0 bytes                     |
| **10 characters**      | 17,329 bytes           | 4,036 bytes          | ~40.3 bytes         | ~4.0 bytes                  |
| **20 characters**      | 23,430 bytes           | 10,137 bytes         | ~101 bytes          | ~10.1 bytes                 |
| **50 characters**      | 40,205 bytes           | 26,912 bytes         | ~269 bytes          | ~26.9 bytes                 |

## Final Summary

1. **Linear Scaling:** The storage cost of tags scales linearly with the total
   number of characters in the tags assigned to a memory.
2. **Compression Ratio:** Because Icing uses Snappy compression on its
   underlying document store, a 100-character tag does not consume exactly 100
   bytes of raw storage. Depending on the entropy of the characters, it
   generally consumes roughly **0.4 to 0.6 bytes of storage per character**.
3. **Deduplication Limits:** Even if you use the exact same tags across multiple
   memories, Icing does not perfectly deduplicate the raw string contents within
   the `DocumentStore`. You still pay a relatively linear cost per assignment.
   The primary storage savings from reusing tags comes from index (lexicon)
   deduplication and Snappy's block-level compression, but the linear cost of
   `~0.4 - 0.6 bytes per char` remains consistent.
