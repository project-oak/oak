//
// Copyright 2026 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

//! HashMap benchmark.
//!
//! Two modes whose difference isolates the allocator's contribution. Insert
//! works on a map with no reserved capacity, so each insert allocates a value
//! and the table periodically grows and rehashes. Lookup queries a fully
//! populated map and allocates nothing, leaving hashing plus a dependent read.
//!
//! Both platforms use `hashbrown::HashMap` with the same explicit hasher.
//! `std::collections::HashMap` is also hashbrown, but with a randomly seeded
//! SipHash-1-3, which would give the two sides different hashing work and
//! different bucket layouts.
//!
//! Hashing happens inside the timed loop, so its cost is part of what the
//! lookup mode reports. That is minor against a lookup that misses to DRAM,
//! but it is the greater part of one that hits in cache, so the small end of
//! an entry count sweep says more about the hasher than about the memory
//! system.

use alloc::{vec, vec::Vec};

use ahash::RandomState;
use hashbrown::HashMap;

use super::MemoryBenchmark;
use crate::{
    BenchmarkError, BenchmarkResult, CHECKSUM_INIT, LCG_MULTIPLIER, MEASURED_SEED_OFFSET,
    checksum_update, timer::BenchmarkTimer,
};

/// Default value size (64 bytes).
pub const DEFAULT_VALUE_SIZE: usize = 64;

/// Maximum value size (4 KB).
pub const MAX_VALUE_SIZE: usize = 4096;

/// Upper bound on entries, to avoid an accidental multi-gigabyte allocation.
pub const MAX_NUM_ENTRIES: u32 = 40_000_000;

/// Approximate per-entry overhead of the hash table itself, on top of the key
/// and value bytes: one control byte plus the load factor headroom hashbrown
/// keeps. Used only to translate a requested working set size into an entry
/// count.
const TABLE_OVERHEAD_PER_ENTRY: usize = 24;

/// Bytes one entry occupies: the `u64` key, the value, and the table's own
/// per-entry overhead. Used for both the reported working set and the
/// translation from a requested working set back to an entry count, so the
/// two cannot disagree.
fn bytes_per_entry(value_size: usize) -> usize {
    size_of::<u64>() + value_size + TABLE_OVERHEAD_PER_ENTRY
}

/// How many keys the post-run checksums fold.
///
/// The keys are a deterministic function of the seed, so a prefix witnesses
/// the whole array: if two platforms agree here they agree everywhere.
const CHECKSUM_SAMPLE_KEYS: usize = 1024;

/// Advance `rng` one step and return the key it selects.
///
/// The warmup and the measured loop share this so that both walk the same
/// sequence from a given starting state, and so that the state left behind
/// afterwards identifies the walk that was taken.
#[inline(always)]
fn next_key(rng: &mut u64, keys: &[u64]) -> u64 {
    *rng = rng.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
    keys[(*rng >> 16) as usize % keys.len()]
}

/// The fixed hash keys both platforms use.
///
/// The default state will not do: `ahash` resolves with `runtime-rng` on the
/// host and with no features in the enclave, so the host would reseed in every
/// process. Differing keys mean differing probe sequences and collision
/// counts, and the two sides would stop measuring the same work. Matching the
/// backend matters as much, since `ahash` picks it from
/// `cfg(target_feature = "aes")`; that is what the matched-ISA build is for.
///
/// The values are the first four 64-bit words of pi's fractional part.
const HASH_STATE: RandomState = RandomState::with_seeds(
    0x243F_6A88_85A3_08D3,
    0x1319_8A2E_0370_7344,
    0xA409_3822_299F_31D0,
    0x082E_FA98_EC4E_6C89,
);

type BenchMap = HashMap<u64, Vec<u8>, RandomState>;

/// HashMap operation mode.
#[derive(Debug, Clone, Copy)]
pub enum HashMapMode {
    /// Insert new keys into an empty, unreserved map.
    Insert,
    /// Look up existing keys. Read-only.
    Lookup,
}

/// HashMap benchmark.
pub struct HashMapBenchmark {
    /// Populated map, used by the lookup mode.
    populated: BenchMap,
    /// Pre-generated keys.
    keys: Vec<u64>,
    /// Value template cloned on each insert.
    value_template: Vec<u8>,
    num_entries: u32,
    seed: u64,
}

// Hand-written rather than derived: the populated map and key vector can hold
// tens of millions of entries, and a derived `Debug` would try to format all
// of them (for example when a test assertion fails).
impl core::fmt::Debug for HashMapBenchmark {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("HashMapBenchmark")
            .field("num_entries", &self.num_entries)
            .field("value_size", &self.value_template.len())
            .field("populated_len", &self.populated.len())
            .field("seed", &self.seed)
            .finish()
    }
}

impl HashMapBenchmark {
    /// Create a new HashMap benchmark.
    ///
    /// Key generation and population happen here, outside any timed region.
    pub fn new(num_entries: u32, value_size: usize, seed: u64) -> Result<Self, BenchmarkError> {
        if num_entries == 0 || num_entries > MAX_NUM_ENTRIES {
            return Err(BenchmarkError::InvalidParameter);
        }
        if value_size == 0 || value_size > MAX_VALUE_SIZE {
            return Err(BenchmarkError::InvalidParameter);
        }
        let n = num_entries as usize;

        // Generate distinct keys. The LCG has full period over u64, so
        // successive outputs never repeat within a run.
        let mut keys = Vec::with_capacity(n);
        let mut rng_state = seed;
        for _ in 0..n {
            rng_state = rng_state.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
            keys.push(rng_state);
        }

        let mut value_template = vec![0u8; value_size];
        for (i, byte) in value_template.iter_mut().enumerate() {
            *byte = i as u8;
        }

        let mut populated = BenchMap::with_capacity_and_hasher(n, HASH_STATE);
        for &key in &keys {
            populated.insert(key, value_template.clone());
        }

        Ok(Self { populated, keys, value_template, num_entries, seed })
    }

    /// Create with the default value size.
    pub fn with_defaults(num_entries: u32, seed: u64) -> Result<Self, BenchmarkError> {
        Self::new(num_entries, DEFAULT_VALUE_SIZE, seed)
    }

    /// Translate a target working set size in bytes into an entry count.
    pub fn entries_for_working_set(working_set_bytes: u64, value_size: usize) -> u32 {
        let per_entry = bytes_per_entry(value_size) as u64;
        let entries = (working_set_bytes / per_entry).max(1);
        entries.min(MAX_NUM_ENTRIES as u64) as u32
    }

    /// Reconfigure for a new entry count or seed, rebuilding if needed.
    pub fn reconfigure(&mut self, num_entries: u32, seed: u64) -> Result<(), BenchmarkError> {
        if self.num_entries == num_entries && self.seed == seed {
            return Ok(());
        }
        *self = Self::new(num_entries, self.value_template.len(), seed)?;
        Ok(())
    }

    /// Run the benchmark for the requested mode.
    pub fn run<T: BenchmarkTimer>(
        &mut self,
        mode: HashMapMode,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        if iterations == 0 {
            return Err(BenchmarkError::InvalidParameter);
        }
        match mode {
            HashMapMode::Insert => self.run_insert::<T>(iterations, warmup_iterations),
            HashMapMode::Lookup => self.run_lookup::<T>(iterations, warmup_iterations),
        }
    }

    /// Measure insertion into an empty map with no reserved capacity.
    ///
    /// Table growth and rehashing are deliberately included: they are a real
    /// part of insertion cost and are exactly where a naive allocator is
    /// expected to differ from the Linux system allocator.
    fn run_insert<T: BenchmarkTimer>(
        &mut self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        let n = iterations as usize;

        // Warmup inserts into a throwaway map, then drops it. Using a separate
        // map keeps the measured run starting from a genuinely empty,
        // unreserved table, matching what the lookup path does (it never
        // benefits from the warmup having touched its data either).
        {
            let mut scratch = BenchMap::with_hasher(HASH_STATE);
            for i in 0..warmup_iterations as usize {
                let key = self.keys[i % self.keys.len()];
                scratch.insert(key, self.value_template.clone());
            }
            core::hint::black_box(&scratch);
        }

        let mut map = BenchMap::with_hasher(HASH_STATE);

        let timer = T::start();

        for i in 0..n {
            let key = self.keys[i % self.keys.len()];
            map.insert(core::hint::black_box(key), self.value_template.clone());
        }

        let timing = timer.stop();

        // Checksum over the resulting map proves the same entries were
        // inserted on both platforms, and forces the map to be materialised.
        let mut checksum = CHECKSUM_INIT;
        checksum = checksum_update(checksum, &(map.len() as u64).to_le_bytes());
        for i in 0..n.min(CHECKSUM_SAMPLE_KEYS) {
            let key = self.keys[i % self.keys.len()];
            if let Some(v) = map.get(&key) {
                checksum = checksum_update(checksum, &key.to_le_bytes());
                checksum = checksum_update(checksum, &v[..1]);
            }
        }

        let bytes_processed = iterations as u64 * (8 + self.value_template.len() as u64);
        let working_set = map.len() as u64 * bytes_per_entry(self.value_template.len()) as u64;
        Ok(BenchmarkResult::new(timing, iterations, bytes_processed, checksum)
            .with_working_set(working_set))
    }

    /// Measure lookups against the fully populated map.
    fn run_lookup<T: BenchmarkTimer>(
        &mut self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        // Warm up with a pseudo-random walk over the whole key space, the same
        // access pattern the measured phase uses. Sampling randomly rather
        // than sequentially avoids priming exactly the lines about to be
        // measured, which would understate miss cost.
        let mut rng = self.seed;
        let mut warm_hits = 0u64;
        for _ in 0..warmup_iterations {
            let key = next_key(&mut rng, &self.keys);
            if self.populated.get(&key).is_some() {
                warm_hits += 1;
            }
        }
        core::hint::black_box(warm_hits);

        // Offset the generator past the sequence the warmup just walked, so
        // the measured loop does not replay it and find those entries still
        // in cache. The offset stays a function of the seed alone, so the
        // warmup count does not change which keys are measured.
        let mut rng = self.seed ^ MEASURED_SEED_OFFSET;
        let mut hits = 0u64;

        let timer = T::start();

        for _ in 0..iterations {
            let key = next_key(&mut rng, &self.keys);
            if let Some(v) = self.populated.get(&core::hint::black_box(key)) {
                hits += 1;
                // Reads the value rather than just the reference, so the
                // lookup pays for reaching the entry's own allocation the way
                // a real one would. `black_box` is what keeps the load alive.
                core::hint::black_box(v[0]);
            }
        }

        let timing = timer.stop();

        // Every key queried is present, so a miss means the map was built
        // wrongly and the timing is not measuring what it claims to.
        if hits != iterations as u64 {
            return Err(BenchmarkError::Generic);
        }

        // Checksum after the clock stops. The generator state left by the loop
        // is a fingerprint of the whole walk, so any divergence in the keys
        // visited, or in how many, shows up here without folding anything per
        // iteration while the measurement is running. Every value stored is a
        // clone of one template, so the entries themselves carry nothing more
        // to witness than the keys do.
        let mut checksum = CHECKSUM_INIT;
        checksum = checksum_update(checksum, &hits.to_le_bytes());
        checksum = checksum_update(checksum, &rng.to_le_bytes());
        for &key in self.keys.iter().take(CHECKSUM_SAMPLE_KEYS) {
            checksum = checksum_update(checksum, &key.to_le_bytes());
        }

        let bytes_processed = iterations as u64 * (8 + self.value_template.len() as u64);
        let working_set =
            self.populated.len() as u64 * bytes_per_entry(self.value_template.len()) as u64;
        Ok(BenchmarkResult::new(timing, iterations, bytes_processed, checksum)
            .with_working_set(working_set))
    }
}

impl MemoryBenchmark for HashMapBenchmark {
    fn working_set_size(&self) -> usize {
        self.populated.len() * bytes_per_entry(self.value_template.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::timer::NativeTimer;

    #[test]
    fn lookup_finds_every_key() {
        let mut bench = HashMapBenchmark::with_defaults(5_000, 1).unwrap();
        let r = bench.run::<NativeTimer>(HashMapMode::Lookup, 20_000, 100).unwrap();
        assert_eq!(r.iterations_completed, 20_000);
    }

    #[test]
    fn iterations_may_exceed_entry_count() {
        // Previously both modes were capped at the pre-generated key count.
        let mut bench = HashMapBenchmark::with_defaults(1_000, 1).unwrap();
        let r = bench.run::<NativeTimer>(HashMapMode::Lookup, 50_000, 0).unwrap();
        assert_eq!(r.iterations_completed, 50_000);
        let r = bench.run::<NativeTimer>(HashMapMode::Insert, 5_000, 0).unwrap();
        assert_eq!(r.iterations_completed, 5_000);
    }

    #[test]
    fn same_seed_gives_same_checksum() {
        let mut a = HashMapBenchmark::with_defaults(2_000, 9).unwrap();
        let mut b = HashMapBenchmark::with_defaults(2_000, 9).unwrap();
        let ra = a.run::<NativeTimer>(HashMapMode::Lookup, 5_000, 0).unwrap();
        let rb = b.run::<NativeTimer>(HashMapMode::Lookup, 5_000, 0).unwrap();
        assert_eq!(ra.checksum, rb.checksum);
    }

    #[test]
    fn warmup_does_not_change_measured_checksum() {
        let mut a = HashMapBenchmark::with_defaults(2_000, 4).unwrap();
        let ra = a.run::<NativeTimer>(HashMapMode::Lookup, 3_000, 0).unwrap();
        let mut b = HashMapBenchmark::with_defaults(2_000, 4).unwrap();
        let rb = b.run::<NativeTimer>(HashMapMode::Lookup, 3_000, 5_000).unwrap();
        assert_eq!(ra.checksum, rb.checksum);
    }

    #[test]
    fn insert_is_repeatable() {
        let mut bench = HashMapBenchmark::with_defaults(2_000, 6).unwrap();
        let a = bench.run::<NativeTimer>(HashMapMode::Insert, 1_500, 0).unwrap().checksum;
        let b = bench.run::<NativeTimer>(HashMapMode::Insert, 1_500, 0).unwrap().checksum;
        assert_eq!(a, b);
    }

    #[test]
    fn entries_for_working_set_scales() {
        let e = HashMapBenchmark::entries_for_working_set(1024 * 1024 * 1024, 64);
        // 1 GB / (8 + 64 + 24) bytes per entry.
        assert!(e > 10_000_000, "expected >10M entries, got {e}");
    }

    #[test]
    fn invalid_parameters_are_rejected() {
        assert_eq!(
            HashMapBenchmark::with_defaults(0, 1).unwrap_err(),
            BenchmarkError::InvalidParameter
        );
        assert_eq!(HashMapBenchmark::new(10, 0, 1).unwrap_err(), BenchmarkError::InvalidParameter);
        let mut bench = HashMapBenchmark::with_defaults(10, 1).unwrap();
        assert_eq!(
            bench.run::<NativeTimer>(HashMapMode::Lookup, 0, 0).unwrap_err(),
            BenchmarkError::InvalidParameter
        );
    }
}
