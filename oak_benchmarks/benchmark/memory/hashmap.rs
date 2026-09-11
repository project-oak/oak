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
//! Three modes whose differences isolate the allocator's contribution. Insert
//! works on a map with no reserved capacity, so each insert allocates a value
//! and the table periodically grows and rehashes. Lookup queries a fully
//! populated map and allocates nothing, leaving hashing plus a dependent read.
//! Churn evicts a resident entry and inserts one that has never been in the
//! map, so the map holds its size while its contents turn over: one free and
//! one allocation of the same size per iteration, on top of the table work of
//! a deletion and an insertion.
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

/// Bytes one entry occupies, to within the factor documented below.
///
/// A bucket holds the key and the `Vec` header inline, so the value's pointer,
/// length and capacity are table rather than value, and one control byte sits
/// alongside. `capacity_to_buckets` allocates `next_power_of_two(ceil(8n/7))`
/// buckets for `n` entries, so the ratio runs from 8/7, reached at
/// `n = 7 * 2^k` when the table is one insert short of doubling, to just under
/// 16/7 straight after. The factor below is the low end, so the bucket term is
/// a lower bound and can be twice this; at a 64-byte value that is 101 bytes
/// per entry rather than 139, since only the bucket term moves.
///
/// Outside it: the allocator's rounding on the value block, which `rlsf` and
/// glibc do differently, and the `keys` array, another 8 bytes per entry that
/// the lookup mode reads at random every iteration.
///
/// <https://docs.rs/hashbrown/0.14.5/src/hashbrown/raw/mod.rs.html>
fn bytes_per_entry(value_size: usize) -> usize {
    let bucket = size_of::<(u64, Vec<u8>)>() + 1;
    bucket * 8 / 7 + value_size
}

/// How many keys the post-run checksums fold.
///
/// The keys are a deterministic function of the seed, so a prefix witnesses
/// the whole array: if two platforms agree here they agree everywhere.
const CHECKSUM_SAMPLE_KEYS: usize = 1024;

/// Advance `rng` one step and return the slot it selects.
#[inline(always)]
fn next_slot(rng: &mut u64, len: usize) -> usize {
    *rng = rng.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
    (*rng >> 16) as usize % len
}

/// Advance `rng` one step and return the key it selects.
///
/// The warmup and the measured loop share this so that both walk the same
/// sequence from a given starting state, and so that the state left behind
/// afterwards identifies the walk that was taken.
#[inline(always)]
fn next_key(rng: &mut u64, keys: &[u64]) -> u64 {
    keys[next_slot(rng, keys.len())]
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
    /// Evict a resident entry and insert a new one, at constant map size.
    Churn,
}

/// HashMap benchmark.
pub struct HashMapBenchmark {
    /// Populated map, used by the lookup and churn modes.
    populated: BenchMap,
    /// Pre-generated keys, one per entry of [`Self::populated`].
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
    ///
    /// This sizes the map the lookup and churn modes run against. The insert
    /// mode builds its own map inside the timed loop, so its footprint follows
    /// the iteration count; see [`Self::run_insert`].
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
            HashMapMode::Churn => self.run_churn::<T>(iterations, warmup_iterations),
        }
    }

    /// Measure insertion into an empty map with no reserved capacity.
    ///
    /// Table growth and rehashing are deliberately included: they are a real
    /// part of insertion cost, and are where the enclave's allocator is
    /// expected to differ from glibc's. That allocator is `rlsf`'s TLSF behind
    /// a spinlock (`oak_enclave_runtime_support::heap`), so the difference to
    /// expect is the lock and the coalescing, not a missing free list.
    ///
    /// Keys come from the generator a step at a time, the way
    /// [`Self::run_churn`] draws its fresh ones, rather than from
    /// [`Self::keys`]. Indexing that array modulo its length, which is what
    /// this used to do, turned every iteration past the entry count into an
    /// overwrite of a key already present, and an overwrite neither grows the
    /// table nor rehashes it.
    ///
    /// The map is what the timed loop builds, so its footprint follows
    /// `--iterations`. `--working-set-size` sizes the pre-built map that the
    /// other two modes run against, and this mode does not read it.
    fn run_insert<T: BenchmarkTimer>(
        &self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        let n = iterations as usize;

        // Warmup inserts into a throwaway map, then drops it, so the measured
        // run starts from a genuinely empty, unreserved table but from an
        // allocator that has already reached steady state. The measured loop
        // is offset past the warmup's key stream for the reason
        // [`MEASURED_SEED_OFFSET`] gives.
        {
            let mut scratch = BenchMap::with_hasher(HASH_STATE);
            let mut key = self.seed;
            for _ in 0..warmup_iterations {
                key = key.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
                scratch.insert(key, self.value_template.clone());
            }
            core::hint::black_box(&scratch);
        }

        let mut map = BenchMap::with_hasher(HASH_STATE);
        let mut key = self.seed ^ MEASURED_SEED_OFFSET;

        let timer = T::start();

        for _ in 0..n {
            key = key.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
            map.insert(core::hint::black_box(key), self.value_template.clone());
        }

        let timing = timer.stop();

        // The generator has full period, so every key was distinct and the map
        // must hold one entry per iteration. Checked for the same reason
        // `run_lookup` checks its hit count and `run_churn` its removal count.
        if map.len() != n {
            return Err(BenchmarkError::Generic);
        }

        // Replay the first keys outside the timed region and read each one
        // back, which is what forces the map to have been materialised. A miss
        // is an error rather than a skipped fold, the way `run_churn` treats
        // one: a checksum that quietly folds fewer keys than it was asked to
        // would still match across platforms.
        let mut checksum = checksum_update(CHECKSUM_INIT, &(map.len() as u64).to_le_bytes());
        let mut key = self.seed ^ MEASURED_SEED_OFFSET;
        for _ in 0..n.min(CHECKSUM_SAMPLE_KEYS) {
            key = key.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
            let value = map.get(&key).ok_or(BenchmarkError::Generic)?;
            checksum = checksum_update(checksum, &key.to_le_bytes());
            checksum = checksum_update(checksum, &value[..1]);
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

    /// Measure deletion paired with insertion, at constant map size.
    ///
    /// Each iteration evicts a randomly chosen resident entry and inserts a
    /// key that has never been in the map, so the map holds the same number
    /// of entries throughout while its contents turn over. That is the
    /// workload the insert mode cannot reach: insert only ever grows the
    /// heap, so it never exercises the allocator's free path, and it puts
    /// every key in a bucket that was empty.
    ///
    /// Evicting one key and inserting a different one is what makes this
    /// churn rather than replacement. Re-inserting the key just removed would
    /// return it to the same bucket with the same tag, leaving hashbrown's
    /// spare capacity untouched and never triggering the periodic rehash that
    /// clears deleted slots. Inserting an unrelated key consumes spare
    /// capacity and so pays for that rehash on the schedule a real workload
    /// would.
    ///
    /// New keys continue the generator that produced [`Self::keys`]. The LCG
    /// has full period, so a key it has not yet emitted cannot already be in
    /// the map, and the eviction cannot miss.
    ///
    /// Slots are chosen pseudo-randomly, the same way the lookup mode chooses
    /// keys. Walking them in order would be much cheaper than it looks: the
    /// values are allocated in key order, so a sequential walk reads the value
    /// heap in ascending address order and the prefetcher covers it, which is
    /// exactly the cost this is supposed to be paying.
    ///
    /// The map is rebuilt afterwards, outside the timed region. Churn is the
    /// only mode that leaves the map holding different keys, and the service
    /// caches one instance across requests, so without the rebuild a later
    /// lookup would report a different checksum than the same request would
    /// in a fresh process.
    fn run_churn<T: BenchmarkTimer>(
        &mut self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        // Warm up by removing and re-inserting the same key. That reaches the
        // allocator's steady state, which is the point of warming this mode,
        // without changing which keys are resident: the measured phase then
        // starts from the same map whatever the warmup count, as it must.
        let mut rng = self.seed;
        for _ in 0..warmup_iterations {
            let key = next_key(&mut rng, &self.keys);
            self.populated.remove(&key);
            self.populated.insert(key, self.value_template.clone());
        }

        // Offset the generator past the warmup's walk, so the measured loop
        // does not begin by revisiting slots it has just left in cache. The
        // offset is a function of the seed alone.
        let mut rng = self.seed ^ MEASURED_SEED_OFFSET;
        // The next key the construction generator would have produced.
        let mut fresh = self.keys[self.keys.len() - 1];
        let mut removed = 0u64;

        let timer = T::start();

        for _ in 0..iterations {
            let slot = next_slot(&mut rng, self.keys.len());
            let old = core::hint::black_box(self.keys[slot]);
            fresh = fresh.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
            // The evicted value drops at the end of this statement, before the
            // insert below allocates. Free then allocate is the order an
            // update takes, and it is the order that lets an allocator with a
            // free list hand the same block straight back.
            removed += self.populated.remove(&old).is_some() as u64;
            self.populated.insert(fresh, self.value_template.clone());
            self.keys[slot] = fresh;
        }

        let timing = timer.stop();

        // Every key evicted was resident, so a miss means the map has lost
        // entries and the timing is not measuring a constant-size map.
        if removed != iterations as u64 {
            return Err(BenchmarkError::Generic);
        }

        // Checksum after the clock stops. The key array now records which slot
        // received which new key, so it is a fingerprint of the walk rather
        // than of the request: a loop that did not run, or ran a different
        // number of times, or visited slots in another order, cannot produce
        // it. The two generator states pin the walk exactly.
        let mut checksum = CHECKSUM_INIT;
        checksum = checksum_update(checksum, &(self.populated.len() as u64).to_le_bytes());
        checksum = checksum_update(checksum, &removed.to_le_bytes());
        checksum = checksum_update(checksum, &rng.to_le_bytes());
        checksum = checksum_update(checksum, &fresh.to_le_bytes());
        for &key in self.keys.iter().take(CHECKSUM_SAMPLE_KEYS) {
            // Resident by construction; if not, the map and the key array have
            // diverged and neither the checksum nor the timing means anything.
            self.populated.get(&key).ok_or(BenchmarkError::Generic)?;
            checksum = checksum_update(checksum, &key.to_le_bytes());
        }

        let bytes_processed = iterations as u64 * (8 + self.value_template.len() as u64);
        let working_set =
            self.populated.len() as u64 * bytes_per_entry(self.value_template.len()) as u64;

        // Drop the churned map before building the replacement, so the peak
        // footprint stays at one map rather than two.
        let (entries, value_size, seed) = (self.num_entries, self.value_template.len(), self.seed);
        self.populated = BenchMap::with_hasher(HASH_STATE);
        self.keys = Vec::new();
        *self = Self::new(entries, value_size, seed)?;

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
    fn insert_grows_the_map_past_the_entry_count() {
        // Iterations beyond the entry count used to wrap around the key array
        // and overwrite entries already present, so the table stopped growing
        // and the working set stopped following the iteration count.
        let mut bench = HashMapBenchmark::with_defaults(64, 7).unwrap();
        let small = bench.run::<NativeTimer>(HashMapMode::Insert, 64, 0).unwrap();
        let large = bench.run::<NativeTimer>(HashMapMode::Insert, 8_192, 0).unwrap();
        assert_eq!(large.working_set_size, 128 * small.working_set_size);
    }

    #[test]
    fn churn_holds_the_map_at_a_constant_size() {
        // Every eviction must hit. `run_churn` returns `Generic` if one misses,
        // which is what would happen if a new key collided with a resident one
        // and shrank the map. More iterations than entries, so slots are
        // revisited and later evictions remove keys churn itself inserted.
        let mut bench = HashMapBenchmark::with_defaults(2_000, 7).unwrap();
        let r = bench.run::<NativeTimer>(HashMapMode::Churn, 5_000, 0).unwrap();
        assert_eq!(r.iterations_completed, 5_000);
        assert_eq!(bench.populated.len(), 2_000);
    }

    #[test]
    fn churn_checksum_witnesses_the_loop() {
        // The failure this guards against is a checksum that is a function of
        // the request alone: it would match across platforms whatever the loop
        // did, or did not do.
        let mut bench = HashMapBenchmark::with_defaults(2_000, 7).unwrap();
        let short = bench.run::<NativeTimer>(HashMapMode::Churn, 1_000, 0).unwrap().checksum;
        let long = bench.run::<NativeTimer>(HashMapMode::Churn, 2_000, 0).unwrap().checksum;
        assert_ne!(short, long);
    }

    #[test]
    fn churn_is_repeatable() {
        // Churn mutates the map it measures, so a second run has to find the
        // map in the state the first one started from.
        let mut bench = HashMapBenchmark::with_defaults(2_000, 7).unwrap();
        let a = bench.run::<NativeTimer>(HashMapMode::Churn, 3_000, 0).unwrap().checksum;
        let b = bench.run::<NativeTimer>(HashMapMode::Churn, 3_000, 0).unwrap().checksum;
        assert_eq!(a, b);
    }

    #[test]
    fn churn_warmup_does_not_change_measured_checksum() {
        let mut a = HashMapBenchmark::with_defaults(2_000, 8).unwrap();
        let ra = a.run::<NativeTimer>(HashMapMode::Churn, 3_000, 0).unwrap();
        let mut b = HashMapBenchmark::with_defaults(2_000, 8).unwrap();
        let rb = b.run::<NativeTimer>(HashMapMode::Churn, 3_000, 5_000).unwrap();
        assert_eq!(ra.checksum, rb.checksum);
    }

    #[test]
    fn churn_leaves_the_map_usable_for_lookups() {
        // Every value is a fresh clone of the template, so a lookup after a
        // churn has to find the same bytes it would have found before.
        let mut bench = HashMapBenchmark::with_defaults(2_000, 9).unwrap();
        let before = bench.run::<NativeTimer>(HashMapMode::Lookup, 4_000, 0).unwrap().checksum;
        bench.run::<NativeTimer>(HashMapMode::Churn, 3_000, 0).unwrap();
        let after = bench.run::<NativeTimer>(HashMapMode::Lookup, 4_000, 0).unwrap().checksum;
        assert_eq!(before, after);
    }

    #[test]
    fn entries_for_working_set_scales() {
        // 33-byte bucket scaled by 8/7, truncated, plus a 64-byte value. The
        // literal is here rather than derived so that changing bytes_per_entry
        // has to show up in this diff.
        assert_eq!(bytes_per_entry(64), 101);
        assert_eq!(HashMapBenchmark::entries_for_working_set(1024 * 1024 * 1024, 64), 10_631_107);
    }

    #[test]
    fn bytes_per_entry_counts_the_vec_header() {
        // The header lives in the bucket, not in the value's allocation, so a
        // 64-byte value costs more than 64 bytes plus a key. Understating it
        // understates every reported working set.
        assert!(bytes_per_entry(64) > 64 + size_of::<u64>() + size_of::<Vec<u8>>());
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_map_clear() {
        let mut benchmark = HashMapBenchmark::with_defaults(10u32, 42u64);

        // Initially empty
        assert!(benchmark.map.is_empty());

        // Populate the map
        benchmark.populate();
        assert_eq!(benchmark.map.len(), 10);

        // Clear the map
        benchmark.map_clear();

        // Verify it's empty
        assert!(benchmark.map.is_empty());
    }
}
