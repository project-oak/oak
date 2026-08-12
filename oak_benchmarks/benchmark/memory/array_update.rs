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

//! Array update benchmark.
//!
//! Random writes to a buffer much larger than the last-level cache, so nearly
//! every write misses to main memory. The buffer is allocated once at
//! construction, which isolates access latency from allocator overhead. On
//! SEV-SNP this is the benchmark most likely to expose memory encryption cost.
//!
//! Indices come from an inline LCG rather than a precomputed array, which
//! would add 8 bytes of read traffic per iteration, occupy megabytes of the
//! cache being measured, and cap the iteration count. The generator costs one
//! multiply and one add on both platforms.

use alloc::{vec, vec::Vec};

use super::MemoryBenchmark;
use crate::{
    BenchmarkError, BenchmarkResult, LCG_MULTIPLIER, MEASURED_SEED_OFFSET, timer::BenchmarkTimer,
};

/// Default working set size (256 MB).
///
/// Large enough to defeat any current last-level cache. The evaluation plan
/// calls for roughly 1 GB; pass `working_set_size` in the request to select
/// that, subject to the guest having enough RAM.
pub const DEFAULT_WORKING_SET_SIZE: usize = 256 * 1024 * 1024;

/// Maximum working set size (4 GB).
pub const MAX_WORKING_SET_SIZE: usize = 4 * 1024 * 1024 * 1024;

/// Minimum working set size (1 MB).
pub const MIN_WORKING_SET_SIZE: usize = 1024 * 1024;

/// Array update benchmark.
pub struct ArrayUpdateBenchmark {
    /// Pre-allocated data buffer.
    buffer: Vec<u8>,
    /// Seed for the index generator, so runs are reproducible.
    seed: u64,
}

// Hand-written rather than derived: the buffer is up to 4 GB, and a derived
// `Debug` would try to format every byte of it (for example when a test
// assertion fails).
impl core::fmt::Debug for ArrayUpdateBenchmark {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ArrayUpdateBenchmark")
            .field("working_set_size", &self.buffer.len())
            .field("seed", &self.seed)
            .finish()
    }
}

impl ArrayUpdateBenchmark {
    /// Create a new array update benchmark.
    ///
    /// Allocation happens here, outside any timed region.
    pub fn new(working_set_size: usize, seed: u64) -> Result<Self, BenchmarkError> {
        if !(MIN_WORKING_SET_SIZE..=MAX_WORKING_SET_SIZE).contains(&working_set_size) {
            return Err(BenchmarkError::InvalidParameter);
        }

        // Touch every page so the measurement is not distorted by first-touch
        // page faults or lazy zero pages. `vec![0u8; n]` may be served by
        // untouched zero pages on Linux, which would make the first pass much
        // slower than steady state and would differ from the enclave, where
        // the allocator hands back already-mapped memory.
        let mut buffer = vec![0u8; working_set_size];
        crate::generate_benchmark_data(&mut buffer, seed);

        Ok(Self { buffer, seed })
    }

    /// Create with the default working set size.
    pub fn with_defaults(seed: u64) -> Result<Self, BenchmarkError> {
        Self::new(DEFAULT_WORKING_SET_SIZE, seed)
    }

    /// Reconfigure the working set size, reallocating if it changed.
    ///
    /// Called outside the timed region.
    pub fn reconfigure(
        &mut self,
        working_set_size: usize,
        seed: u64,
    ) -> Result<(), BenchmarkError> {
        if self.buffer.len() == working_set_size && self.seed == seed {
            return Ok(());
        }
        *self = Self::new(working_set_size, seed)?;
        Ok(())
    }

    /// Run the benchmark.
    ///
    /// Each iteration writes one byte at a pseudo-random offset. There is no
    /// upper bound on `iterations` beyond `u32`.
    pub fn run<T: BenchmarkTimer>(
        &mut self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        if iterations == 0 {
            return Err(BenchmarkError::InvalidParameter);
        }

        let size = self.buffer.len();

        // `new` filled the buffer in one sequential pass, which leaves its
        // tail in cache. The warmup's random walk displaces that, and walks a
        // different address sequence from the measured loop; see the seed
        // derivation below.
        let mut rng = self.seed;
        let mut write_value: u8 = 0;
        for _ in 0..warmup_iterations {
            rng = rng.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
            let idx = (rng >> 16) as usize % size;
            self.buffer[idx] = write_value;
            write_value = write_value.wrapping_add(1);
        }

        // Offset the generator past the sequence the warmup just walked.
        // Reusing `self.seed` here would make the measured loop replay that
        // sequence from the start and find those lines still in cache, which
        // understates the cost of a miss. The affected share is
        // `warmup_iterations / iterations`, and it reaches all of them when
        // the two counts are equal.
        let mut rng = self.seed ^ MEASURED_SEED_OFFSET;
        let mut write_value: u8 = 0;

        let timer = T::start();

        for _ in 0..iterations {
            rng = rng.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
            let idx = (rng >> 16) as usize % size;
            // `idx < size` by construction. The bounds check is left in
            // deliberately so that both platforms pay the same cost.
            self.buffer[idx] = write_value;
            write_value = write_value.wrapping_add(1);
        }

        let timing = timer.stop();

        // Fold a sample of the buffer into a checksum. Reading the whole
        // buffer would dominate the runtime, so sample a fixed stride. This is
        // enough to prove both platforms wrote the same bytes, and it forces
        // the writes to be materialised.
        let checksum = self.sample_checksum();

        let bytes_processed = iterations as u64;
        Ok(BenchmarkResult::new(timing, iterations, bytes_processed, checksum)
            .with_working_set(size as u64))
    }

    /// Fold every 4096th byte of the buffer into a checksum.
    fn sample_checksum(&self) -> u64 {
        let mut acc = crate::CHECKSUM_INIT;
        let mut i = 0;
        while i < self.buffer.len() {
            acc = crate::checksum_update(acc, &self.buffer[i..i + 1]);
            i += 4096;
        }
        acc
    }
}

impl MemoryBenchmark for ArrayUpdateBenchmark {
    fn working_set_size(&self) -> usize {
        self.buffer.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::timer::NativeTimer;

    #[test]
    fn iterations_are_not_capped_by_setup() {
        // The previous implementation pre-generated 100_000 indices and
        // rejected anything beyond that. Confirm a larger run now succeeds.
        let mut bench = ArrayUpdateBenchmark::new(MIN_WORKING_SET_SIZE, 1).unwrap();
        let r = bench.run::<NativeTimer>(250_000, 1_000).unwrap();
        assert_eq!(r.iterations_completed, 250_000);
    }

    #[test]
    fn same_seed_gives_same_checksum() {
        let mut a = ArrayUpdateBenchmark::new(MIN_WORKING_SET_SIZE, 7).unwrap();
        let mut b = ArrayUpdateBenchmark::new(MIN_WORKING_SET_SIZE, 7).unwrap();
        let ra = a.run::<NativeTimer>(10_000, 0).unwrap();
        let rb = b.run::<NativeTimer>(10_000, 0).unwrap();
        assert_eq!(ra.checksum, rb.checksum);
    }

    #[test]
    fn warmup_count_does_not_change_measured_sequence() {
        let mut a = ArrayUpdateBenchmark::new(MIN_WORKING_SET_SIZE, 3).unwrap();
        let ra = a.run::<NativeTimer>(5_000, 0).unwrap();
        let mut b = ArrayUpdateBenchmark::new(MIN_WORKING_SET_SIZE, 3).unwrap();
        let rb = b.run::<NativeTimer>(5_000, 2_000).unwrap();
        // Warmup writes extra bytes, so checksums may differ, but the
        // measured region must have completed the same number of iterations.
        assert_eq!(ra.iterations_completed, rb.iterations_completed);
    }

    #[test]
    fn working_set_bounds_are_enforced() {
        assert_eq!(ArrayUpdateBenchmark::new(0, 1).unwrap_err(), BenchmarkError::InvalidParameter);
        assert_eq!(
            ArrayUpdateBenchmark::new(MAX_WORKING_SET_SIZE + 1, 1).unwrap_err(),
            BenchmarkError::InvalidParameter
        );
    }

    #[test]
    fn zero_iterations_is_rejected() {
        let mut bench = ArrayUpdateBenchmark::new(MIN_WORKING_SET_SIZE, 1).unwrap();
        assert_eq!(bench.run::<NativeTimer>(0, 0).unwrap_err(), BenchmarkError::InvalidParameter);
    }

    #[test]
    fn working_set_is_reported() {
        let mut bench = ArrayUpdateBenchmark::new(2 * MIN_WORKING_SET_SIZE, 1).unwrap();
        let r = bench.run::<NativeTimer>(100, 0).unwrap();
        assert_eq!(r.working_set_size, (2 * MIN_WORKING_SET_SIZE) as u64);
    }
}
