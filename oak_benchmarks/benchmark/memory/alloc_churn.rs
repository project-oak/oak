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

//! Allocation churn benchmark.
//!
//! Each iteration allocates a buffer, touches it and frees it, targeting the
//! Restricted Kernel's allocator.
//!
//! Not `vec![0u8; n]`: that lowers to `alloc_zeroed`, which Linux can serve
//! from fresh anonymous pages that are already zero, while the Restricted
//! Kernel recycles memory and has to write the zeroes. That would measure the
//! memset rather than the allocator, so this allocates without zeroing and
//! writes a fixed number of bytes explicitly.
//!
//! Variable-size mode cycles through a schedule of sizes so that the
//! allocator cannot simply hand back the block just freed, which is what a
//! fixed size lets it do.

use alloc::vec::Vec;

use super::MemoryBenchmark;
use crate::{
    BenchmarkError, BenchmarkResult, CHECKSUM_INIT, checksum_with_witness, timer::BenchmarkTimer,
};

/// Default allocation size (4 KB).
pub const DEFAULT_ALLOC_SIZE: usize = 4096;

/// Maximum allocation size (1 MB).
pub const MAX_ALLOC_SIZE: usize = 1024 * 1024;

/// Number of bytes written into each allocation.
///
/// Enough to force the allocation to be materialised without making the
/// benchmark memory-bandwidth bound rather than allocator bound.
const TOUCH_BYTES: usize = 64;

/// Size schedule used in variable-size mode, in bytes.
///
/// Powers of four from 64 B up to [`MAX_ALLOC_SIZE`], so the schedule spans
/// the whole range a request may ask for. Cycling denies the allocator the
/// block it just freed, which a fixed size hands straight back; the gap
/// between the two modes is why both exist. It does not locate a cliff at any
/// one size class, since one mean over eight sizes hides that. Sweep fixed
/// sizes for that.
///
/// Every entry must be at least [`TOUCH_BYTES`], or touching it would grow
/// the `Vec` and measure the realloc path instead.
const SIZE_SCHEDULE: [usize; 8] = [64, 256, 1024, 4096, 16384, 65536, 262144, MAX_ALLOC_SIZE];

/// Allocation size strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocSizeMode {
    /// Every allocation is the same size.
    Fixed(usize),
    /// Cycle through [`SIZE_SCHEDULE`].
    Variable,
}

/// Allocation churn benchmark.
///
/// Deriving `Debug` is safe here because the struct only holds the size mode;
/// the allocations themselves are made and dropped inside the timed loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AllocChurnBenchmark {
    mode: AllocSizeMode,
}

impl AllocChurnBenchmark {
    /// Create a benchmark with a fixed allocation size.
    pub fn new(alloc_size: usize) -> Result<Self, BenchmarkError> {
        if !(TOUCH_BYTES..=MAX_ALLOC_SIZE).contains(&alloc_size) {
            return Err(BenchmarkError::InvalidParameter);
        }
        Ok(Self { mode: AllocSizeMode::Fixed(alloc_size) })
    }

    /// Create a benchmark that cycles through several size classes.
    pub fn variable() -> Self {
        Self { mode: AllocSizeMode::Variable }
    }

    /// Create with the default allocation size (4 KB).
    pub fn with_defaults() -> Self {
        Self { mode: AllocSizeMode::Fixed(DEFAULT_ALLOC_SIZE) }
    }

    /// Set the size mode.
    pub fn set_mode(&mut self, mode: AllocSizeMode) {
        self.mode = mode;
    }

    #[inline]
    fn size_for(&self, i: usize) -> usize {
        match self.mode {
            AllocSizeMode::Fixed(n) => n,
            AllocSizeMode::Variable => SIZE_SCHEDULE[i % SIZE_SCHEDULE.len()],
        }
    }

    /// Run the benchmark.
    pub fn run<T: BenchmarkTimer>(
        &self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        if iterations == 0 {
            return Err(BenchmarkError::InvalidParameter);
        }

        let mut warm = 0u64;
        for i in 0..warmup_iterations as usize {
            warm = warm.wrapping_add(alloc_touch_free(self.size_for(i), i as u8));
        }
        core::hint::black_box(warm);

        let mut acc = 0u64;
        let mut total_bytes = 0u64;

        let timer = T::start();

        for i in 0..iterations as usize {
            let size = self.size_for(i);
            acc = acc.wrapping_add(alloc_touch_free(size, i as u8));
            total_bytes += size as u64;
        }

        let timing = timer.stop();

        let checksum = checksum_with_witness(CHECKSUM_INIT, acc);
        Ok(BenchmarkResult::new(timing, iterations, total_bytes, checksum))
    }
}

/// Allocate `size` bytes without zeroing, write [`TOUCH_BYTES`] bytes, and
/// free.
///
/// Returns a value derived from the written bytes so the compiler cannot
/// discard the allocation. Using `Vec::with_capacity` rather than `vec![0; n]`
/// avoids `alloc_zeroed`, whose cost differs structurally between the two
/// platforms.
#[inline]
fn alloc_touch_free(size: usize, tag: u8) -> u64 {
    let mut v: Vec<u8> = Vec::with_capacity(size);
    // Writing through `push` keeps the operation in safe Rust. Only the first
    // `TOUCH_BYTES` are written; the remaining capacity stays untouched, which
    // is what makes this an allocator benchmark rather than a memset one.
    for k in 0..TOUCH_BYTES {
        v.push(tag.wrapping_add(k as u8));
    }
    let sum = v.iter().fold(0u64, |a, &b| a.wrapping_add(b as u64));
    core::hint::black_box(&v);
    sum
}

impl MemoryBenchmark for AllocChurnBenchmark {
    fn working_set_size(&self) -> usize {
        match self.mode {
            AllocSizeMode::Fixed(n) => n,
            AllocSizeMode::Variable => *SIZE_SCHEDULE.iter().max().unwrap(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::timer::NativeTimer;

    #[test]
    fn fixed_mode_is_repeatable() {
        let bench = AllocChurnBenchmark::with_defaults();
        let a = bench.run::<NativeTimer>(1_000, 10).unwrap();
        let b = bench.run::<NativeTimer>(1_000, 10).unwrap();
        assert_eq!(a.checksum, b.checksum);
        assert_eq!(a.bytes_processed, 1_000 * DEFAULT_ALLOC_SIZE as u64);
    }

    #[test]
    fn variable_mode_cycles_sizes() {
        let bench = AllocChurnBenchmark::variable();
        let r = bench.run::<NativeTimer>(SIZE_SCHEDULE.len() as u32, 0).unwrap();
        let expected: u64 = SIZE_SCHEDULE.iter().map(|&s| s as u64).sum();
        assert_eq!(r.bytes_processed, expected);
    }

    #[test]
    fn variable_and_fixed_differ() {
        let fixed = AllocChurnBenchmark::with_defaults();
        let variable = AllocChurnBenchmark::variable();
        let a = fixed.run::<NativeTimer>(64, 0).unwrap();
        let b = variable.run::<NativeTimer>(64, 0).unwrap();
        assert_ne!(a.bytes_processed, b.bytes_processed);
    }

    #[test]
    fn too_small_or_too_large_is_rejected() {
        assert_eq!(AllocChurnBenchmark::new(1).unwrap_err(), BenchmarkError::InvalidParameter);
        assert_eq!(
            AllocChurnBenchmark::new(MAX_ALLOC_SIZE + 1).unwrap_err(),
            BenchmarkError::InvalidParameter
        );
    }

    #[test]
    fn zero_iterations_is_rejected() {
        let bench = AllocChurnBenchmark::with_defaults();
        assert_eq!(bench.run::<NativeTimer>(0, 0).unwrap_err(), BenchmarkError::InvalidParameter);
    }
}
