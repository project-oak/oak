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
//! Measures random write performance to a pre-allocated fixed buffer.
//! The buffer (256 MB by default) is much larger than CPU cache, so most
//! writes are cache misses that go to main memory. This isolates memory
//! access latency from allocator overhead — the buffer is allocated once
//! at construction and never resized.
//!
//! Each iteration performs a single random-index byte write. The random
//! indices are pre-generated to avoid RNG overhead during measurement.

use alloc::vec::Vec;

use super::MemoryBenchmark;
use crate::{
    BenchmarkError, BenchmarkResult, LCG_MULTIPLIER, generate_benchmark_data, timer::BenchmarkTimer,
};

/// Default working set size (256 MB).
pub const DEFAULT_WORKING_SET_SIZE: usize = 256 * 1024 * 1024;

/// Maximum working set size (1 GB).
pub const MAX_WORKING_SET_SIZE: usize = 1024 * 1024 * 1024;

/// Array update benchmark.
///
/// Performs random single-byte writes to a pre-allocated buffer. This
/// measures raw memory subsystem throughput without any allocator
/// involvement. Comparing enclave vs. Linux results reveals memory access
/// overhead introduced by the TEE.
pub struct ArrayUpdateBenchmark {
    /// Pre-allocated data buffer.
    buffer: Vec<u8>,
    /// Pre-generated random indices for writes.
    indices: Vec<usize>,
    /// Value to write (changes each iteration to prevent optimization).
    write_value: u8,
}

impl ArrayUpdateBenchmark {
    /// Create a new array update benchmark.
    ///
    /// # Arguments
    /// * `working_set_size` - Size of the buffer in bytes.
    /// * `max_iterations` - Maximum iterations (for index pre-generation).
    /// * `seed` - Random seed for reproducibility.
    pub fn new(working_set_size: usize, max_iterations: u32, seed: u64) -> Self {
        let size = working_set_size.min(MAX_WORKING_SET_SIZE);

        // Allocate and initialize buffer.
        let mut buffer = alloc::vec![0u8; size];
        generate_benchmark_data(&mut buffer, seed);

        // Pre-generate random indices using LCG.
        let mut indices = Vec::with_capacity(max_iterations as usize);
        let mut rng_state = seed;
        for _ in 0..max_iterations {
            rng_state = rng_state.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
            let index = (rng_state as usize) % size;
            indices.push(index);
        }

        Self { buffer, indices, write_value: 0 }
    }

    /// Create with default size (256 MB).
    pub fn with_defaults(seed: u64) -> Self {
        Self::new(DEFAULT_WORKING_SET_SIZE, 100_000, seed)
    }

    /// Run the benchmark with a specific timer type.
    pub fn run<T: BenchmarkTimer>(
        &mut self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        let total_iterations = (warmup_iterations + iterations) as usize;
        if total_iterations > self.indices.len() {
            return Err(BenchmarkError::InvalidParameter);
        }

        // Warmup phase.
        for i in 0..warmup_iterations as usize {
            let idx = self.indices[i];
            self.buffer[idx] = self.write_value;
            self.write_value = self.write_value.wrapping_add(1);
        }

        // Measurement phase.
        let timer = T::start();

        for i in warmup_iterations as usize..total_iterations {
            let idx = self.indices[i];
            self.buffer[idx] = self.write_value;
            self.write_value = self.write_value.wrapping_add(1);
            core::hint::black_box(&self.buffer[idx]);
        }

        let timing = timer.stop();
        let bytes_processed = iterations as u64; // 1 byte per write

        Ok(BenchmarkResult::new(timing, iterations, bytes_processed))
    }
}

impl MemoryBenchmark for ArrayUpdateBenchmark {
    fn working_set_size(&self) -> usize {
        self.buffer.len()
    }
}
