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
//! Measures pure allocator throughput: each iteration allocates a 4 KB
//! vector, touches it (via `black_box`), and immediately drops it. No
//! useful computation is performed — the entire cost is `malloc`/`free`.
//!
//! The working set is tiny (one allocation at a time), so CPU cache is
//! not a factor. This directly measures how efficiently the allocator
//! recycles memory. Comparing enclave vs. Linux results isolates the
//! overhead of Oak's allocator relative to the system allocator.

use alloc::vec::Vec;

use super::MemoryBenchmark;
use crate::{BenchmarkError, BenchmarkResult, timer::BenchmarkTimer};

/// Default allocation size (4 KB).
pub const DEFAULT_ALLOC_SIZE: usize = 4096;

/// Maximum allocation size (1 MB).
pub const MAX_ALLOC_SIZE: usize = 1024 * 1024;

/// Allocation churn benchmark.
///
/// Repeatedly allocates and immediately frees vectors. This is the purest
/// measure of allocator speed — no hashing, no data structure overhead,
/// just allocation and deallocation cycles.
pub struct AllocChurnBenchmark {
    /// Size of each allocation in bytes.
    alloc_size: usize,
}

impl AllocChurnBenchmark {
    /// Create a new allocation churn benchmark.
    pub fn new(alloc_size: usize) -> Self {
        let alloc_size = alloc_size.min(MAX_ALLOC_SIZE);
        Self { alloc_size }
    }

    /// Create with default allocation size (4 KB).
    pub fn with_defaults() -> Self {
        Self::new(DEFAULT_ALLOC_SIZE)
    }

    /// Run the benchmark with a specific timer type.
    pub fn run<T: BenchmarkTimer>(
        &self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        // Warmup phase.
        for _ in 0..warmup_iterations {
            let v: Vec<u8> = alloc::vec![0u8; self.alloc_size];
            core::hint::black_box(&v);
            drop(v);
        }

        // Measurement phase.
        let timer = T::start();

        for _ in 0..iterations {
            let v: Vec<u8> = alloc::vec![0u8; self.alloc_size];
            core::hint::black_box(&v);
            drop(v);
        }

        let timing = timer.stop();
        let bytes_processed = iterations as u64 * self.alloc_size as u64;

        Ok(BenchmarkResult::new(timing, iterations, bytes_processed))
    }
}

impl MemoryBenchmark for AllocChurnBenchmark {
    fn working_set_size(&self) -> usize {
        // Working set is effectively just one allocation at a time.
        self.alloc_size
    }
}
