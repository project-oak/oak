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

//! Memory-bound benchmark implementations.
//!
//! These benchmarks stress memory subsystem performance with large working
//! sets (~1GB) to evaluate allocator efficiency and memory access patterns.

use crate::{BenchmarkError, BenchmarkResult};

/// Trait for memory-bound benchmarks.
///
/// These benchmarks use large working sets to stress the memory subsystem.
pub trait MemoryBenchmark {
    /// Run the benchmark.
    ///
    /// # Arguments
    /// * `iterations` - Number of iterations to run.
    fn run(&mut self, iterations: u32) -> Result<BenchmarkResult, BenchmarkError>;

    /// Size of the working set in bytes.
    fn working_set_size(&self) -> usize;
}

// Future implementations:
// - RandomWriteBenchmark: Random writes to a fixed 1GB buffer.
// - HashMapLookupBenchmark: Read-heavy hash map operations.
// - HashMapModifyBenchmark: Mixed read/write/alloc hash map operations.
// - AllocChurnBenchmark: Repeated allocation/deallocation stress test.
