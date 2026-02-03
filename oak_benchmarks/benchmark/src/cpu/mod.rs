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

//! CPU-bound benchmark implementations.

use crate::{BenchmarkError, BenchmarkResult};

/// Trait for CPU-bound benchmarks.
///
/// These benchmarks measure computational performance with relatively small
/// data sizes and high iteration counts.
pub trait CpuBenchmark {
    /// Run the benchmark.
    ///
    /// # Arguments
    /// * `data_size` - Size of data to process per iteration.
    /// * `iterations` - Number of iterations to run.
    fn run(&mut self, data_size: usize, iterations: u32)
    -> Result<BenchmarkResult, BenchmarkError>;

    /// Maximum data size this benchmark supports.
    fn max_data_size(&self) -> usize;
}
