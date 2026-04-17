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

//! Cryptographic hashing benchmark.
//!
//! Supports multiple hash algorithms using the `Digest` trait.

use alloc::{vec, vec::Vec};

use sha2::{Digest, Sha256, Sha512};
use sha3::{Sha3_256, Sha3_512};

use super::CpuBenchmark;
use crate::{BenchmarkError, BenchmarkResult, generate_benchmark_data, timer::BenchmarkTimer};

/// Maximum data buffer size (1 MB).
pub const MAX_DATA_SIZE: usize = 1024 * 1024;

/// Hashing algorithm to use.
#[derive(Debug, Clone, Copy)]
pub enum HashAlgorithm {
    Sha256,
    Sha512,
    Sha3_256,
    Sha3_512,
}

/// Hashing benchmark.
///
/// Measures the throughput of cryptographic hash operations. The data buffer
/// is pre-generated with pseudo-random data to avoid allocation overhead
/// during the benchmark.
pub struct HashingBenchmark {
    data_buffer: Vec<u8>,
}

impl HashingBenchmark {
    /// Create a new hashing benchmark with pre-generated data.
    pub fn new(seed: u64) -> Self {
        let mut data_buffer = vec![0u8; MAX_DATA_SIZE];
        generate_benchmark_data(&mut data_buffer, seed);
        Self { data_buffer }
    }

    /// Run the benchmark with a specific algorithm and timer type.
    pub fn run<T: BenchmarkTimer>(
        &self,
        algorithm: HashAlgorithm,
        data_size: usize,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        if data_size > MAX_DATA_SIZE {
            return Err(BenchmarkError::DataSizeTooLarge);
        }

        let data = &self.data_buffer[..data_size];

        let result = match algorithm {
            HashAlgorithm::Sha256 => {
                Self::run_hash::<Sha256, T>(data, iterations, warmup_iterations)
            }
            HashAlgorithm::Sha512 => {
                Self::run_hash::<Sha512, T>(data, iterations, warmup_iterations)
            }
            HashAlgorithm::Sha3_256 => {
                Self::run_hash::<Sha3_256, T>(data, iterations, warmup_iterations)
            }
            HashAlgorithm::Sha3_512 => {
                Self::run_hash::<Sha3_512, T>(data, iterations, warmup_iterations)
            }
        };

        Ok(result)
    }

    /// Run a hash benchmark using any Digest-compatible hasher.
    ///
    /// If `warmup_iterations > 0`, those iterations are run first without
    /// timing to warm up the CPU caches and branch predictor.
    fn run_hash<D: Digest, T: BenchmarkTimer>(
        data: &[u8],
        iterations: u32,
        warmup_iterations: u32,
    ) -> BenchmarkResult {
        // Warmup phase: run iterations WITHOUT timing.
        for _ in 0..warmup_iterations {
            let mut hasher = D::new();
            hasher.update(data);
            let result = hasher.finalize();
            core::hint::black_box(&result);
        }

        // Measurement phase: run iterations WITH timing.
        let timer = T::start();

        for _ in 0..iterations {
            let mut hasher = D::new();
            hasher.update(data);
            let result = hasher.finalize();
            core::hint::black_box(&result);
        }

        let timing = timer.stop();
        let bytes_processed = data.len() as u64 * iterations as u64;

        BenchmarkResult::new(timing, iterations, bytes_processed)
    }
}

impl CpuBenchmark for HashingBenchmark {
    fn max_data_size(&self) -> usize {
        MAX_DATA_SIZE
    }
}
