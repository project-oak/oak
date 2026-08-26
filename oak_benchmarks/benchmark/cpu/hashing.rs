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
use crate::{
    BenchmarkError, BenchmarkResult, CHECKSUM_INIT, checksum_update, checksum_with_witness,
    fold_sample, generate_benchmark_data, timer::BenchmarkTimer,
};

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
    /// Seed the buffer was generated from, so a later request that changes it
    /// can be detected.
    seed: u64,
}

impl HashingBenchmark {
    /// Create a new hashing benchmark with pre-generated data.
    pub fn new(seed: u64) -> Self {
        let mut data_buffer = vec![0u8; MAX_DATA_SIZE];
        generate_benchmark_data(&mut data_buffer, seed);
        Self { data_buffer, seed }
    }

    /// Regenerate the data buffer if `seed` differs from the current one.
    ///
    /// A sweep over data sizes at one seed reuses the buffer, so it pays the
    /// generation cost once, while a request that changes the seed gets data
    /// that matches what it asked for.
    pub fn reconfigure(&mut self, seed: u64) {
        if self.seed != seed {
            generate_benchmark_data(&mut self.data_buffer, seed);
            self.seed = seed;
        }
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
        if iterations == 0 {
            return Err(BenchmarkError::InvalidParameter);
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
    /// Each digest goes through [`core::hint::black_box`] so the optimiser
    /// cannot discard the hashing, and [`fold_sample`] carries two bytes of it
    /// into an accumulator. [`checksum_update`] itself is too expensive to run
    /// per iteration: over a 32-byte digest it costs about as much as SHA-256
    /// does at the short end of the sweep, and it costs the same on both
    /// platforms, so it would drag their ratio toward 1.0.
    ///
    /// The reported checksum is the digest of the input, which pins what was
    /// hashed, mixed with the accumulator, which pins how many times and in
    /// what order. Neither alone is enough: the digest is the same at eight
    /// iterations as at a thousand, and the accumulator alone would not show
    /// that the data differed.
    fn run_hash<D: Digest, T: BenchmarkTimer>(
        data: &[u8],
        iterations: u32,
        warmup_iterations: u32,
    ) -> BenchmarkResult {
        // Warmup phase: run iterations WITHOUT timing.
        let mut warmup_acc = CHECKSUM_INIT;
        for _ in 0..warmup_iterations {
            let mut hasher = D::new();
            hasher.update(core::hint::black_box(data));
            warmup_acc = fold_sample(warmup_acc, core::hint::black_box(&hasher.finalize()));
        }
        core::hint::black_box(warmup_acc);

        // Measurement phase: run iterations WITH timing.
        let mut acc = CHECKSUM_INIT;
        let timer = T::start();

        for _ in 0..iterations {
            let mut hasher = D::new();
            hasher.update(core::hint::black_box(data));
            acc = fold_sample(acc, core::hint::black_box(&hasher.finalize()));
        }

        let timing = timer.stop();

        // Hashing is deterministic, so one extra digest outside the timed
        // region reproduces what each iteration of the loop computed.
        let mut hasher = D::new();
        hasher.update(data);
        let checksum =
            checksum_with_witness(checksum_update(CHECKSUM_INIT, &hasher.finalize()), acc);

        let bytes_processed = data.len() as u64 * iterations as u64;

        BenchmarkResult::new(timing, iterations, bytes_processed, checksum)
    }
}

impl CpuBenchmark for HashingBenchmark {
    fn max_data_size(&self) -> usize {
        MAX_DATA_SIZE
    }
}
