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

//! Main benchmark service that dispatches requests to benchmark
//! implementations.

use core::marker::PhantomData;

use oak_benchmark_proto_rust::oak::benchmark::{
    BenchmarkType, RunBenchmarkRequest, RunBenchmarkResponse,
};

use crate::{
    BenchmarkError, BenchmarkResult,
    cpu::hashing::{HashAlgorithm, HashingBenchmark},
    timer::BenchmarkTimer,
};

/// Status codes for benchmark results.
/// These match the values in `BenchmarkError`.
pub mod status {
    /// Benchmark completed successfully.
    pub const OK: u32 = 0;
}

/// Central benchmark service that dispatches requests to individual benchmarks.
///
/// This struct is generic over a [`BenchmarkTimer`] implementation, enabling
/// each host application to inject its own timing mechanism:
/// - Oak enclave: `BenchmarkService::<TscTimer>::new(seed)`
/// - Linux: `BenchmarkService::<NativeTimer>::new(seed)`
///
/// Timing is performed inside the benchmark, correctly excluding warmup
/// iterations.
pub struct BenchmarkService<T: BenchmarkTimer> {
    hashing: HashingBenchmark,
    _timer: PhantomData<T>,
}

impl<T: BenchmarkTimer> BenchmarkService<T> {
    /// Create a new benchmark service with all benchmarks initialized.
    pub fn new(seed: u64) -> Self {
        Self { hashing: HashingBenchmark::new(seed), _timer: PhantomData }
    }

    /// Handle a benchmark request and return the response.
    pub fn handle_request(&self, request: RunBenchmarkRequest) -> RunBenchmarkResponse {
        let result = match request.benchmark_type() {
            // Hashing benchmarks.
            BenchmarkType::Sha256 => self.hashing.run::<T>(
                HashAlgorithm::Sha256,
                request.data_size as usize,
                request.iterations,
                request.warmup_iterations,
            ),
            BenchmarkType::Sha512 => self.hashing.run::<T>(
                HashAlgorithm::Sha512,
                request.data_size as usize,
                request.iterations,
                request.warmup_iterations,
            ),
            BenchmarkType::Sha3256 => self.hashing.run::<T>(
                HashAlgorithm::Sha3_256,
                request.data_size as usize,
                request.iterations,
                request.warmup_iterations,
            ),
            BenchmarkType::Sha3512 => self.hashing.run::<T>(
                HashAlgorithm::Sha3_512,
                request.data_size as usize,
                request.iterations,
                request.warmup_iterations,
            ),

            // Debug/connectivity test: return dummy success values.
            BenchmarkType::Debug => {
                return RunBenchmarkResponse {
                    iterations_completed: request.iterations,
                    bytes_processed: (request.iterations as u64) * (request.data_size as u64),
                    status: status::OK,
                    ..Default::default()
                };
            }

            // All other benchmarks are not implemented yet.
            _ => Err(BenchmarkError::UnsupportedBenchmark),
        };

        Self::result_to_response(result)
    }

    fn result_to_response(result: Result<BenchmarkResult, BenchmarkError>) -> RunBenchmarkResponse {
        match result {
            Ok(result) => RunBenchmarkResponse {
                elapsed_tsc: result.timing.elapsed_tsc,
                elapsed_ns: result.timing.elapsed_ns,
                iterations_completed: result.iterations_completed,
                bytes_processed: result.bytes_processed,
                status: status::OK,
            },
            Err(e) => RunBenchmarkResponse { status: e.as_status_code(), ..Default::default() },
        }
    }
}
