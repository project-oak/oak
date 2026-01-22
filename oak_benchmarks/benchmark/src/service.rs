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

use service::oak::benchmark::{BenchmarkType, RunBenchmarkRequest, RunBenchmarkResponse};

use crate::BenchmarkError;

/// Status codes for benchmark results.
/// These match the values in `BenchmarkError`.
pub mod status {
    /// Benchmark completed successfully.
    pub const OK: u32 = 0;
    // Other error codes are defined in BenchmarkError
}

/// Central benchmark service that dispatches requests to individual benchmarks.
///
/// This struct is shared between Oak enclave and Linux apps, ensuring
/// identical benchmark execution across environments.
pub struct BenchmarkService {}

impl BenchmarkService {
    /// Create a new benchmark service.
    pub fn new(seed: u64) -> Self {
        let _ = seed;
        Self {}
    }

    /// Handle a benchmark request and return the response.
    pub fn handle_request(&mut self, request: RunBenchmarkRequest) -> RunBenchmarkResponse {
        match request.benchmark_type() {
            BenchmarkType::Sha256
            | BenchmarkType::P256Sign
            | BenchmarkType::MemoryInsert
            | BenchmarkType::MemoryLookup
            | BenchmarkType::ArrayUpdate
            | BenchmarkType::Unspecified => RunBenchmarkResponse {
                elapsed_tsc: 0,
                iterations_completed: 0,
                bytes_processed: 0,
                status: BenchmarkError::UnsupportedBenchmark.as_status_code(),
            },
        }
    }
}
