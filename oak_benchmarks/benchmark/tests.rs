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

//! Tests for BenchmarkService.

use oak_benchmark_proto_rust::oak::benchmark::{BenchmarkType, RunBenchmarkRequest};

use super::service::BenchmarkService;
use crate::{BenchmarkError, NativeTimer};

/// Builds a small request for `benchmark_type` with everything else defaulted.
fn request_for(benchmark_type: BenchmarkType) -> RunBenchmarkRequest {
    RunBenchmarkRequest {
        benchmark_type: benchmark_type as i32,
        data_size: 1024,
        iterations: 8,
        warmup_iterations: 1,
        seed: Some(0xABCD_EF01),
        working_set_size: 0,
    }
}

#[test]
fn test_service_unsupported() {
    let mut svc = BenchmarkService::<NativeTimer>::new(0);
    let request = RunBenchmarkRequest {
        benchmark_type: 9999,
        data_size: 1024,
        iterations: 100,
        warmup_iterations: 0,
        seed: None,
        working_set_size: 0,
    };

    let response = svc.handle_request(request);
    assert_eq!(response.status, BenchmarkError::UnsupportedBenchmark.as_status_code());
}

/// Every benchmark type the service claims to support must run end to end.
///
/// This is deliberately a smoke test: it asserts success and a non-zero
/// operation count rather than any particular throughput, so it stays stable
/// across machines.
#[test]
fn test_service_supports_all_benchmark_types() {
    let types = [
        BenchmarkType::Sha256,
        BenchmarkType::Sha512,
        BenchmarkType::Sha3256,
        BenchmarkType::Sha3512,
        BenchmarkType::ArrayUpdate,
        BenchmarkType::MemoryInsert,
        BenchmarkType::MemoryLookup,
        BenchmarkType::AllocChurn,
    ];

    for benchmark_type in types {
        let mut svc = BenchmarkService::<NativeTimer>::new(0);
        let request = request_for(benchmark_type);

        let response = svc.handle_request(request);
        assert_eq!(response.status, 0, "{benchmark_type:?} returned a non-zero status");
        assert!(
            response.iterations_completed > 0,
            "{benchmark_type:?} reported zero completed iterations"
        );
        assert!(response.elapsed_tsc > 0, "{benchmark_type:?} reported zero elapsed TSC");
    }
}
