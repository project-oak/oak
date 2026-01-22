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

use service::oak::benchmark::{BenchmarkType, RunBenchmarkRequest};

use super::service::BenchmarkService;
use crate::BenchmarkError;

#[test]
fn test_service_unsupported() {
    let mut svc = BenchmarkService::new(0);
    let request = RunBenchmarkRequest {
        benchmark_type: BenchmarkType::P256Sign as i32,
        data_size: 1024,
        iterations: 100,
    };

    let response = svc.handle_request(request);
    assert_eq!(response.status, BenchmarkError::UnsupportedBenchmark.as_status_code());
}
