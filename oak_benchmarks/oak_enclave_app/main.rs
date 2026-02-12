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

//! Oak Benchmark Enclave Application.
//!
//! This application runs inside the Oak Restricted Kernel and executes
//! various microbenchmarks based on commands received from the host.
//!
//! Uses the generated micro_rpc `Benchmark` service for communication.

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]
#![feature(never_type)]

extern crate alloc;

use alloc::boxed::Box;

use benchmark::{BenchmarkService, TscTimer, read_tsc};
use oak_benchmark_proto_rust::oak::benchmark::{RunBenchmarkRequest, RunBenchmarkResponse};
use oak_restricted_kernel_sdk::{
    channel::{FileDescriptorChannel, start_blocking_server},
    entrypoint,
    utils::samplestore::StaticSampleStore,
};
use service::oak::benchmark::{Benchmark, BenchmarkServer};

/// Wrapper that implements the micro_rpc Benchmark trait using the shared
/// service.
struct BenchmarkServiceWrapper {
    service: BenchmarkService<TscTimer>,
}

impl BenchmarkServiceWrapper {
    fn new() -> Self {
        let seed = read_tsc();
        Self { service: BenchmarkService::new(seed) }
    }
}

impl Benchmark for BenchmarkServiceWrapper {
    fn run_benchmark(
        &mut self,
        request: RunBenchmarkRequest,
    ) -> Result<RunBenchmarkResponse, micro_rpc::Status> {
        Ok(self.service.handle_request(request))
    }
}

/// Main benchmark loop.
#[entrypoint]
fn run_benchmarks() -> ! {
    let mut invocation_stats = StaticSampleStore::<1000>::new().unwrap();
    let wrapper = BenchmarkServiceWrapper::new();
    let server = BenchmarkServer::new(wrapper);

    start_blocking_server(Box::<FileDescriptorChannel>::default(), server, &mut invocation_stats)
        .expect("server encountered an unrecoverable error");
}
