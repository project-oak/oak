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

//! Dispatches benchmark requests to the benchmark implementations.
//!
//! Benchmarks are built on first use and rebuilt when a request changes their
//! parameters, because allocating every working set at once would exhaust the
//! guest's memory at the sizes the evaluation calls for. All construction
//! happens outside the timed region.

use alloc::boxed::Box;
use core::{
    marker::PhantomData,
    option::Option::{self, None, Some},
    result::Result::{self, Err, Ok},
};

use oak_benchmark_proto_rust::oak::benchmark::{
    BenchmarkType, RunBenchmarkRequest, RunBenchmarkResponse,
};

use crate::{
    BenchmarkError, BenchmarkResult,
    cpu::{
        CpuFeatures,
        hashing::{HashAlgorithm, HashingBenchmark},
    },
    memory::{
        AllocChurnBenchmark, ArrayUpdateBenchmark,
        hashmap::{HashMapBenchmark, HashMapMode},
    },
    timer::BenchmarkTimer,
};

/// Status codes for benchmark results.
pub mod status {
    /// Benchmark completed successfully.
    pub const OK: u32 = 0;
}

/// Default number of hash map entries when no working set size is requested.
const DEFAULT_HASHMAP_ENTRIES: u32 = 100_000;

/// Central benchmark service that dispatches requests to individual
/// benchmarks.
///
/// Generic over a [`BenchmarkTimer`] so each host application injects its own
/// timing mechanism:
/// - Oak enclave: `BenchmarkService::<TscTimer>::new(seed)`
/// - Linux: `BenchmarkService::<NativeTimer>::new(seed)`
pub struct BenchmarkService<T: BenchmarkTimer> {
    seed: u64,
    hashing: Option<Box<HashingBenchmark>>,
    array_update: Option<Box<ArrayUpdateBenchmark>>,
    hashmap_insert: Option<Box<HashMapBenchmark>>,
    hashmap_lookup: Option<Box<HashMapBenchmark>>,
    alloc_churn: AllocChurnBenchmark,
    _timer: PhantomData<T>,
}

impl<T: BenchmarkTimer> BenchmarkService<T> {
    /// Create a new benchmark service.
    ///
    /// No working sets are allocated until the corresponding benchmark is
    /// first requested.
    pub fn new(seed: u64) -> Self {
        Self {
            seed,
            hashing: None,
            array_update: None,
            hashmap_insert: None,
            hashmap_lookup: None,
            alloc_churn: AllocChurnBenchmark::with_defaults(),
            _timer: PhantomData,
        }
    }

    /// Handle a benchmark request and return the response.
    pub fn handle_request(&mut self, request: RunBenchmarkRequest) -> RunBenchmarkResponse {
        // A request may pin the seed so both platforms operate on identical
        // data. Leaving it unset selects the service default; zero is a seed
        // like any other.
        let seed = request.seed.unwrap_or(self.seed);
        let result = self.dispatch(&request, seed);
        Self::result_to_response(result)
    }

    fn dispatch(
        &mut self,
        request: &RunBenchmarkRequest,
        seed: u64,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        let iterations = request.iterations;
        let warmup = request.warmup_iterations;

        match request.benchmark_type() {
            // ── Hashing ──
            BenchmarkType::Sha256 => self.hashing_bench(seed).run::<T>(
                HashAlgorithm::Sha256,
                request.data_size as usize,
                iterations,
                warmup,
            ),
            BenchmarkType::Sha512 => self.hashing_bench(seed).run::<T>(
                HashAlgorithm::Sha512,
                request.data_size as usize,
                iterations,
                warmup,
            ),
            BenchmarkType::Sha3256 => self.hashing_bench(seed).run::<T>(
                HashAlgorithm::Sha3_256,
                request.data_size as usize,
                iterations,
                warmup,
            ),
            BenchmarkType::Sha3512 => self.hashing_bench(seed).run::<T>(
                HashAlgorithm::Sha3_512,
                request.data_size as usize,
                iterations,
                warmup,
            ),

            // ── Public key ──
            BenchmarkType::P256Sign => Err(BenchmarkError::UnsupportedBenchmark),

            // ── Memory ──
            BenchmarkType::ArrayUpdate => {
                self.array_update_bench(seed).run::<T>(iterations, warmup)
            }
            BenchmarkType::MemoryInsert => {
                let b = self.hashmap_insert_bench(seed);
                b.map_clear();
                b.run::<T>(HashMapMode::Insert, iterations, warmup)
            }
            BenchmarkType::MemoryLookup => {
                self.hashmap_lookup_bench(seed).run::<T>(HashMapMode::Lookup, iterations, warmup)
            }
            BenchmarkType::AllocChurn => self.alloc_churn.run::<T>(iterations, warmup),

            // ── Connectivity check ──
            BenchmarkType::Debug => Ok(BenchmarkResult::new(
                Default::default(),
                iterations,
                (iterations as u64) * (request.data_size as u64),
                0,
            )),

            BenchmarkType::Unspecified => Err(BenchmarkError::UnsupportedBenchmark),
        }
    }

    fn hashing_bench(&mut self, seed: u64) -> &mut HashingBenchmark {
        match self.hashing.as_mut() {
            Some(_) => {
                let b = self.hashing.as_mut().unwrap();
                b.reconfigure(seed);
            }
            None => {
                self.hashing = Some(Box::new(HashingBenchmark::new(seed)));
            }
        }
        self.hashing.as_mut().unwrap()
    }

    fn array_update_bench(&mut self, seed: u64) -> &mut ArrayUpdateBenchmark {
        if self.array_update.is_none() {
            self.array_update = Some(Box::new(ArrayUpdateBenchmark::with_defaults(seed)));
        }
        self.array_update.as_mut().unwrap()
    }

    fn hashmap_insert_bench(&mut self, seed: u64) -> &mut HashMapBenchmark {
        if self.hashmap_insert.is_none() {
            self.hashmap_insert =
                Some(Box::new(HashMapBenchmark::with_defaults(DEFAULT_HASHMAP_ENTRIES, seed)));
        }
        self.hashmap_insert.as_mut().unwrap()
    }

    fn hashmap_lookup_bench(&mut self, seed: u64) -> &mut HashMapBenchmark {
        if self.hashmap_lookup.is_none() {
            let mut b = HashMapBenchmark::with_defaults(DEFAULT_HASHMAP_ENTRIES, seed);
            b.populate();
            self.hashmap_lookup = Some(Box::new(b));
        }
        self.hashmap_lookup.as_mut().unwrap()
    }

    fn result_to_response(result: Result<BenchmarkResult, BenchmarkError>) -> RunBenchmarkResponse {
        let cpu_features = CpuFeatures::detect().to_wire();
        match result {
            Ok(result) => RunBenchmarkResponse {
                elapsed_tsc: result.timing.elapsed_tsc,
                elapsed_ns: result.timing.elapsed_ns,
                iterations_completed: result.iterations_completed,
                bytes_processed: result.bytes_processed,
                status: status::OK,
                working_set_size: result.working_set_size,
                checksum: result.checksum,
                cpu_features,
            },
            Err(e) => RunBenchmarkResponse {
                elapsed_tsc: 0,
                elapsed_ns: 0,
                iterations_completed: 0,
                bytes_processed: 0,
                status: e.as_status_code(),
                working_set_size: 0,
                checksum: 0,
                cpu_features,
            },
        }
    }
}
