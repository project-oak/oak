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
        aead::{AeadBenchmark, AeadMode},
        hashing::{HashAlgorithm, HashingBenchmark},
        signing::{SigningBenchmark, SigningMode},
    },
    memory::{
        AllocChurnBenchmark, AllocSizeMode, ArrayUpdateBenchmark,
        hashmap::{HashMapBenchmark, HashMapMode},
        pointer_chase::PointerChaseBenchmark,
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
    signing: Option<Box<SigningBenchmark>>,
    aead: Option<Box<AeadBenchmark>>,
    array_update: Option<Box<ArrayUpdateBenchmark>>,
    hashmap: Option<Box<HashMapBenchmark>>,
    pointer_chase: Option<Box<PointerChaseBenchmark>>,
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
            signing: None,
            aead: None,
            array_update: None,
            hashmap: None,
            pointer_chase: None,
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
            BenchmarkType::P256Sign => {
                let b = self.signing_bench(seed)?;
                b.run::<T>(SigningMode::Sign, iterations, warmup)
            }
            BenchmarkType::P256Verify => {
                let b = self.signing_bench(seed)?;
                b.run::<T>(SigningMode::Verify, iterations, warmup)
            }

            // ── AEAD ──
            BenchmarkType::Aes256GcmSeal => self.aead_bench(seed).run::<T>(
                AeadMode::Seal,
                request.data_size as usize,
                iterations,
                warmup,
            ),
            BenchmarkType::Aes256GcmOpen => self.aead_bench(seed).run::<T>(
                AeadMode::Open,
                request.data_size as usize,
                iterations,
                warmup,
            ),

            // ── Memory ──
            BenchmarkType::ArrayUpdate => {
                let size = Self::working_set_or(
                    request,
                    crate::memory::array_update::DEFAULT_WORKING_SET_SIZE,
                );
                let b = self.array_update_bench(size, seed)?;
                b.run::<T>(iterations, warmup)
            }
            BenchmarkType::MemoryInsert => {
                let entries = Self::hashmap_entries(request);
                let b = self.hashmap_bench(entries, seed)?;
                b.run::<T>(HashMapMode::Insert, iterations, warmup)
            }
            BenchmarkType::MemoryLookup => {
                let entries = Self::hashmap_entries(request);
                let b = self.hashmap_bench(entries, seed)?;
                b.run::<T>(HashMapMode::Lookup, iterations, warmup)
            }
            BenchmarkType::MemoryChurn => {
                let entries = Self::hashmap_entries(request);
                let b = self.hashmap_bench(entries, seed)?;
                b.run::<T>(HashMapMode::Churn, iterations, warmup)
            }
            BenchmarkType::AllocChurn => {
                // `data_size` selects the allocation size; 0 selects the
                // variable-size schedule.
                if request.data_size == 0 {
                    self.alloc_churn.set_mode(AllocSizeMode::Variable);
                } else {
                    self.alloc_churn.set_mode(AllocSizeMode::Fixed(request.data_size as usize));
                }
                self.alloc_churn.run::<T>(iterations, warmup)
            }

            BenchmarkType::PointerChase => {
                let size = Self::working_set_or(
                    request,
                    crate::memory::pointer_chase::DEFAULT_WORKING_SET_SIZE,
                );
                let b = self.pointer_chase_bench(size, seed)?;
                b.run::<T>(iterations, warmup)
            }

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

    /// Resolve a requested working set size, falling back to a default.
    ///
    /// Zero means "unset" on the wire, so every memory benchmark has to make
    /// the same substitution.
    fn working_set_or(request: &RunBenchmarkRequest, default: usize) -> usize {
        if request.working_set_size != 0 { request.working_set_size as usize } else { default }
    }

    fn hashmap_entries(request: &RunBenchmarkRequest) -> u32 {
        if request.working_set_size != 0 {
            HashMapBenchmark::entries_for_working_set(
                request.working_set_size,
                crate::memory::hashmap::DEFAULT_VALUE_SIZE,
            )
        } else {
            DEFAULT_HASHMAP_ENTRIES
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

    fn signing_bench(&mut self, seed: u64) -> Result<&mut SigningBenchmark, BenchmarkError> {
        if self.signing.is_none() {
            self.signing = Some(Box::new(SigningBenchmark::new(seed)?));
        }
        Ok(self.signing.as_mut().unwrap())
    }

    fn aead_bench(&mut self, seed: u64) -> &mut AeadBenchmark {
        if self.aead.is_none() {
            self.aead = Some(Box::new(AeadBenchmark::new(seed)));
        }
        self.aead.as_mut().unwrap()
    }

    fn array_update_bench(
        &mut self,
        working_set_size: usize,
        seed: u64,
    ) -> Result<&mut ArrayUpdateBenchmark, BenchmarkError> {
        match self.array_update.as_mut() {
            Some(_) => {
                let b = self.array_update.as_mut().unwrap();
                b.reconfigure(working_set_size, seed)?;
            }
            None => {
                self.array_update =
                    Some(Box::new(ArrayUpdateBenchmark::new(working_set_size, seed)?));
            }
        }
        Ok(self.array_update.as_mut().unwrap())
    }

    fn hashmap_bench(
        &mut self,
        entries: u32,
        seed: u64,
    ) -> Result<&mut HashMapBenchmark, BenchmarkError> {
        match self.hashmap.as_mut() {
            Some(_) => {
                let b = self.hashmap.as_mut().unwrap();
                b.reconfigure(entries, seed)?;
            }
            None => {
                self.hashmap = Some(Box::new(HashMapBenchmark::with_defaults(entries, seed)?));
            }
        }
        Ok(self.hashmap.as_mut().unwrap())
    }

    fn pointer_chase_bench(
        &mut self,
        working_set_size: usize,
        seed: u64,
    ) -> Result<&mut PointerChaseBenchmark, BenchmarkError> {
        match self.pointer_chase.as_mut() {
            // Reconfiguring rebuilds the cycle, so a second request with
            // different parameters gets the same state a fresh instance
            // would.
            Some(b) => b.reconfigure(working_set_size, seed)?,
            None => {
                self.pointer_chase =
                    Some(Box::new(PointerChaseBenchmark::new(working_set_size, seed)?));
            }
        }
        Ok(self.pointer_chase.as_mut().unwrap())
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
