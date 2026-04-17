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

//! Benchmark service implementations for Oak Paper evaluation.
//!
//! This crate provides the shared benchmark logic used by both the Oak enclave
//! app and the Linux baseline app, ensuring "apples-to-apples" comparison.
//!
//! # Organization
//!
//! - `cpu`: CPU-bound benchmarks (hashing, encryption, signing)
//! - `memory`: Memory-bound benchmarks (random writes, hash maps, allocation)
//! - `service`: Main service that routes requests to benchmark implementations
//! - `timer`: TSC-based timing utilities

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub mod cpu;
pub mod memory;
pub mod service;
pub mod timer;

#[cfg(test)]
mod tests;

// Re-exports for convenience.
pub use service::BenchmarkService;
#[cfg(feature = "std")]
pub use timer::NativeTimer;
pub use timer::{BenchmarkTimer, DEFAULT_TSC_FREQ_HZ, TimerReading, TscTimer, read_tsc};

/// Benchmark result returned on success.
///
/// Use `Result<BenchmarkResult, BenchmarkError>` for fallible benchmark
/// operations.
#[derive(Debug, Clone, Copy)]
pub struct BenchmarkResult {
    /// Timer reading from the benchmark (TSC and/or nanoseconds).
    pub timing: TimerReading,
    /// Number of iterations actually completed.
    pub iterations_completed: u32,
    /// Total bytes processed.
    pub bytes_processed: u64,
}

impl BenchmarkResult {
    /// Create a new benchmark result.
    pub fn new(timing: TimerReading, iterations: u32, bytes: u64) -> Self {
        Self { timing, iterations_completed: iterations, bytes_processed: bytes }
    }
}

/// Multiplier for the 64-bit LCG (Linear Congruential Generator).
///
/// This is the multiplier from Knuth's MMIX LCG, also used by the PCG
/// family of random number generators. It has good statistical properties
/// for generating pseudo-random sequences.
///
/// Source: Knuth, "The Art of Computer Programming", Vol. 2, 3rd ed., p. 106.
/// See also: https://nuclear.llnl.gov/CNP/rng/rngman/node4.html
pub const LCG_MULTIPLIER: u64 = 6364136223846793005;

/// Fill a buffer with deterministic pseudo-random data.
///
/// Uses a simple LCG (Linear Congruential Generator) for reproducible data
/// that works in no_std environments without external dependencies.
///
/// We use pseudo-random data rather than zeroed or constant buffers because
/// some hash implementations and CPU hardware can optimize for patterned
/// input (e.g. zero-byte shortcuts, branch prediction on repeated data).
/// Pseudo-random data ensures the benchmark measures realistic throughput
/// without triggering such optimizations. The data only needs to be
/// "non-patterned", not cryptographically random, so a simple LCG suffices.
pub fn generate_benchmark_data(buffer: &mut [u8], seed: u64) {
    let mut state = seed;
    for byte in buffer.iter_mut() {
        state = state.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
        *byte = (state >> 33) as u8;
    }
}

/// Error codes for benchmark operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum BenchmarkError {
    /// Generic error.
    Generic = 1,
    /// Requested benchmark type is not supported.
    UnsupportedBenchmark = 2,
    /// Requested data size exceeds maximum.
    DataSizeTooLarge = 3,
    /// Invalid parameter (e.g. iterations exceed pre-generated indices).
    InvalidParameter = 4,
}

impl BenchmarkError {
    /// Convert to a status code for proto serialization.
    pub fn as_status_code(&self) -> u32 {
        *self as u32
    }
}
