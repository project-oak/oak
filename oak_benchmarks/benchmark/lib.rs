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

//! Shared benchmark logic for the Oak enclave app and the Linux baseline, so
//! that both run the same code.
//!
//! - `cpu`: CPU-bound benchmarks (hashing, encryption, signing)
//! - `memory`: Memory-bound benchmarks (random writes, hash maps, allocation)
//! - `service`: routes requests to benchmark implementations
//! - `timer`: timing utilities
//!
//! Every benchmark must satisfy three properties, because the numbers feed the
//! paper's evaluation:
//!
//! 1. **Identical work.** The enclave and the baseline must execute the same
//!    operations over the same inputs. All pseudo-random data is derived from a
//!    caller-supplied seed, never from a clock or the TSC.
//! 2. **Verifiable work.** Each benchmark must return a checksum over its
//!    output. Matching checksums across platforms then demonstrate that the
//!    same work was performed and that the optimiser did not elide it.
//! 3. **Untimed setup.** Allocation and input generation happen outside the
//!    timed region.

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
pub use timer::{BenchmarkTimer, TimerReading, TscTimer, read_tsc};

/// Seed used when a request does not pin one.
///
/// A fixed constant rather than anything derived from the clock: both platforms
/// must generate the same input data, or they are not running the same
/// benchmark. It lives here rather than in the CLI so the enclave, which cannot
/// depend on `cli_common`, uses the same value.
pub const DEFAULT_BENCHMARK_SEED: u64 = 0x0A6B_1234_5678_9ABC;

/// Benchmark result returned on success.
///
/// Use `Result<BenchmarkResult, BenchmarkError>` for fallible benchmark
/// operations.
#[derive(Debug, Clone, Copy)]
pub struct BenchmarkResult {
    /// Timer reading from the benchmark (TSC and, where available,
    /// nanoseconds).
    pub timing: TimerReading,
    /// Number of iterations actually completed.
    pub iterations_completed: u32,
    /// Total bytes processed.
    pub bytes_processed: u64,
    /// Checksum over the benchmark output.
    ///
    /// Must be identical across platforms for the same benchmark, seed and
    /// parameters. A mismatch means the two sides did not perform the same
    /// work and the comparison is invalid.
    pub checksum: u64,
    /// Working set size actually used, in bytes.
    pub working_set_size: u64,
}

impl BenchmarkResult {
    /// Create a new benchmark result.
    pub fn new(timing: TimerReading, iterations: u32, bytes: u64, checksum: u64) -> Self {
        Self {
            timing,
            iterations_completed: iterations,
            bytes_processed: bytes,
            checksum,
            working_set_size: 0,
        }
    }

    /// Attach the working set size to this result.
    pub fn with_working_set(mut self, working_set_size: u64) -> Self {
        self.working_set_size = working_set_size;
        self
    }
}

/// Multiplier of Knuth's MMIX linear congruential generator, also used by the
/// PCG family.
///
/// See Knuth, "The Art of Computer Programming", Vol. 2, 3rd ed., p. 106, and
/// <https://nuclear.llnl.gov/CNP/rng/rngman/node4.html>.
pub const LCG_MULTIPLIER: u64 = 6364136223846793005;

/// XORed into a seed to move a generator off a sequence already walked.
///
/// A benchmark that warms up and then measures must not replay the warmup's
/// access sequence, or the measured loop finds lines the warmup left in
/// cache. XORing this into the seed offsets the measured stream instead,
/// while keeping it a function of the seed alone, so the number of warmup
/// iterations does not change what gets measured.
///
/// The value carries no meaning and the ascending nibbles are there to say
/// so. Only two properties matter. It must be non-zero, or the two streams
/// are the same. It must be odd, because the low bits of a linear
/// congruential generator modulo 2^64 form a self-contained generator
/// modulo 2^k: two seeds that agree in their low k bits produce streams
/// that agree there for ever. Differing in bit 0 rules that out at every
/// width.
pub const MEASURED_SEED_OFFSET: u64 = 0x0123_4567_89AB_CDEF;

/// Fill a buffer with deterministic pseudo-random data.
///
/// Zeroed or constant buffers let hash implementations and the hardware take
/// shortcuts, so the data needs to be non-patterned; it does not need to be
/// cryptographically random, so an LCG suffices and keeps this `no_std`.
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
    /// Invalid parameter (e.g. zero iterations, or a size out of range).
    InvalidParameter = 4,
    /// A cryptographic operation failed unexpectedly.
    CryptoFailure = 5,
    /// Allocation of the requested working set failed.
    AllocationFailure = 6,
}

impl BenchmarkError {
    /// Convert to a status code for proto serialization.
    pub fn as_status_code(&self) -> u32 {
        *self as u32
    }

    /// Human-readable description, used by the host CLIs when reporting a
    /// failed run.
    pub fn describe(status: u32) -> &'static str {
        match status {
            0 => "ok",
            1 => "generic error",
            2 => "unsupported benchmark",
            3 => "data size too large",
            4 => "invalid parameter",
            5 => "crypto failure",
            6 => "allocation failure",
            _ => "unknown status",
        }
    }
}

/// Fold a byte slice into a running checksum.
///
/// This is an FNV-1a variant. It is not cryptographic; its only purpose is to
/// make benchmark output observable so the optimiser cannot discard it, and to
/// let the host verify that both platforms computed the same thing.
#[inline]
pub fn checksum_update(acc: u64, bytes: &[u8]) -> u64 {
    const FNV_PRIME: u64 = 1099511628211;
    let mut hash = acc;
    for &b in bytes {
        hash ^= b as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

/// Initial value for [`checksum_update`] chains.
pub const CHECKSUM_INIT: u64 = 14695981039346656037;

/// Fold the endpoints of a byte slice into a running value in constant time.
///
/// [`checksum_update`] is too expensive for a timed loop: around three cycles
/// per byte, where AES-256-GCM with AES-NI runs at well under one. It costs the
/// same on both platforms, so folding it into the measured region would drag
/// their ratio toward 1.0. Timed loops call this instead and checksum once the
/// timer has stopped.
#[inline]
pub fn fold_sample(acc: u64, bytes: &[u8]) -> u64 {
    let first = bytes.first().copied().unwrap_or(0) as u64;
    let last = bytes.last().copied().unwrap_or(0) as u64;
    acc.rotate_left(7) ^ first ^ (last << 8)
}
