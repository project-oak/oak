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

#[cfg(test)]
mod tests;

// Re-exports for convenience.
pub use service::BenchmarkService;

/// Benchmark result returned on success.
///
/// Use `Result<BenchmarkResult, BenchmarkError>` for fallible benchmark
/// operations.
#[derive(Debug, Clone, Copy)]
pub struct BenchmarkResult {
    /// TSC ticks elapsed during the benchmark.
    pub elapsed_tsc: u64,
    /// Number of iterations actually completed.
    pub iterations_completed: u32,
    /// Total bytes processed.
    pub bytes_processed: u64,
}

impl BenchmarkResult {
    /// Create a new benchmark result.
    pub fn new(elapsed_tsc: u64, iterations: u32, bytes: u64) -> Self {
        Self { elapsed_tsc, iterations_completed: iterations, bytes_processed: bytes }
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
}

impl BenchmarkError {
    /// Convert to a status code for proto serialization.
    pub fn as_status_code(&self) -> u32 {
        *self as u32
    }
}
