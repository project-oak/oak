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

//! Timing utilities for benchmarks.
//!
//! Provides the [`BenchmarkTimer`] trait for platform-specific timing:
//! - [`TscTimer`]: Uses the CPU's Time Stamp Counter (TSC) via RDTSC. Works on
//!   both Oak enclave and Linux, but requires TSC frequency for conversion to
//!   wall-clock time.
//! - [`NativeTimer`] (std only): Uses `std::time::Instant` for direct
//!   nanosecond measurement on Linux.

use core::arch::x86_64::{_mm_lfence, _rdtsc};

/// Default assumed TSC frequency in Hz (3.0 GHz).
///
/// This should be calibrated for your specific hardware. Common values:
/// - Intel Xeon (Skylake+): 2.0 - 3.5 GHz
/// - AMD EPYC: 2.0 - 3.0 GHz
pub const DEFAULT_TSC_FREQ_HZ: u64 = 3_000_000_000;

/// Result of a timer measurement.
///
/// At least one of `elapsed_tsc` or `elapsed_ns` will be non-zero,
/// depending on the timer implementation used.
#[derive(Debug, Clone, Copy, Default)]
pub struct TimerReading {
    /// TSC ticks elapsed (non-zero when using [`TscTimer`]).
    pub elapsed_tsc: u64,
    /// Nanoseconds elapsed (non-zero when using [`NativeTimer`]).
    pub elapsed_ns: u64,
}

/// Trait for benchmark timing, injected by the host application.
///
/// This allows the same benchmark code to use different timing mechanisms:
/// - Oak enclave: [`TscTimer`] (TSC-based, no_std compatible)
/// - Linux: [`NativeTimer`] (Instant-based, requires std)
pub trait BenchmarkTimer {
    /// Start a new timer.
    fn start() -> Self
    where
        Self: Sized;

    /// Stop the timer and return the reading.
    fn stop(&self) -> TimerReading;
}

/// Read the current value of the Time Stamp Counter.
///
/// Uses the RDTSC instruction which is not serializing - it may execute
/// out-of-order with surrounding instructions.
#[inline(always)]
pub fn read_tsc() -> u64 {
    // SAFETY: _rdtsc is always available on x86_64 and has no side effects.
    unsafe { _rdtsc() }
}

/// Read the TSC with a serializing instruction barrier.
///
/// Uses LFENCE before RDTSC to ensure all previous instructions complete
/// before reading the counter, providing more accurate timing measurements.
#[inline(always)]
pub fn read_tsc_serialized() -> u64 {
    // SAFETY: _mm_lfence and _rdtsc are safe on x86_64 with no side effects.
    unsafe {
        _mm_lfence();
        _rdtsc()
    }
}

/// A timer that measures elapsed TSC ticks.
///
/// Uses the CPU's RDTSC instruction, which works in both Oak enclave
/// and Linux environments. Requires TSC frequency for conversion to
/// wall-clock time.
pub struct TscTimer {
    start: u64,
}

impl TscTimer {
    /// Get elapsed TSC ticks since start (for backward compatibility).
    #[inline]
    pub fn elapsed_tsc(&self) -> u64 {
        read_tsc_serialized().saturating_sub(self.start)
    }
}

impl BenchmarkTimer for TscTimer {
    #[inline]
    fn start() -> Self {
        Self { start: read_tsc_serialized() }
    }

    #[inline]
    fn stop(&self) -> TimerReading {
        TimerReading { elapsed_tsc: self.elapsed_tsc(), elapsed_ns: 0 }
    }
}

/// A timer that uses `std::time::Instant` for nanosecond measurement.
///
/// Only available with the `std` feature. Returns wall-clock elapsed time
/// in nanoseconds, suitable for the Linux benchmark runner.
#[cfg(feature = "std")]
pub struct NativeTimer {
    start: std::time::Instant,
}

#[cfg(feature = "std")]
impl BenchmarkTimer for NativeTimer {
    #[inline]
    fn start() -> Self {
        Self { start: std::time::Instant::now() }
    }

    #[inline]
    fn stop(&self) -> TimerReading {
        TimerReading { elapsed_tsc: 0, elapsed_ns: self.start.elapsed().as_nanos() as u64 }
    }
}
