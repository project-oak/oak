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
//! [`TscTimer`] reads the TSC, the only option inside the enclave, which has no
//! clock. [`NativeTimer`] (std only) records both wall-clock nanoseconds and
//! TSC ticks.
//!
//! Both record TSC so the platforms can be compared in raw ticks, where the
//! frequency cancels out and a mis-calibrated one cannot distort the ratio. The
//! nanosecond reading is kept for absolute figures, and lets the host derive
//! the true frequency from a baseline run.

use core::{
    arch::x86_64::{_mm_lfence, _rdtsc},
    marker::Sized,
};

/// Result of a timer measurement.
///
/// `elapsed_tsc` is populated by every timer. `elapsed_ns` is only populated
/// where a real clock is available, and is 0 inside the enclave.
#[derive(Debug, Clone, Copy, Default)]
pub struct TimerReading {
    /// TSC ticks elapsed. Always populated.
    pub elapsed_tsc: u64,
    /// Nanoseconds elapsed. Zero when no clock is available.
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

/// A timer that uses `std::time::Instant` alongside the TSC.
///
/// Only available with the `std` feature. Records both wall-clock nanoseconds
/// and TSC ticks so that the Linux baseline is directly comparable to the
/// enclave in raw ticks, and so the host can derive the true TSC frequency
/// from the ratio of the two readings.
#[cfg(feature = "std")]
pub struct NativeTimer {
    start_instant: std::time::Instant,
    start_tsc: u64,
}

#[cfg(feature = "std")]
impl BenchmarkTimer for NativeTimer {
    #[inline]
    fn start() -> Self {
        // Read the TSC first, then the clock, and reverse the order in `stop`.
        // This makes the TSC interval enclose the clock interval, so neither
        // reading is systematically biased low by the cost of the other.
        let start_tsc = read_tsc_serialized();
        Self { start_instant: std::time::Instant::now(), start_tsc }
    }

    #[inline]
    fn stop(&self) -> TimerReading {
        let elapsed_ns = self.start_instant.elapsed().as_nanos() as u64;
        let elapsed_tsc = read_tsc_serialized().saturating_sub(self.start_tsc);
        TimerReading { elapsed_tsc, elapsed_ns }
    }
}
