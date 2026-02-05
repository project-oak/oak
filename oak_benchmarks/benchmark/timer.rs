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

//! Timing utilities for benchmarks using the CPU's Time Stamp Counter (TSC).
//!
//! The TSC provides a high-resolution, low-overhead way to measure elapsed
//! time. It counts CPU cycles since reset and is accessible via the RDTSC
//! instruction.

use core::arch::x86_64::{_mm_lfence, _rdtsc};

/// Default assumed TSC frequency in Hz (3.0 GHz).
///
/// This should be calibrated for your specific hardware. Common values:
/// - Intel Xeon (Skylake+): 2.0 - 3.5 GHz
/// - AMD EPYC: 2.0 - 3.0 GHz
pub const DEFAULT_TSC_FREQ_HZ: u64 = 3_000_000_000;

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

/// A simple timer that measures elapsed TSC ticks.
pub struct TscTimer {
    start: u64,
}

impl TscTimer {
    /// Start a new timer.
    #[inline]
    pub fn start() -> Self {
        Self { start: read_tsc_serialized() }
    }

    /// Get elapsed TSC ticks since start.
    #[inline]
    pub fn elapsed_tsc(&self) -> u64 {
        read_tsc_serialized().saturating_sub(self.start)
    }
}
