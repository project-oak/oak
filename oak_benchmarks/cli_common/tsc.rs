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

//! TSC (Time Stamp Counter) utilities for benchmark timing.

/// Default TSC frequency in Hz (3.0 GHz).
pub const DEFAULT_TSC_FREQ_HZ: u64 = 3_000_000_000;

/// Source of the detected TSC frequency.
///
/// This enum allows callers to handle the detection result appropriately
/// (e.g., log warnings when using fallback values).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TscFreq {
    /// Frequency from /sys/devices/system/cpu/cpu0/cpufreq/base_frequency.
    BaseFrequency(u64),
    /// Frequency from /sys/devices/system/cpu/cpu0/cpufreq/cpuinfo_max_freq.
    CpuInfoMaxFreq(u64),
    /// Default fallback when detection fails.
    Default(u64),
}

impl TscFreq {
    /// Get the frequency value in Hz.
    pub fn hz(&self) -> u64 {
        match self {
            TscFreq::BaseFrequency(hz) => *hz,
            TscFreq::CpuInfoMaxFreq(hz) => *hz,
            TscFreq::Default(hz) => *hz,
        }
    }

    /// Returns true if this is the default fallback frequency.
    pub fn is_default(&self) -> bool {
        matches!(self, TscFreq::Default(_))
    }

    /// Human-readable description of the source.
    pub fn source_description(&self) -> &'static str {
        match self {
            TscFreq::BaseFrequency(_) => "base_frequency",
            TscFreq::CpuInfoMaxFreq(_) => "cpuinfo_max_freq",
            TscFreq::Default(_) => "default (detection failed)",
        }
    }
}

/// Detect TSC frequency from the system.
///
/// Tries to read from /sys/devices/system/cpu/cpu0/cpufreq/base_frequency
/// or cpuinfo_max_freq. Returns TscFreq::Default if detection fails.
pub fn detect_tsc_freq() -> TscFreq {
    // Try base_frequency first (most accurate for constant TSC)
    let base = std::fs::read_to_string("/sys/devices/system/cpu/cpu0/cpufreq/base_frequency")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .map(|khz| khz * 1000); // Convert kHz to Hz

    if let Some(freq) = base {
        return TscFreq::BaseFrequency(freq);
    }

    // Fallback to cpuinfo_max_freq
    let max = std::fs::read_to_string("/sys/devices/system/cpu/cpu0/cpufreq/cpuinfo_max_freq")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .map(|khz| khz * 1000);

    if let Some(freq) = max {
        return TscFreq::CpuInfoMaxFreq(freq);
    }

    TscFreq::Default(DEFAULT_TSC_FREQ_HZ)
}

/// Convert TSC ticks to nanoseconds.
pub fn tsc_to_nanos(ticks: u64, freq_hz: u64) -> u64 {
    let nanos_per_sec: u64 = 1_000_000_000;
    let numerator = ticks as u128 * nanos_per_sec as u128;
    (numerator / freq_hz as u128) as u64
}
