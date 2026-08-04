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
//!
//! The enclave has no wall clock and can only report elapsed TSC ticks, so the
//! host needs the tick rate to turn them into nanoseconds. Getting it wrong
//! scales every enclave result: `cpuinfo_max_freq` in sysfs reports the boost
//! clock, not the invariant TSC rate.
//!
//! So the rate is measured against `CLOCK_MONOTONIC` rather than read from
//! sysfs, and the CLIs report cycles per operation as the primary metric, which
//! needs no frequency at all.
//!
//! On the TSC being invariant see section 13.4 in
//! <https://docs.amd.com/v/u/en-US/24593_3.45_APM_Vol2>, and the
//! `constant_tsc` / `nonstop_tsc` flags in `/proc/cpuinfo`.

use std::time::{Duration, Instant};

/// Default TSC frequency in Hz, used only if calibration fails.
///
/// Deliberately a round, obviously-synthetic number, so that it is recognisable
/// as a fallback if it shows up in results. Callers must check
/// [`TscFreq::is_trustworthy`].
pub const DEFAULT_TSC_FREQ_HZ: u64 = 3_000_000_000;

/// How long to sample the TSC against the monotonic clock when calibrating.
///
/// Long enough that the surrounding `clock_gettime` calls are negligible
/// (relative error < 1e-5), short enough not to delay CLI startup.
pub const CALIBRATION_DURATION: Duration = Duration::from_millis(50);

/// Source of the detected TSC frequency, so callers can warn on a fallback.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TscFreq {
    /// Measured over a known monotonic-clock interval. The only variant that
    /// reflects the actual TSC rate rather than a nominal core frequency.
    Calibrated(u64),
    /// Base (non-boost) core clock from sysfs. Matches the TSC on many Intel
    /// parts, but by coincidence, and the file is absent under `amd_pstate`.
    BaseFrequency(u64),
    /// Maximum boost clock from sysfs. Almost never the TSC rate.
    CpuInfoMaxFreq(u64),
    /// Default fallback when every detection method fails.
    Default(u64),
}

impl TscFreq {
    /// Get the frequency value in Hz.
    pub fn hz(&self) -> u64 {
        match self {
            TscFreq::Calibrated(hz) => *hz,
            TscFreq::BaseFrequency(hz) => *hz,
            TscFreq::CpuInfoMaxFreq(hz) => *hz,
            TscFreq::Default(hz) => *hz,
        }
    }

    /// Returns true if this is the default fallback frequency.
    pub fn is_default(&self) -> bool {
        matches!(self, TscFreq::Default(_))
    }

    /// Returns true if this frequency actually measures the TSC.
    ///
    /// Only [`TscFreq::Calibrated`] does. Every other variant is an inference
    /// from a nominal core frequency and may be wrong by double-digit
    /// percentages; callers converting enclave TSC counts to nanoseconds
    /// should warn the user when this returns false.
    pub fn is_trustworthy(&self) -> bool {
        matches!(self, TscFreq::Calibrated(_))
    }

    /// Human-readable description of the source.
    pub fn source_description(&self) -> &'static str {
        match self {
            TscFreq::Calibrated(_) => "calibrated against CLOCK_MONOTONIC",
            TscFreq::BaseFrequency(_) => "base_frequency (nominal, unverified)",
            TscFreq::CpuInfoMaxFreq(_) => "cpuinfo_max_freq (boost clock, likely wrong)",
            TscFreq::Default(_) => "default (detection failed)",
        }
    }
}

/// Read the time stamp counter.
#[inline]
pub fn read_tsc() -> u64 {
    // SAFETY: `_rdtsc` is `unsafe` only as a raw instruction wrapper. `RDTSC`
    // is unprivileged, always available on x86-64, and has no operands and no
    // memory effects.
    unsafe { core::arch::x86_64::_rdtsc() }
}

/// Measure the TSC frequency against `CLOCK_MONOTONIC`.
///
/// Samples for `duration` and returns ticks per second, or `None` if the
/// counter did not advance, which would mean the TSC is unavailable or
/// emulated. On Linux `Instant` reads `CLOCK_MONOTONIC`, which NTP can slew but
/// never steps; see <https://man7.org/linux/man-pages/man2/clock_gettime.2.html>.
pub fn calibrate_tsc_freq(duration: Duration) -> Option<u64> {
    let start_instant = Instant::now();
    let start_tsc = read_tsc();

    // Spin rather than sleep: sleeping would hand the core to the scheduler
    // and the wake-up latency would be charged to the measured interval.
    while start_instant.elapsed() < duration {
        core::hint::spin_loop();
    }

    let end_tsc = read_tsc();
    let elapsed = start_instant.elapsed();

    let ticks = end_tsc.checked_sub(start_tsc)?;
    if ticks == 0 {
        return None;
    }

    let elapsed_ns = elapsed.as_nanos();
    if elapsed_ns == 0 {
        return None;
    }

    // ticks / seconds = ticks * 1e9 / nanoseconds.
    Some((ticks as u128 * 1_000_000_000 / elapsed_ns) as u64)
}

/// Read a frequency in kHz from a sysfs file and return it in Hz.
///
/// `None` if the file is absent or unparseable. `base_frequency` in particular
/// only exists under the `intel_pstate` driver.
fn read_sysfs_freq_hz(path: &str) -> Option<u64> {
    std::fs::read_to_string(path)
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .map(|khz| khz * 1000)
}

/// Detect TSC frequency, preferring direct measurement.
///
/// Falls back to the sysfs nominal frequencies and finally to
/// [`DEFAULT_TSC_FREQ_HZ`]. Check [`TscFreq::is_trustworthy`] on the result
/// before using it to convert enclave tick counts into wall-clock units.
pub fn detect_tsc_freq() -> TscFreq {
    if let Some(freq) = calibrate_tsc_freq(CALIBRATION_DURATION) {
        return TscFreq::Calibrated(freq);
    }

    if let Some(freq) = read_sysfs_freq_hz("/sys/devices/system/cpu/cpu0/cpufreq/base_frequency") {
        return TscFreq::BaseFrequency(freq);
    }

    if let Some(freq) = read_sysfs_freq_hz("/sys/devices/system/cpu/cpu0/cpufreq/cpuinfo_max_freq")
    {
        return TscFreq::CpuInfoMaxFreq(freq);
    }

    TscFreq::Default(DEFAULT_TSC_FREQ_HZ)
}

/// Convert TSC ticks to nanoseconds.
///
/// Returns 0 for a zero frequency rather than dividing by zero, which a failed
/// benchmark's all-zero response would otherwise do.
pub fn tsc_to_nanos(ticks: u64, freq_hz: u64) -> u64 {
    if freq_hz == 0 {
        return 0;
    }
    let nanos_per_sec: u64 = 1_000_000_000;
    let numerator = ticks as u128 * nanos_per_sec as u128;
    (numerator / freq_hz as u128) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tsc_advances() {
        let a = read_tsc();
        // Enough work that the counter must move even at a low clock.
        for _ in 0..10_000 {
            core::hint::spin_loop();
        }
        let b = read_tsc();
        assert!(b > a, "TSC did not advance: {a} -> {b}");
    }

    #[test]
    fn calibration_returns_a_plausible_frequency() {
        let freq = calibrate_tsc_freq(Duration::from_millis(20))
            .expect("calibration should succeed on x86-64");
        // Any real x86-64 TSC is between 500 MHz and 10 GHz.
        assert!(
            (500_000_000..=10_000_000_000).contains(&freq),
            "implausible TSC frequency: {freq} Hz"
        );
    }

    #[test]
    fn calibration_is_repeatable() {
        let a = calibrate_tsc_freq(Duration::from_millis(20)).unwrap() as f64;
        let b = calibrate_tsc_freq(Duration::from_millis(20)).unwrap() as f64;
        let relative_error = (a - b).abs() / a;
        // An invariant TSC should agree closely across back-to-back runs. The
        // bound is loose because 20 ms of spinning can be preempted on a busy
        // machine, and the failure this guards against is tens of percent.
        assert!(relative_error < 0.03, "calibration unstable: {a} Hz vs {b} Hz");
    }

    #[test]
    fn detect_prefers_calibration() {
        let freq = detect_tsc_freq();
        assert!(freq.is_trustworthy(), "expected a calibrated frequency, got {freq:?}");
        assert!(!freq.is_default());
    }

    #[test]
    fn sysfs_freq_reads_khz_as_hz() {
        assert_eq!(read_sysfs_freq_hz("/nonexistent/cpufreq/base_frequency"), None);

        let path = std::env::temp_dir().join(format!("oak_tsc_freq_{}", std::process::id()));
        std::fs::write(&path, "4200000\n").unwrap();
        let freq = read_sysfs_freq_hz(path.to_str().unwrap());
        let _ = std::fs::remove_file(&path);
        assert_eq!(freq, Some(4_200_000_000));
    }

    #[test]
    fn zero_frequency_does_not_panic() {
        assert_eq!(tsc_to_nanos(0, 0), 0);
        assert_eq!(tsc_to_nanos(12345, 0), 0);
    }

    #[test]
    fn tsc_to_nanos_converts() {
        // 1 GHz: one tick is one nanosecond.
        assert_eq!(tsc_to_nanos(1_000, 1_000_000_000), 1_000);
        // 2 GHz: two ticks per nanosecond.
        assert_eq!(tsc_to_nanos(1_000, 2_000_000_000), 500);
    }
}
