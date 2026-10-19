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

use std::{
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};

use procfs::{Current, Meminfo};

/// Default minimum ratio of available memory (`MemAvailable / MemTotal`)
/// required to admit a new session, corresponding to 80% RAM utilization (20%
/// available).
pub const DEFAULT_MIN_AVAILABLE_MEMORY_RATIO: f64 = 0.20;

/// Default minimum ratio of available memory (`MemAvailable / MemTotal`)
/// required to admit a follow-up RPC on an already-open session, corresponding
/// to 90% RAM utilization (10% available).
pub const DEFAULT_REQUEST_MIN_AVAILABLE_MEMORY_RATIO: f64 = 0.10;

/// How long a sample of `/proc/meminfo` stays fresh for admission control.
///
/// The kernel regenerates `/proc/meminfo` on every read
/// (<https://docs.kernel.org/filesystems/proc.html#meminfo>), so reading and
/// parsing it costs about 30 µs. Admission control checks memory on
/// every follow-up RPC, so the reading is cached to bound that cost no matter
/// how many requests arrive. One second of staleness matches the map count
/// sample interval (`admission::MAP_COUNT_SAMPLE_INTERVAL`) and is small next
/// to the 10% RAM buffer between the new-session and follow-up RPC thresholds.
pub const MEMINFO_SAMPLE_INTERVAL: Duration = Duration::from_secs(1);

/// Function that reads the current system memory info.
pub type MemInfoReader = Arc<dyn Fn() -> Result<MemoryInfo, anyhow::Error> + Send + Sync>;

/// Memory usage information wrapper over procfs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemoryInfo {
    /// Total usable RAM in bytes.
    pub total_bytes: u64,
    /// Available RAM in bytes.
    pub available_bytes: u64,
}

impl MemoryInfo {
    /// Reads current memory info using `procfs`.
    pub fn current() -> Result<Self, anyhow::Error> {
        let meminfo = Meminfo::current()?;
        let available_bytes = meminfo
            .mem_available
            .ok_or_else(|| anyhow::anyhow!("MemAvailable not found in /proc/meminfo"))?;
        Ok(Self { total_bytes: meminfo.mem_total, available_bytes })
    }

    /// Calculates the ratio of available memory to total memory (between 0.0
    /// and 1.0).
    pub fn available_ratio(&self) -> f64 {
        assert!(
            self.total_bytes > 0,
            "MemTotal from /proc/meminfo is zero; cannot compute memory ratio"
        );
        (self.available_bytes as f64 / self.total_bytes as f64).clamp(0.0, 1.0)
    }

    /// Returns true if available memory ratio is below the given threshold
    /// ratio.
    pub fn is_below_threshold(&self, threshold_ratio: f64) -> bool {
        self.available_ratio() < threshold_ratio
    }
}

/// Reads the current system memory info. Used by `app/admission.rs`.
pub fn read_system_meminfo() -> Result<MemoryInfo, anyhow::Error> {
    MemoryInfo::current()
}

/// Wraps `inner` so that it is called at most once per `interval`: calls within
/// the interval return the last successful sample. Errors are not cached, so
/// the next call retries `inner`.
pub fn caching_reader(inner: MemInfoReader, interval: Duration) -> MemInfoReader {
    let cached: Mutex<Option<(Instant, MemoryInfo)>> = Mutex::new(None);
    Arc::new(move || {
        // The lock is held while reading on purpose: concurrent callers wait
        // for, and share, a single read instead of all reading at once.
        let mut cached = cached.lock().unwrap_or_else(|e| e.into_inner());
        if let Some((taken_at, meminfo)) = *cached
            && taken_at.elapsed() < interval
        {
            return Ok(meminfo);
        }
        let meminfo = inner()?;
        *cached = Some((Instant::now(), meminfo));
        Ok(meminfo)
    })
}

/// Returns the reader that admission control uses by default: the system
/// memory info, sampled at most once per [`MEMINFO_SAMPLE_INTERVAL`].
pub fn system_meminfo_reader() -> MemInfoReader {
    caching_reader(Arc::new(read_system_meminfo), MEMINFO_SAMPLE_INTERVAL)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "MemTotal from /proc/meminfo is zero")]
    fn test_zero_total_memory_safety() {
        let meminfo = MemoryInfo { total_bytes: 0, available_bytes: 0 };
        meminfo.available_ratio();
    }

    #[test]
    fn test_ratio_calculation() {
        let meminfo = MemoryInfo { total_bytes: 1000, available_bytes: 500 };
        assert!((meminfo.available_ratio() - 0.50).abs() < 0.001);
        assert!(!meminfo.is_below_threshold(DEFAULT_MIN_AVAILABLE_MEMORY_RATIO));
        assert!(!meminfo.is_below_threshold(DEFAULT_REQUEST_MIN_AVAILABLE_MEMORY_RATIO));

        let meminfo_at_session_threshold = MemoryInfo { total_bytes: 1000, available_bytes: 200 };
        assert!((meminfo_at_session_threshold.available_ratio() - 0.20).abs() < 0.001);
        assert!(
            !meminfo_at_session_threshold.is_below_threshold(DEFAULT_MIN_AVAILABLE_MEMORY_RATIO)
        );

        let meminfo_over_80_pct_used = MemoryInfo { total_bytes: 1000, available_bytes: 150 };
        assert!((meminfo_over_80_pct_used.available_ratio() - 0.15).abs() < 0.001);
        assert!(meminfo_over_80_pct_used.is_below_threshold(DEFAULT_MIN_AVAILABLE_MEMORY_RATIO));
        assert!(
            !meminfo_over_80_pct_used
                .is_below_threshold(DEFAULT_REQUEST_MIN_AVAILABLE_MEMORY_RATIO)
        );

        let meminfo_at_request_threshold = MemoryInfo { total_bytes: 1000, available_bytes: 100 };
        assert!((meminfo_at_request_threshold.available_ratio() - 0.10).abs() < 0.001);
        assert!(
            !meminfo_at_request_threshold
                .is_below_threshold(DEFAULT_REQUEST_MIN_AVAILABLE_MEMORY_RATIO)
        );

        let meminfo_over_90_pct_used = MemoryInfo { total_bytes: 1000, available_bytes: 90 };
        assert!((meminfo_over_90_pct_used.available_ratio() - 0.09).abs() < 0.001);
        assert!(
            meminfo_over_90_pct_used.is_below_threshold(DEFAULT_REQUEST_MIN_AVAILABLE_MEMORY_RATIO)
        );
    }

    /// Returns a reader that reports `available_bytes` out of 1000 and counts
    /// how often it is called, or fails while `available_bytes` is 0.
    fn counting_reader(
        available_bytes: Arc<std::sync::atomic::AtomicU64>,
        calls: Arc<std::sync::atomic::AtomicUsize>,
    ) -> MemInfoReader {
        use std::sync::atomic::Ordering;
        Arc::new(move || {
            calls.fetch_add(1, Ordering::SeqCst);
            match available_bytes.load(Ordering::SeqCst) {
                0 => Err(anyhow::anyhow!("procfs unavailable")),
                available_bytes => Ok(MemoryInfo { total_bytes: 1000, available_bytes }),
            }
        })
    }

    #[test]
    fn caching_reader_reuses_sample_within_interval() {
        use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

        let available = Arc::new(AtomicU64::new(500));
        let calls = Arc::new(AtomicUsize::new(0));
        let reader = caching_reader(
            counting_reader(available.clone(), calls.clone()),
            Duration::from_secs(3600),
        );

        assert_eq!(reader().unwrap().available_bytes, 500);
        available.store(100, Ordering::SeqCst);
        // Still the cached sample, without reading again.
        assert_eq!(reader().unwrap().available_bytes, 500);
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn caching_reader_resamples_after_interval() {
        use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

        let available = Arc::new(AtomicU64::new(500));
        let calls = Arc::new(AtomicUsize::new(0));
        let reader =
            caching_reader(counting_reader(available.clone(), calls.clone()), Duration::ZERO);

        assert_eq!(reader().unwrap().available_bytes, 500);
        available.store(100, Ordering::SeqCst);
        assert_eq!(reader().unwrap().available_bytes, 100);
        assert_eq!(calls.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn caching_reader_does_not_cache_errors() {
        use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

        let available = Arc::new(AtomicU64::new(0));
        let calls = Arc::new(AtomicUsize::new(0));
        let reader = caching_reader(
            counting_reader(available.clone(), calls.clone()),
            Duration::from_secs(3600),
        );

        assert!(reader().is_err());
        available.store(500, Ordering::SeqCst);
        assert_eq!(reader().unwrap().available_bytes, 500);
        assert_eq!(calls.load(Ordering::SeqCst), 2);
    }
}
