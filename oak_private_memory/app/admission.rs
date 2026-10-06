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

//! Admission control for new sessions.
//!
//! [`AdmissionController`] decides, before any expensive per-session work,
//! whether the enclave accepts a new session. It rejects the session with
//! `RESOURCE_EXHAUSTED` when any of these limits is reached:
//!
//! - **Live sessions:** the number of live sessions reaches
//!   `max_active_sessions`.
//! - **Memory mappings:** the process map count reaches `max_map_count_ratio`
//!   of the kernel's `vm.max_map_count`.
//! - **Available memory:** `MemAvailable / MemTotal` falls below
//!   `min_available_memory_ratio`.
//!
//! A session is counted from admission until its [`ActiveSessionGuard`] is
//! dropped. The guard travels with the session's `UserSessionContext` into
//! the persistence worker, so sessions waiting to be persisted keep counting.
//!
//! ## Why limit memory mappings
//!
//! Each session owns an Icing instance, which uses ~55-70 memory mappings but
//! little RAM. Once the process reaches `vm.max_map_count`, every `mmap` fails
//! and Icing crashes the whole server, so the memory check alone cannot
//! prevent it. `vm.max_map_count` is read once at startup: it is a guest
//! kernel sysctl that doesn't change while the enclave runs, so a new limit
//! takes effect on the next restart.

use std::{
    io::Read,
    path::{Path, PathBuf},
    sync::{
        Arc, Mutex,
        atomic::{AtomicUsize, Ordering},
    },
    time::{Duration, Instant},
};

use metrics::SessionRejectReason;

pub const DEFAULT_MAX_ACTIVE_SESSIONS: usize = 1000;

/// Default fraction of `vm.max_map_count` above which new sessions are
/// rejected. The remaining 20% is headroom for sessions admitted before the
/// next sample and for maps that existing sessions add as they grow.
pub const DEFAULT_MAX_MAP_COUNT_RATIO: f64 = 0.8;

/// Fallback value for `vm.max_map_count` when `/proc/sys/vm/max_map_count`
/// cannot be read or parsed. Matches the `sysctl.vm.max_map_count=1048576`
/// guest kernel boot parameter configured by the host (see
/// <https://docs.kernel.org/admin-guide/sysctl/vm.html#max-map-count>).
pub const DEFAULT_MAX_MAP_COUNT: u64 = 1_048_576;

/// How long a sampled map count stays fresh. Linux procfs
/// (<https://docs.kernel.org/filesystems/proc.html>) does not expose a
/// `/proc/self/map_count` file or include `mm_struct::map_count` in
/// `/proc/self/status` or `/proc/self/stat`, so the VMA count is read by
/// counting lines in `/proc/self/maps`. Near the limit that means reading a
/// few MB, so it is done at most once per interval no matter how many sessions
/// arrive.
pub const MAP_COUNT_SAMPLE_INTERVAL: Duration = Duration::from_secs(1);

const PROC_SELF_MAPS: &str = "/proc/self/maps";
const PROC_MAX_MAP_COUNT: &str = "/proc/sys/vm/max_map_count";

/// Counts live sessions. Slots are reserved with [`Self::try_acquire`] and
/// released when the returned [`ActiveSessionGuard`] is dropped.
pub struct SessionCounter {
    active: AtomicUsize,
    metrics: Arc<metrics::Metrics>,
}

impl SessionCounter {
    pub fn new(metrics: Arc<metrics::Metrics>) -> Arc<Self> {
        Arc::new(Self { active: AtomicUsize::new(0), metrics })
    }

    /// Returns the number of currently live sessions.
    pub fn active(&self) -> usize {
        self.active.load(Ordering::Acquire)
    }

    /// Atomically reserves a session slot.
    ///
    /// Returns the current count as the error if `max` sessions are already
    /// live.
    pub fn try_acquire(self: &Arc<Self>, max: usize) -> Result<ActiveSessionGuard, usize> {
        let previous =
            self.active.fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
                if current >= max { None } else { Some(current + 1) }
            })?;
        self.metrics.record_active_sessions((previous + 1) as u64);
        Ok(ActiveSessionGuard { counter: self.clone() })
    }

    fn release(&self) {
        // Every guard comes from `try_acquire`, so the count can't underflow.
        // Saturate anyway: a wrapped counter would reject every new session
        // until restart.
        let previous = self
            .active
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |c| Some(c.saturating_sub(1)))
            .expect("closure always returns Some");
        debug_assert!(previous > 0, "session counter underflow");
        if previous == 0 {
            // The debug_assert above is compiled out in release builds.
            log::error!("session counter underflow: released a slot with no active sessions");
        }
        self.metrics.record_active_sessions(previous.saturating_sub(1) as u64);
    }
}

/// RAII guard for one live session. Dropping it releases the slot.
pub struct ActiveSessionGuard {
    counter: Arc<SessionCounter>,
}

impl std::fmt::Debug for ActiveSessionGuard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ActiveSessionGuard").finish_non_exhaustive()
    }
}

impl Drop for ActiveSessionGuard {
    fn drop(&mut self) {
        self.counter.release();
    }
}

/// Samples the process map count and compares it to `vm.max_map_count`.
pub struct MapCountMonitor {
    maps_path: PathBuf,
    /// `vm.max_map_count`, read once at startup (or
    /// [`DEFAULT_MAX_MAP_COUNT`] if unreadable).
    max_map_count: u64,
    sample_interval: Duration,
    /// The last sample and when it was taken.
    cached: Mutex<Option<(Instant, u64)>>,
}

impl MapCountMonitor {
    /// Creates a monitor for the current process using `/proc`.
    pub fn new_for_current_process() -> Self {
        Self::new(
            Path::new(PROC_SELF_MAPS),
            Path::new(PROC_MAX_MAP_COUNT),
            MAP_COUNT_SAMPLE_INTERVAL,
        )
    }

    pub fn new(maps_path: &Path, max_map_count_path: &Path, sample_interval: Duration) -> Self {
        let max_map_count = match std::fs::read_to_string(max_map_count_path)
            .map_err(anyhow::Error::from)
            .and_then(|s| s.trim().parse::<u64>().map_err(anyhow::Error::from))
            .and_then(|v| {
                if v > 0 {
                    Ok(v)
                } else {
                    Err(anyhow::anyhow!("vm.max_map_count must be greater than 0"))
                }
            }) {
            Ok(v) => v,
            Err(e) => {
                log::warn!(
                    "reading {max_map_count_path:?}: {e}, falling back to default ({DEFAULT_MAX_MAP_COUNT})"
                );
                DEFAULT_MAX_MAP_COUNT
            }
        };
        Self {
            maps_path: maps_path.to_path_buf(),
            max_map_count,
            sample_interval,
            cached: Mutex::new(None),
        }
    }

    /// The cached `vm.max_map_count`.
    pub fn max_map_count(&self) -> u64 {
        self.max_map_count
    }

    /// Returns the process map count, re-reading it only if the cached sample
    /// is older than the sample interval. Returns `None` if it can't be read.
    pub fn map_count(&self, metrics: &metrics::Metrics) -> Option<u64> {
        let mut cached = self.cached.lock().unwrap_or_else(|e| e.into_inner());
        if let Some((taken_at, count)) = *cached
            && taken_at.elapsed() < self.sample_interval
        {
            metrics.record_process_map_count(count);
            return Some(count);
        }
        match count_lines(&self.maps_path) {
            Ok(count) => {
                *cached = Some((Instant::now(), count));
                metrics.record_process_map_count(count);
                Some(count)
            }
            Err(e) => {
                log::warn!("reading {:?}: {e}", self.maps_path);
                None
            }
        }
    }
}

/// Counts newline characters in a file without allocating it in full.
fn count_lines(path: &Path) -> std::io::Result<u64> {
    let mut file = std::fs::File::open(path)?;
    let mut buf = vec![0u8; 64 * 1024];
    let mut count = 0u64;
    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            return Ok(count);
        }
        count += buf[..n].iter().filter(|&&b| b == b'\n').count() as u64;
    }
}

/// Decides whether a new session may start.
pub struct AdmissionController {
    max_active_sessions: usize,
    max_map_count_ratio: f64,
    min_available_memory_ratio: f64,
    sessions: Arc<SessionCounter>,
    map_monitor: MapCountMonitor,
    metrics: Arc<metrics::Metrics>,
}

impl AdmissionController {
    pub fn new(
        max_active_sessions: usize,
        max_map_count_ratio: f64,
        min_available_memory_ratio: f64,
        map_monitor: MapCountMonitor,
        metrics: Arc<metrics::Metrics>,
    ) -> Self {
        // Panic on misconfiguration to surface the error early rather than
        // silently disabling.
        assert!(
            min_available_memory_ratio > 0.0 && min_available_memory_ratio < 1.0,
            "Misconfigured min_available_memory_ratio! Must be in (0.0, 1.0)."
        );
        assert!(
            max_active_sessions > 0,
            "Misconfigured max_active_sessions! Must be greater than 0."
        );
        assert!(
            max_map_count_ratio > 0.0 && max_map_count_ratio <= 1.0,
            "Misconfigured max_map_count_ratio! Must be in (0.0, 1.0]."
        );
        log::info!(
            "admission control: max_active_sessions={max_active_sessions}, max_map_count_ratio={max_map_count_ratio} (vm.max_map_count={}), min_available_memory_ratio={min_available_memory_ratio}",
            map_monitor.max_map_count()
        );
        metrics.record_max_active_sessions(max_active_sessions as u64);
        Self {
            max_active_sessions,
            max_map_count_ratio,
            min_available_memory_ratio,
            sessions: SessionCounter::new(metrics.clone()),
            map_monitor,
            metrics,
        }
    }

    /// Number of currently live sessions.
    pub fn active_sessions(&self) -> usize {
        self.sessions.active()
    }

    /// Refreshes the `active_sessions`, `max_active_sessions` and
    /// `process_map_count` gauges. Intended to be called periodically so the
    /// gauges stay fresh even when no new sessions arrive.
    pub fn refresh_gauges(&self) {
        self.metrics.record_active_sessions(self.sessions.active() as u64);
        self.metrics.record_max_active_sessions(self.max_active_sessions as u64);
        let _ = self.map_monitor.map_count(&self.metrics);
    }

    /// Admits a new session or rejects it with `RESOURCE_EXHAUSTED`.
    ///
    /// Call this before any expensive work (handshake, Icing init). The
    /// returned guard must be kept alive for as long as the session (and its
    /// Icing instance) lives.
    pub fn admit(&self) -> tonic::Result<ActiveSessionGuard> {
        // Cheapest check first; it also atomically reserves the slot, so
        // concurrent admissions can't overshoot the cap.
        let guard = match self.sessions.try_acquire(self.max_active_sessions) {
            Ok(guard) => guard,
            Err(active) => {
                return Err(self.reject(
                    SessionRejectReason::MaxSessions,
                    format!(
                        "too many active sessions: {active} (limit: {})",
                        self.max_active_sessions
                    ),
                ));
            }
        };
        // On rejection below, `guard` is dropped and the slot released.
        self.check_map_count()?;
        self.check_memory_availability()?;
        Ok(guard)
    }

    fn check_map_count(&self) -> tonic::Result<()> {
        // Fail open if the map count can't be read.
        let Some(map_count) = self.map_monitor.map_count(&self.metrics) else {
            return Ok(());
        };
        let max_map_count = self.map_monitor.max_map_count();
        let limit = (max_map_count as f64 * self.max_map_count_ratio) as u64;
        if map_count >= limit {
            return Err(self.reject(
                SessionRejectReason::MapCount,
                format!(
                    "server is close to its memory mapping limit: {map_count} maps (limit: {limit} = {:.0}% of vm.max_map_count {max_map_count})",
                    self.max_map_count_ratio * 100.0
                ),
            ));
        }
        Ok(())
    }

    /// Checks system available memory against `min_available_memory_ratio`.
    fn check_memory_availability(&self) -> tonic::Result<()> {
        let threshold = self.min_available_memory_ratio;
        match crate::meminfo::read_system_meminfo() {
            Ok(meminfo) => {
                if meminfo.is_below_threshold(threshold) {
                    return Err(self.reject(
                        SessionRejectReason::LowMemory,
                        format!(
                            "server memory is critically low: {:.1}% available (threshold: {:.1}%)",
                            meminfo.available_ratio() * 100.0,
                            threshold * 100.0
                        ),
                    ));
                }
            }
            Err(e) => {
                // Log warning when meminfo cannot be read (e.g. non-Linux or test env), fail
                // open.
                log::warn!("reading /proc/meminfo: {e}");
            }
        }
        Ok(())
    }

    fn reject(&self, reason: SessionRejectReason, message: String) -> tonic::Status {
        self.metrics.inc_session_rejected(reason);
        log::warn!("rejecting new session ({}): {message}", reason.as_str());
        tonic::Status::resource_exhausted(message)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use super::*;

    struct TempFiles {
        dir: PathBuf,
    }

    impl TempFiles {
        fn new(name: &str) -> Self {
            let dir = std::env::temp_dir().join(format!(
                "admission-test-{name}-{}-{:?}",
                std::process::id(),
                std::thread::current().id()
            ));
            std::fs::create_dir_all(&dir).unwrap();
            Self { dir }
        }

        fn write(&self, name: &str, contents: &str) -> PathBuf {
            let path = self.dir.join(name);
            std::fs::File::create(&path).unwrap().write_all(contents.as_bytes()).unwrap();
            path
        }
    }

    impl Drop for TempFiles {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.dir);
        }
    }

    fn maps_with_lines(n: usize) -> String {
        "00400000-00452000 r-xp 00000000 08:02 173521 /bin/x\n".repeat(n)
    }

    fn controller(ratio: f64, monitor: MapCountMonitor) -> AdmissionController {
        controller_with_cap(DEFAULT_MAX_ACTIVE_SESSIONS, ratio, monitor)
    }

    fn controller_with_cap(
        max_active_sessions: usize,
        ratio: f64,
        monitor: MapCountMonitor,
    ) -> AdmissionController {
        AdmissionController::new(
            max_active_sessions,
            ratio,
            crate::meminfo::DEFAULT_MIN_AVAILABLE_MEMORY_RATIO,
            monitor,
            metrics::get_global_metrics(),
        )
    }

    fn disabled_monitor() -> MapCountMonitor {
        MapCountMonitor::new(
            Path::new("/nonexistent/maps"),
            Path::new("/nonexistent/max_map_count"),
            Duration::ZERO,
        )
    }

    #[test]
    fn session_counter_tracks_guards() {
        let counter = SessionCounter::new(metrics::get_global_metrics());
        assert_eq!(counter.active(), 0);
        let a = counter.try_acquire(2).unwrap();
        let b = counter.try_acquire(2).unwrap();
        assert_eq!(counter.active(), 2);
        drop(a);
        assert_eq!(counter.active(), 1);
        drop(b);
        assert_eq!(counter.active(), 0);
    }

    #[test]
    fn session_counter_enforces_max() {
        let counter = SessionCounter::new(metrics::get_global_metrics());
        let a = counter.try_acquire(2).unwrap();
        let _b = counter.try_acquire(2).unwrap();
        assert_eq!(counter.try_acquire(2).unwrap_err(), 2);
        drop(a);
        assert!(counter.try_acquire(2).is_ok());
    }

    #[test]
    fn session_counter_concurrent_acquire_never_overshoots() {
        let counter = SessionCounter::new(metrics::get_global_metrics());
        let held: Vec<ActiveSessionGuard> = std::thread::scope(|s| {
            let handles: Vec<_> = (0..8)
                .map(|_| {
                    let counter = counter.clone();
                    s.spawn(move || {
                        (0..100).filter_map(|_| counter.try_acquire(500).ok()).collect::<Vec<_>>()
                    })
                })
                .collect();
            handles.into_iter().flat_map(|h| h.join().unwrap()).collect()
        });
        assert_eq!(held.len(), 500);
        assert_eq!(counter.active(), 500);
        drop(held);
        assert_eq!(counter.active(), 0);
    }

    #[test]
    fn admit_rejects_at_max_active_sessions() {
        let admission = controller_with_cap(2, DEFAULT_MAX_MAP_COUNT_RATIO, disabled_monitor());
        let a = admission.admit().unwrap();
        let _b = admission.admit().unwrap();
        let err = admission.admit().unwrap_err();
        assert_eq!(err.code(), tonic::Code::ResourceExhausted);
        assert!(err.message().contains("too many active sessions"), "{}", err.message());
        assert_eq!(admission.active_sessions(), 2);
        // Closing a session frees a slot.
        drop(a);
        assert!(admission.admit().is_ok());
    }

    #[test]
    #[should_panic(expected = "Misconfigured max_active_sessions")]
    fn zero_max_active_sessions_panics() {
        controller_with_cap(0, DEFAULT_MAX_MAP_COUNT_RATIO, disabled_monitor());
    }

    #[test]
    fn slot_is_released_when_a_later_check_rejects() {
        let files = TempFiles::new("slot_released");
        let maps = files.write("maps", &maps_with_lines(80));
        let max = files.write("max_map_count", "100\n");
        let admission =
            controller_with_cap(1, 0.8, MapCountMonitor::new(&maps, &max, Duration::ZERO));
        assert!(admission.admit().is_err());
        assert_eq!(admission.active_sessions(), 0);
        // Once maps drop, the single slot is still available.
        files.write("maps", &maps_with_lines(10));
        assert!(admission.admit().is_ok());
    }

    #[test]
    fn admitted_sessions_are_counted_until_dropped() {
        let admission = controller(DEFAULT_MAX_MAP_COUNT_RATIO, disabled_monitor());
        let a = admission.admit().unwrap();
        let _b = admission.admit().unwrap();
        assert_eq!(admission.active_sessions(), 2);
        drop(a);
        assert_eq!(admission.active_sessions(), 1);
    }

    #[test]
    fn admit_rejects_when_map_count_above_ratio() {
        let files = TempFiles::new("map_count_reject");
        let maps = files.write("maps", &maps_with_lines(80));
        let max = files.write("max_map_count", "100\n");
        let admission = controller(0.8, MapCountMonitor::new(&maps, &max, Duration::ZERO));
        let err = admission.admit().unwrap_err();
        assert_eq!(err.code(), tonic::Code::ResourceExhausted);
        assert!(err.message().contains("memory mapping limit"), "{}", err.message());
        // Rejected sessions are not counted.
        assert_eq!(admission.active_sessions(), 0);

        // Below the threshold, sessions are admitted.
        files.write("maps", &maps_with_lines(79));
        let _guard = admission.admit().unwrap();
        assert_eq!(admission.active_sessions(), 1);
    }

    #[test]
    fn admit_fails_open_when_proc_unreadable() {
        let admission = controller(0.8, disabled_monitor());
        assert!(admission.admit().is_ok());
    }

    #[test]
    fn map_count_is_cached_within_sample_interval() {
        let files = TempFiles::new("map_count_cache");
        let maps = files.write("maps", &maps_with_lines(10));
        let max = files.write("max_map_count", "65530");
        let monitor = MapCountMonitor::new(&maps, &max, Duration::from_secs(3600));
        let metrics = metrics::get_global_metrics();
        assert_eq!(monitor.max_map_count(), 65530);
        assert_eq!(monitor.map_count(&metrics), Some(10));
        files.write("maps", &maps_with_lines(20));
        // Still the cached value.
        assert_eq!(monitor.map_count(&metrics), Some(10));

        let fresh = MapCountMonitor::new(&maps, &max, Duration::ZERO);
        assert_eq!(fresh.map_count(&metrics), Some(20));
    }

    #[test]
    fn max_map_count_falls_back_to_default_when_unreadable_or_zero() {
        let files = TempFiles::new("max_map_count_default");
        let maps = files.write("maps", &maps_with_lines(10));
        let missing = Path::new("/nonexistent/max_map_count");
        let monitor = MapCountMonitor::new(&maps, missing, Duration::ZERO);
        assert_eq!(monitor.max_map_count(), DEFAULT_MAX_MAP_COUNT);

        let zero = files.write("max_map_count", "0\n");
        let zero_monitor = MapCountMonitor::new(&maps, &zero, Duration::ZERO);
        assert_eq!(zero_monitor.max_map_count(), DEFAULT_MAX_MAP_COUNT);
    }

    #[test]
    fn current_process_map_count_is_readable() {
        let monitor = MapCountMonitor::new_for_current_process();
        let metrics = metrics::get_global_metrics();
        assert!(monitor.max_map_count() > 0);
        assert!(monitor.map_count(&metrics).unwrap() > 0);
    }

    #[test]
    #[should_panic(expected = "Misconfigured max_map_count_ratio")]
    fn invalid_map_count_ratio_panics() {
        controller(1.5, disabled_monitor());
    }
}
