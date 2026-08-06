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

//! Null syscall latency, the cost of one user/kernel round trip.
//!
//! The analogue of lmbench's `lat_syscall null`, which measures `getppid()` on
//! the grounds that it is the cheapest call the kernel offers, so what remains
//! is almost entirely entry and exit cost. See McVoy and Staelin, "lmbench:
//! Portable Tools for Performance Analysis" (USENIX ATC 1996),
//! <https://www.usenix.org/legacy/publications/library/proceedings/sd96/mcvoy.html>.
//!
//! This crate compiles unchanged for both platforms and so cannot name a
//! syscall itself; the host application installs a [`NullSyscall`] probe. With
//! none installed the benchmark returns
//! [`BenchmarkError::UnsupportedBenchmark`] rather than measuring something
//! else.
//!
//! The two sides do not run the same syscall, and any figure from this has to
//! say so. Oak invokes `write(-1, NULL, 0)`, which the Restricted Kernel
//! returns from before looking up the descriptor
//! (`oak_restricted_kernel/src/syscall/fd.rs`), while Linux invokes
//! `getppid()`. Using `write` on both would charge Linux for the `fdget_pos` it
//! does before noticing the zero length, in `fs/read_write.c`. Taking each
//! kernel's cheapest call is lmbench's approach, but it makes this a comparison
//! of kernels rather than of one syscall.
//!
//! Several small effects push in both directions, and they depend on the host,
//! so record the mitigation state from
//! `/sys/devices/system/cpu/vulnerabilities/` with each run rather than
//! trusting this comment. Oak's entry stub pushes fourteen general-purpose
//! registers and then saves 512 bytes of `YMM` state on top
//! (`oak_restricted_kernel/src/syscall/mod.rs`), where Linux pushes a
//! comparable `pt_regs` frame but is built without SSE and brackets its own
//! SIMD with `kernel_fpu_begin`. Oak in exchange dispatches through a `match`
//! on a small enum rather than a several-hundred-entry call table, and runs no
//! exit-to-user work loop. KPTI is not a factor: Linux leaves it off on AMD
//! parts, which are not affected by Meltdown, unless `pti=on` is forced — the
//! mitigation state above will show that.
//!
//! The checksum here witnesses nothing. The two syscalls return different
//! values by construction, so it can only be folded from the count of
//! successful returns — and the run already fails with
//! [`BenchmarkError::SyscallFailure`] unless that count equals the requested
//! iterations. It therefore matches across platforms for free. The error return
//! is the guard. Nothing detects a probe that succeeds while doing less than it
//! should; for that, compare against [`NoSyscall`] and treat a ratio near one
//! as a failed run.
//!
//! [`NoSyscall`] performs no syscall, so running against it measures the
//! harness: the loop, the indirect call, the barrier and the timer. Subtracting
//! a platform's control from its own figure estimates the kernel transition,
//! but only estimates it, since the two loops leave the branch predictor and
//! caches in different states. Report both numbers. Without the control, a
//! difference in how well each build devirtualises the probe would be
//! indistinguishable from a difference in syscall cost.

use crate::{
    BenchmarkError, BenchmarkResult, CHECKSUM_INIT, checksum_update, timer::BenchmarkTimer,
};

/// A platform-specific syscall for the null syscall benchmark to invoke.
///
/// Installed on the service with
/// [`with_null_syscall`](crate::service::BenchmarkService::with_null_syscall).
///
/// A trait rather than a function pointer so a test can supply an
/// implementation that counts its own calls, which a `fn() -> i64` could only
/// do through a global. `Sync` because the Linux baseline shares one probe
/// across a thread pool.
pub trait NullSyscall: Sync {
    /// Invokes the syscall and returns its raw result.
    ///
    /// Must return a negative value if and only if the call failed, following
    /// the usual kernel convention. The benchmark checks this on every
    /// iteration, because a failing syscall may take a much shorter path than
    /// a successful one.
    ///
    /// Implementations must not allocate, must not block, and must not perform
    /// any work beyond the call itself. Nothing enforces this.
    fn invoke(&self) -> i64;

    /// Name of the syscall, reported alongside the result.
    ///
    /// The two platforms invoke different syscalls, so a result is only
    /// interpretable if it says which one produced it.
    fn name(&self) -> &'static str;
}

/// A probe that invokes nothing, for measuring the harness overhead.
///
/// See the module documentation on loop overhead.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoSyscall;

impl NullSyscall for NoSyscall {
    #[inline]
    fn invoke(&self) -> i64 {
        0
    }

    fn name(&self) -> &'static str {
        "none (control)"
    }
}

/// Null syscall latency benchmark.
pub struct NullSyscallBenchmark<'a> {
    probe: &'a dyn NullSyscall,
}

impl core::fmt::Debug for NullSyscallBenchmark<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("NullSyscallBenchmark").field("syscall", &self.probe.name()).finish()
    }
}

impl<'a> NullSyscallBenchmark<'a> {
    /// Create a benchmark that invokes `probe`.
    pub fn new(probe: &'a dyn NullSyscall) -> Self {
        Self { probe }
    }

    /// The syscall this benchmark invokes.
    pub fn syscall_name(&self) -> &'static str {
        self.probe.name()
    }

    /// Invoke the syscall `iterations` times and report the elapsed time.
    ///
    /// There is no allocation and no setup, so nothing needs to happen
    /// outside the timed region other than the warmup, which exists to fault
    /// in the entry path and settle the branch predictors.
    pub fn run<T: BenchmarkTimer>(
        &self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        if iterations == 0 {
            return Err(BenchmarkError::InvalidParameter);
        }

        for _ in 0..warmup_iterations {
            if self.probe.invoke() < 0 {
                return Err(BenchmarkError::SyscallFailure);
            }
        }

        // The count is incremented from the syscall's actual return value, so
        // it is evidence that the calls happened rather than a restatement of
        // the request. The `black_box` makes the result opaque to the
        // optimiser: today both probes are `asm!` blocks with side effects and
        // cannot be hoisted or collapsed anyway, but the trait admits probes
        // for which that is not true, and the control probe is one of them.
        let mut successes = 0u64;
        let timer = T::start();
        for _ in 0..iterations {
            if core::hint::black_box(self.probe.invoke()) >= 0 {
                successes += 1;
            }
        }
        let timing = timer.stop();

        if successes != iterations as u64 {
            return Err(BenchmarkError::SyscallFailure);
        }

        // No bytes move, so throughput is not a meaningful metric here; the
        // host reports time and cycles per operation instead.
        let bytes_processed = 0;
        let checksum = checksum_update(CHECKSUM_INIT, &successes.to_le_bytes());
        Ok(BenchmarkResult::new(timing, iterations, bytes_processed, checksum))
    }
}

#[cfg(test)]
mod tests {
    use core::sync::atomic::{AtomicU64, Ordering};

    use super::*;
    use crate::timer::NativeTimer;

    /// A probe that counts its own invocations.
    ///
    /// Each test constructs its own, so tests running in parallel cannot
    /// disturb each other's counts.
    #[derive(Default)]
    struct CountingProbe {
        calls: AtomicU64,
    }

    impl CountingProbe {
        fn calls(&self) -> u64 {
            self.calls.load(Ordering::Relaxed)
        }
    }

    impl NullSyscall for CountingProbe {
        fn invoke(&self) -> i64 {
            self.calls.fetch_add(1, Ordering::Relaxed);
            0
        }

        fn name(&self) -> &'static str {
            "counting"
        }
    }

    struct FailingProbe;

    impl NullSyscall for FailingProbe {
        fn invoke(&self) -> i64 {
            -1
        }

        fn name(&self) -> &'static str {
            "failing"
        }
    }

    #[test]
    fn invokes_the_probe_once_per_iteration_plus_warmup() {
        let probe = CountingProbe::default();
        NullSyscallBenchmark::new(&probe).run::<NativeTimer>(100, 7).unwrap();
        assert_eq!(probe.calls(), 107);
    }

    #[test]
    fn zero_iterations_is_rejected() {
        let probe = CountingProbe::default();
        let bench = NullSyscallBenchmark::new(&probe);
        assert_eq!(bench.run::<NativeTimer>(0, 0).unwrap_err(), BenchmarkError::InvalidParameter);
        assert_eq!(probe.calls(), 0);
    }

    /// A syscall that fails takes a different, usually shorter path, so a run
    /// containing failures is not a measurement of anything.
    #[test]
    fn a_failing_syscall_fails_the_benchmark() {
        let bench = NullSyscallBenchmark::new(&FailingProbe);
        assert_eq!(bench.run::<NativeTimer>(10, 0).unwrap_err(), BenchmarkError::SyscallFailure);
        assert_eq!(bench.run::<NativeTimer>(10, 1).unwrap_err(), BenchmarkError::SyscallFailure);
    }

    /// The checksum follows the requested iterations and ignores the warmup.
    ///
    /// A count that does not match the request cannot reach the checksum at
    /// all; `a_failing_syscall_fails_the_benchmark` covers that.
    #[test]
    fn checksum_varies_with_the_iteration_count_but_not_the_warmup() {
        let probe = CountingProbe::default();
        let bench = NullSyscallBenchmark::new(&probe);
        let a = bench.run::<NativeTimer>(64, 0).unwrap();
        let b = bench.run::<NativeTimer>(64, 4).unwrap();
        let c = bench.run::<NativeTimer>(65, 0).unwrap();
        assert_eq!(a.checksum, b.checksum);
        assert_ne!(a.checksum, c.checksum);
    }

    #[test]
    fn reports_the_syscall_name() {
        let probe = CountingProbe::default();
        assert_eq!(NullSyscallBenchmark::new(&probe).syscall_name(), "counting");
        assert_eq!(NullSyscallBenchmark::new(&NoSyscall).syscall_name(), "none (control)");
    }

    /// The control probe has to be runnable on both platforms, which means it
    /// must satisfy the same success convention as a real syscall.
    #[test]
    fn the_control_probe_runs() {
        let result = NullSyscallBenchmark::new(&NoSyscall).run::<NativeTimer>(1000, 10).unwrap();
        assert_eq!(result.iterations_completed, 1000);
        assert_eq!(result.bytes_processed, 0);
    }
}
