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

//! Tests for BenchmarkService.

use oak_benchmark_proto_rust::oak::benchmark::{BenchmarkType, RunBenchmarkRequest};

use super::service::BenchmarkService;
use crate::{BenchmarkError, NativeTimer, NullSyscall};

/// Builds a small request for `benchmark_type` with everything else defaulted.
fn request_for(benchmark_type: BenchmarkType) -> RunBenchmarkRequest {
    RunBenchmarkRequest {
        benchmark_type: benchmark_type as i32,
        data_size: 1024,
        iterations: 8,
        warmup_iterations: 1,
        seed: Some(0xABCD_EF01),
        working_set_size: 0,
    }
}

#[test]
fn test_service_unsupported() {
    let mut svc = BenchmarkService::<NativeTimer>::new(0);
    let request = RunBenchmarkRequest {
        benchmark_type: 9999,
        data_size: 1024,
        iterations: 100,
        warmup_iterations: 0,
        seed: None,
        working_set_size: 0,
    };

    let response = svc.handle_request(request);
    assert_eq!(response.status, BenchmarkError::UnsupportedBenchmark.as_status_code());
}

#[test]
fn test_service_rejects_zero_iterations() {
    let mut svc = BenchmarkService::<NativeTimer>::new(0);
    let mut request = request_for(BenchmarkType::Sha256);
    request.iterations = 0;

    let response = svc.handle_request(request);
    assert_ne!(response.status, 0, "zero iterations must be rejected");
}

/// Whether the service can run this benchmark type with no host support.
///
/// Written as an exhaustive `match` on purpose. Adding a variant to the proto
/// stops this compiling until the new benchmark is classified, which is what
/// keeps [`test_service_supports_all_benchmark_types`] honest: the list it
/// used to iterate was maintained by hand, so a new benchmark could be added
/// and never smoke tested.
fn is_self_contained(benchmark_type: BenchmarkType) -> bool {
    match benchmark_type {
        BenchmarkType::Sha256
        | BenchmarkType::Sha512
        | BenchmarkType::Sha3256
        | BenchmarkType::Sha3512
        | BenchmarkType::P256Sign
        | BenchmarkType::P256Verify
        | BenchmarkType::Ed25519Sign
        | BenchmarkType::Ed25519Verify
        | BenchmarkType::Aes256GcmSeal
        | BenchmarkType::Aes256GcmOpen
        | BenchmarkType::MemoryInsert
        | BenchmarkType::MemoryLookup
        | BenchmarkType::MemoryChurn
        | BenchmarkType::ArrayUpdate
        | BenchmarkType::AllocChurn
        | BenchmarkType::PointerChase
        | BenchmarkType::PageTouch
        | BenchmarkType::SyscallControl => true,

        // Needs a probe only a host application can supply; covered by
        // [`test_null_syscall_runs_with_a_probe`].
        BenchmarkType::NullSyscall => false,

        // Not benchmarks.
        BenchmarkType::Debug | BenchmarkType::Unspecified => false,
    }
}

/// Every benchmark type the service should be able to run unaided.
///
/// Discovered by scanning the proto's tag space rather than listed here, so
/// that nothing can be added to the enum and quietly left out. The range
/// covers every tag currently assigned in `proto/benchmark.proto`, where the
/// largest is `BENCHMARK_TYPE_DEBUG = 100`; a variant numbered above 255 would
/// be classified by [`is_self_contained`] but never scanned, so keep new tags
/// inside it.
fn self_contained_types() -> alloc::vec::Vec<BenchmarkType> {
    (0..=255i32)
        .filter_map(|tag| BenchmarkType::try_from(tag).ok())
        .filter(|&t| is_self_contained(t))
        .collect()
}

/// Number of types [`is_self_contained`] accepts.
///
/// Asserted exactly rather than as a lower bound, so that deleting a benchmark
/// is as visible as adding one.
const SELF_CONTAINED_COUNT: usize = 18;

/// Every benchmark type the service claims to support must run end to end.
///
/// This is deliberately a smoke test: it asserts success and a non-trivial
/// result rather than any particular throughput, so it stays stable across
/// machines. `iterations_completed` is echoed from the request rather than
/// counted, so it cannot stand in for evidence that anything happened; the
/// checksum is the field that can.
#[test]
fn test_service_supports_all_benchmark_types() {
    let types = self_contained_types();
    assert_eq!(types.len(), SELF_CONTAINED_COUNT, "enum scan found {} types", types.len());

    for benchmark_type in types {
        let mut svc = BenchmarkService::<NativeTimer>::new(0);
        let mut request = request_for(benchmark_type);
        // Keep the memory benchmarks small so the test stays fast.
        request.working_set_size = 1 << 20;

        let response = svc.handle_request(request);
        assert_eq!(response.status, 0, "{benchmark_type:?} returned a non-zero status");
        assert!(
            response.iterations_completed > 0,
            "{benchmark_type:?} reported zero completed iterations"
        );
        assert!(response.elapsed_tsc > 0, "{benchmark_type:?} reported zero elapsed TSC");
        assert_ne!(response.checksum, 0, "{benchmark_type:?} reported an empty checksum");
    }
}

/// Without a probe the service must say so rather than return a number.
#[test]
fn test_null_syscall_is_unsupported_without_a_probe() {
    let mut svc = BenchmarkService::<NativeTimer>::new(0);
    let response = svc.handle_request(request_for(BenchmarkType::NullSyscall));
    assert_eq!(response.status, BenchmarkError::UnsupportedBenchmark.as_status_code());
}

/// With a probe installed it must run, invoke the probe once per iteration
/// plus warmup, and report which syscall it was.
#[test]
fn test_null_syscall_runs_with_a_probe() {
    use alloc::boxed::Box;
    use core::sync::atomic::{AtomicU64, Ordering};

    #[derive(Default)]
    struct Probe {
        calls: AtomicU64,
    }

    impl NullSyscall for Probe {
        fn invoke(&self) -> i64 {
            self.calls.fetch_add(1, Ordering::Relaxed);
            0
        }

        fn name(&self) -> &'static str {
            "test"
        }
    }

    let request = request_for(BenchmarkType::NullSyscall);
    // The probe runs during warmup as well as during the timed loop, so that
    // the first timed call is not the one that faults the code path in.
    let expected_calls = u64::from(request.iterations + request.warmup_iterations);

    // The count lives in the probe rather than in a `static`, so it starts at
    // zero however many times a harness runs this test in one process.
    // `with_null_syscall` takes a `'static` reference, which a local cannot
    // satisfy, so the probe is leaked; it is a few bytes in a test binary.
    let probe: &'static Probe = Box::leak(Box::new(Probe::default()));

    let mut svc = BenchmarkService::<NativeTimer>::new(0).with_null_syscall(probe);
    let response = svc.handle_request(request);
    assert_eq!(response.status, 0);
    assert_eq!(probe.calls.load(Ordering::Relaxed), expected_calls);
    assert_eq!(response.detail, "test");
}

/// The control benchmark needs no probe and must name itself, so a recorded
/// result cannot be mistaken for a real syscall measurement.
#[test]
fn test_syscall_control_needs_no_probe() {
    let mut svc = BenchmarkService::<NativeTimer>::new(0);
    let response = svc.handle_request(request_for(BenchmarkType::SyscallControl));
    assert_eq!(response.status, 0);
    assert_eq!(response.detail, "none (control)");
}

/// Only the syscall benchmarks carry a detail string; anything else would be
/// a stray field in the recorded results.
#[test]
fn test_other_benchmarks_report_no_detail() {
    let mut svc = BenchmarkService::<NativeTimer>::new(0);
    let response = svc.handle_request(request_for(BenchmarkType::Sha256));
    assert!(response.detail.is_empty());
}

/// The same seed must produce the same checksum, otherwise cross-platform
/// comparisons are meaningless.
///
/// Runs over every self-contained type rather than a sample: determinism is
/// the property the whole cross-platform comparison rests on, and it costs
/// little to check all of them.
#[test]
fn test_service_is_deterministic_across_runs() {
    for benchmark_type in self_contained_types() {
        let mut request = request_for(benchmark_type);
        request.working_set_size = 1 << 20;

        let mut first_svc = BenchmarkService::<NativeTimer>::new(0);
        let first = first_svc.handle_request(request);
        let mut second_svc = BenchmarkService::<NativeTimer>::new(0);
        let second = second_svc.handle_request(request);

        assert_eq!(first.status, 0);
        assert_eq!(second.status, 0);
        // Without this the assertion below holds trivially for any benchmark
        // that does not compute a checksum at all.
        assert_ne!(first.checksum, 0, "{benchmark_type:?} reported no checksum");
        assert_eq!(
            first.checksum, second.checksum,
            "{benchmark_type:?} is not deterministic for a fixed seed"
        );
    }
}

/// A later request that changes the seed must not reuse the earlier seed's
/// data, which is what makes `--seed` meaningful within a single session.
#[test]
fn test_service_honours_a_changed_seed() {
    let mut svc = BenchmarkService::<NativeTimer>::new(0);

    let mut first = request_for(BenchmarkType::Sha256);
    first.seed = Some(1);
    let first = svc.handle_request(first);

    let mut second = request_for(BenchmarkType::Sha256);
    second.seed = Some(2);
    let second = svc.handle_request(second);

    assert_eq!(first.status, 0);
    assert_eq!(second.status, 0);
    assert_ne!(
        first.checksum, second.checksum,
        "the second request reused the data generated for the first seed"
    );
}

/// A benchmark that ignored its working set parameter would still pass the
/// smoke test, so check that the value travels back in the response.
#[test]
fn test_working_set_is_echoed_by_memory_benchmarks() {
    let sized = [BenchmarkType::ArrayUpdate, BenchmarkType::PointerChase, BenchmarkType::PageTouch];

    for benchmark_type in sized {
        let mut request = request_for(benchmark_type);
        request.working_set_size = 4 << 20;

        let mut svc = BenchmarkService::<NativeTimer>::new(0);
        let response = svc.handle_request(request);

        assert_eq!(response.status, 0, "{benchmark_type:?} returned a non-zero status");
        assert!(
            response.working_set_size >= 4 << 20,
            "{benchmark_type:?} did not use the requested working set"
        );
    }
}

/// Whether this benchmark's checksum should change when the seed changes.
///
/// Exhaustive for the same reason as [`is_self_contained`]: a new benchmark
/// has to be classified before it compiles, and the default should not be
/// silence.
fn checksum_depends_on_seed(benchmark_type: BenchmarkType) -> bool {
    match benchmark_type {
        // Operate on seed-derived input data.
        BenchmarkType::Sha256
        | BenchmarkType::Sha512
        | BenchmarkType::Sha3256
        | BenchmarkType::Sha3512
        | BenchmarkType::P256Sign
        | BenchmarkType::P256Verify
        | BenchmarkType::Ed25519Sign
        | BenchmarkType::Ed25519Verify
        | BenchmarkType::Aes256GcmSeal
        | BenchmarkType::Aes256GcmOpen
        | BenchmarkType::MemoryInsert
        | BenchmarkType::MemoryLookup
        | BenchmarkType::MemoryChurn
        | BenchmarkType::ArrayUpdate
        | BenchmarkType::PointerChase
        | BenchmarkType::PageTouch => true,

        // Constructed by `AllocChurnBenchmark::with_defaults`, which takes no
        // seed: the size sequence is a fixed cycle. Its checksum still has to
        // witness the work, but seed sensitivity is not the way to check that.
        BenchmarkType::AllocChurn => false,

        // Checksums are a function of the iteration count by construction,
        // which the syscall module documents as a weakened gate.
        BenchmarkType::SyscallControl | BenchmarkType::NullSyscall => false,

        // Not benchmarks.
        BenchmarkType::Debug | BenchmarkType::Unspecified => false,
    }
}

/// The checksum has to witness the work, not just the request parameters.
///
/// Without this a benchmark that returned a constant, or whose accumulator
/// cancelled itself out, would pass every other test in this file: the smoke
/// test would see a status of zero and the determinism test would see two
/// equal constants. Page touch shipped with exactly that defect, and it was
/// invisible because its own unit tests used a region size at which the
/// cancellation did not occur.
///
/// The working set here is deliberately a size the suite actually runs at.
#[test]
fn test_checksums_witness_the_seed() {
    for benchmark_type in self_contained_types() {
        if !checksum_depends_on_seed(benchmark_type) {
            continue;
        }

        let mut request = request_for(benchmark_type);
        request.working_set_size = 1 << 20;

        // The request seed, not the service seed: `handle_request` prefers the
        // request seed whenever it is set, and `request_for` always sets one.
        let mut first_request = request;
        first_request.seed = Some(0x1111_1111);
        let mut second_request = request;
        second_request.seed = Some(0x5EED_5EED);

        let mut first_svc = BenchmarkService::<NativeTimer>::new(0);
        let first = first_svc.handle_request(first_request);
        let mut second_svc = BenchmarkService::<NativeTimer>::new(0);
        let second = second_svc.handle_request(second_request);

        assert_eq!(first.status, 0, "{benchmark_type:?} returned a non-zero status");
        assert_eq!(second.status, 0, "{benchmark_type:?} returned a non-zero status");
        assert_ne!(
            first.checksum, second.checksum,
            "{benchmark_type:?} produces the same checksum for two different seeds, \
             so it cannot witness the work it performed"
        );
    }
}
