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

//! Page touch: the cost of obtaining a fresh region and first writing to it.
//!
//! One iteration allocates `region_size` bytes, writes eight bytes to each
//! 4 KiB page and frees it. The allocation is inside the timed region, because
//! how a platform provisions memory is the thing being measured.
//!
//! On Linux an allocation above glibc's mmap threshold goes to `mmap` and each
//! first write takes a minor fault that the kernel resolves by allocating and
//! zeroing a page. The threshold is dynamic, starting at 128 KiB and rising to
//! the size of any mmapped chunk that is freed; see `M_MMAP_THRESHOLD` in
//! <https://man7.org/linux/man-pages/man3/mallopt.3.html>. On the Restricted
//! Kernel there is no fault path: `syscall::mmap` maps and zeroes the whole
//! request up front, and the enclave heap requests memory in 2 MiB units and
//! never releases it, so only the first iteration reaches the kernel.
//!
//! This measures the end-to-end cost of getting usable memory. It does not
//! isolate the page fault, and no single ratio from it should be quoted without
//! these five caveats:
//!
//! 1. The ratio is a function of the iteration count. Linux re-pays every
//!    iteration; with no warmup the enclave pays once, so its cost is `touch +
//!    one_time / iterations`, falling towards `touch` and taking the ratio up
//!    towards `linux / touch`. At 64 MiB and `--warmup-iterations=0` the
//!    enclave looks 2.6x cheaper at 10 iterations and 26x at 10000, which is
//!    already within a percent of that ceiling. With the default warmup the
//!    one-time cost lands before the timer starts and the ratio is flat. Quote
//!    the curve, and never a single point without its iteration count.
//! 2. The platforms move different volumes of memory: at 64 MiB Linux zeroes
//!    all of it while the enclave writes 16384 words. This is the one place in
//!    the suite where the identical-work rule in [`crate`] is knowingly broken.
//! 3. The enclave reuses one block, so its lines are still resident, while
//!    Linux gets cold physical pages every time.
//! 4. Freeing a block and immediately requesting an identical one is a best
//!    case for TLSF: the block goes back on the free list for its own size
//!    class and comes straight off again, so neither splitting nor coalescing
//!    is exercised.
//! 5. The cold number is partly the host's. Guest RAM is demand-paged from an
//!    ordinary anonymous mapping, so the host faults in and zeroes the same
//!    memory underneath, inside the guest's timed region: a cold 64 MiB region
//!    raises QEMU's peak RSS by 66 MiB, almost all `AnonHugePages`. With
//!    preallocated or pinned private memory this term would be absent.
//!
//! The most defensible configuration is a region at or below 1 MiB, where both
//! allocators recycle in user space and the comparison is TLSF against a glibc
//! arena and nothing else.
//!
//! `vec![0u8; n]` cannot be used to get untouched memory: it routes to
//! `alloc_zeroed`, which glibc serves from lazily-zeroed pages while the
//! enclave allocator really writes the zeroes. `Vec::try_reserve` plus
//! `spare_capacity_mut` gives a `&mut [MaybeUninit<u64>]` neither platform has
//! written, and `MaybeUninit::write` returns `&mut T` so the checksum can read
//! the value back without `unsafe`.

use alloc::vec::Vec;

use crate::{
    BenchmarkError, BenchmarkResult, CHECKSUM_INIT, GOLDEN_RATIO_64, LCG_MULTIPLIER,
    checksum_update, timer::BenchmarkTimer,
};

/// Page size assumed when deciding how far apart to write.
///
/// This is the x86-64 base page size. The enclave's pages are 2 MiB, so it
/// takes 512 of these writes to cover one of its pages; that is the point, and
/// the stride is deliberately the same on both platforms so the two run
/// identical loops over identically sized regions.
pub const PAGE_SIZE: usize = 4096;

/// `u64` elements per page.
const ELEMENTS_PER_PAGE: usize = PAGE_SIZE / core::mem::size_of::<u64>();

/// Default region size (64 MiB), above glibc's 32 MiB mmap threshold cap.
pub const DEFAULT_REGION_SIZE: usize = 64 * 1024 * 1024;

/// Smallest region (64 KiB, 16 pages).
///
/// Small enough that unit tests are cheap. A region this size is below glibc's
/// initial 128 KiB mmap threshold, so it exercises the recycling path rather
/// than the fault path.
pub const MIN_REGION_SIZE: usize = 16 * PAGE_SIZE;

/// Largest region (1 GiB).
///
/// This is allocated and freed once per iteration, so a larger value makes a
/// single iteration take long enough that the iteration count loses its
/// meaning as a calibration knob.
pub const MAX_REGION_SIZE: usize = 1024 * 1024 * 1024;

/// Outcome of one allocate-touch-free cycle.
struct TouchOutcome {
    /// Fold over every value written, read back from memory.
    accumulator: u64,
    /// Pages actually written. Returned rather than recomputed so a test can
    /// assert against what the loop did.
    pages: usize,
    /// Bytes the allocator actually reserved, which is at least the request.
    reserved_bytes: usize,
}

/// Page touch benchmark.
///
/// Holds no working set of its own: every iteration allocates and frees. Only
/// the seed is carried, so that the values written differ between runs with
/// different seeds and the checksum is not a constant.
#[derive(Debug, Clone, Copy)]
pub struct PageTouchBenchmark {
    seed: u64,
}

impl PageTouchBenchmark {
    /// Create a page touch benchmark.
    pub fn new(seed: u64) -> Self {
        Self { seed }
    }

    /// Allocate, touch and free `iterations` times.
    ///
    /// `cycles_per_op` in the result is the cost of one whole
    /// allocate-touch-free cycle. Divide by `working_set_size / PAGE_SIZE` for
    /// a per-page figure; the working set is reported so the caller can.
    ///
    /// Read the module documentation before interpreting the number. In
    /// particular it depends on `iterations` by construction.
    pub fn run<T: BenchmarkTimer>(
        &mut self,
        region_size: usize,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        if iterations == 0 {
            return Err(BenchmarkError::InvalidParameter);
        }
        if !(MIN_REGION_SIZE..=MAX_REGION_SIZE).contains(&region_size) {
            return Err(BenchmarkError::InvalidParameter);
        }
        let elements = region_size / core::mem::size_of::<u64>();

        for i in 0..warmup_iterations {
            Self::touch_once(elements, self.seed ^ i as u64)?;
        }

        let mut accumulator = 0u64;
        let mut pages = 0usize;
        let mut reserved_bytes = 0usize;

        let timer = T::start();

        for i in 0..iterations {
            let outcome = Self::touch_once(elements, self.seed ^ i as u64)?;
            accumulator = accumulator.wrapping_mul(GOLDEN_RATIO_64) ^ outcome.accumulator;
            pages = outcome.pages;
            reserved_bytes = outcome.reserved_bytes;
        }

        let timing = timer.stop();

        core::hint::black_box(accumulator);

        let mut checksum = checksum_update(CHECKSUM_INIT, &accumulator.to_le_bytes());
        checksum = checksum_update(checksum, &(pages as u64).to_le_bytes());
        checksum = checksum_update(checksum, &(iterations as u64).to_le_bytes());

        // Reported as zero on purpose, which makes the harness print `n/a`
        // rather than a throughput. Only eight bytes per page are stored, so
        // billing the whole region would imply hundreds of GB/s for the warm
        // enclave, and the same column would mean bytes-provisioned on one
        // platform and bytes-stored on the other. The interpretable figures
        // here are cycles per iteration and cycles per page.
        let bytes_processed = 0;

        // Derived from what the allocator actually handed over, so a run that
        // ignored `region_size` could not report the requested size anyway.
        Ok(BenchmarkResult::new(timing, iterations, bytes_processed, checksum)
            .with_working_set(reserved_bytes as u64))
    }

    /// One allocate-touch-free cycle.
    #[inline]
    fn touch_once(elements: usize, value: u64) -> Result<TouchOutcome, BenchmarkError> {
        let mut region: Vec<u64> = Vec::new();
        // `try_reserve` rather than `with_capacity`: the enclave has a fixed
        // guest memory budget and aborting on a large request would take the
        // whole run down instead of reporting a failed benchmark.
        region.try_reserve(elements).map_err(|_| BenchmarkError::AllocationFailure)?;
        let reserved_bytes = region.capacity() * core::mem::size_of::<u64>();

        let spare = region.spare_capacity_mut();
        let mut accumulator = 0u64;
        let mut pages = 0usize;
        let mut i = 0;
        while i < elements {
            // Multiplied because `i` is always a multiple of 512, so mixing
            // the raw index would only ever touch bits 9 and above.
            let written = value ^ (i as u64).wrapping_mul(LCG_MULTIPLIER);

            // The `black_box` is what makes the accumulator a witness. Without
            // it LLVM forwards the just-stored value to the read and the fold
            // is computed from a register, so it would be unchanged if the
            // store were removed. Routing the reference through `black_box`
            // makes the pointer escape, which forces the store to be
            // materialised and the read back to be a real load. It fires once
            // per 4 KiB, against a fault path costing hundreds of cycles.
            let read_back = *core::hint::black_box(spare[i].write(written));

            // Folded with a multiply rather than a rotate. Rotation is a
            // linear bijection that distributes over XOR and generates a group
            // of order 64, so a rotate-XOR fold cancels the value term exactly
            // whenever the page count is a multiple of 128 — which is every
            // region size that is a multiple of 512 KiB, including every size
            // this benchmark is run at. That bug shipped once already.
            accumulator = accumulator.wrapping_mul(GOLDEN_RATIO_64) ^ read_back;
            pages += 1;
            i += ELEMENTS_PER_PAGE;
        }

        // `region.len()` is still zero, so this frees without dropping any
        // element and without reading the region back.
        drop(region);
        Ok(TouchOutcome { accumulator, pages, reserved_bytes })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::timer::NativeTimer;

    /// A region whose page count is a multiple of 128.
    ///
    /// The rotate-XOR fold this benchmark used to have cancelled the seed out
    /// exactly at such sizes, and every size the suite actually runs at is one
    /// of them. Tests that only use [`MIN_REGION_SIZE`] (16 pages) cannot see
    /// that class of bug.
    const CANCELLATION_PRONE_REGION: usize = 1024 * 1024;

    #[test]
    fn same_seed_gives_same_checksum() {
        let mut a = PageTouchBenchmark::new(3);
        let mut b = PageTouchBenchmark::new(3);
        let ra = a.run::<NativeTimer>(MIN_REGION_SIZE, 4, 0).unwrap();
        let rb = b.run::<NativeTimer>(MIN_REGION_SIZE, 4, 0).unwrap();
        assert_eq!(ra.checksum, rb.checksum);
    }

    #[test]
    fn different_seeds_give_different_checksums() {
        let mut a = PageTouchBenchmark::new(3);
        let mut b = PageTouchBenchmark::new(4);
        let ra = a.run::<NativeTimer>(MIN_REGION_SIZE, 4, 0).unwrap();
        let rb = b.run::<NativeTimer>(MIN_REGION_SIZE, 4, 0).unwrap();
        assert_ne!(ra.checksum, rb.checksum);
    }

    #[test]
    fn seed_is_witnessed_at_sizes_where_folds_tend_to_cancel() {
        // Regression test for the rotate-XOR cancellation. The page count and
        // the iteration count are identical across the two runs, so the only
        // thing that can make the checksums differ is the accumulator.
        let mut a = PageTouchBenchmark::new(3);
        let mut b = PageTouchBenchmark::new(4);
        let ra = a.run::<NativeTimer>(CANCELLATION_PRONE_REGION, 2, 0).unwrap();
        let rb = b.run::<NativeTimer>(CANCELLATION_PRONE_REGION, 2, 0).unwrap();
        assert_ne!(
            ra.checksum, rb.checksum,
            "checksum does not witness the seed at {CANCELLATION_PRONE_REGION} bytes"
        );
    }

    #[test]
    fn accumulator_depends_on_the_values_written() {
        // Holds pages and iterations fixed, so this constrains the accumulator
        // alone rather than the fields folded in beside it.
        let elements = CANCELLATION_PRONE_REGION / core::mem::size_of::<u64>();
        let a = PageTouchBenchmark::touch_once(elements, 0x1234).unwrap();
        let b = PageTouchBenchmark::touch_once(elements, 0x5678).unwrap();
        assert_eq!(a.pages, b.pages);
        assert_ne!(a.accumulator, b.accumulator);
    }

    #[test]
    fn checksum_depends_on_the_region_size() {
        let mut bench = PageTouchBenchmark::new(9);
        let small = bench.run::<NativeTimer>(MIN_REGION_SIZE, 2, 0).unwrap().checksum;
        let large = bench.run::<NativeTimer>(2 * MIN_REGION_SIZE, 2, 0).unwrap().checksum;
        assert_ne!(small, large);
    }

    #[test]
    fn warmup_does_not_change_the_checksum() {
        let mut a = PageTouchBenchmark::new(1);
        let ra = a.run::<NativeTimer>(MIN_REGION_SIZE, 3, 0).unwrap();
        let mut b = PageTouchBenchmark::new(1);
        let rb = b.run::<NativeTimer>(MIN_REGION_SIZE, 3, 5).unwrap();
        assert_eq!(ra.checksum, rb.checksum);
    }

    #[test]
    fn working_set_and_bytes_are_reported() {
        let mut bench = PageTouchBenchmark::new(1);
        let r = bench.run::<NativeTimer>(MIN_REGION_SIZE, 3, 0).unwrap();
        assert!(r.working_set_size >= MIN_REGION_SIZE as u64);
        // Suppressed on purpose; see `run`.
        assert_eq!(r.bytes_processed, 0);
        assert_eq!(r.iterations_completed, 3);
    }

    #[test]
    fn region_bounds_are_enforced() {
        let mut bench = PageTouchBenchmark::new(1);
        assert_eq!(
            bench.run::<NativeTimer>(MIN_REGION_SIZE - 1, 1, 0).unwrap_err(),
            BenchmarkError::InvalidParameter
        );
        assert_eq!(
            bench.run::<NativeTimer>(MAX_REGION_SIZE + 1, 1, 0).unwrap_err(),
            BenchmarkError::InvalidParameter
        );
    }

    #[test]
    fn zero_iterations_is_rejected() {
        let mut bench = PageTouchBenchmark::new(1);
        assert_eq!(
            bench.run::<NativeTimer>(MIN_REGION_SIZE, 0, 0).unwrap_err(),
            BenchmarkError::InvalidParameter
        );
    }

    #[test]
    fn every_page_is_written() {
        // Asserts against the count the touch loop reports, so shortening the
        // loop or widening the stride fails here.
        let elements = MIN_REGION_SIZE / core::mem::size_of::<u64>();
        let outcome = PageTouchBenchmark::touch_once(elements, 1).unwrap();
        assert_eq!(outcome.pages, MIN_REGION_SIZE / PAGE_SIZE);
    }
}
