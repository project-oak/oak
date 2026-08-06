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

//! Pointer chase: dependent-load memory latency.
//!
//! Walks a randomly permuted list of cache lines, where each address is the
//! value returned by the previous access. No two accesses can be in flight at
//! once, so this measures load-to-use latency, not throughput. Same
//! construction as lmbench's `lat_mem_rd`,
//! <https://lmbench.sourceforge.net/man/lat_mem_rd.8.html>, which cannot run
//! here because it needs `fork`, signals and a filesystem.
//!
//! Sweeping the working set across the cache hierarchy gives the classic
//! latency curve, directly comparable with published `lat_mem_rd` figures.
//!
//! It was also expected to expose a page-size difference, since the enclave
//! heap (`oak_enclave_runtime_support::heap`) is 2 MiB-aligned by construction.
//! At the top of the range there is none: the baseline gets transparent huge
//! pages too (`AnonHugePages` covers 100% of a 256 MiB or 1 GiB working set),
//! and [`MAX_WORKING_SET_SIZE`] fits in the reference part's L2 TLB with 2048
//! of its 3072 entries, so walks should be rare on either. Around 1 MiB there
//! is a real band of roughly 2x, but a Linux process that aligns its `mmap` or
//! asks for `MADV_HUGEPAGE` closes it completely, so it reflects allocator
//! defaults rather than a capability the enclave has and Linux lacks.
//!
//! Outside that band there is no translation term and the DRAM is the host's on
//! both sides, so a ratio of 1.0 is a testable prediction and this works as a
//! positive control on the virtualisation wrapper. The 32 KiB point is the
//! tightest form: both platforms are L1-resident, so agreement there rules out
//! codegen divergence between the `x86_64-unknown-linux-gnu` and
//! `x86_64-unknown-none` builds.
//!
//! `run` rounds `iterations` up so the walk always laps the buffer, otherwise
//! the measured footprint would be the prefix visited rather than the working
//! set. There is no cold mode either: the constructor verifies the cycle by
//! walking the whole buffer, so cached working sets always report warm
//! latency.
//!
//! The permutation comes from the request's seed via the suite's LCG, so both
//! platforms build and walk an identical cycle, and the checksum is sensitive
//! to the order visited.

use alloc::vec::Vec;

use super::MemoryBenchmark;
use crate::{
    BenchmarkError, BenchmarkResult, CHECKSUM_INIT, GOLDEN_RATIO_64, LCG_MULTIPLIER,
    checksum_update, timer::BenchmarkTimer,
};

/// Bytes per slot: one cache line on every x86-64 part in use.
///
/// One slot per line means consecutive hops never share a line, so each hop
/// costs a full miss at whatever level of the hierarchy the working set lives
/// in. Only the first `usize` of each slot is used; the rest is padding whose
/// purpose is to occupy the line.
pub const SLOT_BYTES: usize = 64;

/// `usize` elements per slot.
const ELEMENTS_PER_SLOT: usize = SLOT_BYTES / core::mem::size_of::<usize>();

/// Default working set size (256 MiB), comfortably past any current L3.
pub const DEFAULT_WORKING_SET_SIZE: usize = 256 * 1024 * 1024;

/// Smallest working set (4 KiB, 64 slots).
///
/// Small enough to be entirely L1-resident, which makes it the control point
/// of the sweep, and large enough to be a legal request.
pub const MIN_WORKING_SET_SIZE: usize = 4096;

/// Largest working set (4 GiB).
pub const MAX_WORKING_SET_SIZE: usize = 4 * 1024 * 1024 * 1024;

/// Pointer chase benchmark.
pub struct PointerChaseBenchmark {
    /// Slot array. Element `ELEMENTS_PER_SLOT * k` holds the *element* index
    /// of the slot to visit after slot `k`; the remaining elements of each
    /// slot are padding.
    slots: Vec<usize>,
    seed: u64,
}

// Hand-written rather than derived: the slot array is up to 4 GiB and a
// derived `Debug` would try to format all of it.
impl core::fmt::Debug for PointerChaseBenchmark {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PointerChaseBenchmark")
            .field("working_set_size", &(self.slots.len() * core::mem::size_of::<usize>()))
            .field("slots", &(self.slots.len() / ELEMENTS_PER_SLOT))
            .field("seed", &self.seed)
            .finish()
    }
}

impl PointerChaseBenchmark {
    /// Build the cycle. Allocation and permutation happen here, outside any
    /// timed region.
    ///
    /// Fails with [`BenchmarkError::Generic`] if the permutation is not a
    /// single full-length cycle. Sattolo's algorithm makes that impossible, but
    /// the failure mode is silent: a walk trapped in a short cycle stays in
    /// cache and reports an excellent latency for the wrong reason.
    pub fn new(working_set_size: usize, seed: u64) -> Result<Self, BenchmarkError> {
        if !(MIN_WORKING_SET_SIZE..=MAX_WORKING_SET_SIZE).contains(&working_set_size) {
            return Err(BenchmarkError::InvalidParameter);
        }
        let num_slots = working_set_size / SLOT_BYTES;

        // Sattolo draws `j` from `0..i` rather than `0..=i`, so the result is
        // always one cycle spanning every element, where Fisher-Yates would
        // usually give several disjoint cycles and the walk would see only one.
        // <https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle#Sattolo's_algorithm>
        //
        // Permuting a dense `Vec<usize>` first rather than the strided slots in
        // place keeps the random-access swaps to an eighth of the footprint, at
        // the cost of a ninth more peak setup memory.
        let mut permutation: Vec<usize> = Vec::new();
        permutation.try_reserve_exact(num_slots).map_err(|_| BenchmarkError::AllocationFailure)?;
        permutation.extend(0..num_slots);

        // Not `seed | 1`: the LCG has increment 1 and modulus 2^64, so it has
        // full period for every seed including zero, and forcing the low bit
        // would make seeds 2k and 2k+1 generate identical permutations.
        let mut rng = seed;
        for i in (1..num_slots).rev() {
            rng = rng.wrapping_mul(LCG_MULTIPLIER).wrapping_add(1);
            let j = ((rng >> 16) as usize) % i;
            permutation.swap(i, j);
        }

        // Scatter into the strided slot array, converting slot indices into
        // element indices so the timed loop needs no multiply.
        let mut slots: Vec<usize> = Vec::new();
        slots
            .try_reserve_exact(num_slots * ELEMENTS_PER_SLOT)
            .map_err(|_| BenchmarkError::AllocationFailure)?;
        slots.resize(num_slots * ELEMENTS_PER_SLOT, 0);
        for (slot, &next) in permutation.iter().enumerate() {
            slots[slot * ELEMENTS_PER_SLOT] = next * ELEMENTS_PER_SLOT;
        }
        drop(permutation);

        let benchmark = Self { slots, seed };
        benchmark.verify_single_cycle(num_slots)?;
        Ok(benchmark)
    }

    /// Reconfigure the working set, rebuilding the cycle if it changed.
    pub fn reconfigure(
        &mut self,
        working_set_size: usize,
        seed: u64,
    ) -> Result<(), BenchmarkError> {
        // Compared in slots, not bytes: `working_set_size()` reports the
        // rounded-down size, so comparing against the raw request would
        // rebuild on every call for any request that is not a multiple of the
        // slot size.
        let requested_slots = working_set_size / SLOT_BYTES;
        if self.slots.len() / ELEMENTS_PER_SLOT == requested_slots && self.seed == seed {
            return Ok(());
        }
        *self = Self::new(working_set_size, seed)?;
        Ok(())
    }

    /// Confirm the walk from slot 0 visits every slot exactly once and returns
    /// to the start on the last hop.
    ///
    /// Each hop is checked to be in range and slot-aligned; given both, an
    /// orbit of length `num_slots` returning to 0 only on the final hop must
    /// cover every slot. Without the alignment check a walk could step through
    /// padding and report L1 latency while claiming a large working set.
    fn verify_single_cycle(&self, num_slots: usize) -> Result<(), BenchmarkError> {
        let mut idx = 0usize;
        for hop in 1..=num_slots {
            // Indexed with a value read from the data, so this uses `get`
            // rather than `[]`: a gate whose failure mode is a panic is not a
            // gate, and in the enclave a panic ends the process.
            idx = *self.slots.get(idx).ok_or(BenchmarkError::Generic)?;
            if !idx.is_multiple_of(ELEMENTS_PER_SLOT) {
                return Err(BenchmarkError::Generic);
            }
            if idx == 0 && hop != num_slots {
                return Err(BenchmarkError::Generic);
            }
        }
        if idx != 0 {
            return Err(BenchmarkError::Generic);
        }
        Ok(())
    }

    /// Walk the cycle.
    ///
    /// Each iteration is one dependent load, so `cycles_per_op` in the result
    /// is the access latency directly.
    pub fn run<T: BenchmarkTimer>(
        &mut self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        if iterations == 0 {
            return Err(BenchmarkError::InvalidParameter);
        }

        // Round up to a full lap. A shorter walk visits only its own prefix,
        // which for the default working set is a few hundred KiB and stays in
        // L2, so the result would be that prefix's latency while the response
        // claimed the whole working set. Lapping also means each run evicts
        // what the last one left behind, which matters because `service`
        // reuses this instance across requests. The count is reported back as
        // `iterations_completed`.
        let num_slots = self.slots.len() / ELEMENTS_PER_SLOT;
        let iterations = iterations.max(num_slots as u32);

        // The measured walk continues from where the warmup stopped rather
        // than restarting at slot 0. Restarting would leave the first
        // `warmup_iterations` measured accesses hitting lines the warmup had
        // just pulled in, which biases the result downward by
        // `warmup / iterations` — the opposite of what a warmup is for.
        let mut idx = 0usize;
        for _ in 0..warmup_iterations {
            idx = self.slots[idx];
        }
        core::hint::black_box(idx);

        let mut visited = 0u64;

        let timer = T::start();

        for _ in 0..iterations {
            idx = self.slots[idx];
            // Off the critical path: three cycles per iteration against a
            // load chain of at least four. Multiply rather than add, because a
            // commutative fold over a whole number of laps is the same for
            // every permutation and would stop witnessing the seed.
            visited = visited.wrapping_mul(GOLDEN_RATIO_64) ^ idx as u64;
        }

        let timing = timer.stop();

        // Outside the loop deliberately. A barrier inside would add a
        // scheduling constraint to every iteration and inflate the latency by
        // a constant; the dependency chain is what keeps the loop honest, and
        // making the accumulator escape here is what keeps the chain alive.
        core::hint::black_box(idx);
        core::hint::black_box(visited);

        let mut checksum = checksum_update(CHECKSUM_INIT, &visited.to_le_bytes());
        checksum = checksum_update(checksum, &(idx as u64).to_le_bytes());
        checksum = checksum_update(checksum, &(iterations as u64).to_le_bytes());

        // Suppressed, which makes the harness print `n/a` rather than a
        // throughput. This is a latency benchmark: the hardware moves a whole
        // 64-byte line per hop but only eight bytes are consumed, so either
        // figure printed as a throughput would invite the wrong comparison.
        let bytes_processed = 0;

        Ok(BenchmarkResult::new(timing, iterations, bytes_processed, checksum)
            .with_working_set(self.working_set_size() as u64))
    }
}

impl MemoryBenchmark for PointerChaseBenchmark {
    fn working_set_size(&self) -> usize {
        self.slots.len() * core::mem::size_of::<usize>()
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;
    use crate::timer::NativeTimer;

    const SMALL: usize = 64 * 1024;

    #[test]
    fn cycle_covers_every_slot() {
        let bench = PointerChaseBenchmark::new(SMALL, 11).unwrap();
        let num_slots = SMALL / SLOT_BYTES;

        // Independent of `verify_single_cycle`: collect the orbit and check
        // it is the whole slot set, so a bug that made both the constructor
        // and its own check wrong in the same way would still be caught.
        let mut seen = vec![false; num_slots];
        let mut idx = 0usize;
        for _ in 0..num_slots {
            let slot = idx / ELEMENTS_PER_SLOT;
            assert!(!seen[slot], "slot {slot} visited twice in {num_slots} hops");
            seen[slot] = true;
            idx = bench.slots[idx];
        }
        assert_eq!(idx, 0, "walk did not return to the start");
        assert!(seen.iter().all(|&s| s), "some slots were never visited");
    }

    #[test]
    fn a_short_request_is_rounded_up_to_a_full_lap() {
        let num_slots = SMALL / SLOT_BYTES;
        let mut bench = PointerChaseBenchmark::new(SMALL, 7).unwrap();

        // Asking for far fewer hops than there are slots would otherwise walk
        // a prefix that stays in cache while the result claimed `SMALL`.
        let short = bench.run::<NativeTimer>(8, 0).unwrap();
        assert_eq!(short.iterations_completed as usize, num_slots);
        assert_eq!(short.working_set_size as usize, SMALL);

        // A request longer than a lap is left alone.
        let long = bench.run::<NativeTimer>(num_slots as u32 * 2, 0).unwrap();
        assert_eq!(long.iterations_completed as usize, num_slots * 2);
    }

    #[test]
    fn consecutive_seeds_give_different_cycles() {
        // Consecutive values specifically: the generator used to force the low
        // bit of the seed, which made 2k and 2k+1 produce identical cycles.
        let a = PointerChaseBenchmark::new(SMALL, 2).unwrap();
        let b = PointerChaseBenchmark::new(SMALL, 3).unwrap();
        assert_ne!(a.slots, b.slots);
    }

    #[test]
    fn same_seed_gives_same_checksum() {
        let mut a = PointerChaseBenchmark::new(SMALL, 5).unwrap();
        let mut b = PointerChaseBenchmark::new(SMALL, 5).unwrap();
        let ra = a.run::<NativeTimer>(10_000, 0).unwrap();
        let rb = b.run::<NativeTimer>(10_000, 0).unwrap();
        assert_eq!(ra.checksum, rb.checksum);
    }

    #[test]
    fn checksum_witnesses_the_order_of_a_whole_number_of_laps() {
        // An exact multiple of the cycle length visits every slot the same
        // number of times whatever the permutation, so an order-insensitive
        // fold would return the same value for both seeds here. Iterations
        // and slot count are equal across the two runs, so the accumulator is
        // the only thing that can differ.
        let num_slots = (SMALL / SLOT_BYTES) as u32;
        let mut a = PointerChaseBenchmark::new(SMALL, 5).unwrap();
        let mut b = PointerChaseBenchmark::new(SMALL, 6).unwrap();
        let ra = a.run::<NativeTimer>(num_slots * 4, 0).unwrap();
        let rb = b.run::<NativeTimer>(num_slots * 4, 0).unwrap();
        assert_ne!(ra.checksum, rb.checksum);
    }

    #[test]
    fn iterations_may_exceed_the_cycle_length() {
        // The walk wraps; there is no cap at the number of slots.
        let mut bench = PointerChaseBenchmark::new(MIN_WORKING_SET_SIZE, 3).unwrap();
        let r = bench.run::<NativeTimer>(100_000, 0).unwrap();
        assert_eq!(r.iterations_completed, 100_000);
    }

    #[test]
    fn reconfigure_rebuilds_only_on_change() {
        let mut bench = PointerChaseBenchmark::new(SMALL, 4).unwrap();
        // Compared by address: rebuilding with the same seed produces an equal
        // array, so comparing contents could not tell the two apart.
        let before = bench.slots.as_ptr();
        bench.reconfigure(SMALL, 4).unwrap();
        assert_eq!(bench.slots.as_ptr(), before, "rebuilt despite no change");
        bench.reconfigure(2 * SMALL, 4).unwrap();
        assert_eq!(bench.working_set_size(), 2 * SMALL);
    }

    #[test]
    fn reconfigure_ignores_sub_slot_differences() {
        // A request that is not a multiple of the slot size rounds to the same
        // slot count, so it must not trigger a rebuild.
        let mut bench = PointerChaseBenchmark::new(SMALL, 4).unwrap();
        let before = bench.slots.as_ptr();
        bench.reconfigure(SMALL + SLOT_BYTES - 1, 4).unwrap();
        assert_eq!(bench.slots.as_ptr(), before);
    }

    #[test]
    fn working_set_bounds_are_enforced() {
        assert_eq!(PointerChaseBenchmark::new(0, 1).unwrap_err(), BenchmarkError::InvalidParameter);
        assert_eq!(
            PointerChaseBenchmark::new(MAX_WORKING_SET_SIZE + 1, 1).unwrap_err(),
            BenchmarkError::InvalidParameter
        );
    }

    #[test]
    fn zero_iterations_is_rejected() {
        let mut bench = PointerChaseBenchmark::new(SMALL, 1).unwrap();
        assert_eq!(bench.run::<NativeTimer>(0, 0).unwrap_err(), BenchmarkError::InvalidParameter);
    }

    #[test]
    fn a_short_cycle_is_detected() {
        // Corrupt the cycle into a two-slot loop and confirm the check that
        // runs at construction would have rejected it.
        let mut bench = PointerChaseBenchmark::new(SMALL, 2).unwrap();
        let second = bench.slots[0];
        bench.slots[second] = 0;
        assert_eq!(
            bench.verify_single_cycle(SMALL / SLOT_BYTES).unwrap_err(),
            BenchmarkError::Generic
        );
    }

    #[test]
    fn a_walk_through_padding_is_detected() {
        // A full-length orbit that steps through padding rather than slot
        // heads touches an eighth of the lines it claims. Checking only the
        // orbit length accepts it; checking alignment does not.
        let num_slots = SMALL / SLOT_BYTES;
        let mut bench = PointerChaseBenchmark::new(SMALL, 2).unwrap();
        // Point slot 0 at the second element of slot 0, which is padding.
        bench.slots[0] = 1;
        assert_eq!(bench.verify_single_cycle(num_slots).unwrap_err(), BenchmarkError::Generic);
    }
}
