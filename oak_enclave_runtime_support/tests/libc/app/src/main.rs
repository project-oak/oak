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

//! FFI test application for Oak Restricted Kernel.
//!
//! Demonstrates calling C functions from Rust inside an enclave application,
//! including memory allocation and deallocation performed by C code.

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;

use oak_restricted_kernel_sdk::entrypoint;

// Helper C functions implemented in `cc/ffi_demo.c`. They internally use LLVM
// libc (`malloc`/`free`, `memcpy`, etc.). The libc's OS-level vendor callbacks
// (heap, exit, stdio) are provided by `oak_enclave_runtime_support`, which
// every enclave application links via the SDK, so nothing libc-specific needs
// to live here.
unsafe extern "C" {
    fn create_greeting(name: *const u8) -> *mut u8;
    fn free_greeting(greeting: *mut u8);
    fn fill_and_checksum(buf: *mut u8, len: usize) -> u32;
}

// Standard C allocation functions provided directly by the Oak LLVM libc port.
// Per C11 §7.22.3, memory obtained from `malloc`/`aligned_alloc` is released
// with the ordinary `free` (there is no separate "aligned free").
// See <https://en.cppreference.com/w/c/memory/aligned_alloc>.
unsafe extern "C" {
    fn malloc(size: usize) -> *mut u8;
    fn aligned_alloc(alignment: usize, size: usize) -> *mut u8;
    fn free(ptr: *mut u8);
}

/// Alignments (in bytes) exercised by the `aligned_alloc` test. They range from
/// the default fundamental alignment up to a 4 KiB page, and include values
/// larger than the allocation header so that the header padding logic is
/// exercised.
const ALIGNMENTS: [usize; 9] = [16, 32, 64, 128, 256, 512, 1024, 2048, 4096];

/// Sizes (in bytes) exercised by the `malloc` fundamental-alignment test.
const MALLOC_SIZES: [usize; 14] = [1, 2, 3, 4, 7, 8, 15, 16, 17, 32, 64, 100, 1024, 4096];

/// The minimum alignment that `malloc(size)` must guarantee: the largest
/// fundamental alignment (a power of two, capped at `alignof(max_align_t)`,
/// i.e. 16 on x86_64) that an object fitting in `size` bytes could require. For
/// example 2 -> 2, 4 -> 4, 8 -> 8, and every size >= 16 -> 16.
///
/// Per <https://en.cppreference.com/w/c/memory/malloc>, the returned pointer is
/// "suitably aligned for any object type with fundamental alignment". The Oak
/// libc actually returns 16-aligned memory for every size (see
/// `third_party/llvm_libc/overlay/libc/src/stdlib/oak/oak_malloc.h`), which is
/// stronger; this is the minimum the standard requires.
fn required_alignment(size: usize) -> usize {
    let mut alignment = 1;
    while alignment < 16 && alignment * 2 <= size {
        alignment *= 2;
    }
    alignment
}

/// Allocates memory with `malloc` for each size in [`MALLOC_SIZES`], asserts
/// the returned pointer satisfies the fundamental-alignment guarantee for that
/// size (see [`required_alignment`]) and is usable, then frees it.
fn run_malloc_alignment_tests() {
    for &size in MALLOC_SIZES.iter() {
        let ptr = unsafe { malloc(size) };
        assert!(!ptr.is_null(), "malloc(size={size}) returned null");

        let expected = required_alignment(size);
        assert_eq!(
            ptr as usize % expected,
            0,
            "malloc(size={size}) -> {ptr:p} is not aligned to {expected}"
        );

        // Touch the whole block to make sure it is usable.
        let bytes = unsafe { core::slice::from_raw_parts_mut(ptr, size) };
        bytes.fill(0xAB);

        unsafe { free(ptr) };
        log::info!("malloc(size={size}) -> {ptr:p} aligned to {expected} ok");
    }
    log::info!("malloc alignment tests passed");
}

/// Allocates memory with `aligned_alloc` for each alignment in [`ALIGNMENTS`],
/// asserts the returned pointer is actually aligned and usable, and then
/// releases every block with `free`.
///
/// This exercises the alignment bookkeeping in the Oak libc `malloc` family
/// (see `third_party/llvm_libc/overlay/libc/src/stdlib/oak/oak_malloc.h`): each
/// allocation is offset past an `AllocHeader` that must keep the user pointer
/// aligned, and the recorded size/alignment must round-trip through `free`.
fn run_aligned_alloc_tests() {
    // Hold every allocation live at once so their headers cannot overlap and so
    // the allocator must hand out distinct, independently aligned blocks.
    let mut ptrs = [core::ptr::null_mut::<u8>(); ALIGNMENTS.len()];

    for (slot, &alignment) in ptrs.iter_mut().zip(ALIGNMENTS.iter()) {
        // `aligned_alloc` requires the size to be an integral multiple of the
        // alignment; use a few multiples so there is room to write into.
        let size = alignment * 3;
        let ptr = unsafe { aligned_alloc(alignment, size) };
        assert!(!ptr.is_null(), "aligned_alloc(alignment={alignment}) returned null");
        assert_eq!(ptr as usize % alignment, 0, "pointer {ptr:p} is not aligned to {alignment}");

        // Write the whole block and read it back to confirm the memory is
        // usable and that the allocation header (which lives immediately before
        // the returned pointer) does not overlap the user region.
        let bytes = unsafe { core::slice::from_raw_parts_mut(ptr, size) };
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = (i & 0xFF) as u8;
        }
        for (i, b) in bytes.iter().enumerate() {
            assert_eq!(*b, (i & 0xFF) as u8, "byte {i} corrupted (alignment={alignment})");
        }

        *slot = ptr;
        log::info!("aligned_alloc(alignment={alignment}) -> {ptr:p} ok");
    }

    // Release every block. If the size/alignment recorded in the header were
    // wrong, the Rust global allocator would deallocate with a mismatched
    // layout.
    for &ptr in ptrs.iter() {
        unsafe { free(ptr) };
    }
    log::info!("aligned_alloc tests passed");
}

#[entrypoint]
fn run_ffi_demo() -> ! {
    log::set_max_level(log::LevelFilter::Info);

    // Test 1: String construction with malloc/free.
    let name = b"Oak Restricted Kernel\0";
    let greeting = unsafe { create_greeting(name.as_ptr()) };
    assert!(!greeting.is_null(), "allocation failed in C");

    let msg = unsafe { core::ffi::CStr::from_ptr(greeting as *const core::ffi::c_char) };
    log::info!("FFI greeting: {}", msg.to_str().unwrap_or("invalid UTF-8"));

    unsafe { free_greeting(greeting) };
    log::info!("successfully freed C allocation");

    // Test 2: Memory fill and checksum.
    let mut buf = [0u8; 256];
    let checksum = unsafe { fill_and_checksum(buf.as_mut_ptr(), buf.len()) };
    log::info!("fill_and_checksum result: {checksum:#010x}");

    // Verify the pattern was written correctly.
    for (i, byte) in buf.iter().enumerate() {
        let expected = ((i * 7 + 13) & 0xFF) as u8;
        assert_eq!(*byte, expected, "pattern mismatch at index {i}");
    }
    log::info!("pattern verification passed");

    // Test 3: malloc returns memory with fundamental alignment for its size.
    run_malloc_alignment_tests();

    // Test 4: aligned_alloc honors alignment and round-trips through free.
    run_aligned_alloc_tests();

    log::info!("all FFI tests passed");
    oak_restricted_kernel_interface::syscall::exit(0);
}
