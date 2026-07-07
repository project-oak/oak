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

//! Vendor callbacks required by the Oak LLVM libc port.
//!
//! The Oak port of LLVM libc does not implement OS primitives itself. Instead
//! it declares a small set of `__llvm_libc_*` symbols that the enclave runtime
//! must provide, following the same convention as LLVM libc's upstream
//! baremetal port. The port's C sources live under
//! `third_party/llvm_libc/overlay/libc/`; the symbols implemented here are
//! consumed by:
//!
//! - `src/stdlib/oak/` (the `malloc` family) via
//!   [`__llvm_libc_malloc`]/[`__llvm_libc_free`], and
//! - `src/__support/OSUtil/oak/` (exit and stdio) via [`__llvm_libc_exit`],
//!   [`__llvm_libc_stdio_write`], [`__llvm_libc_stdio_read`], and the
//!   stdin/stdout/stderr cookies.
//!
//! Providing these here (rather than in each enclave application) means any
//! binary that links `oak_enclave_runtime_support` and the Oak libc gets a
//! working C runtime automatically. Because the symbols are `#[no_mangle]`,
//! the linker only pulls them in when the libc archive actually references
//! them, so binaries that don't use libc pay no cost.

use core::alloc::Layout;

// --- Heap ---
//
// The `malloc` family is routed to these callbacks by the Oak libc port. They
// delegate to Rust's global allocator so that C and Rust share the single
// enclave heap (the `#[global_allocator]` installed by
// `oak_restricted_kernel_sdk::entrypoint`, backed by [`crate::heap`]), rather
// than the C library carving out a separate static region.
//
// The callback signatures mirror [`core::alloc::GlobalAlloc`]: the size and
// alignment recorded by the C side are replayed on free so the [`Layout`] can
// be reconstructed exactly.

/// Allocates `size` bytes aligned to `alignment` via the Rust global allocator.
#[unsafe(no_mangle)]
pub extern "C" fn __llvm_libc_malloc(size: usize, alignment: usize) -> *mut core::ffi::c_void {
    match Layout::from_size_align(size, alignment) {
        // SAFETY: the C side always reserves room for its allocation header, so
        // the layout is valid and never zero-sized.
        Ok(layout) => unsafe { alloc::alloc::alloc(layout) as *mut core::ffi::c_void },
        Err(_) => core::ptr::null_mut(),
    }
}

/// Frees a block previously returned by [`__llvm_libc_malloc`]; `size` and
/// `alignment` must match the values used to allocate it.
#[unsafe(no_mangle)]
pub extern "C" fn __llvm_libc_free(ptr: *mut core::ffi::c_void, size: usize, alignment: usize) {
    if ptr.is_null() {
        return;
    }
    if let Ok(layout) = Layout::from_size_align(size, alignment) {
        // SAFETY: `ptr` came from `__llvm_libc_malloc` with exactly this
        // `size`/`alignment` pair (stored and replayed by the C side), so the
        // layout matches the original allocation.
        unsafe { alloc::alloc::dealloc(ptr as *mut u8, layout) };
    }
}

// --- Exit and stdio ---
//
// These are consumed by `src/__support/OSUtil/oak/`, and follow the upstream
// baremetal convention documented in the LLVM libc source at
// `libc/src/__support/OSUtil/baremetal/io.cpp`.

/// Called by LLVM libc's `internal::exit()`.
#[unsafe(no_mangle)]
pub extern "C" fn __llvm_libc_exit(status: i32) -> ! {
    oak_restricted_kernel_interface::syscall::exit(status);
}

/// Opaque cookies for stdin/stdout/stderr, following the baremetal convention.
#[unsafe(no_mangle)]
pub static __llvm_libc_stdin_cookie: u8 = 0;
#[unsafe(no_mangle)]
pub static __llvm_libc_stdout_cookie: u8 = 1;
#[unsafe(no_mangle)]
pub static __llvm_libc_stderr_cookie: u8 = 2;

/// Called by LLVM libc's `write_to_stderr` and stdio output functions.
#[unsafe(no_mangle)]
pub extern "C" fn __llvm_libc_stdio_write(
    cookie: *mut core::ffi::c_void,
    buf: *const u8,
    size: usize,
) -> isize {
    let fd = cookie as usize as i32;
    // SAFETY: the libc caller guarantees `buf` points to at least `size` bytes.
    let data = unsafe { core::slice::from_raw_parts(buf, size) };
    match oak_restricted_kernel_interface::syscall::write(fd, data) {
        Ok(n) => n as isize,
        Err(_) => -1,
    }
}

/// Called by LLVM libc's `read_from_stdin`. Not supported in Oak.
#[unsafe(no_mangle)]
pub extern "C" fn __llvm_libc_stdio_read(
    _cookie: *mut core::ffi::c_void,
    _buf: *mut u8,
    _size: usize,
) -> isize {
    -1 // not supported
}
