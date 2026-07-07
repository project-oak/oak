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
//!   stdin/stdout/stderr cookies, and
//! - `src/time/oak/` (`timespec_get`) via [`__llvm_libc_timespec_get_utc`].
//!
//! It additionally provides the two C++ CRT symbols the compiler emits for
//! static-destructor registration ([`__cxa_atexit`] and [`__dso_handle`]),
//! which libc++abi does not own. See the "C++ CRT" section at the bottom of
//! this file.
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
///
/// libc treats each `FILE *` as a pointer to its cookie (see the Oak
/// `src/__support/OSUtil/oak/io.cpp` port, which sets
/// `stderr = reinterpret_cast<FILE *>(&__llvm_libc_stderr_cookie)`), and passes
/// that same pointer back to
/// [`__llvm_libc_stdio_write`]/[`__llvm_libc_stdio_read`].
///
/// Each cookie's *value* is its destination file descriptor. The callbacks map
/// an incoming `FILE *` to an fd with [`cookie_to_fd`], which matches the
/// pointer against these three known addresses by *identity* and never
/// dereferences the caller-supplied pointer. This way a null or otherwise
/// invalid `FILE *` (e.g. from buggy caller code, for which the C stdio
/// contract makes such a call undefined behavior) is rejected with an error
/// rather than triggering an out-of-bounds read.
///
/// The three values are distinct (0/1/2) and the symbols are exported
/// (`#[no_mangle]`), both of which prevent the linker from merging them to a
/// single address and collapsing the identity check.
#[unsafe(no_mangle)]
pub static __llvm_libc_stdin_cookie: u8 = 0;
#[unsafe(no_mangle)]
pub static __llvm_libc_stdout_cookie: u8 = 1;
#[unsafe(no_mangle)]
pub static __llvm_libc_stderr_cookie: u8 = 2;

/// Maps a libc stream cookie pointer to its destination file descriptor.
///
/// Returns `None` for any pointer that is not one of the three known stream
/// cookies (`stdin`/`stdout`/`stderr`). Matching is by pointer identity, so the
/// untrusted `FILE *` is never dereferenced; recovering the fd afterwards reads
/// only our own immutable statics.
fn cookie_to_fd(cookie: *const core::ffi::c_void) -> Option<i32> {
    let cookie = cookie as *const u8;
    if core::ptr::eq(cookie, &raw const __llvm_libc_stdin_cookie) {
        Some(__llvm_libc_stdin_cookie as i32)
    } else if core::ptr::eq(cookie, &raw const __llvm_libc_stdout_cookie) {
        Some(__llvm_libc_stdout_cookie as i32)
    } else if core::ptr::eq(cookie, &raw const __llvm_libc_stderr_cookie) {
        Some(__llvm_libc_stderr_cookie as i32)
    } else {
        None
    }
}

/// Called by LLVM libc's `write_to_stderr` and stdio output functions.
#[unsafe(no_mangle)]
pub extern "C" fn __llvm_libc_stdio_write(
    cookie: *mut core::ffi::c_void,
    buf: *const u8,
    size: usize,
) -> isize {
    // Reject any stream we don't recognise (including a null `FILE *`) instead
    // of dereferencing an untrusted cookie pointer.
    let Some(fd) = cookie_to_fd(cookie) else {
        return -1;
    };
    if size == 0 {
        return 0;
    }
    // A null `buf` with a non-zero `size` is a caller contract violation
    // (undefined behavior under C 7.1.4); reject it rather than form an invalid
    // slice.
    if buf.is_null() {
        return -1;
    }
    // SAFETY: `buf` is non-null and the caller must guarantee it points to at least
    // `size` initialized bytes.
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

// --- Time ---

/// Called by LLVM libc's `timespec_get` to obtain the current UTC time.
///
/// The Restricted Kernel exposes no clock syscall (see
/// `oak_restricted_kernel_interface::syscalls`), so there is no time source
/// available to the enclave. Reporting failure here makes `timespec_get` return
/// `0`, which is the contract for "time not available". When the kernel gains a
/// clock syscall, only this callback needs to change.
#[unsafe(no_mangle)]
pub extern "C" fn __llvm_libc_timespec_get_utc(_ts: *mut core::ffi::c_void) -> bool {
    false // no clock source in the Restricted Kernel
}

// --- Errno ---

/// Backing storage for the C `errno`.
static mut ERRNO: core::ffi::c_int = 0;

/// Returns a pointer to the enclave's single `errno` slot, as required by LLVM
/// libc's EXTERNAL errno mode.
#[unsafe(no_mangle)]
pub extern "C" fn __llvm_libc_errno() -> *mut core::ffi::c_int {
    &raw mut ERRNO
}

// --- C++ CRT ---
//
// These are the two C runtime symbols the compiler references for a C++
// translation unit that has static-storage-duration objects, and which
// libc++abi does not itself provide.
//
// Reference: Itanium C++ ABI
// <https://itanium-cxx-abi.github.io/cxx-abi/abi.html#dso-dtor>

/// The per-DSO handle the compiler passes as the third argument to
/// [`__cxa_atexit`]. Only its address is used to identify the (single, nominal)
/// DSO of a statically linked enclave, so a zero-initialized, pointer-sized
/// slot is sufficient; the value is never dereferenced.
#[unsafe(no_mangle)]
pub static __dso_handle: usize = 0;

/// Registers a destructor to run at "program exit". An Oak enclave application
/// never returns (it terminates via the exit syscall), so registered static
/// destructors need never run: registration is a no-op that reports success
/// (`0`). The function/argument/DSO handle are intentionally ignored.
#[unsafe(no_mangle)]
pub extern "C" fn __cxa_atexit(
    _func: Option<unsafe extern "C" fn(*mut core::ffi::c_void)>,
    _arg: *mut core::ffi::c_void,
    _dso_handle: *mut core::ffi::c_void,
) -> core::ffi::c_int {
    0
}
