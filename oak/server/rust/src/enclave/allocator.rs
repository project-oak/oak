//
// Copyright 2019 The Project Oak Authors
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

//! Allocator backed by base C library allocation via Asylo, suitable for use as
//! a global allocator.

use core::alloc::{GlobalAlloc, Layout};
use core::panic::PanicInfo;

use crate::enclave;

extern "C" {
    // Signatures of the functions exposed by the underlying standard library used in Asylo
    // (newlib). They are statically linked when producing the final enclave executable.
    //
    // See https://www.sourceware.org/newlib/libc.html#malloc.
    fn malloc(nbytes: usize) -> *mut u8;
    fn memalign(align: usize, nbytes: usize) -> *mut u8;
    fn free(aptr: *mut u8);
}

// This aligment is defined in the Intel SGX SDK, and it is used in this allocator to enable a fast
// path optimization for low alignment values.
//
// See the `MALLOC_ALIGNMENT` value for `_TLIBC_` in
// https://github.com/intel/linux-sgx/blob/d166ff0c808e2f78d37eebf1ab614d944437eea3/sdk/tlibc/stdlib/malloc.c#L541.
//
// Also see this paragraph from
// https://github.com/intel/linux-sgx/blob/d166ff0c808e2f78d37eebf1ab614d944437eea3/sdk/tlibc/stdlib/malloc.c#L248-L253:
//
// > MALLOC_ALIGNMENT         default: (size_t)(2 * sizeof(void *))
// > Controls the minimum alignment for malloc'ed chunks.  It must be a
// > power of two and at least 8, even on machines for which smaller
// > alignments would suffice. It may be defined as larger than this
// > though. Note however that code and data structures are optimized for
// > the case of 8-byte alignment.
const MIN_ALIGN: usize = 8;

/// A global memory allocator that links directly to the primitives exposed by Asylo, which in turn
/// relies on [newlib](http://www.sourceware.org/newlib/libc.html) for standard `malloc` and `free`
/// calls.
///
/// The allocator can be registered with the `#[global_allocator]` attribute (see
/// https://doc.rust-lang.org/edition-guide/rust-2018/platform-and-target-support/global-allocators.html).
pub struct System;

// Inspired by https://github.com/apache/incubator-mesatee-sgx/blob/master/sgx_alloc/src/lib.rs.
unsafe impl GlobalAlloc for System {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // If the alignment requested by the caller is sufficiently small, use a fast path. Since
        // the alignment is usually a constant at the call site, only the correct branch will be
        // inlined.
        if layout.align() <= MIN_ALIGN {
            malloc(layout.size())
        } else {
            memalign(layout.align(), layout.size())
        }
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        free(ptr);
    }
}

//// TODO: Move to separate crate and expose safe wrappers.
#[link(name = "sgx_trts")]
extern "C" {
    // SGX-enabled abort function that causes an undefined instruction (`UD2`) to be executed, which
    // terminates the enclave execution.
    //
    // The C type of this function is `extern "C" void abort(void) __attribute__(__noreturn__);`
    //
    // See https://github.com/intel/linux-sgx/blob/d166ff0c808e2f78d37eebf1ab614d944437eea3/sdk/trts/linux/trts_pic.S#L565.
    fn abort() -> !;
}


#[global_allocator]
static A: enclave::allocator::System = enclave::allocator::System;

// Define what happens in an Out Of Memory (OOM) condition.
#[alloc_error_handler]
fn alloc_error(_layout: Layout) -> ! {
    unsafe { abort() }
}

// See https://doc.rust-lang.org/nomicon/panic-handler.html.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    unsafe { abort() }
}

/// Provide the entrypoint needed by the compiler's failure mechanisms when
/// `std` is unavailable.  See ["No
/// stdlib" documentation](https://doc.rust-lang.org/1.2.0/book/no-stdlib.html).
#[lang = "eh_personality"]
pub extern "C" fn eh_personality() {}
