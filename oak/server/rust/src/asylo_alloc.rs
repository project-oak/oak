use core::alloc::{GlobalAlloc, Layout};

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
