//
// Copyright 2022 The Project Oak Authors
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

//! Exported interface for interacting with the kernel from C.

use alloc::alloc::{alloc, dealloc, Layout};
use core::{
    cell::{LazyCell, RefCell},
    ffi::c_void,
    ptr::null_mut,
};
use hashbrown::HashMap;
use spinning_top::{const_spinlock, Spinlock};
use static_assertions::const_assert;

/// The maximum alignment that we need to support any C type that has fundamental alignment.
const MAX_ALIGNMENT: usize = core::mem::align_of::<libc::max_align_t>();

const_assert!(MAX_ALIGNMENT.is_power_of_two());

/// Cache for keeping track of which memory locations we allocated and the layout (size and
/// alignment) that was used for each allocation.
static ALLOCATED_ITEMS: Spinlock<LazyCell<RefCell<HashMap<usize, Layout>>>> =
    const_spinlock(LazyCell::new(|| RefCell::new(HashMap::new())));

/// Allocates memory of the given size with alignment that is suitable for any C type that has
/// fundamental alignment.
///
/// This function returns a pointer to the allocated memory if the allocation succeeds and null if
/// it fails. All allocated memory must be deallocated using `free`.
#[no_mangle]
pub extern "C" fn malloc(size: usize) -> *mut c_void {
    if size == 0 {
        return null_mut();
    }

    // This should never panic since we checked that the size is non-zero and calculated a valid
    // alignment.
    let layout = Layout::from_size_align(size, calculate_alignment(size))
        .expect("Invalid alignment calculated.");

    // Safety: we ensured that the size is not 0.
    let result = unsafe { alloc(layout) as *mut c_void };
    if !result.is_null() {
        ALLOCATED_ITEMS
            .lock()
            .borrow_mut()
            .insert(result as usize, layout);
    }

    result
}

#[inline]
fn calculate_alignment(size: usize) -> usize {
    MAX_ALIGNMENT.min(size.next_power_of_two())
}

/// Frees memory that was previously allocated using `malloc`.
///
/// If the pointer is null, it does nothing. Panics if the pointer is non-null but was not allocated
/// using `malloc`, or if it was already freed.
#[no_mangle]
pub extern "C" fn free(ptr: *mut c_void) {
    if ptr.is_null() {
        return;
    }

    let key = ptr as usize;
    let layout = ALLOCATED_ITEMS
        .lock()
        .borrow_mut()
        .remove(&key)
        .expect("Invalid memory region pointer. It was either already freed or not allocated.");

    // Safety: we have validated that we previously allocated the memory, found the layout that was
    // used to allocate it, and it was not yet freed.
    unsafe {
        dealloc(ptr as *mut u8, layout);
    }
}
