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

use crate::{i8042::shutdown, logging::SERIAL1};
use alloc::alloc::{alloc, dealloc, Layout};
use core::{
    cell::{LazyCell, RefCell},
    ffi::c_void,
    ptr::null_mut,
};
use hashbrown::HashMap;
use log::info;
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
/// it fails. All allocated memory must be deallocated using `heap_free`.
///
/// The function is intentionally not named "malloc" to avoid naming clashes. It is up to the
/// compatibility layer to make sure that this function is used for allocating memory.
#[no_mangle]
pub extern "C" fn heap_alloc(size: usize) -> *mut c_void {
    if size == 0 {
        return null_mut();
    }

    // This should never panic since we checked that the size is non-zero and calculated a valid
    // alignment.
    let layout = Layout::from_size_align(size, calculate_alignment(size))
        .expect("Invalid alignment calculated.");

    // We use the global allocator directly (rather than using e.g. `Vec<u8>`) so that we have the
    // required control over the alignment of the allocated memory.
    //
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

/// Frees memory that was previously allocated using `heap_alloc`.
///
/// If the pointer is null, it does nothing. Panics if the pointer is non-null but was not allocated
/// using `heap_alloc`, or if it was already freed.
///
/// The function is intentionally not named "free" to avoid naming clashes. It is up to the
/// compatibility layer to make sure that this function is used for freeing memory.
#[no_mangle]
pub extern "C" fn heap_free(ptr: *mut c_void) {
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

/// Writes the specified number of bytes from a buffer to the serial console.
///
/// To be compatible with C write semantics the number of bytes written is returned on success and
/// -1 on failure.
///
/// #Safety
///
/// The pointer must point to a valid location of a buffer with at least the specified size.
#[no_mangle]
pub unsafe extern "C" fn write_console(ptr: *const u8, size: usize) -> isize {
    if ptr.is_null() {
        return -1;
    }

    let bytes = core::slice::from_raw_parts(ptr, size);
    let mut serial = SERIAL1.borrow_mut();
    for byte in bytes {
        if serial.send(*byte).is_err() {
            return -1;
        }
    }

    size as isize
}

/// Causes the VM to exit after logging the code.
///
/// The function is intentionally not named "exit" to avoid naming clashes. It is up to the
/// compatibility layer to make sure that this function is used for exiting.
#[no_mangle]
pub extern "C" fn exit_vm(code: i32) {
    info!("Exit called with code: {}", code);
    shutdown();
}
