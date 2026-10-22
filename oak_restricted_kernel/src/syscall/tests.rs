//
// Copyright 2023 The Project Oak Authors
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

use alloc::boxed::Box;

use oak_restricted_kernel_interface::{
    Errno,
    syscalls::{MmapFlags, MmapProtection},
};
use x86_64::{
    VirtAddr,
    structures::paging::{Page, PageTable, Size2MiB},
};

use super::{fd::copy_max_slice, mmap::mmap};
use crate::mm::page_tables::RootPageTable;

#[test]
fn shorter_dst_copy() {
    let src: &[u8; 6] = &[0, 1, 2, 3, 4, 5];
    let dst: &mut [u8; 5] = &mut [0; 5];
    let length = copy_max_slice(src, dst);
    assert_eq!(length, 5);
    assert_eq!(dst, &[0, 1, 2, 3, 4])
}

#[test]
fn longer_dst_copy() {
    let src: &[u8; 6] = &[0, 1, 2, 3, 4, 5];
    let dst: &mut [u8; 8] = &mut [0; 8];
    let length = copy_max_slice(src, dst);
    assert_eq!(length, 6);
    assert_eq!(dst, &[0, 1, 2, 3, 4, 5, 0, 0])
}

#[test]
fn empty_copy() {
    let src: &[u8; 0] = &[];
    let dst: &mut [u8; 5] = &mut [1; 5];
    let length = copy_max_slice(src, dst);
    assert_eq!(length, 0);
    assert_eq!(dst, &[1; 5])
}

#[test]
fn mmap_fixed_range_past_user_space() {
    // Starts in user space, but the 4 MiB range ends past the lower half.
    let result = mmap(
        Some(VirtAddr::new(0x7FFF_FFE0_0000)),
        4 << 20,
        MmapProtection::PROT_READ,
        MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE | MmapFlags::MAP_FIXED,
    );
    assert!(matches!(result, Err(Errno::EINVAL)));
}

#[test]
fn find_unallocated_pages_range_past_address_space() {
    let page_table = RootPageTable::new(Box::leak(Box::new(PageTable::new())), VirtAddr::zero());
    let start = Page::<Size2MiB>::containing_address(VirtAddr::new(0x20_0000));

    // The end of the range would be past the canonical lower half.
    assert_eq!(page_table.find_unallocated_pages(start, 1 << 26), None);
    // The end of the range would overflow.
    let high_start = Page::<Size2MiB>::containing_address(VirtAddr::new(0xFFFF_FFFF_FFC0_0000));
    assert_eq!(page_table.find_unallocated_pages(high_start, 2), None);
    // A range that fits is still found.
    assert_eq!(page_table.find_unallocated_pages(start, 2), Some(Page::range(start, start + 2)));
}
