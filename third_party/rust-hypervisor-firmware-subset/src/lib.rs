//
// Copyright © 2019 Intel Corporation
// SPDX-License-Identifier: Apache-2.0
//
// Copyright 2022 The Project Oak Authors
// SPDX-License-Identifier: Apache-2.0
//

#![no_std]

use core::ffi::c_void;

mod asm;
pub mod boot;
mod common;
pub mod device;
mod gdt;
pub mod mem;
pub mod paging;
pub mod pci;
pub mod pvh;
pub mod virtio;

extern "C" {
    #[link_name = "ram_min"]
    static RAM_MIN: c_void;
    #[link_name = "text_start"]
    static TEXT_START: c_void;
    #[link_name = "text_end"]
    static TEXT_END: c_void;
    #[link_name = "stack_start"]
    static STACK_START: c_void;
}

const PAGE_SIZE: u64 = 4096;

pub fn ram_min() -> u64 {
    let ram_min = unsafe { &RAM_MIN as *const _ as u64 };
    assert!(ram_min % PAGE_SIZE == 0);
    ram_min
}

pub fn text_start() -> u64 {
    let text_start = unsafe { &TEXT_START as *const _ as u64 };
    assert!(text_start % PAGE_SIZE == 0);
    text_start
}

pub fn text_end() -> u64 {
    let text_end = unsafe { &TEXT_END as *const _ as u64 };
    assert!(text_end % PAGE_SIZE == 0);
    text_end
}

pub fn stack_start() -> u64 {
    let stack_start = unsafe { &STACK_START as *const _ as u64 };
    assert!(stack_start % PAGE_SIZE == 0);
    stack_start
}
