//
// Copyright © 2019 Intel Corporation
// SPDX-License-Identifier: Apache-2.0
//
// Copyright 2022 The Project Oak Authors
// SPDX-License-Identifier: Apache-2.0
//

#![no_std]

use core::ffi::c_void;

pub mod paging;

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

pub fn ram_min() -> usize {
    (unsafe { &RAM_MIN as *const _ }) as usize
}

pub fn text_start() -> usize {
    (unsafe { &TEXT_START as *const _ }) as usize
}

pub fn text_end() -> usize {
    (unsafe { &TEXT_END as *const _ }) as usize
}

pub fn stack_start() -> usize {
    (unsafe { &STACK_START as *const _ }) as usize
}
