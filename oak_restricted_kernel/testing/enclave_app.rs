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

//! A minimal test application executed by the Restricted Kernel orchestrator.
//!
//! It reads the DICE data and derived key from the kernel descriptors (which
//! also causes the kernel to zeroize its own copies in the file descriptor
//! table), zeroizes its local buffers, wipes its stack, and signals ready for
//! memory dump.

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;

use core::fmt::Write;

use oak_restricted_kernel_interface::{DERIVED_KEY_FD, DICE_DATA_FD, syscall};
use oak_restricted_kernel_sdk::{entrypoint, utils::Stderr};
use zerocopy::{FromZeros, IntoBytes};
use zeroize::Zeroize;

pub const READY_MARKER: &str = "test application ready for memory dump";

#[entrypoint]
fn run() -> ! {
    let mut dice_data = oak_dice::evidence::RestrictedKernelDiceData::new_zeroed();
    let read_len =
        syscall::read(DICE_DATA_FD, dice_data.as_mut_bytes()).expect("couldn't read dice data");
    assert_eq!(read_len, dice_data.as_mut_bytes().len());

    let mut derived_key = [0u8; 32];
    let read_len =
        syscall::read(DERIVED_KEY_FD, &mut derived_key).expect("couldn't read derived key");
    assert_eq!(read_len, derived_key.len());

    // Zeroize application local copies.
    dice_data.as_mut_bytes().zeroize();
    derived_key.zeroize();

    // Wipe dead stack frames.
    zeroize::zeroize_stack::<{ 64 * 1024 }>();

    writeln!(Stderr {}, "{}", READY_MARKER).unwrap();
    Stderr::flush();

    loop {
        core::hint::spin_loop();
    }
}
