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

//! A minimal test orchestrator for Oak Restricted Kernel key handling tests.

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;

use core::fmt::Write;

use oak_dice::evidence::Stage0DiceData;
use oak_restricted_kernel_interface::{DERIVED_KEY_FD, DICE_DATA_FD, syscall};
use oak_restricted_kernel_sdk::{entrypoint, utils::Stderr};
use zerocopy::{FromZeros, IntoBytes};
use zeroize::Zeroize;

pub const READY_MARKER: &str = "test application ready for memory dump";

fn print_key(tag: &str, key: &[u8; 32]) {
    write!(Stderr {}, "{tag}=").unwrap();
    for byte in key.iter() {
        write!(Stderr {}, "{byte:02x}").unwrap();
    }
    writeln!(Stderr {}).unwrap();
}

#[entrypoint]
fn run() -> ! {
    let mut stage0_dice_data =
        Stage0DiceData::new_box_zeroed().expect("failed to allocate memory for Stage0DiceData");
    let read_len = syscall::read(DICE_DATA_FD, stage0_dice_data.as_mut_bytes())
        .expect("couldn't read stage0 dice data");
    assert_eq!(read_len, stage0_dice_data.as_mut_bytes().len());

    let mut layer_1_key = [0u8; 32];
    let mut layer_1_cdi = [0u8; 32];
    layer_1_key
        .copy_from_slice(&stage0_dice_data.layer_1_certificate_authority.eca_private_key[..32]);
    layer_1_cdi.copy_from_slice(&stage0_dice_data.layer_1_cdi.cdi);

    let app_digest = [0x5au8; 32];
    let mut derived_key =
        oak_restricted_kernel_dice::generate_derived_key(&stage0_dice_data, &app_digest);
    let mut dice_data =
        oak_restricted_kernel_dice::generate_dice_data(stage0_dice_data, &app_digest);

    syscall::write(DERIVED_KEY_FD, derived_key.as_bytes()).expect("couldn't write derived key");
    syscall::write(DICE_DATA_FD, dice_data.as_bytes()).expect("couldn't write dice data");

    derived_key.zeroize();
    dice_data.as_mut_bytes().zeroize();

    print_key("LAYER1_KEY", &layer_1_key);
    layer_1_key.zeroize();
    print_key("LAYER1_CDI", &layer_1_cdi);
    layer_1_cdi.zeroize();

    zeroize::zeroize_stack::<{ 64 * 1024 }>();

    writeln!(Stderr {}, "{}", READY_MARKER).unwrap();
    Stderr::flush();

    loop {
        core::hint::spin_loop();
    }
}
