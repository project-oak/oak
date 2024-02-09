//
// Copyright 2024 The Project Oak Authors
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

#![no_std]

extern crate alloc;

use oak_channel::basic_framed::load_raw;
use oak_dice::evidence::Stage0DiceData;

pub struct AttestedApp {
    pub elf_binary: alloc::vec::Vec<u8>,
    pub derived_key: oak_restricted_kernel_dice::DerivedKey,
    pub dice_data: oak_dice::evidence::RestrictedKernelDiceData,
}

impl AttestedApp {
    pub fn load_and_attest<C: oak_channel::Channel>(
        mut channel: C,
        stage0_dice_data: Stage0DiceData,
    ) -> Self {
        let elf_binary = load_raw::<C, 4096>(&mut channel).expect("failed to load");
        log::info!("Binary loaded, size: {}", elf_binary.len());
        let app_digest = oak_restricted_kernel_dice::measure_app_digest_sha2_256(&elf_binary);
        log::info!(
            "Application digest (sha2-256): {}",
            app_digest.map(|x| alloc::format!("{:02x}", x)).join("")
        );
        let derived_key =
            oak_restricted_kernel_dice::generate_derived_key(&stage0_dice_data, &app_digest);
        let dice_data =
            oak_restricted_kernel_dice::generate_dice_data(stage0_dice_data, &app_digest);
        Self {
            elf_binary,
            derived_key,
            dice_data,
        }
    }
}
