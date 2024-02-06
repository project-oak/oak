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

pub fn entrypoint<C: oak_channel::Channel>(mut channel: C, _stage0_dice_data: Stage0DiceData) -> ! {
    let application_bytes = load_raw::<C, 4096>(&mut channel).expect("failed to load");
    log::info!("Binary loaded, size: {}", application_bytes.len());
    let app_digest = oak_restricted_kernel_dice::measure_app_digest_sha2_256(&application_bytes);
    log::info!(
        "Application digest (sha2-256): {}",
        app_digest.map(|x| alloc::format!("{:02x}", x)).join("")
    );
    unimplemented!();
}
