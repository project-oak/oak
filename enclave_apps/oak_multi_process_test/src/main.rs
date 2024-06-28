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
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;

use oak_restricted_kernel_interface::syscall;
use oak_restricted_kernel_sdk::entrypoint;

#[entrypoint]
fn entrypoint() -> ! {
    oak_restricted_kernel_sdk::utils::log::set_logger(&LOGGER).expect("failed to set logger");
    oak_restricted_kernel_sdk::utils::log::set_max_level(
        oak_restricted_kernel_sdk::utils::log::LevelFilter::Debug,
    );
    loop {
        log::info!("BEEP BEEP BEEP! (awaking orchestrator)");
        let _ = syscall::unstable_switch_proccess(0);
    }
}
