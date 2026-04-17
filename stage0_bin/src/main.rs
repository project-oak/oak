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

#![no_std]
#![no_main]

use core::panic::PanicInfo;

pub use oak_stage0::paging;

mod asm;

/// Entry point for the Rust code in the stage0 BIOS.
///
/// # Arguments
///
/// * `encrypted` - If not zero, the `encrypted`-th bit will be set in the page
///   tables.
#[unsafe(no_mangle)]
pub extern "C" fn rust64_start() -> ! {
    oak_stage0::rust64_start::<oak_stage0_sev::Sev>()
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_stage0::panic(info)
}
