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

#![no_std]
#![no_main]

mod asm;

use core::panic::PanicInfo;
use oak_linux_boot_params::BootParams;

/// Entry point for the 64-bit Rust code.
#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, _rsi: &BootParams) -> ! {
    let _payload = include_bytes!(env!("PAYLOAD_PATH"));
    loop {}
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    // For now just go into an infinite loop when panicking.
    loop {}
}
