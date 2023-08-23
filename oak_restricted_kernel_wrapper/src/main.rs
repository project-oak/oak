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
use x86_64::registers::{
    control::{Cr0, Cr0Flags, Cr4, Cr4Flags},
    xcontrol::{XCr0, XCr0Flags},
};

/// Entry point for the 64-bit Rust code.
#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, _rsi: &BootParams) -> ! {
    enable_avx();
    // The path to the artifact from the binary dependency is stored in the
    // CARGO_<ARTIFACT-TYPE>_FILE_<DEP> environment variable.
    // See <https://doc.rust-lang.org/nightly/cargo/reference/unstable.html?#artifact-dependencies-environment-variables>.
    let _payload = include_bytes!(env!("CARGO_BIN_FILE_OAK_RESTRICTED_KERNEL_BIN"));
    loop {}
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    // For now just go into an infinite loop when panicking.
    loop {}
}

/// Enables Streaming SIMD Extensions (SEE) and Advanced Vector Extensions (AVX).
///
/// See <https://wiki.osdev.org/SSE> for more information.
fn enable_avx() {
    unsafe {
        let mut cr0 = Cr0::read();
        cr0 &= !Cr0Flags::EMULATE_COPROCESSOR;
        cr0 |= Cr0Flags::MONITOR_COPROCESSOR;
        Cr0::write(cr0);
        let cr0 = Cr0::read();
        assert!(cr0 & Cr0Flags::TASK_SWITCHED != Cr0Flags::TASK_SWITCHED);
        let mut cr4 = Cr4::read();
        cr4 |= Cr4Flags::OSFXSR | Cr4Flags::OSXMMEXCPT_ENABLE | Cr4Flags::OSXSAVE;
        Cr4::write(cr4);
        let mut xcr0 = XCr0::read();
        xcr0 |= XCr0Flags::X87 | XCr0Flags::SSE | XCr0Flags::AVX;
        XCr0::write(xcr0);
    }
}
