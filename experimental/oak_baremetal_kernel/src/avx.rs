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

use x86_64::registers::{
    control::{Cr0, Cr0Flags, Cr4, Cr4Flags},
    xcontrol::{XCr0, XCr0Flags},
};

/// Enables Streaming SIMD Extensions (SEE) and Advanced Vector Extensions (AVX).
///
/// See <https://wiki.osdev.org/SSE> for more information.
pub fn enable_avx() {
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
