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

use core::arch::x86_64::CpuidResult;

use oak_sev_guest::cpuid::CpuidInput;

use crate::sev::GHCB_WRAPPER;

pub fn cpuid(leaf: u32) -> CpuidResult {
    if let Some(ghcb) = GHCB_WRAPPER.get() {
        ghcb.lock().get_cpuid(CpuidInput { eax: leaf, ecx: 0, xcr0: 0, xss: 0 }).unwrap().into()
    } else {
        crate::hal::base::cpuid(leaf)
    }
}
