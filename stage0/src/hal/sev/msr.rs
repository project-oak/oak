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

use crate::sev::GHCB_WRAPPER;

/// Read a MSR.
///
/// ## Safety
///
/// The caller must guarantee that the MSR is valid.
pub unsafe fn read_msr(msr: &crate::hal::base::Msr, msr_id: u32) -> u64 {
    if let Some(mut ghcb) = GHCB_WRAPPER.get() {
        ghcb.msr_read(msr_id).expect("couldn't read the MSR using the GHCB protocol")
    } else {
        msr.read()
    }
}

/// Write to a MSR.
///
/// ## Safety
///
/// The caller must guarantee that the MSR is valid.
pub unsafe fn write_msr(msr: &mut crate::hal::base::Msr, msr_id: u32, val: u64) {
    if let Some(mut ghcb) = GHCB_WRAPPER.get() {
        ghcb.msr_write(msr_id, val).expect("couldn't write the MSR using the GHCB protocol")
    } else {
        msr.write(val)
    }
}
