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

mod accept_memory;
mod cpuid;
mod mmio;
mod msr;
mod port;

pub use cpuid::*;
pub use mmio::*;
pub use msr::*;
use oak_linux_boot_params::BootE820Entry;
use oak_sev_guest::msr::SevStatus;
pub use port::*;

pub fn accept_memory(e820_table: &[BootE820Entry]) {
    if crate::sev_status().contains(SevStatus::SNP_ACTIVE) {
        accept_memory::validate_memory(e820_table)
    }
}
