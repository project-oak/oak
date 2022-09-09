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

use core::mem::MaybeUninit;
use sev_guest::ghcb::{Ghcb, GhcbProtocol};

#[link_section = ".ghcb"]
static mut GHCB: MaybeUninit<Ghcb> = MaybeUninit::uninit();

/// Initializes the GHCB and shares it with the hypervisor.
pub fn init_ghcb(snp_enabled: bool) -> GhcbProtocol<'static> {
    // Safety: this data structure is placed in valid memory so we won't page fault when accessing
    // it. We reset the value of the GHCB immediately after shareing it with the hypervisor, so it
    // will be fine if it is not initialized.
    let ghcb: &mut Ghcb = unsafe { GHCB.assume_init_mut() };
    share_ghcb_with_hypervisor(ghcb, snp_enabled);
    ghcb.reset();
    GhcbProtocol::new(ghcb)
}

/// Sets up the page containing the GHCB data structure to be shared with the hypervisor.
fn share_ghcb_with_hypervisor(ghcb: &Ghcb, snp_enabled: bool) {
    // Assume identity mapping for now.
    let ghcb_gpa = ghcb as *const Ghcb as usize;
    if snp_enabled {
        // This code will eventually also mark the page as shared in the RMP and use the MSR
        // protocol to register the page with the hypervisor.
        unimplemented!("SNP support is not yet implemented.");
    }
}
