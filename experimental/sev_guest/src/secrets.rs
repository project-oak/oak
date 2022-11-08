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

//! This module contains structs that can be used to interpret the contents of the secrets page that
//! is provisioned into the VM guest memory during SEV-SNP startup.

use strum::FromRepr;
use zerocopy::FromBytes;

/// The size of the secrets page.
pub const SECRETS_PAGE_SIZE: usize = 4096;

/// The version of the secrets pages that we expect to receive.
pub const SECRETS_PAGE_VERSION: u32 = 3;

/// Representation of the secrets page.
///
/// See: Table 68 in <https://www.amd.com/system/files/TechDocs/56860.pdf>
#[repr(C, align(4096))]
#[derive(Debug, FromBytes)]
pub struct SecretsPage {
    /// The version of the secrets page.
    pub version: u32,
    /// The least significant bit indicates whether an initial migration image is enabled in the
    /// guest context. All other bits are reserved and must be zero.
    ///
    /// Use `SecretsPage::get_imi_en` to try to get this as an `Imi` enum.
    pub imi_en: u32,
    /// The family, model and stepping of the CPU as reported in CPUID Fn0000_0001_EAX.
    /// See <https://en.wikipedia.org/wiki/CPUID#EAX=1:_Processor_Info_and_Feature_Bits>.
    pub fms: u32,
    /// Reserved. Must be 0.
    _reserved: u32,
    /// Guest-OS-visible workarounds provided by the hypervisor during SNP_LAUNCH_START. The format
    /// is hypervisor-defined.
    pub gosv: [u8; 16],
    /// VM-platform communication key 0. AES key used for encrypting messages to the platform.
    pub vmpck_0: [u8; 32],
    /// VM-platform communication key 1. AES key used for encrypting messages to the platform.
    pub vmpck_1: [u8; 32],
    /// VM-platform communication key 2. AES key used for encrypting messages to the platform.
    pub vmpck_2: [u8; 32],
    /// VM-platform communication key 3. AES key used for encrypting messages to the platform.
    pub vmpck_3: [u8; 32],
    /// Area reserved for guest OS use.
    pub guest_area_0: [u8; 96],
    /// Bitmap indicating which quadwords of the VM Save Area have been tweaked. This is only used
    /// if the VMSA Register Protection feature is enabled.
    pub vmsa_tweak_bitmap: [u8; 64],
    /// Area reserved for guest OS use.
    pub guest_area_1: [u8; 32],
    /// Scaling factor that can be used for calculating the real CPU frequency.
    pub tsc_factor: u32,
}

impl SecretsPage {
    /// Gets the IMI enabled field as and `Imi` enum if possible.
    pub fn get_imi_en(&self) -> Option<Imi> {
        Imi::from_repr(self.imi_en)
    }
}

static_assertions::assert_eq_size!(SecretsPage, [u8; SECRETS_PAGE_SIZE]);

/// Whether an initial migration image is enabled.
#[derive(Debug, FromRepr)]
#[repr(u32)]
pub enum Imi {
    /// The initial migration image is not enabled.
    Disabled = 0,
    /// The initial migration image is enabled.
    Enabled = 1,
}
