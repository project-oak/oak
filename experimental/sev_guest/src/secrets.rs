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
//! is provisioned during SEV-SNP startup.

use zerocopy::FromBytes;

/// The size of the secrets page.
pub const SECRETS_PAGE_SIZE: usize = 4096;

/// The version of the secrets pages the we expect to receive.
pub const SECRETS_PAGE_VERSION: u32 = 3;

/// Representation of the secrets page.
///
/// See: Table 68 in <https://www.amd.com/system/files/TechDocs/56860.pdf>
#[repr(C, align(4096))]
#[derive(Debug, FromBytes)]
pub struct SecretsPage {
    /// The version of the secrets page.
    pub version: u32,
    /// The least significant bit indicates where an initial imigration image is enabled in the
    /// guest context. All other bits are reserved and must be zero.
    pub imi_en: u32,
    /// The family, model and stepping of the CPU as reported in CPUID Fn0000_0001_EAX.
    pub fms: u32,
    _reserved_0: u32,
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

static_assertions::assert_eq_size!(SecretsPage, [u8; SECRETS_PAGE_SIZE]);
