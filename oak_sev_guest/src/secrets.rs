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

//! This module contains structs that can be used to interpret the contents of
//! the secrets page that is provisioned into the VM guest memory during SEV-SNP
//! startup.

use strum::FromRepr;
use zerocopy::FromBytes;

/// The size of the secrets page.
pub const SECRETS_PAGE_SIZE: usize = 4096;

/// The minimum version of the secrets pages that we expect to receive.
pub const SECRETS_PAGE_MIN_VERSION: u32 = 2;

/// Representation of the Secrets Page Guest Reserved Area.
///
/// See Table 4 in <https://www.amd.com/content/dam/amd/en/documents/epyc-technical-docs/specifications/56421-guest-hypervisor-communication-block-standardization.pdf>
#[repr(C)]
#[derive(Debug, FromBytes)]
pub struct GuestReservedArea {
    /// VMPL0 Current Guest Message Sequence Number \[31:0\]
    pub vmpl0_guest_seq_low: u32,

    /// VMPL1 Current Guest Message Sequence Number \[31:0\]
    pub vmpl1_guest_seq_low: u32,

    /// VMPL2 Current Guest Message Sequence Number \[31:0\]
    pub vmpl2_guest_seq_low: u32,

    /// VMPL3 Current Guest Message Sequence Number \[31:0\]
    pub vmpl3_guest_seq_low: u32,

    /// AP Jump Table Physical Address
    pub ap_jump_table_pa: u64,

    /// (Rev 2.01+) VMPL0 Current Guest Message Sequence Number \[63:32\]
    /// Otherwise: Reseved, MBZ
    pub vmpl0_guest_seq_high: u32,

    /// (Rev 2.01+) VMPL1 Current Guest Message Sequence Number \[63:32\]
    /// Otherwise: Reseved, MBZ
    pub vmpl1_guest_seq_high: u32,

    /// (Rev 2.01+) VMPL2 Current Guest Message Sequence Number \[63:32\]
    /// Otherwise: Reseved, MBZ
    pub vmpl2_guest_seq_high: u32,

    /// (Rev 2.01+) VMPL3 Current Guest Message Sequence Number \[63:32\]
    /// Otherwise: Reseved, MBZ
    pub vmpl3_guest_seq_high: u32,

    /// Reserved: MBZ
    _reserved_4: [u8; 0x16],

    /// (Rev 2.01+) Version (1 = 2.01)
    /// Otherwise: Reserved, MBZ
    pub version: u16,

    /// Guest Usage
    pub guest_usage: [u8; 0x20],
}
static_assertions::assert_eq_size!(GuestReservedArea, [u8; 96]);

/// Representation of the secrets page.
///
/// See: Table 71 in <https://www.amd.com/system/files/TechDocs/56860.pdf>
#[repr(C, align(4096))]
#[derive(Debug, FromBytes)]
pub struct SecretsPage {
    /// The version of the secrets page.
    pub version: u32,
    /// The least significant bit indicates whether an initial migration image
    /// is enabled in the guest context. All other bits are reserved and
    /// must be zero.
    ///
    /// Use `SecretsPage::get_imi_en` to try to get this as an `Imi` enum.
    pub imi_en: u32,
    /// The family, model and stepping of the CPU as reported in CPUID
    /// Fn0000_0001_EAX. See <https://en.wikipedia.org/wiki/CPUID#EAX=1:_Processor_Info_and_Feature_Bits>.
    pub fms: u32,
    /// Reserved.
    _reserved_0: u32,
    /// Guest-OS-visible workarounds provided by the hypervisor during
    /// SNP_LAUNCH_START. The format is hypervisor-defined.
    pub gosv: [u8; 16],
    /// VM-platform communication key 0. AES key used for encrypting messages to
    /// the platform.
    pub vmpck_0: [u8; 32],
    /// VM-platform communication key 1. AES key used for encrypting messages to
    /// the platform.
    pub vmpck_1: [u8; 32],
    /// VM-platform communication key 2. AES key used for encrypting messages to
    /// the platform.
    pub vmpck_2: [u8; 32],
    /// VM-platform communication key 3. AES key used for encrypting messages to
    /// the platform.
    pub vmpck_3: [u8; 32],
    /// Area reserved for guest OS use.
    pub guest_area_0: GuestReservedArea,
    /// Bitmap indicating which quadwords of the VM Save Area have been tweaked.
    /// This is only used if the VMSA Register Protection feature is
    /// enabled.
    pub vmsa_tweak_bitmap: [u8; 64],
    /// Area reserved for guest OS use.
    pub guest_area_1: [u8; 32],
    /// Scaling factor that can be used for calculating the real CPU frequency.
    pub tsc_factor: u32,
    /// Reserved.
    _reserved_1: u32,
    /// Set to the current mitigation vector when the VM was launched.
    pub launch_mit_vector: u64,
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

impl SecretsPage {
    /// Checks that version is the expected value, `SecretsPage::imi_en` has a
    /// valid value, and that the reserved bytes are all zero.
    pub fn validate(&self) -> Result<(), &'static str> {
        if SECRETS_PAGE_MIN_VERSION > self.version {
            return Err("invalid version");
        }
        if self.get_imi_en().is_none() {
            return Err("invalid value for imi_en");
        }
        Ok(())
    }
}
