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

//! AMD SEV-SNP data structures for attestation reports.

// TODO(#3703): Remove when fixed.
#![allow(clippy::extra_unused_type_parameters)]
#![no_std]

use bitflags::bitflags;
use strum::FromRepr;
use zerocopy::{AsBytes, FromBytes, FromZeroes};

/// A signed attestation report.
///
/// See Table 22 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, AsBytes, FromZeroes, FromBytes)]
pub struct AttestationReport {
    /// The data contained in the report.
    pub data: AttestationReportData,
    /// The signature over the data.
    pub signature: EcdsaSignature,
}
static_assertions::assert_eq_size!(AttestationReport, [u8; 1184]);

impl AttestationReport {
    /// Creates a new AttestationReport with all zeros and the provided value on the
    /// data.report_data field.
    pub fn from_report_data(report_data: [u8; REPORT_DATA_SIZE]) -> Self {
        let mut result = AttestationReport::new_zeroed();
        result.data.report_data = report_data;
        result
    }

    /// Checks that the report data is valid and the signature has the expected format.
    pub fn validate(&self) -> Result<(), &'static str> {
        self.data.validate()?;
        self.signature.validate_format()
    }

    pub fn has_debug_flag(&self) -> Result<bool, &'static str> {
        let policy_flags: PolicyFlags = self
            .data
            .policy
            .get_flags()
            .ok_or("Failed to parse flags")?;

        Ok(policy_flags.contains(PolicyFlags::DEBUG))
    }
}

/// The number of bytes of custom data that can be included in the attestation report.
///
/// See Table 22 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
pub const REPORT_DATA_SIZE: usize = 64;

/// The data contained in an attestation report.
///
/// See Table 22 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, AsBytes, FromZeroes, FromBytes)]
pub struct AttestationReportData {
    /// The version of the attestation report format.
    ///
    /// This implementation is based on version 2.
    pub version: u32,
    /// The guest security version number.
    pub guest_svn: u32,
    /// The policy required by the guest VM to be launched.
    pub policy: GuestPolicy,
    /// The family ID provided at launch.
    pub family_id: [u8; 16],
    /// The image ID provided at launch.
    pub image_id: [u8; 16],
    /// The VMPL value that was passed in the request.
    pub vmpl: u32,
    /// The algorithm used to sign the report.
    ///
    /// Use `AttestationReportData::get_signature_algo` to try to convert this to a
    /// `SigningAlgorithm` enum.
    pub signature_algo: u32,
    /// The current version of each of the components in the Trusted Computing Base (TCB). This
    /// could be different from the committed value during provisional execution when firmware
    /// is being updated.
    pub current_tcb: TcbVersion,
    /// Information about the platform.
    ///
    /// Use `AttestationReportData::get_platform_info` to try to convert this to a `PlatformInfo`
    /// biflag representation.
    pub platform_info: u64,
    /// The least significant bit indicates Whether the digest of the author key is included in the
    /// report, all other bits are reserved and must be zero.
    ///
    /// Use `AttestationReportData::get_author_key_en` to try to convert this to an `AuthorKey`
    /// enum.
    pub author_key_en: u64,
    /// Guest-provided data. The custom data provided in the attestation request.
    pub report_data: [u8; REPORT_DATA_SIZE],
    /// The measurement of the VM memory calculated at launch.
    pub measurement: [u8; 48],
    /// Custom data provided by the hypervisor at launch.
    pub host_data: [u8; 32],
    /// The SHA-384 digest of the ID public key used to sign the ID block that was provided in
    /// SNP_LAUNCH_FINISH.
    pub id_key_digest: [u8; 48],
    /// The SHA-384 digest of the author public key used to certify the ID key, if the least
    /// significant bit of `author_key_en` is 1, or all zeroes otherwise.
    pub author_key_digest: [u8; 48],
    /// The report ID of this guest.
    pub report_id: [u8; 32],
    /// The report ID of this guest's migration agent.
    pub report_id_ma: [u8; 32],
    /// The reported TCB version that was used to generate the versioned chip endorsement key
    /// (VCEK) used to sign this report.
    pub reported_tcb: TcbVersion,
    /// Reserved, must be zero.
    _reserved_0: [u8; 24],
    /// Identifier unique to the chip, unless the ID has been masked in configuration in which case
    /// it is all zeroes.
    pub chip_id: [u8; 64],
    /// The committed TCB version.
    pub committed_tcb: TcbVersion,
    /// The build number of the current secure firmware ABI version.
    pub current_build: u8,
    /// The minor number of the current secure firmware ABI version.
    pub current_minor: u8,
    /// The major number of the current secure firmware ABI version.
    pub current_major: u8,
    /// Reserved, must be zero.
    _reserved_1: u8,
    /// The build number of the committed secure firmware ABI version.
    pub committed_build: u8,
    /// The minor number of the committed secure firmware ABI version.
    pub committed_minor: u8,
    /// The major number of the committed secure firmware ABI version.
    pub committed_major: u8,
    /// Reserved, must be zero.
    _reserved_2: u8,
    /// The value of the current TCB version when the guest was launched or imported.
    pub launch_tcb: TcbVersion,
    /// Reserved, must be zero.
    _reserved_3: [u8; 168],
}

static_assertions::assert_eq_size!(AttestationReportData, [u8; 672]);

impl AttestationReportData {
    /// Gets the platform info field as a `PlatformInfo` representation if possible.
    pub fn get_platform_info(&self) -> Option<PlatformInfo> {
        PlatformInfo::from_bits(self.platform_info)
    }

    /// Gets the author key enabled field as an `AuthorKey` enum if possible.
    pub fn get_author_key_en(&self) -> Option<AuthorKey> {
        AuthorKey::from_repr(self.author_key_en)
    }

    /// Gets the signing algorithm field as a `SigningAlgorithm` enum if possible.
    pub fn get_signature_algo(&self) -> Option<SigningAlgorithm> {
        SigningAlgorithm::from_repr(self.signature_algo)
    }

    /// Checks that fields with specific expected values or ranges are valid and the reserved bytes
    /// are all zero.
    pub fn validate(&self) -> Result<(), &'static str> {
        self.policy.validate()?;
        self.current_tcb.validate()?;
        self.reported_tcb.validate()?;
        self.committed_tcb.validate()?;
        if self._reserved_0.iter().any(|&value| value != 0) {
            return Err("nonzero value in _reserved_0");
        }
        if self._reserved_1 != 0 {
            return Err("nonzero value in _reserved_1");
        }
        if self._reserved_2 != 0 {
            return Err("nonzero value in _reserved_2");
        }
        if self._reserved_3.iter().any(|&value| value != 0) {
            return Err("nonzero value in _reserved_3");
        }
        if self.get_signature_algo().is_none() {
            return Err("invalid signature algorithm");
        }
        if self.get_platform_info().is_none() {
            return Err("invalid platform info");
        }
        if self.get_author_key_en().is_none() {
            return Err("invalid value for author_key_en");
        }
        Ok(())
    }
}

bitflags! {
    /// Information on the platform configuration.
    #[derive(Default)]
    pub struct PlatformInfo: u64 {
        /// Indicates that simulatneous multi-threading (SMT) is enabled.
        const SMT_EN = (1 << 0);
        /// Indicates that transparent secure memory encryption (TSME) is enabled.
        const TSME_EN = (1 << 1);
    }
}

/// The signing algorithm used for the report signature.
///
/// See Table 117 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[derive(Debug, FromRepr, PartialEq)]
#[repr(u32)]
pub enum SigningAlgorithm {
    /// Invalid.
    Invalid = 0,
    /// ECDSA using curve P-384 with SHA-384.
    EcdsaP384Sha384 = 1,
}

/// The required policy for a guest to run.
///
/// See Table 9 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, AsBytes, FromZeroes, FromBytes)]
pub struct GuestPolicy {
    /// The minimum ABI minor version required to launch the guest.
    pub abi_minor: u8,
    /// The minimum ABI major version required to launch the guest.
    pub abi_major: u8,
    /// The allowed settings for the guest.
    ///
    /// Use `GuestPolicy::get_flags` to try to convert this to a `PolicyFlags` enum.
    pub flags: u16,
    /// Reserved, must be zero.
    _reserved: u32,
}

static_assertions::assert_eq_size!(GuestPolicy, u64);

impl GuestPolicy {
    /// Gets the flags field as a `PolicyFlags` representation if possible.
    pub fn get_flags(&self) -> Option<PolicyFlags> {
        PolicyFlags::from_bits(self.flags)
    }

    /// Checks that the flags are valid and the reserved bytes are all zero.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self._reserved != 0 {
            return Err("nonzero value in _reserved");
        }
        if self.get_flags().is_none() {
            return Err("invalid flags");
        }
        Ok(())
    }
}

/// The version of all the components in the Trusted Computing Base (TCB).
///
/// See Table 3 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, AsBytes, FromZeroes, FromBytes)]
pub struct TcbVersion {
    /// The current security version number (SVN) of the secure processor (PSP) bootloader.
    pub boot_loader: u8,
    /// The current SVN of the PSP operating system.
    pub tee: u8,
    /// Reserved, must be zero.
    _reserved: [u8; 4],
    /// The current SVN of the SNP firmware.
    pub snp: u8,
    /// The lowest current patch level of all the CPU cores.
    pub microcode: u8,
}

static_assertions::assert_eq_size!(TcbVersion, u64);

impl TcbVersion {
    /// Checks that the reserved bytes are all zero.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self._reserved.iter().any(|&value| value != 0) {
            return Err("nonzero value in _reserved");
        }
        Ok(())
    }
}

bitflags! {
    /// Flags indicating allowed policy options.
    #[derive(Default)]
    pub struct PolicyFlags: u16 {
        /// Simulatneous multi-threading (SMT) is allowed.
        const SMT = (1 << 0);
        /// Reserved, must always be 1.
        const RESERVED = (1 << 1);
        /// The guest can be associated with a migration agent.
        const MIGRATE_MA = (1 << 2);
        /// Debugging the guest is allowed.
        const DEBUG = (1 << 3);
        /// The guest can only be activated on a single socket.
        const SINGLE_SOCKET = (1 << 4);
    }
}

/// Whether the author key digest is included in the report.
#[derive(Debug, FromRepr)]
#[repr(u64)]
pub enum AuthorKey {
    /// The author key digest is not present.
    No = 0,
    /// The author key digest is present.
    Yes = 1,
}

/// An ECDSA signature.
///
/// See Table 119 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, AsBytes, FromZeroes, FromBytes)]
pub struct EcdsaSignature {
    /// The R component of this signature. The value is zero-extended and little-endian encoded.
    pub r: [u8; 72],
    /// The S component of this signature. The value is zero-extended and little-endian encoded.
    pub s: [u8; 72],
    /// Reserved, must be zero.
    _reserved: [u8; 368],
}
static_assertions::assert_eq_size!(EcdsaSignature, [u8; 512]);

impl EcdsaSignature {
    /// Checks that the reserved bytes are all zero.
    pub fn validate_format(&self) -> Result<(), &'static str> {
        if self._reserved.iter().any(|&value| value != 0) {
            return Err("nonzero value in _reserved");
        }
        Ok(())
    }
}
