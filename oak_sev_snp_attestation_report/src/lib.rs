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
//!
//! This is based on revision 1.58 of <https://www.amd.com/system/files/TechDocs/56860.pdf>
//! Content-addressed link for the specific revision of the specification:
//! <https://static.space/sha2-512:56e501d2fca015ab1d13d2ec8934b16af989373437706d6a3d258c00fb170a833d76e264ae8fd5709bcdcf3d5fcb7a52faf47a6191c7fe1d0940a2f492183ba8>

// TODO(#3703): Remove when fixed.
#![allow(clippy::extra_unused_type_parameters)]
#![no_std]

use bitflags::bitflags;
use strum::FromRepr;
use zerocopy::{FromBytes, FromZeros, Immutable, IntoBytes, KnownLayout};

/// A signed attestation report.
///
/// See Table 23 of the specification.
#[repr(C)]
#[derive(Debug, IntoBytes, FromBytes, Immutable, KnownLayout)]
pub struct AttestationReport {
    /// The data contained in the report.
    pub data: AttestationReportData,
    /// The signature over the data.
    pub signature: EcdsaSignature,
}
static_assertions::assert_eq_size!(AttestationReport, [u8; 1184]);

impl AttestationReport {
    /// Creates a new AttestationReport with all zeros and the provided value on
    /// the data.report_data field.
    pub fn from_report_data(report_data: [u8; REPORT_DATA_SIZE]) -> Self {
        let mut result = AttestationReport::new_zeroed();
        result.data.report_data = report_data;
        result
    }

    /// Checks that the report data is valid and the signature has the expected
    /// format.
    pub fn validate(&self) -> Result<(), &'static str> {
        self.data.validate()?;
        self.signature.validate_format()
    }

    pub fn has_debug_flag(&self) -> Result<bool, &'static str> {
        let policy_flags: PolicyFlags =
            self.data.policy.get_flags().ok_or("Failed to parse flags")?;

        Ok(policy_flags.contains(PolicyFlags::DEBUG))
    }
}

/// The number of bytes of custom data that can be included in the attestation
/// report.
///
/// See Table 23 of the specification.
pub const REPORT_DATA_SIZE: usize = 64;

/// A byte array which is interpreted depending on the CPU model.
///
/// See Tables 3 and 4 of the specification.
pub type RawTcbVersion = [u8; 8];

/// The data contained in an attestation report.
///
/// See Table 23 of the specification.
#[repr(C)]
#[derive(Debug, IntoBytes, FromBytes, Immutable, KnownLayout)]
pub struct AttestationReportData {
    /// The version of the attestation report format.
    ///
    /// This implementation is based on version 5 and is backwards compatible
    /// down to version 3. Versions 1 and 2 can be parsed but won't validate.
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
    /// Use `AttestationReportData::get_signature_algo` to try to convert this
    /// to a `SigningAlgorithm` enum.
    pub signature_algo: u32,
    /// The current version of each of the components in the Trusted Computing
    /// Base (TCB). This could be different from the committed value during
    /// provisional execution when firmware is being updated.
    pub current_tcb: RawTcbVersion,
    /// Information about the platform.
    ///
    /// Use `AttestationReportData::get_platform_info` to try to convert this to
    /// a `PlatformInfo` biflag representation.
    pub platform_info: u64,
    /// Bit-packed field containing the following:
    /// 31:5 -- reserved, MBZ
    /// 4:2 -- SIGNING_KEY, key used to sign this report
    /// 1 - MASK_CHIP_KEY
    /// 0 - AUTHOR_KEY_EN
    key: u32,

    /// Reserved. Must be zero.
    _reserved_4: u32,
    /// Guest-provided data. The custom data provided in the attestation
    /// request.
    pub report_data: [u8; REPORT_DATA_SIZE],
    /// The measurement of the VM memory calculated at launch.
    pub measurement: [u8; 48],
    /// Custom data provided by the hypervisor at launch.
    pub host_data: [u8; 32],
    /// The SHA-384 digest of the ID public key used to sign the ID block that
    /// was provided in SNP_LAUNCH_FINISH.
    pub id_key_digest: [u8; 48],
    /// The SHA-384 digest of the author public key used to certify the ID key,
    /// if the least significant bit of `author_key_en` is 1, or all zeroes
    /// otherwise.
    pub author_key_digest: [u8; 48],
    /// The report ID of this guest.
    pub report_id: [u8; 32],
    /// The report ID of this guest's migration agent.
    pub report_id_ma: [u8; 32],
    /// The reported TCB version that was used to generate the versioned chip
    /// endorsement key (VCEK) used to sign this report.
    pub reported_tcb: RawTcbVersion,
    /// Family ID (combined Extended Family ID and Family ID).
    pub cpuid_fam_id: u8,
    /// Model (combined Extended Model and Model fields).
    pub cpuid_mod_id: u8,
    /// Stepping.
    pub cpuid_step: u8,
    /// Reserved.
    _reserved_0: [u8; 21],
    /// Identifier unique to the chip, unless the ID has been masked in
    /// configuration in which case it is all zeroes. Older CPU models
    /// (Milan, Genoa) use the full 64 bytes, newer models (Turin and beyond)
    /// use only the first 8 bytes and the rest is zeroed out.
    pub chip_id: [u8; 64],
    /// The committed TCB version.
    pub committed_tcb: RawTcbVersion,
    /// The build number of the current secure firmware ABI version.
    pub current_build: u8,
    /// The minor number of the current secure firmware ABI version.
    pub current_minor: u8,
    /// The major number of the current secure firmware ABI version.
    pub current_major: u8,
    /// Reserved.
    _reserved_1: u8,
    /// The build number of the committed secure firmware ABI version.
    pub committed_build: u8,
    /// The minor number of the committed secure firmware ABI version.
    pub committed_minor: u8,
    /// The major number of the committed secure firmware ABI version.
    pub committed_major: u8,
    /// Reserved.
    _reserved_2: u8,
    /// The value of the current TCB version when the guest was launched or
    /// imported.
    pub launch_tcb: RawTcbVersion,
    /// The value of the verified mitigation vector when the guest was launched.
    pub launch_mit_vector: u64,
    /// The value of the current verified mitigation vector.
    pub current_mit_vector: u64,

    /// Reserved.
    _reserved_3: [u8; 152],
}

static_assertions::assert_eq_size!(AttestationReportData, [u8; 672]);

/// The AMD EPYC CPU model.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AmdProduct {
    /// Any model that does not support SEV-SNP, or is not explicitly listed.
    Unsupported = 0,
    Milan = 1,
    Genoa = 2,
    Turin = 3,
}

impl AttestationReportData {
    /// Gets the platform info field as a `PlatformInfo` representation.
    pub fn get_platform_info(&self) -> PlatformInfo {
        // The latest documentation defines only the lowest 5 bits, with the others
        // reserved. We, however, have encountered the reserved bits being set in the
        // wild; therefore, mask them out here.
        PlatformInfo::from_bits_truncate(self.platform_info)
    }

    /// Determines the AMD CPU model from the attestation report. Source:
    /// https://github.com/LIT-Protocol/sev-snp-utils/blob/2db12052f1daa0b240594cb2e24d73c66d3379a5/src/guest/measure/vcpu_types.rs#L71
    pub fn get_product(&self) -> AmdProduct {
        if self.cpuid_fam_id == 0x1a {
            if self.cpuid_mod_id == 0x02 {
                AmdProduct::Turin
            } else {
                AmdProduct::Unsupported
            }
        } else if self.cpuid_fam_id == 0x19 {
            if self.cpuid_mod_id == 0x01 {
                AmdProduct::Milan
            } else if self.cpuid_mod_id == 0x11 {
                AmdProduct::Genoa
            } else {
                AmdProduct::Unsupported
            }
        } else {
            AmdProduct::Unsupported
        }
    }

    /// Switch to decide whether Table 3 or Table 4 applies.
    ///
    /// Right now this only makes the Turin test attestation example pass.
    /// Needs refinement - the assignment of CPU IDs and product names
    /// (resp. TCB version encoding) in the spec is somewhat ambiguous.
    fn has_legacy_tcb_version_encoding(&self) -> bool {
        self.cpuid_fam_id != 0x1a
    }

    /// Parses the TCB version from the 8-byte RawTcbVersion.
    ///
    /// See Tables 3 and 4 of the specification.
    fn parse_raw_tcb_version(&self, raw: RawTcbVersion) -> TcbVersion {
        if self.has_legacy_tcb_version_encoding() {
            TcbVersion {
                boot_loader: raw[0],
                microcode: raw[7],
                snp: raw[6],
                tee: raw[1],
                ..Default::default()
            }
        } else {
            TcbVersion {
                boot_loader: raw[1],
                microcode: raw[7],
                snp: raw[3],
                tee: raw[2],
                fmc: raw[0],
            }
        }
    }

    /// Gets the current TCB version as Rust struct.
    pub fn get_current_tcb_version(&self) -> TcbVersion {
        self.parse_raw_tcb_version(self.current_tcb)
    }

    /// Gets the reported TCB version as Rust struct.
    pub fn get_reported_tcb_version(&self) -> TcbVersion {
        self.parse_raw_tcb_version(self.reported_tcb)
    }

    /// Gets the key used to sign this report.
    pub fn get_signing_key(&self) -> Option<SigningKey> {
        // Only bits 2, 3, 4 are of interest, mask out the rest and shift.
        SigningKey::from_repr((self.key & 0b11100) >> 2)
    }

    /// Gets the value of MaskChipKey.
    pub fn get_mask_chip_key(&self) -> bool {
        self.key & 0b10 > 0
    }

    /// Returns the value of AUTHOR_KEY_EN, i.e. whether the author key digest
    /// is included in the report.
    pub fn has_author_key(&self) -> bool {
        self.key & 1 > 0
    }

    /// Gets the signing algorithm field as a `SigningAlgorithm` enum if
    /// possible.
    pub fn get_signature_algo(&self) -> Option<SigningAlgorithm> {
        SigningAlgorithm::from_repr(self.signature_algo)
    }

    /// Checks that fields with specific expected values or ranges are valid and
    /// the reserved bytes are all zero.
    pub fn validate(&self) -> Result<(), &'static str> {
        // We require attestation report version at least three since we
        // rely on the availability of CPU ID. Version zero must go through
        // since it represents the fake/insecure case.
        if self.version == 1 || self.version == 2 {
            return Err("outdated attestation report version - upgrade firmware");
        }
        self.policy.validate()?;
        if self._reserved_4 != 0 {
            return Err("nonzero value in _reserved_4");
        }
        if self.get_signing_key().is_none() {
            return Err("invalid signing key setting");
        }
        if self.get_signature_algo().is_none() {
            return Err("invalid signature algorithm");
        }
        Ok(())
    }
}

bitflags! {
    /// Information on the platform configuration.
    #[derive(Default)]
    pub struct PlatformInfo: u64 {
        /// Indicates that simultaneous multi-threading (SMT) is enabled.
        const SMT_EN = (1 << 0);
        /// Indicates that transparent secure memory encryption (TSME) is enabled.
        const TSME_EN = (1 << 1);
        /// Indicates that the platform is using error correcting codes for memory.
        const ECC_EN = (1 << 2);
        /// Indicates that the RAPL feature is disabled.
        const RAPL_DIS = (1 << 3);
        /// Indicates ciphertext hiding is enabled for the DRAM.
        const CIPHERTEXT_HIDING_DRAM_EN = (1 << 4);
        /// Indicates that alias checking has completed since the last reboot.
        /// Mitigation for CVE-2024-21944.
        const ALIAS_CHECK_COMPLETE = (1 << 5);
        /// Indicates whether SEV-TIO is enabled.
        const TIO_EN = (1 << 7);
    }
}

/// The signing algorithm used for the report signature.
///
/// See Table 139 of the specification.
#[derive(Debug, FromRepr, PartialEq)]
#[repr(u32)]
pub enum SigningAlgorithm {
    /// Invalid.
    Invalid = 0,
    /// ECDSA using curve P-384 with SHA-384.
    EcdsaP384Sha384 = 1,
}

/// Key used to sign the attestation report.
///
/// See Table 23 of the specification.
#[derive(Debug, FromRepr, PartialEq)]
#[repr(u32)]
pub enum SigningKey {
    VCEK = 0,
    VLEK = 1,
    // Values 2 through 6 are reserved.
    None = 7,
}

/// The required policy for a guest to run.
///
/// See Table 9 of the specification.
#[repr(C)]
#[derive(Debug, IntoBytes, FromBytes, Immutable)]
pub struct GuestPolicy {
    /// The minimum ABI minor version required to launch the guest.
    pub abi_minor: u8,
    /// The minimum ABI major version required to launch the guest.
    pub abi_major: u8,
    /// The allowed settings for the guest.
    ///
    /// Use `GuestPolicy::get_flags` to try to convert this to a `PolicyFlags`
    /// enum.
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
#[derive(Debug, Default, Immutable, PartialEq)]
pub struct TcbVersion {
    /// The current security version number (SVN) of the secure processor (PSP)
    /// bootloader.
    pub boot_loader: u8,
    /// The current SVN of the PSP operating system.
    pub tee: u8,
    /// The current SVN of the SNP firmware.
    pub snp: u8,
    /// The lowest current patch level of all the CPU cores.
    pub microcode: u8,
    /// The current SVN of the Flexible Memory Controller (FMC) firmware.
    /// Zero for Milan and Genoa models.
    pub fmc: u8,
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
        /// CXL can be populated with devices or memory.
        const CXL_ALLOW = (1 << 5);
        /// AES 256 XTS is required for memory encryption.
        const MEM_AES_256_XTS = (1 << 6);
        /// Running Average Power Limit is disabled.
        const RAPL_DIS = (1 << 7);
        /// Ciphertext hiding for DRAM must be enabled.
        const CIPHERTEXT_HIDING_DRAM = (1 << 8);
        /// Disable Guest support for Page Swap and Page Move commands.
        const PAGE_SWAP_DISABLE = (1 << 9);
    }
}

/// An ECDSA signature.
///
/// See Table 141 of the specification.
#[repr(C)]
#[derive(Debug, IntoBytes, FromBytes, Immutable, KnownLayout)]
pub struct EcdsaSignature {
    /// The R component of this signature. The value is zero-extended and
    /// little-endian encoded.
    pub r: [u8; 72],
    /// The S component of this signature. The value is zero-extended and
    /// little-endian encoded.
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
