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

//! Utilities for creating and processing SNP Guest Request protocol messages.

use bitflags::bitflags;
use strum::FromRepr;

/// The size of a guest message, including the header and maximum payload size.
pub const GUEST_MESSAGE_SIZE: usize = 4096;

/// The currently supported header version number.
pub const CURRENT_HEADER_VERSION: u8 = 1;

/// The currently supported message version number.
pub const CURRENT_MESSAGE_VERSION: u8 = 1;

/// The currently supported attestation report version number.
pub const CURRENT_ATTESTATION_VERSION: u8 = 2;

/// An encrypted guest message.
///
/// The same data structure is used for requests and responses.
///
/// See section 8.26 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C, align(4096))]
#[derive(Debug)]
pub struct GuestMessage {
    /// The message header.
    pub header: GuestMessageHeader,
    /// The encrypted payload.
    pub payload: [u8; 4000],
}

static_assertions::assert_eq_size!(GuestMessage, [u8; GUEST_MESSAGE_SIZE]);

/// The header for an encrypted guest request message.
///
/// See Table 97 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
pub struct GuestMessageHeader {
    /// The authentication tag for the payload and additional data.
    pub auth_tag: [u8; 32],
    /// The message sequence number. This is used as the IV for the AEAD.
    ///
    /// The same sequence number must never be reused with the same key.
    pub sequence_number: u64,
    /// Reserved. Must be zero.
    _reserved_0: u64,
    /// The algorithm used to encrypt the payload.
    pub algorithm: AeadAlgorithm,
    /// The header version. Currently only version 1 is supported.
    pub header_version: u8,
    /// The size of the header in bytes.
    pub header_size: u16,
    /// The type of message that the payload represents.
    pub message_type: MessageType,
    /// The version of the message. Currently only version 1 is supported for all message types.
    pub message_version: u8,
    /// The size of the encrypted message payload in bytes.
    pub message_size: u16,
    /// Reserved. Must be zero.
    _reserved_1: u32,
    /// The ID of the VM communication key that was used to encrypt the payload.
    pub message_vmpck: u8,
    /// Reserved. Must be zero.
    _reserved_2: [u8; 35],
}

static_assertions::assert_eq_size!(GuestMessageHeader, [u8; 96]);

/// The AEAD algorithm used for encryption.
///
/// See Table 98 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[derive(Debug, FromRepr)]
#[repr(u8)]
pub enum AeadAlgorithm {
    /// Invalid encryption algorithm.
    Invalid = 0,
    /// 256-bit AES-GCM.
    Aes256Gcm = 1,
}

/// The type of message represented by the payload.
///
/// See Table 99 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[derive(Debug, FromRepr)]
#[repr(u8)]
pub enum MessageType {
    /// Invalid message type.
    Invalid = 0,
    /// CPUID request.
    CpuidRequest = 1,
    /// CPUID response.
    CpuidResponse = 2,
    /// Request for a derivce key.
    KeyRequest = 3,
    /// Derived key response.
    KeyResponse = 4,
    /// Attestation report request.
    ReportRequest = 5,
    /// Attestation report response.
    ReportResponse = 6,
    /// VM export request. Used for VM migration.
    ExportRequest = 7,
    /// VM export response. Used for VM migration.
    ExportResponse = 8,
    /// VM import request. Used during VM migration, typically by a migration agent.
    ImportRequest = 9,
    /// VM import response. Used during VM migration.
    ImportResponse = 10,
    /// VM absorb request by a migration agent.
    AbsorbRequest = 11,
    /// VM absorb response.
    AbsorbResponse = 12,
    /// VMRK request. Provides the VM root key to use after migration.
    VmrkRequest = 13,
    /// VMRK response. Status of using the VM root key after migration.
    VmrkResponse = 14,
    // VM absorb request when no migration agent is used.
    AbsorbNomaRequest = 15,
    // VM absorb response when no migration agent is used.
    AbsorbNomaResponse = 16,
    // Timestamp counter information request.
    TscInfoRequest = 17,
    /// Timestamp counter information response.
    TccInfoReqsponse = 18,
}

/// Request for an attestation report.
///
/// See Table 20 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
pub struct AttestationRequest {
    /// The custom data to be included in the attestation report.
    pub report_data: [u8; 64],
    /// The VM Protection Level (VMPL) to be used in the attestation report.
    ///
    /// Must be greater or equal to the current VMPL and at most 3.
    pub vmpl: u32,
    /// Reserved, must be zero.
    _reserved: [u8; 28],
}

static_assertions::assert_eq_size!(AttestationRequest, [u8; 96]);

/// Response containing the attestation report.
///
/// See Table 23 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
pub struct AttestationResponse {
    /// The status of the operation.
    pub status: ReportStatus,
    /// The size of the report.
    pub report_size: u32,
    /// Reserved, must be zero.
    _reserved: [u8; 24],
    /// The attestation report.
    pub report: AttestationReport,
}

static_assertions::assert_eq_size!(AttestationResponse, [u8; 1216]);

/// A signed attestation report.
///
/// See Table 21 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
pub struct AttestationReport {
    /// The data contained in the report.
    pub data: AttestationReportData,
    /// The signature over the data.
    pub signature: EcdsaSignature,
}

static_assertions::assert_eq_size!(AttestationReport, [u8; 1184]);

/// The data contained in an attestation report.
///
/// See Table 21 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
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
    pub signature_algo: SigningAlgorithm,
    /// The current version of each of the components in the Trusted Computing Base (TCB). This
    /// could be different from the committed value during provisional execution when firmware
    /// is being updated.
    pub current_tcb: TcbVersion,
    /// Information about the platform.
    pub platform_info: PlatformInfo,
    /// Whether the digest of the author key is included in the report.
    pub author_key_en: AuthorKey,
    /// The custom data provided in the attestation request.
    pub report_data: [u8; 64],
    /// The measurement of the VM memory calculated at launch.
    pub measurement: [u8; 48],
    /// Custom data provided by the hypervisor at launch.
    pub host_data: [u8; 32],
    /// The SHA-384 digest of the ID public key used to sign the ID block that was provided in
    /// SNP_LAUNCH_FINISH.
    pub id_key_digest: [u8; 48],
    /// The SHA-384 digest of the author public key used to certify the ID key, if `author_key_en`
    /// is `AuthorKey::Yes`, or all zeroes otherwise.
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

/// The required policy for a guest to run.
///
/// See Table 8 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
pub struct GuestPolicy {
    /// The minimum ABI minor version required to launch the guest.
    pub abi_minor: u8,
    /// The minimum ABI major version required to launch the guest.
    pub abi_major: u8,
    /// The allowed settings for the guest.
    pub flags: PolicyFlags,
    /// Reserved, must be zero.
    _reserved: u32,
}

static_assertions::assert_eq_size!(GuestPolicy, u64);

/// The version of all the components in the Trusted Computing Base (TCB).
///
/// See Table 3 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
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

/// The status of the report response.
#[derive(Debug, FromRepr)]
#[repr(u32)]
pub enum ReportStatus {
    /// Report was successfully generated.
    Success = 0,
    /// The supplied parameters in the request was invalid.
    InvalidParams = 0x16,
}

/// An ECDSA signature.
///
/// See Table 107 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
pub struct EcdsaSignature {
    /// The R component of this signature. The value is zero-extended and little-endian encoded.
    pub r: [u8; 72],
    /// The S component of this signature. The value is zero-extended and little-endian encoded.
    pub s: [u8; 72],
    /// Reserved, must be zero.
    _reserved: [u8; 368],
}

static_assertions::assert_eq_size!(EcdsaSignature, [u8; 512]);

/// An ECDSA public key.
///
/// See Table 108 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
pub struct EcdsaPublicKey {
    /// The curve for this public key.
    pub curve: EccCurve,
    /// The R component of this public. The value is zero-extended and little-endian encoded.
    pub r: [u8; 72],
    /// The S component of this public key. The value is zero-extended and little-endian encoded.
    pub s: [u8; 72],
    /// Reserved, must be zero.
    _reserved: [u8; 880],
}

static_assertions::assert_eq_size!(EcdsaPublicKey, [u8; 1028]);

/// The signing algorithm used for the report signature.
///
/// See Table 105 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[derive(Debug, FromRepr)]
#[repr(u32)]
pub enum SigningAlgorithm {
    /// Invalid.
    Invalid = 0,
    /// ECDSA using curve P-384 with SHA-384.
    EcdsaP384Sha384 = 1,
}

/// The elliptic curve used.
///
/// See Table 106 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[derive(Debug, FromRepr)]
#[repr(u32)]
pub enum EccCurve {
    /// Invalid.
    Invalid = 0,
    /// Curve P-384.
    P384 = 2,
}
