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

// TODO(#3703): Remove when fixed.
#![allow(clippy::extra_unused_type_parameters)]

use bitflags::bitflags;
use core::mem::size_of;
use strum::{EnumIter, FromRepr};
use zerocopy::{AsBytes, FromBytes, FromZeroes};

/// The size of a guest message, including the header and maximum payload size.
pub const GUEST_MESSAGE_SIZE: usize = 4096;

/// The maximum payload size.
pub const MAX_PAYLOAD_SIZE: usize = 4000;

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
#[derive(Debug, AsBytes, FromZeroes, FromBytes)]
pub struct GuestMessage {
    /// The message header.
    pub header: GuestMessageHeader,
    /// The encrypted payload.
    pub payload: [u8; MAX_PAYLOAD_SIZE],
}

static_assertions::assert_eq_size!(GuestMessage, [u8; GUEST_MESSAGE_SIZE]);

impl GuestMessage {
    pub const fn new() -> Self {
        GuestMessage {
            header: GuestMessageHeader::new(),
            payload: [0; MAX_PAYLOAD_SIZE],
        }
    }

    /// Checks that header is valid.
    pub fn validate(&self) -> Result<(), &'static str> {
        self.header.validate()
    }
}

/// The authenticated subsection of the header used for an encrypted guest request message.
///
/// See Table 99 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, AsBytes, FromZeroes, FromBytes)]
pub struct AuthenticatedHeader {
    /// The algorithm used to encrypt the payload.
    ///
    /// Use `GuestMessageHeader::get_algorithm` to try to convert this to an `AeadAlgorithm` enum.
    pub algorithm: u8,
    /// The header version. Currently only version 1 is supported.
    pub header_version: u8,
    /// The size of the header in bytes.
    pub header_size: u16,
    /// The type of message that the payload represents.
    ///
    /// Use `GuestMessageHeader::get_message_type` to try to convert this to a `MessageType` enum.
    pub message_type: u8,
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

static_assertions::assert_eq_size!(AuthenticatedHeader, [u8; 48]);

/// The header for an encrypted guest request message.
///
/// See Table 99 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, AsBytes, FromZeroes, FromBytes)]
pub struct GuestMessageHeader {
    /// The authentication tag for the payload and additional data.
    pub auth_tag: [u8; 32],
    /// The message sequence number. This is used as the IV for the AEAD.
    ///
    /// The same sequence number must never be reused with the same key.
    pub sequence_number: u64,
    /// Reserved. Must be zero.
    _reserved_0: u64,
    /// The the sub-section of the header that is treated as additional data in the AEAD.
    pub auth_header: AuthenticatedHeader,
}

static_assertions::assert_eq_size!(GuestMessageHeader, [u8; 96]);

impl GuestMessageHeader {
    pub const fn new() -> Self {
        GuestMessageHeader {
            auth_tag: [0; 32],
            sequence_number: 0,
            _reserved_0: 0,
            auth_header: AuthenticatedHeader {
                algorithm: AeadAlgorithm::Aes256Gcm as u8,
                header_version: CURRENT_HEADER_VERSION,
                header_size: size_of::<Self>() as u16,
                message_type: MessageType::Invalid as u8,
                message_version: CURRENT_MESSAGE_VERSION,
                message_size: 0,
                _reserved_1: 0,
                message_vmpck: 0,
                _reserved_2: [0; 35],
            },
        }
    }

    /// Gets the algorithm field as an `AeadAlgorithm` enum if possible.
    pub fn get_algorithm(&self) -> Option<AeadAlgorithm> {
        AeadAlgorithm::from_repr(self.auth_header.algorithm)
    }

    /// Gets the message type field as a `MessageType` enum if possible.
    pub fn get_message_type(&self) -> Option<MessageType> {
        MessageType::from_repr(self.auth_header.message_type)
    }

    /// Checks that the authenticated header subsection is valid.
    ///
    /// The reserved fields do not have zero values in the guest messages returned from the Platform
    /// Secure Processor, so we don't validate these.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.get_algorithm().is_none()
            || self.auth_header.algorithm == AeadAlgorithm::Invalid as u8
        {
            return Err("invalid AEAD algorithm");
        }
        if self.get_message_type().is_none()
            || self.auth_header.message_type == MessageType::Invalid as u8
        {
            return Err("invalid message type");
        }
        if self.auth_header.header_version != CURRENT_HEADER_VERSION {
            return Err("invalid header version");
        }
        if self.auth_header.message_version != CURRENT_MESSAGE_VERSION {
            return Err("invalid message version");
        }
        // For now we always assume we use VMPCK_0 to encrypt all messages.
        if self.auth_header.message_vmpck != 0 {
            return Err("invalid message VMPCK");
        }
        if self.auth_header.header_size != size_of::<Self>() as u16 {
            return Err("invalid header size");
        }
        if self.auth_header.message_size as usize > MAX_PAYLOAD_SIZE {
            return Err("invalid message size");
        }
        Ok(())
    }
}

/// The AEAD algorithm used for encryption.
///
/// See Table 100 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
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
/// See Table 101 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[derive(Debug, FromRepr)]
#[repr(u8)]
pub enum MessageType {
    /// Invalid message type.
    Invalid = 0,
    /// CPUID request.
    CpuidRequest = 1,
    /// CPUID response.
    CpuidResponse = 2,
    /// Request for a derived key.
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

/// Request for a derived key.
///
/// See Table 18 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, AsBytes, FromZeroes, FromBytes)]
pub struct KeyRequest {
    /// Selects which key will be used to derive the key.
    ///
    /// This contains the ROOT_KEY_SELECT and KEY_SEL bit-fields. To interact with the individual
    /// bit-fields use `KeyRequest::get_key_select`, `KeyRequest::get_root_key_select`,
    /// `KeyRequest::set_key_select` or `KeyRequest::set_root_key_select`
    key_select: u32,
    /// Reserved, must be zero.
    _reserved: u32,
    /// Mask indicating which guest data will be mixed into the derived key.
    ///
    /// Use `KeyRequest::get_guest_field_select_flags` to try to convert this to a
    /// `GuestFieldFlags` enum.
    pub guest_field_select: u64,
    /// The VM Protection Level (VMPL) to mix into the derived key.
    ///
    /// Must be greater or equal to the current VMPL and at most 3.
    pub vmpl: u32,
    /// The guest security version number (SVN) to mix into the key.
    ///
    /// Must not exceed the guest SVN provided at launch in the ID block.
    pub guest_svn: u32,
    /// The TCB version to mix into the key.
    ///
    /// Must not exceed the committed TCB.
    pub tcb_version: u64,
}

static_assertions::assert_eq_size!(KeyRequest, [u8; 32]);

impl KeyRequest {
    /// The bit mask for the root key select bit.
    const ROOT_KEY_SELECT_MASK: u32 = 1 << 0;

    /// The bit mask for the key select bits.
    const KEY_SELECT_MASK: u32 = (1 << 1) | (1 << 2);

    pub const fn new() -> Self {
        Self {
            key_select: 0,
            _reserved: 0,
            guest_field_select: 0,
            vmpl: 0,
            guest_svn: 0,
            tcb_version: 0,
        }
    }

    /// Gets the `guest_field_select` field as a `GuestFieldFlags` representation if possible.
    pub fn get_guest_field_select_flags(&self) -> Option<GuestFieldFlags> {
        GuestFieldFlags::from_bits(self.guest_field_select)
    }

    /// Gets bit 0 of the `key_select` field as a `RootKeySelect` enum.
    pub fn get_root_key_select(&self) -> RootKeySelect {
        RootKeySelect::from_repr(self.key_select & KeyRequest::ROOT_KEY_SELECT_MASK).unwrap()
    }

    /// Gets bits 1 and 2 of the `key_select` field as a `KeySelect` enum.
    pub fn get_key_select(&self) -> KeySelect {
        KeySelect::from_repr((self.key_select & KeyRequest::KEY_SELECT_MASK) >> 1).unwrap()
    }

    /// Sets bit 0 of the `key_select` field.
    pub fn set_root_key_select(&mut self, root_key_select: RootKeySelect) {
        self.key_select = self.key_select & !KeyRequest::ROOT_KEY_SELECT_MASK
            | (root_key_select as u32) & KeyRequest::ROOT_KEY_SELECT_MASK;
    }

    /// Sets bits 1 and 2 of the `key_select` field.
    pub fn set_key_select(&mut self, key_select: KeySelect) {
        self.key_select = self.key_select & !KeyRequest::KEY_SELECT_MASK
            | (key_select as u32) << 1 & KeyRequest::KEY_SELECT_MASK;
    }
}

impl Message for KeyRequest {
    fn get_message_type() -> MessageType {
        MessageType::KeyRequest
    }
}

/// Response containing the derived key.
///
/// See Table 19 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, FromZeroes, FromBytes, AsBytes)]
pub struct KeyResponse {
    /// The status of the operation.
    ///
    /// Use `KeyResponse::get_status` to try to convert this to a `KeyStatus` enum.
    pub status: u32,
    /// Reserved. Must be 0.
    _reserved: [u8; 28],
    /// The derived key if status is `KeyStatus::Success`.
    pub derived_key: [u8; 32],
}

static_assertions::assert_eq_size!(KeyResponse, [u8; 64]);

impl Message for KeyResponse {
    fn get_message_type() -> MessageType {
        MessageType::KeyResponse
    }
}

impl KeyResponse {
    /// Gets the status field as a `KeyStatus` enum if possible.
    pub fn get_status(&self) -> Option<KeyStatus> {
        KeyStatus::from_repr(self.status)
    }

    /// Checks that all reserved bytes are zero and that the status field, the report size and the
    /// report format are all valid.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self._reserved.iter().any(|&value| value != 0) {
            return Err("nonzero value in _reserved");
        }
        if self.get_status().is_none() {
            return Err("invalid status");
        }
        Ok(())
    }
}

/// The selected key to use for key derivation.
#[derive(Clone, Copy, Debug, EnumIter, FromRepr, PartialEq)]
#[repr(u32)]
pub enum KeySelect {
    /// Use VLEK if installed, otherwise use the VCEK.
    Default = 0,
    /// Use the Versioned Chip Endorsement Key (VCEK).
    VCEK = 1,
    /// Use the Loaded Chip Endorsement Key (VLEK).
    VLEK = 2,
    /// Reserved.
    Reserved = 3,
}

/// The selected root key to use for key derivation.
#[derive(Clone, Copy, Debug, EnumIter, FromRepr, PartialEq)]
#[repr(u32)]
pub enum RootKeySelect {
    /// Use the Versioned Chip Endorsement Key (VCEK).
    VCEK = 0,
    /// Use the Virtual Machine Root Key (VMRK) provided by the migration agent.
    VMRK = 1,
}

/// The status of the report response.
#[derive(Debug, FromRepr, PartialEq)]
#[repr(u32)]
pub enum KeyStatus {
    /// Report was successfully generated.
    Success = 0,
    /// The supplied parameters in the request was invalid.
    InvalidParams = 0x16,
    /// The key selection field was invalid.
    InvalidKeySelection = 0x27,
}

bitflags! {
    /// Flags indicating allowed policy options.
    #[derive(Default)]
    pub struct GuestFieldFlags: u64 {
        /// The guest policy will be mixed into the key.
        const GUEST_POLICY = (1 << 0);
        /// The image ID provided in the ID block will be mixed into the key.
        const IMAGE_ID = (1 << 1);
        /// The family ID provided in the ID block will be mixed into the key.
        const FAMILY_ID = (1 << 2);
        /// The launch measurement of the VM will be mixed into the key.
        const MEASUREMENT = (1 << 3);
        /// The guest-provided SVN will be mixed into the key.
        const GUEST_SVN = (1 << 4);
        /// The guest-provided TCB version will be mixed into the key.
        const TCB_VERSION = (1 << 5);
    }
}

/// Request for an attestation report.
///
/// See Table 20 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, AsBytes, FromZeroes, FromBytes)]
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

impl AttestationRequest {
    pub const fn new() -> Self {
        AttestationRequest {
            report_data: [0; 64],
            vmpl: 0,
            _reserved: [0; 28],
        }
    }
}

impl Message for AttestationRequest {
    fn get_message_type() -> MessageType {
        MessageType::ReportRequest
    }
}

/// Response containing the attestation report.
///
/// See Table 23 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, FromZeroes, FromBytes, AsBytes)]
pub struct AttestationResponse {
    /// The status of the operation.
    ///
    /// Use `AttestationResponse::get_status` to try to convert this to a `ReportStatus` enum.
    pub status: u32,
    /// The size of the report.
    pub report_size: u32,
    /// Reserved, must be zero.
    _reserved: [u8; 24],
    /// The attestation report.
    pub report: AttestationReport,
}

static_assertions::assert_eq_size!(AttestationResponse, [u8; 1216]);

impl Message for AttestationResponse {
    fn get_message_type() -> MessageType {
        MessageType::ReportResponse
    }
}

impl AttestationResponse {
    /// Gets the status field as a `ReportStatus` enum if possible.
    pub fn get_status(&self) -> Option<ReportStatus> {
        ReportStatus::from_repr(self.status)
    }

    /// Checks that all reserved bytes are zero and that the status field, the report size and the
    /// report format are all valid.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self._reserved.iter().any(|&value| value != 0) {
            return Err("nonzero value in _reserved");
        }
        if self.get_status().is_none() {
            return Err("invalid status");
        }
        if self.report_size != size_of::<AttestationReport>() as u32 {
            return Err("invalid report size");
        }
        self.report.validate()
    }
}

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
    /// Checks that the report data is valid and the signature has the expected format.
    pub fn validate(&self) -> Result<(), &'static str> {
        self.data.validate()?;
        self.signature.validate_format()
    }
}

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
    /// The custom data provided in the attestation request.
    pub report_data: [u8; 64],
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
        if self.signature_algo != SigningAlgorithm::EcdsaP384Sha384 as u32 {
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

/// The status of the report response.
#[derive(Debug, FromRepr, PartialEq)]
#[repr(u32)]
pub enum ReportStatus {
    /// Report was successfully generated.
    Success = 0,
    /// The supplied parameters in the request was invalid.
    InvalidParams = 0x16,
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

/// An ECDSA public key.
///
/// See Table 120 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
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
/// See Table 117 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
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
/// See Table 118 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[derive(Debug, FromRepr)]
#[repr(u32)]
pub enum EccCurve {
    /// Invalid.
    Invalid = 0,
    /// Curve P-384.
    P384 = 2,
}

pub trait Message {
    fn get_message_type() -> MessageType;
}

#[cfg(test)]
mod tests {
    //! Test to check the getters and setters for the bit fields of the `key_select` field in the
    //! `KeyRequest` struct.

    use super::*;
    use strum::IntoEnumIterator;

    #[test]
    fn test_key_request_key_select() {
        let mut request = KeyRequest::new();
        assert_eq!(request.get_key_select(), KeySelect::Default);
        assert_eq!(request.get_root_key_select(), RootKeySelect::VCEK);

        for key_select in KeySelect::iter() {
            let current_root = request.get_root_key_select();
            request.set_key_select(key_select);
            assert_eq!(request.get_key_select(), key_select);
            assert_eq!(request.get_root_key_select(), current_root);
            for root_key_select in RootKeySelect::iter() {
                request.set_root_key_select(root_key_select);
                assert_eq!(request.get_key_select(), key_select);
                assert_eq!(request.get_root_key_select(), root_key_select);
            }
        }
    }
}
