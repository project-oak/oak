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

use core::mem::size_of;

use bitflags::bitflags;
use strum::{EnumIter, FromRepr};
use zerocopy::{FromBytes, Immutable, IntoBytes};

/// The size of a guest message, including the header and maximum payload size.
pub const GUEST_MESSAGE_SIZE: usize = 4096;

/// The maximum payload size.
pub const MAX_PAYLOAD_SIZE: usize = 4000;

/// The currently supported header version number.
pub const CURRENT_HEADER_VERSION: u8 = 1;

/// An encrypted guest message.
///
/// The same data structure is used for requests and responses.
///
/// See section 8.26 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C, align(4096))]
#[derive(Debug, IntoBytes, FromBytes)]
pub struct GuestMessage {
    /// The message header.
    pub header: GuestMessageHeader,
    /// The encrypted payload.
    pub payload: [u8; MAX_PAYLOAD_SIZE],
}

static_assertions::assert_eq_size!(GuestMessage, [u8; GUEST_MESSAGE_SIZE]);

impl GuestMessage {
    pub const fn new() -> Self {
        GuestMessage { header: GuestMessageHeader::new(), payload: [0; MAX_PAYLOAD_SIZE] }
    }

    /// Checks that header is valid.
    pub fn validate(&self) -> Result<(), &'static str> {
        self.header.validate()
    }
}

impl Default for GuestMessage {
    fn default() -> Self {
        Self::new()
    }
}

/// The authenticated subsection of the header used for an encrypted guest
/// request message.
///
/// See Table 100 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, IntoBytes, FromBytes, Immutable)]
pub struct AuthenticatedHeader {
    /// The algorithm used to encrypt the payload.
    ///
    /// Use `GuestMessageHeader::get_algorithm` to try to convert this to an
    /// `AeadAlgorithm` enum.
    pub algorithm: u8,
    /// The header version. Currently only version 1 is supported.
    pub header_version: u8,
    /// The size of the header in bytes.
    pub header_size: u16,
    /// The type of message that the payload represents.
    ///
    /// Use `GuestMessageHeader::get_message_type` to try to convert this to a
    /// `MessageType` enum.
    pub message_type: u8,
    /// The version of the message. Currently only version 1 is supported for
    /// all message types.
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
/// See Table 100 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, IntoBytes, FromBytes, Immutable)]
pub struct GuestMessageHeader {
    /// The authentication tag for the payload and additional data.
    pub auth_tag: [u8; 32],
    /// The message sequence number. This is used as the IV for the AEAD.
    ///
    /// The same sequence number must never be reused with the same key.
    pub sequence_number: u64,
    /// Reserved. Must be zero.
    _reserved_0: u64,
    /// The the sub-section of the header that is treated as additional data in
    /// the AEAD.
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
                message_version: 0,
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
    /// The reserved fields do not have zero values in the guest messages
    /// returned from the Platform Secure Processor, so we don't validate
    /// these.
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

impl Default for GuestMessageHeader {
    fn default() -> Self {
        Self::new()
    }
}

/// The AEAD algorithm used for encryption.
///
/// See Table 101 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
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
/// See Table 102 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
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
    /// VM import request. Used during VM migration, typically by a migration
    /// agent.
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
        /// The launch mitigation vector will be mixed into the key.
        ///
        /// This is only valid when using version 2 of the key request guest message.
        const LAUCNH_MIT_VECTOR = (1 << 6);
    }
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

/// An ECDSA public key.
///
/// See Table 142 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
pub struct EcdsaPublicKey {
    /// The curve for this public key.
    pub curve: EccCurve,
    /// The R component of this public. The value is zero-extended and
    /// little-endian encoded.
    pub r: [u8; 72],
    /// The S component of this public key. The value is zero-extended and
    /// little-endian encoded.
    pub s: [u8; 72],
    /// Reserved, must be zero.
    _reserved: [u8; 880],
}

static_assertions::assert_eq_size!(EcdsaPublicKey, [u8; 1028]);

/// The elliptic curve used.
///
/// See Table 140 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[derive(Debug, FromRepr)]
#[repr(u32)]
pub enum EccCurve {
    /// Invalid.
    Invalid = 0,
    /// Curve P-384.
    P384 = 2,
}

pub trait Message {
    const MESSAGE_TYPE: MessageType;
    const MESSAGE_VERSION: u8;
}

pub mod v1 {
    use oak_sev_snp_attestation_report::AttestationReport;

    use super::*;

    /// Request for a derived key.
    ///
    /// See Table 19 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
    #[repr(C)]
    #[derive(Debug, IntoBytes, FromBytes)]
    pub struct KeyRequest {
        /// Selects which key will be used to derive the key.
        ///
        /// This contains the ROOT_KEY_SELECT and KEY_SEL bit-fields. To
        /// interact with the individual bit-fields use
        /// `KeyRequest::get_key_select`,
        /// `KeyRequest::get_root_key_select`, `KeyRequest::set_key_select` or
        /// `KeyRequest::set_root_key_select`
        key_select: u32,
        /// Reserved, must be zero.
        _reserved: u32,
        /// Mask indicating which guest data will be mixed into the derived key.
        ///
        /// Use `KeyRequest::get_guest_field_select_flags` to try to convert
        /// this to a `GuestFieldFlags` enum.
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

        /// Gets the `guest_field_select` field as a `GuestFieldFlags`
        /// representation if possible.
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
                | ((key_select as u32) << 1) & KeyRequest::KEY_SELECT_MASK;
        }
    }

    impl Default for KeyRequest {
        fn default() -> Self {
            Self::new()
        }
    }

    impl Message for KeyRequest {
        const MESSAGE_TYPE: MessageType = MessageType::KeyRequest;
        const MESSAGE_VERSION: u8 = 1;
    }

    /// Response containing the derived key.
    ///
    /// See Table 21 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
    #[repr(C)]
    #[derive(Debug, FromBytes, IntoBytes)]
    pub struct KeyResponse {
        /// The status of the operation.
        ///
        /// Use `KeyResponse::get_status` to try to convert this to a
        /// `KeyStatus` enum.
        pub status: u32,
        /// Reserved. Must be 0.
        _reserved: [u8; 28],
        /// The derived key if status is `KeyStatus::Success`.
        pub derived_key: [u8; 32],
    }

    static_assertions::assert_eq_size!(KeyResponse, [u8; 64]);

    impl Message for KeyResponse {
        const MESSAGE_TYPE: MessageType = MessageType::KeyResponse;
        const MESSAGE_VERSION: u8 = 1;
    }

    impl KeyResponse {
        /// Gets the status field as a `KeyStatus` enum if possible.
        pub fn get_status(&self) -> Option<KeyStatus> {
            KeyStatus::from_repr(self.status)
        }

        /// Checks that all reserved bytes are zero and that the status field,
        /// the report size and the report format are all valid.
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

    /// Request for an attestation report.
    ///
    /// See Table 22 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
    #[repr(C)]
    #[derive(Debug, IntoBytes, FromBytes)]
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
            AttestationRequest { report_data: [0; 64], vmpl: 0, _reserved: [0; 28] }
        }
    }

    impl Default for AttestationRequest {
        fn default() -> Self {
            Self::new()
        }
    }

    impl Message for AttestationRequest {
        const MESSAGE_TYPE: MessageType = MessageType::ReportRequest;
        const MESSAGE_VERSION: u8 = 1;
    }

    /// Response containing the attestation report.
    ///
    /// See Table 25 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
    #[repr(C)]
    #[derive(Debug, FromBytes, IntoBytes)]
    pub struct AttestationResponse {
        /// The status of the operation.
        ///
        /// Use `AttestationResponse::get_status` to try to convert this to a
        /// `ReportStatus` enum.
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
        const MESSAGE_TYPE: MessageType = MessageType::ReportResponse;
        const MESSAGE_VERSION: u8 = 1;
    }

    impl AttestationResponse {
        /// Gets the status field as a `ReportStatus` enum if possible.
        pub fn get_status(&self) -> Option<ReportStatus> {
            ReportStatus::from_repr(self.status)
        }

        /// Checks that all reserved bytes are zero and that the status field,
        /// the report size and the report format are all valid.
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
}

pub mod v2 {
    use super::*;

    /// Request for a derived key.
    ///
    /// See Table 19 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
    #[repr(C)]
    #[derive(Debug, IntoBytes, FromBytes)]
    pub struct KeyRequest {
        pub base_key_request: super::v1::KeyRequest,
        /// The launch mitigation vector to mix into the key.
        ///
        /// The guest cannot set bits that were not originally set when the
        /// guest was launched.
        pub launch_mit_vector: u64,
    }

    static_assertions::assert_eq_size!(KeyRequest, [u8; 40]);

    impl KeyRequest {
        pub const fn new() -> Self {
            Self { base_key_request: super::v1::KeyRequest::new(), launch_mit_vector: 0 }
        }
    }

    impl Default for KeyRequest {
        fn default() -> Self {
            Self::new()
        }
    }

    impl Message for KeyRequest {
        const MESSAGE_TYPE: MessageType = MessageType::KeyRequest;
        const MESSAGE_VERSION: u8 = 2;
    }
}

#[cfg(test)]
mod tests {
    // Test to check the getters and setters for the bit fields of the
    // `key_select` field in the `KeyRequest` struct.

    use strum::IntoEnumIterator;

    use super::*;

    #[test]
    fn test_key_request_key_select() {
        let mut request = v1::KeyRequest::new();
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
