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

use strum::FromRepr;

/// The size of a guest message, including the header and maximum payload size.
pub const GUEST_MESSAGE_SIZE: usize = 4096;

/// The currently supported header version number.
pub const CURRENT_HEADER_VERSION: u8 = 1;

/// The currently supported message version number.
pub const CURRENT_MESSAGE_VERSION: u8 = 1;

/// An encrypted guest message.
///
/// The same data structure is used for requests and responses.
///
/// See section 8.26 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C, align(4096))]
#[derive(Debug)]
pub struct GuestMessage {
    /// The message header.
    header: GuestMessageHeader,
    /// The encrypted payload.
    payload: [u8; 4000],
}

static_assertions::assert_eq_size!(GuestMessage, [u8; GUEST_MESSAGE_SIZE]);

/// The header for an encrypted guest request message.
///
/// See Table 97 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug)]
pub struct GuestMessageHeader {
    /// The authentication tag for the payload and additional data.
    auth_tag: [u8; 32],
    /// Reserved. Must be zero.
    _reserved_0: u64,
    /// The message sequence number. This is used as the IV for the AEAD.
    ///
    /// The same sequence number must never be reused with the same key.
    sequence_number: u64,
    /// The algorithm used to encrypt the payload.
    algorithm: AeadAlgorithm,
    /// The header version. Currently only version 1 is supported.
    header_version: u8,
    /// The size of the header in bytes.
    header_size: u16,
    /// The type of message that the payload represents.
    message_type: MessageType,
    /// The version of the message. Currently only version 1 is supported for all message types.
    message_version: u8,
    /// The size of the encrypted message payload in bytes.
    message_size: u16,
    /// Reserved. Must be zero.
    _reserved_1: u32,
    /// The ID of the VM communication key that was used to encrypt the payload.
    message_vmpck: u8,
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
