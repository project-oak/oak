//
// Copyright 2021 The Project Oak Authors
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

// Messages that implement a simplified version of the Enclave Key Exchange
// Protocol (EKEP).
//
// Unlike other messages exchanged between client & server, these are expressed
// as Rust structs and serialized with custom logic. This is done to maintain
// binary-compatibility with other implementations of this protocol.

use crate::crypto::{
    KEY_AGREEMENT_ALGORITHM_KEY_LENGTH, NONCE_LENGTH, SIGNATURE_LENGTH,
    SIGNING_ALGORITHM_KEY_LENGTH,
};
use alloc::vec::Vec;
use anyhow::{anyhow, bail, Context};
use bytes::{Buf, BufMut};

/// Maximum handshake message size is set to be equal to 1KiB.
pub const MAXIMUM_MESSAGE_SIZE: usize = 1_024;

// Message header values.
pub(crate) const CLIENT_HELLO_HEADER: u8 = 1;
pub(crate) const SERVER_IDENTITY_HEADER: u8 = 2;
pub(crate) const CLIENT_IDENTITY_HEADER: u8 = 3;
pub(crate) const ENCRYPTED_DATA_HEADER: u8 = 4;

/// Remote attestation protocol version.
pub const PROTOCOL_VERSION: u8 = 1;

/// Length (in bytes) of the random vector sent in messages for preventing replay attacks.
pub const REPLAY_PROTECTION_ARRAY_LENGTH: usize = 32;

/// Length (in bytes) of a message header.
pub const MESSAGE_HEADER_LENGTH: usize = 1;

/// Length (in bytes) of the protocol version.
pub const PROTOCOL_VERSION_LENGTH: usize = 1;

/// Length (in bytes) of the prefix that is used for Little-Endian encoding of the size of a vector
/// during serailization.
pub const VEC_SIZE_PREFIX_LENGTH: usize = 8;

// TODO(#2295): Add Frame struct to remote attestation messages.
/// Convenience struct that wraps attestation messages.
#[allow(clippy::large_enum_variant)]
#[derive(PartialEq)]
pub enum MessageWrapper {
    ClientHello(ClientHello),
    ServerIdentity(ServerIdentity),
    ClientIdentity(ClientIdentity),
    EncryptedData(EncryptedData),
}

impl core::fmt::Debug for MessageWrapper {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Self::ClientHello(_) => write!(f, "ClientHello"),
            Self::ServerIdentity(_) => write!(f, "ServerIdentity"),
            Self::ClientIdentity(_) => write!(f, "ClientIdentity"),
            Self::EncryptedData(_) => write!(f, "EncryptedData"),
        }
    }
}

// TODO(#2105): Implement challenge-response in remote attestation.
// TODO(#2106): Support various claims in remote attestation.
/// Initial message that starts remote attestation handshake.
#[derive(Clone, PartialEq)]
pub struct ClientHello {
    /// Random vector sent in messages for preventing replay attacks.
    pub random: [u8; REPLAY_PROTECTION_ARRAY_LENGTH],
}

/// Server identity message containing remote attestation information and a public key for
/// Diffie-Hellman key negotiation.
#[derive(Clone, PartialEq)]
pub struct ServerIdentity {
    /// Remote attestation protocol version.
    pub version: u8,
    /// Public key needed to establish a session key.
    pub ephemeral_public_key: [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
    /// Random vector sent in messages for preventing replay attacks.
    pub random: [u8; REPLAY_PROTECTION_ARRAY_LENGTH],
    /// Signature of the SHA-256 hash of all previously sent and received messages.
    /// Transcript signature is sent in messages to prevent replay attacks.
    ///
    /// Signature must be an IEEE-P1363 encoded ECDSA-P256 signature.
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc6979>
    ///
    /// <https://standards.ieee.org/standard/1363-2000.html>
    pub transcript_signature: [u8; SIGNATURE_LENGTH],
    /// Public key used to sign transcripts.
    ///
    /// Public key must be an OpenSSL ECDSA-P256 key, which is represented as
    /// `0x04 | X: 32-byte | Y: 32-byte`.
    ///
    /// Where X and Y are big-endian coordinates of an Elliptic Curve point.
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc6979>
    pub signing_public_key: [u8; SIGNING_ALGORITHM_KEY_LENGTH],
    /// Information used for remote attestation such as a TEE report and a TEE provider's
    /// certificate. TEE report contains a hash of the `signing_public_key` and `additional_info`.
    ///
    /// Attestation info must be a serialized `oak.remote_attestation.AttestationInfo` Protobuf
    /// message.
    pub attestation_info: Vec<u8>,
    /// Additional info to be checked when verifying the identity. This may include server
    /// configuration details, and inclusion proofs on a verifiable log (e.g., LogEntry on Rekor).
    ///
    /// The server and the client must be able to agree on a canonical representation of the
    /// content to be able to deterministically compute the hash of this field.
    pub additional_info: Vec<u8>,
}

/// Client identity message containing remote attestation information and a public key for
/// Diffie-Hellman key negotiation.
#[derive(Clone, PartialEq)]
pub struct ClientIdentity {
    /// Public key needed to establish a session key.
    pub ephemeral_public_key: [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
    /// Signature of the SHA-256 hash of all previously sent and received messages.
    /// Transcript signature is sent in messages to prevent replay attacks.
    ///
    /// Signature must be an IEEE-P1363 encoded ECDSA-P256 signature.
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc6979>
    ///
    /// <https://standards.ieee.org/standard/1363-2000.html>
    pub transcript_signature: [u8; SIGNATURE_LENGTH],
    /// Public key used to sign transcripts.
    ///
    /// Public key must be an OpenSSL ECDSA-P256 key, which is represented as
    /// `0x04 | X: 32-byte | Y: 32-byte`.
    ///
    /// Where X and Y are big-endian coordinates of an Elliptic Curve point.
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc6979>
    pub signing_public_key: [u8; SIGNING_ALGORITHM_KEY_LENGTH],
    /// Information used for remote attestation such as a TEE report and a TEE provider's
    /// certificate. TEE report contains a hash of the `signing_public_key`.
    ///
    /// Attestation info must be a serialized `oak.remote_attestation.AttestationInfo` Protobuf
    /// message.
    pub attestation_info: Vec<u8>,
}

/// Message containing data encrypted using a session key.
#[derive(Clone, Debug, PartialEq)]
pub struct EncryptedData {
    /// Random nonce (initialization vector) used for encryption/decryption.
    pub nonce: [u8; NONCE_LENGTH],
    /// Data encrypted using the session key.
    pub data: Vec<u8>,
}

pub trait Serializable {
    fn serialize(&self) -> anyhow::Result<Vec<u8>>;
}

pub trait Deserializable {
    fn deserialize(bytes: &[u8]) -> anyhow::Result<Self>
    where
        Self: Sized;
}

impl ClientHello {
    pub fn new(random: [u8; REPLAY_PROTECTION_ARRAY_LENGTH]) -> Self {
        Self { random }
    }

    const fn len() -> usize {
        MESSAGE_HEADER_LENGTH + REPLAY_PROTECTION_ARRAY_LENGTH
    }
}

impl Serializable for ClientHello {
    fn serialize(&self) -> anyhow::Result<Vec<u8>> {
        let mut result = Vec::with_capacity(ClientHello::len());
        result.put_u8(CLIENT_HELLO_HEADER);
        result.put_slice(&self.random);
        Ok(result)
    }
}

impl Deserializable for ClientHello {
    fn deserialize(input: &[u8]) -> anyhow::Result<Self> {
        if input.len() != ClientHello::len() {
            bail!(
                "Invalid client hello message length: expected {}, found {}",
                ClientHello::len(),
                input.len(),
            );
        }
        let mut input = input;
        if input.get_u8() != CLIENT_HELLO_HEADER {
            bail!("Invalid client hello message header");
        }
        let mut random = [0u8; REPLAY_PROTECTION_ARRAY_LENGTH];
        input.copy_to_slice(&mut random);
        Ok(Self { random })
    }
}

impl ServerIdentity {
    pub fn new(
        ephemeral_public_key: [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
        random: [u8; REPLAY_PROTECTION_ARRAY_LENGTH],
        signing_public_key: [u8; SIGNING_ALGORITHM_KEY_LENGTH],
        attestation_info: Vec<u8>,
        additional_info: Vec<u8>,
    ) -> Self {
        Self {
            version: PROTOCOL_VERSION,
            ephemeral_public_key,
            random,
            transcript_signature: [Default::default(); SIGNATURE_LENGTH],
            signing_public_key,
            attestation_info,
            additional_info,
        }
    }

    pub fn clear_transcript_signature(&mut self) {
        self.transcript_signature = [Default::default(); SIGNATURE_LENGTH];
    }

    pub fn set_transcript_signature(&mut self, transcript_signature: &[u8; SIGNATURE_LENGTH]) {
        self.transcript_signature = *transcript_signature;
    }

    const fn min_len() -> usize {
        MESSAGE_HEADER_LENGTH
            + PROTOCOL_VERSION_LENGTH
            + KEY_AGREEMENT_ALGORITHM_KEY_LENGTH
            + REPLAY_PROTECTION_ARRAY_LENGTH
            + SIGNATURE_LENGTH
            + SIGNING_ALGORITHM_KEY_LENGTH
            + 2 * VEC_SIZE_PREFIX_LENGTH
    }
}

impl Serializable for ServerIdentity {
    fn serialize(&self) -> anyhow::Result<Vec<u8>> {
        let mut result = Vec::with_capacity(
            ServerIdentity::min_len() + self.attestation_info.len() + self.additional_info.len(),
        );
        result.put_u8(SERVER_IDENTITY_HEADER);
        result.put_u8(self.version);
        result.put_slice(&self.ephemeral_public_key);
        result.put_slice(&self.random);
        result.put_slice(&self.transcript_signature);
        result.put_slice(&self.signing_public_key);
        put_vec(&mut result, &self.attestation_info);
        put_vec(&mut result, &self.additional_info);
        Ok(result)
    }
}

impl Deserializable for ServerIdentity {
    fn deserialize(input: &[u8]) -> anyhow::Result<Self> {
        if input.len() < ServerIdentity::min_len() {
            bail!(
                "Server identity message too short: expected at least {} bytes, found {}",
                ServerIdentity::min_len(),
                input.len(),
            );
        }
        if input.len() > MAXIMUM_MESSAGE_SIZE {
            bail!(
                "Maximum handshake message size of {} exceeded, found {}",
                MAXIMUM_MESSAGE_SIZE,
                input.len(),
            );
        }
        let mut input = input;
        if input.get_u8() != SERVER_IDENTITY_HEADER {
            bail!("Invalid server identity message header");
        }

        let version = input.get_u8();
        let mut ephemeral_public_key = [0u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH];
        input.copy_to_slice(&mut ephemeral_public_key);
        let mut random = [0u8; REPLAY_PROTECTION_ARRAY_LENGTH];
        input.copy_to_slice(&mut random);
        let mut transcript_signature = [0u8; SIGNATURE_LENGTH];
        input.copy_to_slice(&mut transcript_signature);
        let mut signing_public_key = [0u8; SIGNING_ALGORITHM_KEY_LENGTH];
        input.copy_to_slice(&mut signing_public_key);
        let attestation_info = get_vec(&mut input)?;
        let additional_info = get_vec(&mut input)?;

        if input.has_remaining() {
            bail!(
                "Invalid server identity message: {} unused bytes detected",
                input.remaining()
            );
        }

        Ok(Self {
            version,
            ephemeral_public_key,
            random,
            transcript_signature,
            signing_public_key,
            attestation_info,
            additional_info,
        })
    }
}

impl ClientIdentity {
    pub fn new(
        ephemeral_public_key: [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
        signing_public_key: [u8; SIGNING_ALGORITHM_KEY_LENGTH],
        attestation_info: Vec<u8>,
    ) -> Self {
        Self {
            ephemeral_public_key,
            transcript_signature: [Default::default(); SIGNATURE_LENGTH],
            signing_public_key,
            attestation_info,
        }
    }

    pub fn clear_transcript_signature(&mut self) {
        self.transcript_signature = [Default::default(); SIGNATURE_LENGTH];
    }

    pub fn set_transcript_signature(&mut self, transcript_signature: &[u8; SIGNATURE_LENGTH]) {
        self.transcript_signature = *transcript_signature;
    }

    const fn min_len() -> usize {
        MESSAGE_HEADER_LENGTH
            + KEY_AGREEMENT_ALGORITHM_KEY_LENGTH
            + SIGNATURE_LENGTH
            + SIGNING_ALGORITHM_KEY_LENGTH
            + VEC_SIZE_PREFIX_LENGTH
    }
}

impl Serializable for ClientIdentity {
    fn serialize(&self) -> anyhow::Result<Vec<u8>> {
        let mut result =
            Vec::with_capacity(ClientIdentity::min_len() + self.attestation_info.len());
        result.put_u8(CLIENT_IDENTITY_HEADER);
        result.put_slice(&self.ephemeral_public_key);
        result.put_slice(&self.transcript_signature);
        result.put_slice(&self.signing_public_key);
        put_vec(&mut result, &self.attestation_info);
        Ok(result)
    }
}

impl Deserializable for ClientIdentity {
    fn deserialize(input: &[u8]) -> anyhow::Result<Self> {
        if input.len() < ClientIdentity::min_len() {
            bail!(
                "Client identity message too short: expected at least {} bytes, found {}",
                ClientIdentity::min_len(),
                input.len(),
            );
        }
        if input.len() > MAXIMUM_MESSAGE_SIZE {
            bail!(
                "Maximum handshake message size of {} exceeded, found {}",
                MAXIMUM_MESSAGE_SIZE,
                input.len(),
            );
        }
        let mut input = input;
        if input.get_u8() != CLIENT_IDENTITY_HEADER {
            bail!("Invalid client identity message header");
        }

        let mut ephemeral_public_key = [0u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH];
        input.copy_to_slice(&mut ephemeral_public_key);
        let mut transcript_signature = [0u8; SIGNATURE_LENGTH];
        input.copy_to_slice(&mut transcript_signature);
        let mut signing_public_key = [0u8; SIGNING_ALGORITHM_KEY_LENGTH];
        input.copy_to_slice(&mut signing_public_key);
        let attestation_info = get_vec(&mut input)?;

        if input.has_remaining() {
            bail!(
                "Invalid client identity message: {} unused bytes detected",
                input.remaining()
            );
        }

        Ok(Self {
            ephemeral_public_key,
            transcript_signature,
            signing_public_key,
            attestation_info,
        })
    }
}

impl EncryptedData {
    pub fn new(nonce: [u8; NONCE_LENGTH], data: Vec<u8>) -> Self {
        Self { nonce, data }
    }

    const fn min_len() -> usize {
        MESSAGE_HEADER_LENGTH + NONCE_LENGTH + VEC_SIZE_PREFIX_LENGTH
    }
}

impl Serializable for EncryptedData {
    fn serialize(&self) -> anyhow::Result<Vec<u8>> {
        let mut result = Vec::with_capacity(EncryptedData::min_len() + self.data.len());
        result.put_u8(ENCRYPTED_DATA_HEADER);
        result.put_slice(&self.nonce);
        put_vec(&mut result, &self.data);
        Ok(result)
    }
}

impl Deserializable for EncryptedData {
    fn deserialize(input: &[u8]) -> anyhow::Result<Self> {
        if input.len() < EncryptedData::min_len() {
            bail!(
                "Encrypted data message too short: expected at least {} bytes, found {}",
                EncryptedData::min_len(),
                input.len(),
            );
        }
        let mut input = input;
        if input.get_u8() != ENCRYPTED_DATA_HEADER {
            bail!("Invalid encrypted data message header");
        }

        let mut nonce = [0u8; NONCE_LENGTH];
        input.copy_to_slice(&mut nonce);
        let data = get_vec(&mut input)?;

        if input.has_remaining() {
            bail!(
                "Invalid encrypted data message: {} unused bytes detected",
                input.remaining()
            );
        }

        Ok(Self { nonce, data })
    }
}

/// Deserializes an attestation message from a serialized `input` and wraps in a
/// [`MessageWrapper`].
pub fn deserialize_message(input: &[u8]) -> anyhow::Result<MessageWrapper> {
    if input.is_empty() {
        return Err(anyhow!("Empty input"));
    }
    match input[0] {
        CLIENT_HELLO_HEADER => {
            let message: ClientHello = Deserializable::deserialize(input)
                .context("Couldn't deserialize client hello message")?;
            Ok(MessageWrapper::ClientHello(message))
        }
        SERVER_IDENTITY_HEADER => {
            let message: ServerIdentity = Deserializable::deserialize(input)
                .context("Couldn't deserialize server identity message")?;
            Ok(MessageWrapper::ServerIdentity(message))
        }
        CLIENT_IDENTITY_HEADER => {
            let message: ClientIdentity = Deserializable::deserialize(input)
                .context("Couldn't deserialize client identity message")?;
            Ok(MessageWrapper::ClientIdentity(message))
        }
        ENCRYPTED_DATA_HEADER => {
            let message: EncryptedData = Deserializable::deserialize(input)
                .context("Couldn't deserialize encrypted data message")?;
            Ok(MessageWrapper::EncryptedData(message))
        }
        header => Err(anyhow!("Unknown message header: {:#02x}", header)),
    }
}

fn put_vec(target: &mut Vec<u8>, source: &[u8]) {
    target.put_u64_le(source.len() as u64);
    target.put_slice(source);
}

fn get_vec(source: &mut &[u8]) -> anyhow::Result<Vec<u8>> {
    let length = source.get_u64_le();
    if length > source.remaining() as u64 {
        bail!(
            "Invalid vector serialization: required length is {} but only {} bytes provided",
            length,
            source.remaining()
        )
    }
    Ok(source.copy_to_bytes(length as usize).to_vec())
}
