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

use crate::crypto::{
    KEY_AGREEMENT_ALGORITHM_KEY_LENGTH, NONCE_LENGTH, SIGNATURE_LENGTH,
    SIGNING_ALGORITHM_KEY_LENGTH,
};
use anyhow::{anyhow, Context};
use bincode;
use serde::{Deserialize, Serialize};
use serde_big_array::BigArray;

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

impl std::fmt::Debug for MessageWrapper {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
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
// TODO(#2294): Remove `bincode` and use manual message serialization.
/// Initial message that starts remote attestation handshake.
#[derive(Serialize, Deserialize, Clone, PartialEq)]
pub struct ClientHello {
    /// Message header.
    header: u8,
    /// Random vector sent in messages for preventing replay attacks.
    pub random: [u8; REPLAY_PROTECTION_ARRAY_LENGTH],
}

/// Server identity message containing remote attestation information and a public key for
/// Diffie-Hellman key negotiation.
#[derive(Serialize, Deserialize, Clone, PartialEq)]
pub struct ServerIdentity {
    /// Message header.
    header: u8,
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
    /// https://datatracker.ietf.org/doc/html/rfc6979
    /// https://standards.ieee.org/standard/1363-2000.html
    #[serde(with = "BigArray")]
    pub transcript_signature: [u8; SIGNATURE_LENGTH],
    /// Public key used to sign transcripts.
    ///
    /// Public key must be an OpenSSL ECDSA-P256 key, which is represented as
    /// `0x04 | X: 32-byte | Y: 32-byte`.
    /// Where X and Y are big-endian coordinates of an Elliptic Curve point.
    /// https://datatracker.ietf.org/doc/html/rfc6979
    #[serde(with = "BigArray")]
    pub signing_public_key: [u8; SIGNING_ALGORITHM_KEY_LENGTH],
    /// Information used for remote attestation such as a TEE report and a TEE provider's
    /// certificate. TEE report contains a hash of the `signing_public_key` and `additional_info`.
    ///
    /// Attestation info must be a serialized `oak.remote_attestation.AttestationInfo` Protobuf
    /// message.
    pub attestation_info: Vec<u8>,
    /// Additional info to be checked when verifying the identity. This may include server
    /// configuration details, and inclusion proofs on a verifiable log (e.g., LogEntry on Rekor).
    /// The server and the client must be able to agree on a canonical representation of the
    /// content to be able to deterministically compute the hash of this field.
    pub additional_info: Vec<u8>,
}

/// Client identity message containing remote attestation information and a public key for
/// Diffie-Hellman key negotiation.
#[derive(Serialize, Deserialize, Clone, PartialEq)]
pub struct ClientIdentity {
    /// Message header.
    header: u8,
    /// Public key needed to establish a session key.
    pub ephemeral_public_key: [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
    /// Signature of the SHA-256 hash of all previously sent and received messages.
    /// Transcript signature is sent in messages to prevent replay attacks.
    ///
    /// Signature must be an IEEE-P1363 encoded ECDSA-P256 signature.
    /// https://datatracker.ietf.org/doc/html/rfc6979
    /// https://standards.ieee.org/standard/1363-2000.html
    #[serde(with = "BigArray")]
    pub transcript_signature: [u8; SIGNATURE_LENGTH],
    /// Public key used to sign transcripts.
    ///
    /// Public key must be an OpenSSL ECDSA-P256 key, which is represented as
    /// `0x04 | X: 32-byte | Y: 32-byte`.
    /// Where X and Y are big-endian coordinates of an Elliptic Curve point.
    /// https://datatracker.ietf.org/doc/html/rfc6979
    #[serde(with = "BigArray")]
    pub signing_public_key: [u8; SIGNING_ALGORITHM_KEY_LENGTH],
    /// Information used for remote attestation such as a TEE report and a TEE provider's
    /// certificate. TEE report contains a hash of the `signing_public_key`.
    ///
    /// Attestation info must be a serialized `oak.remote_attestation.AttestationInfo` Protobuf
    /// message.
    pub attestation_info: Vec<u8>,
}

/// Message containing data encrypted using a session key.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct EncryptedData {
    /// Message header.
    header: u8,
    /// Random nonce (initialization vector) used for encryption/decryption.
    #[serde(with = "BigArray")]
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
        Self {
            header: CLIENT_HELLO_HEADER,
            random,
        }
    }
}

impl Serializable for ClientHello {
    fn serialize(&self) -> anyhow::Result<Vec<u8>> {
        bincode::serialize(&self).context("Couldn't serialize client hello message")
    }
}

impl Deserializable for ClientHello {
    fn deserialize(input: &[u8]) -> anyhow::Result<Self> {
        if input.len() <= MAXIMUM_MESSAGE_SIZE {
            let message: Self =
                bincode::deserialize(input).context("Couldn't deserialize client hello message")?;
            if message.header == CLIENT_HELLO_HEADER {
                Ok(message)
            } else {
                Err(anyhow!("Incorrect client hello message header"))
            }
        } else {
            Err(anyhow!(
                "Maximum handshake message size of {} exceeded, found {}",
                MAXIMUM_MESSAGE_SIZE,
                input.len(),
            ))
        }
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
            header: SERVER_IDENTITY_HEADER,
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
}

impl Serializable for ServerIdentity {
    fn serialize(&self) -> anyhow::Result<Vec<u8>> {
        bincode::serialize(&self).context("Couldn't serialize server identity message")
    }
}

impl Deserializable for ServerIdentity {
    fn deserialize(input: &[u8]) -> anyhow::Result<Self> {
        if input.len() <= MAXIMUM_MESSAGE_SIZE {
            let message: Self = bincode::deserialize(input)
                .context("Couldn't deserialize server identity message")?;
            if message.header != SERVER_IDENTITY_HEADER {
                return Err(anyhow!("Incorrect server identity message header"));
            }
            if message.version != PROTOCOL_VERSION {
                return Err(anyhow!("Incorrect remote attestation protocol version"));
            }
            Ok(message)
        } else {
            Err(anyhow!(
                "Maximum handshake message size of {} exceeded, found {}",
                MAXIMUM_MESSAGE_SIZE,
                input.len(),
            ))
        }
    }
}

impl ClientIdentity {
    pub fn new(
        ephemeral_public_key: [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
        signing_public_key: [u8; SIGNING_ALGORITHM_KEY_LENGTH],
        attestation_info: Vec<u8>,
    ) -> Self {
        Self {
            header: CLIENT_IDENTITY_HEADER,
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
}

impl Serializable for ClientIdentity {
    fn serialize(&self) -> anyhow::Result<Vec<u8>> {
        bincode::serialize(&self).context("Couldn't serialize client identity message")
    }
}

impl Deserializable for ClientIdentity {
    fn deserialize(input: &[u8]) -> anyhow::Result<Self> {
        if input.len() <= MAXIMUM_MESSAGE_SIZE {
            let message: Self = bincode::deserialize(input)
                .context("Couldn't deserialize client identity message")?;
            if message.header == CLIENT_IDENTITY_HEADER {
                Ok(message)
            } else {
                Err(anyhow!("Incorrect client identity message header"))
            }
        } else {
            Err(anyhow!(
                "Maximum handshake message size of {} exceeded, found {}",
                MAXIMUM_MESSAGE_SIZE,
                input.len(),
            ))
        }
    }
}

impl EncryptedData {
    pub fn new(nonce: [u8; NONCE_LENGTH], data: Vec<u8>) -> Self {
        Self {
            header: ENCRYPTED_DATA_HEADER,
            nonce,
            data,
        }
    }
}

impl Serializable for EncryptedData {
    fn serialize(&self) -> anyhow::Result<Vec<u8>> {
        bincode::serialize(&self).context("Couldn't serialize encrypted data message")
    }
}

impl Deserializable for EncryptedData {
    fn deserialize(bytes: &[u8]) -> anyhow::Result<Self> {
        let message: Self =
            bincode::deserialize(bytes).context("Couldn't deserialize encrypted data message")?;
        if message.header == ENCRYPTED_DATA_HEADER {
            Ok(message)
        } else {
            Err(anyhow!("Incorrect encrypted data message header"))
        }
    }
}

/// Deserializes an attestation message from a serialized [`input`] and wraps in a
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
