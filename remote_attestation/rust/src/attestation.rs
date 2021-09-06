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

// Remote attestation protocol handshake implementation.
//
// During the attestation protocol handshake participants send the following messages:
// - [`Client`] -> [`Server`]: [`AttestationInit`]
// - [`Server`] -> [`Client`]: [`ServerIdentity`]
// - [`Client`] -> [`Server`]: [`ClientIdentity`]
//
// After the protocol handshake both sides create [`AeadEncryptor`] for exchanging encrypted
// messages.

use crate::{
    crypto::{
        get_random, get_sha256, AeadEncryptor, KeyNegotiator, KeyNegotiatorType, SignatureVerifier,
        Signer,
    },
    proto::{AttestationInfo, AttestationInit, AttestationReport, ClientIdentity, ServerIdentity},
};
use anyhow::{anyhow, Context};

const ATTESTATION_PROTOCOL_VERSION: u8 = 1;
/// Size (in bytes) of a random array sent in messages to prevent replay attacks.
const REPLAY_PROTECTION_ARRAY_SIZE_BYTES: usize = 32;

/// Client of the Remote attestation protocol handshake.
pub struct ClientAttestationEngine<S>
where
    S: AttestationState,
{
    /// Behavior of the remote attestation protocol.
    behavior: AttestationBehavior,
    /// Current state of the remote attestation protocol.
    state: S,
    /// Collection of previously send and received messaged.
    /// Signed transcript is sent in messages to prevent replay attacks.
    transcript: Transcript,
}

/// Server of the Remote attestation protocol handshake.
pub struct ServerAttestationEngine<S>
where
    S: AttestationState,
{
    /// Behavior of the remote attestation protocol.
    behavior: AttestationBehavior,
    /// Current state of the remote attestation protocol.
    state: S,
    /// Collection of previously send and received messaged.
    /// Signed transcript is sent in messages to prevent replay attacks.
    transcript: Transcript,
}

impl ClientAttestationEngine<Initializing> {
    pub fn new(behavior: AttestationBehavior) -> Self {
        Self {
            behavior,
            state: Initializing::new(),
            transcript: Transcript::new(),
        }
    }

    /// Initializes the Remote Attestation handshake by creating an `AttestationInit` message.
    ///
    /// Transitions [`ClientAttestationEngine`] state from [`Initializing`] to [`Attesting`] state.
    pub fn attestation_init(
        mut self,
    ) -> anyhow::Result<(AttestationInit, ClientAttestationEngine<Attesting>)> {
        let attestation_init = AttestationInit {
            random: self.state.random.to_vec(),
        };

        // Update current transcript.
        self.transcript
            .append(&attestation_init)
            .context("Couldn't append attestation init to transcript")?;

        let key_negotiator = KeyNegotiator::create(KeyNegotiatorType::Client)
            .context("Couldn't create key negotiator")?;

        let next_state =
            Attesting::create(key_negotiator).context("Couldn't create attesting state")?;
        let attestation_engine = ClientAttestationEngine {
            behavior: self.behavior,
            state: next_state,
            transcript: self.transcript,
        };
        Ok((attestation_init, attestation_engine))
    }
}

impl ServerAttestationEngine<Initializing> {
    pub fn new(behavior: AttestationBehavior) -> Self {
        Self {
            behavior,
            state: Initializing::new(),
            transcript: Transcript::new(),
        }
    }

    /// Responds to `AttestationInit` message by creating a `ServerIdentity` message.
    ///
    /// `ServerIdentity` message contains an ephemeral public key for negotiating session keys.
    /// If self attestation is enabled this message also provides necessary information to perform
    /// remote attestation.
    ///
    /// Transitions [`ServerAttestationEngine`] state from [`Initializing`] to [`Attesting`] state.
    pub fn process_attestation_init(
        mut self,
        attestation_init: &AttestationInit,
    ) -> anyhow::Result<(ServerIdentity, ServerAttestationEngine<Attesting>)> {
        // Create server identity message.
        let key_negotiator = KeyNegotiator::create(KeyNegotiatorType::Server)
            .context("Couldn't create key negotiator")?;
        let ephemeral_public_key = key_negotiator
            .public_key()
            .context("Couldn't get ephemeral public key")?;
        let server_identity = if self.behavior.contains_self_attestation() {
            let signer = self
                .behavior
                .get_signer()
                .as_ref()
                .context("Couldn't get attestation signer")?;
            let tee_certificate = self
                .behavior
                .get_tee_certificate()
                .as_ref()
                .context("Couldn't get TEE certificate")?;

            let attestation_info = create_attestation_info(&signer, &tee_certificate)
                .context("Couldn't get attestation info")?;

            let mut server_identity = ServerIdentity {
                version: ATTESTATION_PROTOCOL_VERSION as i32,
                ephemeral_public_key,
                random: self.state.random.to_vec(),
                transcript_signature: vec![],
                signing_public_key: signer.public_key(),
                attestation_info: Some(attestation_info),
            };

            // Update current transcript.
            // Transcript doesn't include transcript signature from the server identity message.
            self.transcript
                .append(attestation_init)
                .context("Couldn't append attestation init to transcript")?;
            self.transcript
                .append(&server_identity)
                .context("Couldn't append server identity to transcript")?;

            // Add transcript signature to the server identity message.
            let transcript_signature = signer
                .sign(&self.transcript.get_sha256())
                .context("Couldn't create transcript signature")?;
            server_identity.transcript_signature = transcript_signature;
            server_identity
        } else {
            ServerIdentity {
                version: ATTESTATION_PROTOCOL_VERSION as i32,
                ephemeral_public_key,
                random: self.state.random.to_vec(),
                transcript_signature: vec![],
                signing_public_key: vec![],
                attestation_info: None,
            }
        };

        let next_state =
            Attesting::create(key_negotiator).context("Couldn't create attesting state")?;
        let attestation_engine = ServerAttestationEngine {
            behavior: self.behavior,
            state: next_state,
            transcript: self.transcript,
        };
        Ok((server_identity, attestation_engine))
    }
}

impl ClientAttestationEngine<Attesting> {
    /// Responds to `AttestationInit` message by creating a `ClientIdentity` message and derives
    /// session keys for encrypting/decrypting messages from the server.
    ///
    /// `ClientIdentity` message contains an ephemeral public key for negotiating session keys.
    /// If self attestation is enabled this message also provides necessary information to perform
    /// remote attestation.
    ///
    /// Transitions [`ClientAttestationEngine`] state from [`Attesting`] to [`Attested`] state.
    pub fn process_server_identity(
        mut self,
        server_identity: &ServerIdentity,
    ) -> anyhow::Result<(ClientIdentity, ClientAttestationEngine<Attested>)> {
        if self.behavior.contains_peer_attestation() {
            // Verify server transcript signature.
            // Transcript doesn't include transcript signature from the server identity message.
            let mut server_identity_no_signature = server_identity.clone();
            server_identity_no_signature.transcript_signature = vec![];
            self.transcript
                .append(&server_identity_no_signature)
                .context("Couldn't append server identity to transcript")?;
            let verifier = SignatureVerifier::new(&server_identity.signing_public_key);
            verifier
                .verify(
                    &self.transcript.get_sha256(),
                    &server_identity.transcript_signature,
                )
                .context("Couldn't verify server transcript")?;

            // Verify server attestation info.
            let server_attestation_info = &server_identity
                .attestation_info
                .as_ref()
                .context("Couldn't get server attestation info")?;
            let expected_tee_measurement = self
                .behavior
                .get_expected_tee_measurement()
                .as_ref()
                .context("Couldn't get expected TEE measurement")?;
            verify_attestation_info(&server_attestation_info, &expected_tee_measurement)
                .context("Couldn't verify server attestation info")?;
        }

        // Create client identity message.
        let ephemeral_public_key = self
            .state
            .key_negotiator
            .public_key()
            .context("Couldn't get ephemeral public key")?;
        let client_identity = if self.behavior.contains_self_attestation() {
            let signer = self
                .behavior
                .get_signer()
                .as_ref()
                .context("Couldn't access attestation signer")?;
            let tee_certificate = self
                .behavior
                .get_tee_certificate()
                .as_ref()
                .context("Couldn't access TEE certificate")?;

            let attestation_info = create_attestation_info(&signer, &tee_certificate)
                .context("Couldn't create attestation info")?;

            let mut client_identity = ClientIdentity {
                ephemeral_public_key,
                transcript_signature: vec![],
                signing_public_key: signer.public_key(),
                attestation_info: Some(attestation_info),
            };

            // Update current transcript.
            // Transcript doesn't include transcript signature from the client identity message.
            self.transcript
                .append(&client_identity)
                .context("Couldn't append client identity to transcript")?;

            // Add transcript signature to the client identity message.
            let transcript_signature = signer
                .sign(&self.transcript.get_sha256())
                .context("Couldn't create transcript signature")?;
            client_identity.transcript_signature = transcript_signature;
            client_identity
        } else {
            ClientIdentity {
                ephemeral_public_key,
                transcript_signature: vec![],
                signing_public_key: vec![],
                attestation_info: None,
            }
        };

        // Agree on session keys and create an encryptor.
        let next_state = Attested::create(
            self.state.key_negotiator,
            &server_identity.ephemeral_public_key,
        )
        .context("Couldn't create attested state")?;
        let attestation_engine = ClientAttestationEngine {
            behavior: self.behavior,
            state: next_state,
            transcript: self.transcript,
        };
        Ok((client_identity, attestation_engine))
    }
}

impl ServerAttestationEngine<Attesting> {
    /// Finishes the remote attestation protocol handshake and derives session keys for
    /// encrypting/decrypting messages from the client.
    ///
    /// Transitions [`ServerAttestationEngine`] state from [`Attesting`] to [`Attested`] state.
    pub fn process_client_identity(
        mut self,
        client_identity: &ClientIdentity,
    ) -> anyhow::Result<ServerAttestationEngine<Attested>> {
        if self.behavior.contains_peer_attestation() {
            // Verify client transcript signature.
            // Transcript doesn't include transcript signature from the client identity message.
            let mut client_identity_no_signature = client_identity.clone();
            client_identity_no_signature.transcript_signature = vec![];
            self.transcript
                .append(&client_identity_no_signature)
                .context("Couldn't append client identity to transcript")?;
            let verifier = SignatureVerifier::new(&client_identity.signing_public_key);
            verifier
                .verify(
                    &self.transcript.get_sha256(),
                    &client_identity.transcript_signature,
                )
                .context("Couldn't verify client transcript")?;

            // Verify client attestation info.
            let client_attestation_info = &client_identity
                .attestation_info
                .as_ref()
                .context("Couldn't get client attestation info")?;
            let expected_tee_measurement = self
                .behavior
                .get_expected_tee_measurement()
                .as_ref()
                .context("Couldn't get expected TEE measurement")?;
            verify_attestation_info(&client_attestation_info, &expected_tee_measurement)
                .context("Couldn't verify client attestation info")?;
        }

        // Agree on session keys and create an encryptor.
        let next_state = Attested::create(
            self.state.key_negotiator,
            &client_identity.ephemeral_public_key,
        )
        .context("Couldn't create attested state")?;
        let attestation_engine = ServerAttestationEngine {
            behavior: self.behavior,
            state: next_state,
            transcript: self.transcript,
        };
        Ok(attestation_engine)
    }
}

impl ClientAttestationEngine<Attested> {
    /// Returns an encryptor created based on the negotiated ephemeral keys.
    pub fn get_encryptor(self) -> AeadEncryptor {
        self.state.encryptor
    }
}

impl ServerAttestationEngine<Attested> {
    /// Returns an encryptor created based on the negotiated ephemeral keys.
    pub fn get_encryptor(self) -> AeadEncryptor {
        self.state.encryptor
    }
}

/// Defines the behavior of the remote attestation protocol.
/// It can be one of:
/// - Peer Attestation:
///   - Represents an attestation process, where current machine remotely attests a remote peer and
///     verifies its attestation info.
/// - Self Attestation:
///   - Represents an attestation process, where current machine remotely attests to a remote peer
///     and sends attestation info to it.
/// - Bidirectional Attestation:
///   - Represents an attestation process, where current machine and a remote peer remotely attest
///     each other.
pub struct AttestationBehavior {
    /// Expected value of the peer's TEE measurement.
    expected_tee_measurement: Option<Vec<u8>>,
    // /// Convenience struct for creating attestation info and signing data with TEE
    // /// firmware key.
    // tee_provider: Option<TeeProvider>,
    /// PEM encoded X.509 certificate that signs TEE firmware key.
    tee_certificate: Option<Vec<u8>>,
    /// Signer containing a key which public part is signed by the TEE firmware key.
    /// Used for signing protocol transcripts and preventing replay attacks.
    signer: Option<Signer>,
}

impl AttestationBehavior {
    /// Represents an attestation process, where current machine remotely attests a remote peer and
    /// verifies its attestation info.
    pub fn create_peer_attestation(expected_tee_measurement: &[u8]) -> anyhow::Result<Self> {
        Ok(Self {
            expected_tee_measurement: Some(expected_tee_measurement.to_vec()),
            tee_certificate: None,
            signer: None,
        })
    }

    /// Represents an attestation process, where current machine remotely attests to a remote peer
    /// and sends attestation info to it.
    pub fn create_self_attestation(tee_certificate: &[u8]) -> anyhow::Result<Self> {
        Ok(Self {
            expected_tee_measurement: None,
            tee_certificate: Some(tee_certificate.to_vec()),
            signer: Some(Signer::create().context("Couldn't create signer")?),
        })
    }

    /// Represents an attestation process, where current machine and a remote peer remotely attest
    /// each other.
    pub fn create_bidirectional_attestation(
        tee_certificate: &[u8],
        expected_tee_measurement: &[u8],
    ) -> anyhow::Result<Self> {
        Ok(Self {
            expected_tee_measurement: Some(expected_tee_measurement.to_vec()),
            tee_certificate: Some(tee_certificate.to_vec()),
            signer: Some(Signer::create().context("Couldn't create signer")?),
        })
    }

    pub fn contains_peer_attestation(&self) -> bool {
        self.expected_tee_measurement.is_some()
    }

    pub fn contains_self_attestation(&self) -> bool {
        self.tee_certificate.is_some() && self.signer.is_some()
    }

    pub fn get_expected_tee_measurement(&self) -> &Option<Vec<u8>> {
        &self.expected_tee_measurement
    }

    pub fn get_tee_certificate(&self) -> &Option<Vec<u8>> {
        &self.tee_certificate
    }

    pub fn get_signer(&self) -> &Option<Signer> {
        &self.signer
    }
}

pub trait AttestationState {}
impl AttestationState for Initializing {}
impl AttestationState for Attesting {}
impl AttestationState for Attested {}

/// Represents the starting state of the attestation handshake.
/// I.e. client is preparing to send `AttestationInit`.
pub struct Initializing {
    /// Random vector sent in messages for preventing replay attacks.
    random: Vec<u8>,
}

impl Initializing {
    pub fn new() -> Self {
        Self {
            random: get_random(REPLAY_PROTECTION_ARRAY_SIZE_BYTES),
        }
    }
}

impl Default for Initializing {
    fn default() -> Self {
        Self::new()
    }
}

/// Represents an ongoing state of the attestation handshake.
/// I.e. client has sent `AttestationInit` and server has sent `ServerIdentity`.
pub struct Attesting {
    /// Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
    key_negotiator: KeyNegotiator,
}

impl Attesting {
    pub fn create(key_negotiator: KeyNegotiator) -> anyhow::Result<Self> {
        Ok(Self { key_negotiator })
    }
}

/// Represents a finished state of the attestation handshake.
/// I.e. client has sent `ClientIdentity` and both Client and Server agreed on
/// session keys.
pub struct Attested {
    /// Encryptor that was created during the attestation handshake.
    encryptor: AeadEncryptor,
}

impl Attested {
    pub fn create(
        key_negotiator: KeyNegotiator,
        peer_ephemeral_public_key: &[u8],
    ) -> anyhow::Result<Self> {
        let encryptor = key_negotiator
            .create_encryptor(peer_ephemeral_public_key)
            .context("Couldn't derive session key")?;
        Ok(Self { encryptor })
    }
}

/// Convenience struct for managing protocol transcripts.
/// Transcript is a concatenation of all sent and received messages, which is used for preventing
/// replay attacks.
struct Transcript {
    value: Vec<u8>,
}

impl Transcript {
    pub fn new() -> Self {
        Self { value: vec![] }
    }

    /// Append `message` to the and of [`Transcript::value`].
    pub fn append<M: prost::Message>(&mut self, message: &M) -> anyhow::Result<()> {
        let bytes = serialize_protobuf(message).context("Couldn't serialize message")?;
        self.value.extend(bytes);
        Ok(())
    }

    /// Get SHA-256 hash of the [`Transcript::value`].
    pub fn get_sha256(&self) -> Vec<u8> {
        get_sha256(&self.value)
    }
}

/// Generate attestation info with a TEE report.
/// TEE report contains a hash of the signer's public key.
pub fn create_attestation_info(
    signer: &Signer,
    tee_certificate: &[u8],
) -> anyhow::Result<AttestationInfo> {
    let signing_public_key = signer.public_key();
    let signing_public_key_hash = get_sha256(signing_public_key.as_ref());
    let report = AttestationReport::new(&signing_public_key_hash);
    Ok(AttestationInfo {
        report: Some(report),
        certificate: tee_certificate.to_vec(),
    })
}

/// Verifies the validity of the attestation info:
/// - Checks that the TEE report is signed by TEE Provider’s root key.
/// - Checks that the public key hash from the TEE report is equal to the hash of the public key
///   presented in the server response.
/// - Extracts the TEE measurement from the TEE report and compares it to the
///   `expected_tee_measurement`.
fn verify_attestation_info(
    peer_attestation_info: &AttestationInfo,
    expected_tee_measurement: &[u8],
) -> anyhow::Result<()> {
    // TODO(#1867): Add remote attestation support, use real TEE reports and check that
    // `AttestationInfo::certificate` is signed by one of the root certificates.

    // Verify peer TEE measurement.
    let peer_report = peer_attestation_info
        .report
        .as_ref()
        .context("Couldn't find report in peer attestation info")?;
    if expected_tee_measurement == peer_report.measurement {
        Ok(())
    } else {
        Err(anyhow!("Incorrect TEE measurement"))
    }
}

// TODO(#2273): Use raw bytes for messages since Protobuf is not deterministic.
pub fn serialize_protobuf<M: prost::Message>(message: &M) -> anyhow::Result<Vec<u8>> {
    let mut message_bytes = Vec::new();
    message
        .encode(&mut message_bytes)
        .context("Couldn't serialize Protobuf message to bytes")?;
    Ok(message_bytes)
}
