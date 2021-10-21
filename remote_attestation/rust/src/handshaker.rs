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
// - [`Client`] -> [`Server`]: [`ClientHello`]
// - [`Server`] -> [`Client`]: [`ServerIdentity`]
// - [`Client`] -> [`Server`]: [`ClientIdentity`]
//
// After the protocol handshake both sides create [`Encryptor`] for exchanging encrypted messages.

use crate::{
    crypto::{
        get_random, get_sha256, AeadEncryptor, KeyNegotiator, KeyNegotiatorType, SignatureVerifier,
        Signer, SHA256_HASH_LENGTH, SIGNING_ALGORITHM_KEY_LENGTH,
    },
    message::{
        deserialize_message, ClientHello, ClientIdentity, MessageWrapper, Serializable,
        ServerIdentity,
    },
    proto::{AttestationInfo, AttestationReport},
};
use anyhow::{anyhow, Context};
use prost::Message;

pub type ServerIdentityVerifier = Box<dyn Fn(ServerIdentity) -> anyhow::Result<()>>;

enum ClientHandshakerState {
    Initializing,
    ExpectingServerIdentity(KeyNegotiator),
    Completed(AeadEncryptor),
    Aborted,
    /// Additional state that represents ongoing message processing.
    MessageProcessing,
}

impl Default for ClientHandshakerState {
    fn default() -> Self {
        Self::MessageProcessing
    }
}

impl std::fmt::Debug for ClientHandshakerState {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Initializing => write!(f, "Initializing"),
            Self::ExpectingServerIdentity(_) => write!(f, "ExpectingServerIdentity"),
            Self::Completed(_) => write!(f, "Completed"),
            Self::Aborted => write!(f, "Aborted"),
            Self::MessageProcessing => write!(f, "MessageProcessing"),
        }
    }
}

enum ServerHandshakerState {
    ExpectingClientHello,
    ExpectingClientIdentity(KeyNegotiator),
    Completed(AeadEncryptor),
    Aborted,
    /// Additional state that represents ongoing message processing.
    MessageProcessing,
}

impl Default for ServerHandshakerState {
    fn default() -> Self {
        Self::MessageProcessing
    }
}

impl std::fmt::Debug for ServerHandshakerState {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::ExpectingClientHello => write!(f, "ExpectingClientHello"),
            Self::ExpectingClientIdentity(_) => write!(f, "ExpectingClientIdentity"),
            Self::Completed(_) => write!(f, "Completed"),
            Self::Aborted => write!(f, "Aborted"),
            Self::MessageProcessing => write!(f, "MessageProcessing"),
        }
    }
}

/// Client of the remote attestation protocol handshake.
pub struct ClientHandshaker {
    /// Behavior of the remote attestation protocol.
    behavior: AttestationBehavior,
    /// Current state of the remote attestation protocol handshake.
    state: ClientHandshakerState,
    /// Collection of previously sent and received messages.
    /// Signed transcript is sent in messages to prevent replay attacks.
    transcript: Transcript,
    /// Function for verifying the identity of the server.
    server_verifier: ServerIdentityVerifier,
}

impl ClientHandshaker {
    /// Creates [`ClientHandshaker`] with [`HandshakerState::Initializing`] state.
    pub fn new(behavior: AttestationBehavior, server_verifier: ServerIdentityVerifier) -> Self {
        Self {
            behavior,
            state: ClientHandshakerState::Initializing,
            transcript: Transcript::new(),
            server_verifier,
        }
    }

    /// Processes incoming `message` and returns a serialized remote attestation message.
    /// If [`None`] is returned, then no messages should be sent out to the server.
    pub fn next_step(&mut self, message: &[u8]) -> anyhow::Result<Option<Vec<u8>>> {
        self.next_step_util(message).map_err(|error| {
            self.state = ClientHandshakerState::Aborted;
            error
        })
    }

    fn next_step_util(&mut self, message: &[u8]) -> anyhow::Result<Option<Vec<u8>>> {
        let deserialized_message =
            deserialize_message(message).context("Couldn't deserialize message")?;
        match deserialized_message {
            MessageWrapper::ServerIdentity(server_identity) => {
                match std::mem::take(&mut self.state) {
                    ClientHandshakerState::ExpectingServerIdentity(key_negotiator) => {
                        let client_identity = self
                            .process_server_identity(server_identity, key_negotiator)
                            .context("Couldn't process server identity message")?;
                        let serialized_client_identity = client_identity
                            .serialize()
                            .context("Couldn't serialize client identity message")?;
                        Ok(Some(serialized_client_identity))
                    }
                    ClientHandshakerState::Aborted => {
                        Err(anyhow!("Remote attestation handshake is aborted",))
                    }
                    ClientHandshakerState::MessageProcessing => Err(anyhow!(
                        "Cannot process new messages while in the MessageProcessing state",
                    )),
                    _ => Err(anyhow!(
                        "Incorrect handshake message received, in state {:?}, found ServerIdentity",
                        self.state
                    )),
                }
            }
            unsupported_message => Err(anyhow!(
                "Receiving {:?} is not supported by the client handshaker",
                unsupported_message
            )),
        }
    }

    pub fn is_completed(&self) -> bool {
        matches!(self.state, ClientHandshakerState::Completed(_))
    }

    pub fn is_aborted(&self) -> bool {
        matches!(self.state, ClientHandshakerState::Aborted)
    }

    pub fn get_encryptor(self) -> anyhow::Result<Encryptor> {
        match self.state {
            ClientHandshakerState::Completed(encryptor) => Ok(Encryptor { encryptor }),
            _ => Err(anyhow!("Handshake is not complete")),
        }
    }

    /// Initializes the remote attestation handshake by creating a serialized [`ClientHello`]
    /// message.
    ///
    /// Transitions [`ClientHandshaker`] state from [`HandshakerState::Initializing`] to
    /// [`HandshakerState::ExpectingServerIdentity`] state.
    pub fn create_client_hello(&mut self) -> anyhow::Result<Vec<u8>> {
        self.create_client_hello_util().map_err(|error| {
            self.state = ClientHandshakerState::Aborted;
            error
        })
    }

    fn create_client_hello_util(&mut self) -> anyhow::Result<Vec<u8>> {
        match self.state {
            ClientHandshakerState::Initializing => {
                let key_negotiator = KeyNegotiator::create(KeyNegotiatorType::Client)
                    .context("Couldn't create key negotiator")?;

                // Create client hello message.
                let client_hello =
                    ClientHello::new(get_random().context("Couldn't generate random array")?);

                // Update current transcript.
                self.transcript
                    .append(&client_hello)
                    .context("Couldn't append client hello to the transcript")?;

                let serialized_client_hello = client_hello
                    .serialize()
                    .context("Couldn't serialize client hello message")?;

                self.state = ClientHandshakerState::ExpectingServerIdentity(key_negotiator);
                Ok(serialized_client_hello)
            }
            _ => Err(anyhow!(
                "Client hello message can't be created in {:?} state, needed Initializing",
                self.state
            )),
        }
    }

    /// Responds to [`ServerIdentity`] message by creating a [`ClientIdentity`] message and derives
    /// session keys for encrypting/decrypting messages from the server.
    ///
    /// [`ClientIdentity`] message contains an ephemeral public key for negotiating session keys.
    /// If self attestation is enabled this message also provides necessary information to perform
    /// remote attestation.
    ///
    /// Transitions [`ClientHandshaker`] state from [`HandshakerState::ExpectingServerIdentity`] to
    /// [`HandshakerState::Completed`] state.
    fn process_server_identity(
        &mut self,
        server_identity: ServerIdentity,
        key_negotiator: KeyNegotiator,
    ) -> anyhow::Result<ClientIdentity> {
        if self.behavior.contains_peer_attestation() {
            // Verify server transcript signature.
            // Transcript doesn't include transcript signature from the server identity message.
            let mut server_identity_no_signature = server_identity.clone();
            server_identity_no_signature.clear_transcript_signature();
            self.transcript
                .append(&server_identity_no_signature)
                .context("Couldn't append server identity to the transcript")?;
            let verifier = SignatureVerifier::new(&server_identity.signing_public_key);
            verifier
                .verify(
                    &self.transcript.get_sha256(),
                    &server_identity.transcript_signature,
                )
                .context("Couldn't verify server transcript")?;

            // Verify server attestation info.
            let server_attestation_info = &server_identity.attestation_info;
            let expected_tee_measurement = self
                .behavior
                .get_expected_tee_measurement()
                .as_ref()
                .context("Couldn't get expected TEE measurement")?;
            verify_attestation_info(server_attestation_info, expected_tee_measurement)
                .context("Couldn't verify server attestation info")?;
        }

        // Create client identity message.
        let ephemeral_public_key = key_negotiator
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

            let attestation_info = create_attestation_info(signer, &[], tee_certificate)
                .context("Couldn't create attestation info")?;

            let mut client_identity = ClientIdentity::new(
                ephemeral_public_key,
                signer
                    .public_key()
                    .context("Couldn't get singing public key")?,
                attestation_info,
            );

            // Update current transcript.
            // Transcript doesn't include transcript signature from the client identity message.
            self.transcript
                .append(&client_identity)
                .context("Couldn't append client identity to transcript")?;

            // Add transcript signature to the client identity message.
            let transcript_signature = signer
                .sign(&self.transcript.get_sha256())
                .context("Couldn't create transcript signature")?;
            client_identity.set_transcript_signature(&transcript_signature);
            client_identity
        } else {
            ClientIdentity::new(
                ephemeral_public_key,
                // Signing public key.
                [Default::default(); SIGNING_ALGORITHM_KEY_LENGTH],
                // Attestation info.
                vec![],
            )
        };

        (self.server_verifier)(server_identity.clone())?;

        // Agree on session keys and create an encryptor.
        let encryptor = key_negotiator
            .create_encryptor(&server_identity.ephemeral_public_key)
            .context("Couldn't derive session key")?;
        self.state = ClientHandshakerState::Completed(encryptor);

        Ok(client_identity)
    }
}

/// Server of the remote attestation protocol handshake.
pub struct ServerHandshaker {
    /// Behavior of the remote attestation protocol.
    behavior: AttestationBehavior,
    /// Current state of the remote attestation protocol handshake.
    state: ServerHandshakerState,
    /// Collection of previously sent and received messages.
    /// Signed transcript is sent in messages to prevent replay attacks.
    transcript: Transcript,
    /// Additional info about the server, including configuration information and proof of
    /// inclusion in a verifiable log.
    additional_info: Vec<u8>,
}

impl ServerHandshaker {
    /// Creates [`ServerHandshaker`] with [`HandshakerState::ExpectingClientIdentity`]
    /// state.
    pub fn new(behavior: AttestationBehavior, additional_info: Vec<u8>) -> Self {
        Self {
            behavior,
            state: ServerHandshakerState::ExpectingClientHello,
            transcript: Transcript::new(),
            additional_info,
        }
    }

    /// Processes incoming `message` and returns a serialized remote attestation message.
    /// If [`None`] is returned, then no messages should be sent out to the client.
    pub fn next_step(&mut self, message: &[u8]) -> anyhow::Result<Option<Vec<u8>>> {
        self.next_step_util(message).map_err(|error| {
            self.state = ServerHandshakerState::Aborted;
            error
        })
    }

    fn next_step_util(&mut self, message: &[u8]) -> anyhow::Result<Option<Vec<u8>>> {
        let deserialized_message =
            deserialize_message(message).context("Couldn't deserialize message")?;
        match deserialized_message {
            MessageWrapper::ClientHello(client_hello) => match &self.state {
                ServerHandshakerState::ExpectingClientHello => {
                    let server_identity = self
                        .process_client_hello(client_hello)
                        .context("Couldn't process client hello message")?;
                    let serialized_server_identity = server_identity
                        .serialize()
                        .context("Couldn't serialize server identity message")?;
                    Ok(Some(serialized_server_identity))
                }
                ServerHandshakerState::Aborted => {
                    Err(anyhow!("Remote attestation handshake is aborted",))
                }
                ServerHandshakerState::MessageProcessing => Err(anyhow!(
                    "Cannot process new messages while in the MessageProcessing state",
                )),
                _ => Err(anyhow!(
                    "Incorrect handshake message received, in state {:?}, found ClientHello",
                    self.state
                )),
            },
            MessageWrapper::ClientIdentity(client_identity) => {
                match std::mem::take(&mut self.state) {
                    ServerHandshakerState::ExpectingClientIdentity(key_negotiator) => {
                        self.process_client_identity(client_identity, key_negotiator)
                            .context("Couldn't process client identity message")?;
                        Ok(None)
                    }
                    ServerHandshakerState::MessageProcessing => Err(anyhow!(
                        "Cannot process new messages while in the MessageProcessing state",
                    )),
                    _ => Err(anyhow!(
                        "Incorrect handshake message received, in state {:?}, found ClientIdentity",
                        self.state
                    )),
                }
            }
            unsupported_message => Err(anyhow!(
                "Receiving {:?} is not supported by the server handshaker",
                unsupported_message
            )),
        }
    }

    pub fn is_completed(&self) -> bool {
        matches!(self.state, ServerHandshakerState::Completed(_))
    }

    pub fn is_aborted(&self) -> bool {
        matches!(self.state, ServerHandshakerState::Aborted)
    }

    pub fn get_encryptor(self) -> anyhow::Result<Encryptor> {
        match self.state {
            ServerHandshakerState::Completed(encryptor) => Ok(Encryptor { encryptor }),
            _ => Err(anyhow!("Handshake is not complete")),
        }
    }

    /// Responds to [`ClientHello`] message by creating a [`ServerIdentity`] message.
    ///
    /// [`ServerIdentity`] message contains an ephemeral public key for negotiating session keys.
    /// If self attestation is enabled this message also provides necessary information to perform
    /// remote attestation.
    ///
    /// Transitions [`ServerHandshaker`] state from [`HandshakerState::ExpectingClientHello`] to
    /// [`HandshakerState::ExpectingClientIdentity`] state.
    fn process_client_hello(
        &mut self,
        client_hello: ClientHello,
    ) -> anyhow::Result<ServerIdentity> {
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

            let additional_info = self.additional_info.clone();
            let attestation_info =
                create_attestation_info(signer, additional_info.as_ref(), tee_certificate)
                    .context("Couldn't get attestation info")?;

            let mut server_identity = ServerIdentity::new(
                ephemeral_public_key,
                get_random().context("Couldn't generate random array")?,
                signer
                    .public_key()
                    .context("Couldn't get singing public key")?,
                attestation_info,
                additional_info,
            );

            // Update current transcript.
            // Transcript doesn't include transcript signature from the server identity message.
            self.transcript
                .append(&client_hello)
                .context("Couldn't append client hello to the transcript")?;
            self.transcript
                .append(&server_identity)
                .context("Couldn't append server identity to the transcript")?;

            // Add transcript signature to the server identity message.
            let transcript_signature = signer
                .sign(&self.transcript.get_sha256())
                .context("Couldn't create transcript signature")?;
            server_identity.set_transcript_signature(&transcript_signature);
            server_identity
        } else {
            ServerIdentity::new(
                ephemeral_public_key,
                get_random().context("Couldn't generate random array")?,
                // Signing public key.
                [Default::default(); SIGNING_ALGORITHM_KEY_LENGTH],
                // Attestation info.
                vec![],
                // Additional info.
                vec![],
            )
        };

        self.state = ServerHandshakerState::ExpectingClientIdentity(key_negotiator);
        Ok(server_identity)
    }

    /// Finishes the remote attestation protocol handshake and derives session keys for
    /// encrypting/decrypting messages from the client.
    ///
    /// Transitions [`ServerHandshaker`] state from
    /// [`HandshakerState::ExpectingClientIdentity`] to [`HandshakerState::Completed`] state.
    fn process_client_identity(
        &mut self,
        client_identity: ClientIdentity,
        key_negotiator: KeyNegotiator,
    ) -> anyhow::Result<()> {
        if self.behavior.contains_peer_attestation() {
            // Verify client transcript signature.
            // Transcript doesn't include transcript signature from the client identity message.
            let mut client_identity_no_signature = client_identity.clone();
            client_identity_no_signature.clear_transcript_signature();
            self.transcript
                .append(&client_identity_no_signature)
                .context("Couldn't append client identity to the transcript")?;
            let verifier = SignatureVerifier::new(&client_identity.signing_public_key);
            verifier
                .verify(
                    &self.transcript.get_sha256(),
                    &client_identity.transcript_signature,
                )
                .context("Couldn't verify client transcript")?;

            // Verify client attestation info.
            let client_attestation_info = &client_identity.attestation_info;
            let expected_tee_measurement = self
                .behavior
                .get_expected_tee_measurement()
                .as_ref()
                .context("Couldn't get expected TEE measurement")?;
            verify_attestation_info(client_attestation_info, expected_tee_measurement)
                .context("Couldn't verify client attestation info")?;
        }

        // Agree on session keys and create an encryptor.
        let encryptor = key_negotiator
            .create_encryptor(&client_identity.ephemeral_public_key)
            .context("Couldn't derive session key")?;
        self.state = ServerHandshakerState::Completed(encryptor);

        Ok(())
    }
}

pub struct Encryptor {
    encryptor: AeadEncryptor,
}

impl Encryptor {
    pub fn new(encryptor: AeadEncryptor) -> Self {
        Self { encryptor }
    }

    pub fn decrypt(&mut self, message: &[u8]) -> anyhow::Result<Vec<u8>> {
        let deserialized_message =
            deserialize_message(message).context("Couldn't deserialize message")?;
        match deserialized_message {
            MessageWrapper::EncryptedData(data) => self
                .encryptor
                .decrypt(&data)
                .context("Couldn't decrypt message"),
            incorrect_message => Err(anyhow!(
                "Incorrect protocol message received, in state EncryptedData, found {:?}",
                incorrect_message
            )),
        }
    }

    pub fn encrypt(&mut self, message: &[u8]) -> anyhow::Result<Vec<u8>> {
        let encrypted_message = self
            .encryptor
            .encrypt(message)
            .context("Couldn't encrypt message")?;
        let serialized_message = encrypted_message
            .serialize()
            .context("Couldn't serialize encrypted data message")?;
        Ok(serialized_message)
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

impl std::fmt::Debug for AttestationBehavior {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match (
            self.contains_peer_attestation(),
            self.contains_self_attestation(),
        ) {
            (true, false) => write!(f, "PeerAttestation"),
            (false, true) => write!(f, "SelfAttestation"),
            (true, true) => write!(f, "BidirectionalAttestation"),
            (false, false) => write!(f, "InvalidAttestation"),
        }
    }
}

impl AttestationBehavior {
    /// Represents an attestation process, where current machine remotely attests a remote peer and
    /// verifies its attestation info.
    pub fn create_peer_attestation(expected_tee_measurement: &[u8]) -> Self {
        Self {
            expected_tee_measurement: Some(expected_tee_measurement.to_vec()),
            tee_certificate: None,
            signer: None,
        }
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

    /// Appends a serialized `message` to the end of [`Transcript::value`].
    pub fn append<M: Serializable>(&mut self, message: &M) -> anyhow::Result<()> {
        let bytes = message.serialize().context("Couldn't serialize message")?;
        self.value.extend(bytes);
        Ok(())
    }

    /// Get SHA-256 hash of the [`Transcript::value`].
    pub fn get_sha256(&self) -> [u8; SHA256_HASH_LENGTH] {
        get_sha256(&self.value)
    }
}

/// Generates attestation info with a TEE report.
/// TEE report contains a hash of the signer's public key, and additional info if provided as a
/// non-empty string by the caller.
pub fn create_attestation_info(
    signer: &Signer,
    additional_info: &[u8],
    tee_certificate: &[u8],
) -> anyhow::Result<Vec<u8>> {
    let signing_public_key = signer
        .public_key()
        .context("Couldn't get singing public key")?;
    let mut data = get_sha256(signing_public_key.as_ref()).to_vec();
    if !additional_info.is_empty() {
        data.extend(get_sha256(additional_info));
        data = get_sha256(&data).to_vec();
    }
    let report = AttestationReport::new(&data);
    let attestation_info = AttestationInfo {
        report: Some(report),
        certificate: tee_certificate.to_vec(),
    };
    serialize_protobuf(&attestation_info)
        .context("Couldn't encode attestation info Protobuf message")
}

/// Verifies the validity of the attestation info:
/// - Checks that the TEE report is signed by TEE Provider’s root key.
/// - Checks that the public key hash from the TEE report is equal to the hash of the public key
///   presented in the server response.
/// - Extracts the TEE measurement from the TEE report and compares it to the
///   `expected_tee_measurement`.
pub fn verify_attestation_info(
    attestation_info_bytes: &[u8],
    expected_tee_measurement: &[u8],
) -> anyhow::Result<()> {
    let attestation_info = AttestationInfo::decode(attestation_info_bytes)
        .context("Couldn't decode attestation info Protobuf message")?;

    // TODO(#1867): Add remote attestation support, use real TEE reports and check that
    // `AttestationInfo::certificate` is signed by one of the root certificates.

    let report = attestation_info
        .report
        .as_ref()
        .context("Couldn't find report in peer attestation info")?;

    // Check that the report contains non-empty data. This should be a hash of the public key
    // and the additional info field.
    if report.data.is_empty() {
        anyhow::bail!("Hash of the public key and additional info is not provided.")
    }

    // Verify TEE measurement.
    if expected_tee_measurement == report.measurement {
        Ok(())
    } else {
        Err(anyhow!("Incorrect TEE measurement"))
    }
}

pub fn serialize_protobuf<M: prost::Message>(message: &M) -> anyhow::Result<Vec<u8>> {
    let mut message_bytes = Vec::new();
    message
        .encode(&mut message_bytes)
        .context("Couldn't serialize Protobuf message to bytes")?;
    Ok(message_bytes)
}
