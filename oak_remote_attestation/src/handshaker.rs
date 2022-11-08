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

///! Remote attestation protocol handshake implementation.
///!
///! During the attestation protocol handshake participants send the following messages:
///!
///! - [`Client`] -> [`Server`]: [`ClientHello`]
///! - [`Server`] -> [`Client`]: [`ServerIdentity`]
///! - [`Client`] -> [`Server`]: [`ClientIdentity`]
///!
///! After the protocol handshake both sides create [`Encryptor`] for exchanging encrypted
///! messages.
use crate::{
    crypto::{
        get_random, get_sha256, AeadEncryptor, KeyNegotiator, KeyNegotiatorType, SignatureVerifier,
        Signer, KEY_AGREEMENT_ALGORITHM_KEY_LENGTH, SHA256_HASH_LENGTH, SIGNATURE_LENGTH,
        SIGNING_ALGORITHM_KEY_LENGTH,
    },
    message::{
        deserialize_message, ClientHello, ClientIdentity, MessageWrapper, Serializable,
        ServerIdentity,
    },
};
use alloc::{sync::Arc, vec, vec::Vec};
use anyhow::{anyhow, Context};
use core::fmt::Debug;

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

impl core::fmt::Debug for ClientHandshakerState {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
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

impl core::fmt::Debug for ServerHandshakerState {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
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
pub struct ClientHandshaker<G: AttestationGenerator + Clone, V: AttestationVerifier> {
    /// Behavior of the remote attestation protocol.
    behavior: AttestationBehavior<G, V>,
    /// Current state of the remote attestation protocol handshake.
    state: ClientHandshakerState,
    /// Collection of previously sent and received messages.
    /// Signed transcript is sent in messages to prevent replay attacks.
    transcript: Transcript,
    /// Signer containing a key which public part is signed by the TEE firmware key.
    /// Used for signing protocol transcripts and preventing replay attacks.
    transcript_signer: Signer,
}

impl<G: AttestationGenerator + Clone, V: AttestationVerifier> ClientHandshaker<G, V> {
    /// Creates [`ClientHandshaker`] with `Initializing` state.
    pub fn new(behavior: AttestationBehavior<G, V>) -> anyhow::Result<Self> {
        Ok(Self {
            behavior,
            state: ClientHandshakerState::Initializing,
            transcript: Transcript::new(),
            transcript_signer: Signer::create().context("Couldn't create signer")?,
        })
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
                match core::mem::take(&mut self.state) {
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
    /// Transitions [`ClientHandshaker`] state from `Initializing` to `ExpectingServerIdentity`
    /// state.
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
    /// Transitions [`ClientHandshaker`] state from
    /// [`ClientHandshakerState::ExpectingServerIdentity`] to [`ClientHandshakerState::Completed`]
    /// state.
    fn process_server_identity(
        &mut self,
        server_identity: ServerIdentity,
        key_negotiator: KeyNegotiator,
    ) -> anyhow::Result<ClientIdentity> {
        // Verify server transcript signature.
        // Transcript doesn't include transcript signature from the server identity message.
        let mut server_identity_no_signature = server_identity.clone();
        server_identity_no_signature.clear_transcript_signature();
        self.transcript
            .append(&server_identity_no_signature)
            .context("Couldn't append server identity to the transcript")?;
        let server_signing_public_key = &server_identity.signing_public_key;
        let transcript_signature_verifier = SignatureVerifier::new(server_signing_public_key)?;
        transcript_signature_verifier
            .verify(
                &self.transcript.get_sha256(),
                &server_identity.transcript_signature,
            )
            .context("Couldn't verify server transcript")?;

        let expected_attested_data = attestation_data(
            &server_identity.ephemeral_public_key,
            server_signing_public_key,
        );

        // Verify server attestation info.
        let server_attestation_report = &server_identity.attestation_report;
        self.behavior
            .verifier
            .verify_attestation(server_attestation_report, &expected_attested_data)?;

        // Create client identity message.
        let ephemeral_public_key = key_negotiator
            .public_key()
            .context("Couldn't get ephemeral public key")?;

        let attested_data =
            attestation_data(&ephemeral_public_key, &self.transcript_signer.public_key()?);
        let attestation_report = self
            .behavior
            .generator
            .generate_attestation(&attested_data)
            .context("Couldnt' create attestation report")?;

        let mut client_identity = ClientIdentity::new(
            ephemeral_public_key,
            self.transcript_signer
                .public_key()
                .context("Couldn't get signing public key")?,
            attestation_report,
        );

        // Update current transcript.
        // Transcript doesn't include transcript signature from the client identity message.
        self.transcript
            .append(&client_identity)
            .context("Couldn't append client identity to transcript")?;

        // Add transcript signature to the client identity message.
        let transcript_signature = self
            .transcript_signer
            .sign(&self.transcript.get_sha256())
            .context("Couldn't create transcript signature")?;
        client_identity.set_transcript_signature(&transcript_signature);

        // Agree on session keys and create an encryptor.
        let encryptor = key_negotiator
            .create_encryptor(&server_identity.ephemeral_public_key)
            .context("Couldn't derive session key")?;
        self.state = ClientHandshakerState::Completed(encryptor);

        Ok(client_identity)
    }
}

/// Server of the remote attestation protocol handshake.
pub struct ServerHandshaker<G: AttestationGenerator + Clone, V: AttestationVerifier> {
    /// Behavior of the remote attestation protocol.
    behavior: AttestationBehavior<G, V>,
    /// Current state of the remote attestation protocol handshake.
    state: ServerHandshakerState,
    /// Collection of previously sent and received messages.
    /// Signed transcript is sent in messages to prevent replay attacks.
    transcript: Transcript,
    /// Signer containing a key which public part is signed by the TEE firmware key.
    /// Used for signing protocol transcripts and preventing replay attacks.
    transcript_signer: Arc<Signer>,
}

impl<G: AttestationGenerator + Clone, V: AttestationVerifier> ServerHandshaker<G, V> {
    /// Creates [`ServerHandshaker`] with `ServerHandshakerState::ExpectingClientIdentity`
    /// state.
    pub fn new(
        behavior: AttestationBehavior<G, V>,
        transcript_signer: Arc<Signer>,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            behavior,
            state: ServerHandshakerState::ExpectingClientHello,
            transcript: Transcript::new(),
            transcript_signer,
        })
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
                match core::mem::take(&mut self.state) {
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
    /// Transitions [`ServerHandshaker`] state from [`ServerHandshakerState::ExpectingClientHello`]
    /// to [`ServerHandshakerState::ExpectingClientIdentity`] state.
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

        let attestation_data =
            attestation_data(&ephemeral_public_key, &self.transcript_signer.public_key()?);
        let attestation_report = self
            .behavior
            .generator
            .generate_attestation(&attestation_data)?;

        let mut server_identity = ServerIdentity::new(
            ephemeral_public_key,
            get_random().context("Couldn't generate random array")?,
            self.transcript_signer
                .public_key()
                .context("Couldn't get singing public key")?,
            attestation_report,
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
        let transcript_signature = self
            .transcript_signer
            .sign(&self.transcript.get_sha256())
            .context("Couldn't create transcript signature")?;
        server_identity.set_transcript_signature(&transcript_signature);

        self.state = ServerHandshakerState::ExpectingClientIdentity(key_negotiator);
        Ok(server_identity)
    }

    /// Finishes the remote attestation protocol handshake and derives session keys for
    /// encrypting/decrypting messages from the client.
    ///
    /// Transitions [`ServerHandshaker`] state from
    /// [`ServerHandshakerState::ExpectingClientIdentity`] to [`ServerHandshakerState::Completed`]
    /// state.
    fn process_client_identity(
        &mut self,
        client_identity: ClientIdentity,
        key_negotiator: KeyNegotiator,
    ) -> anyhow::Result<()> {
        // Verify client transcript signature.
        // Transcript doesn't include transcript signature from the client identity message.
        let mut client_identity_no_signature = client_identity.clone();
        client_identity_no_signature.clear_transcript_signature();
        self.transcript
            .append(&client_identity_no_signature)
            .context("Couldn't append client identity to the transcript")?;
        let client_signing_public_key = &client_identity.signing_public_key;

        // TODO(#2918): Remove this check when the Java client generates a non-empty signature, and
        // always verify the signature.
        if client_identity.transcript_signature == [0; SIGNATURE_LENGTH] {
            // We skip verifying the signature because of #2918, until it is implemented in the Java
            // client.
            // Until this is fixed, this version of the server must not be used in production.
        } else {
            let transcript_signature_verifier = SignatureVerifier::new(client_signing_public_key)?;
            transcript_signature_verifier
                .verify(
                    &self.transcript.get_sha256(),
                    &client_identity.transcript_signature,
                )
                .context("Couldn't verify client transcript")?;
        }

        let expected_attested_data = attestation_data(
            &client_identity.ephemeral_public_key,
            client_signing_public_key,
        );

        // Verify client attestation info.
        let client_attestation_report = &client_identity.attestation_report;
        self.behavior
            .verifier
            .verify_attestation(client_attestation_report, &expected_attested_data)?;

        // Agree on session keys and create an encryptor.
        let encryptor = key_negotiator
            .create_encryptor(&client_identity.ephemeral_public_key)
            .context("Couldn't derive session key")?;
        self.state = ServerHandshakerState::Completed(encryptor);

        Ok(())
    }
}

/// Used by the client and server to encrypt and decrypt messages with the keys established in the
/// remote attestation protocol handshake.
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
///
/// It is composed of an [`AttestationGenerator`] and an [`AttestationVerifier`], which may be
/// combined to achieve any of the following high level configurations:
///
/// - Peer Attestation:
///   - Represents an attestation process, where current machine remotely attests a remote peer and
///     verifies its attestation info.
/// - Self Attestation:
///   - Represents an attestation process, where current machine remotely attests to a remote peer
///     and sends attestation info to it.
/// - Bidirectional Attestation:
///   - Represents an attestation process, where current machine and a remote peer remotely attest
///     each other.
#[derive(Debug, Clone)]
pub struct AttestationBehavior<G: AttestationGenerator + Clone, V: AttestationVerifier> {
    pub generator: G,
    pub verifier: V,
}

/// A trait implementing the functionality of generating a remote attestation report.
///
/// An implementation of this trait is expected to run in a TEE (i.e. it is usually in the server).
pub trait AttestationGenerator: Send + Sync {
    /// Generate a remote attestation report, ensuring that `attested_data` is cryptographically
    /// bound to the result (e.g. via a signature).
    ///
    /// That is usually verified by [`AttestationVerifier::verify_attestation`].
    fn generate_attestation(&self, attested_data: &[u8]) -> anyhow::Result<Vec<u8>>;
}

/// An instance of [`AttestationGenerator`] that always returns an empty attestation.
///
/// Useful when no attestation is expected to be genereated by the current side of a remotely
/// attested connection.
#[derive(Clone)]
pub struct EmptyAttestationGenerator;

impl AttestationGenerator for EmptyAttestationGenerator {
    fn generate_attestation(&self, _attested_data: &[u8]) -> anyhow::Result<Vec<u8>> {
        Ok(Vec::new())
    }
}

/// A trait implementing the functionality of verifying a remote attestation report.
///
/// An implementation of this trait is not expected to run in a TEE (i.e. it is usually in the
/// client).
pub trait AttestationVerifier: Clone + Send + Sync {
    /// Verify the provided remote attestation report, checking that `expected_attested_data` is
    /// cryptographically bound to it (e.g. via a signature).
    ///
    /// That is usually generated by [`AttestationGenerator::generate_attestation`].
    fn verify_attestation(
        &self,
        attestation: &[u8],
        expected_attested_data: &[u8],
    ) -> anyhow::Result<()>;
}

/// An instance of [`AttestationVerifier`] that succeeds iff the provided attestation is empty.
///
/// Useful when no attestation is expected to be genereated by the other side of a remotely
/// attested connection.
#[derive(Clone)]
pub struct EmptyAttestationVerifier;

impl AttestationVerifier for EmptyAttestationVerifier {
    fn verify_attestation(
        &self,
        attestation: &[u8],
        _expected_attested_data: &[u8],
    ) -> anyhow::Result<()> {
        // We check that the attestation is empty in order to avoid accidentally ignoring a real
        // attestation from the other side, although in principle a more lenient implementation of
        // this struct could be used that always ignores also non-empty attestations.
        if attestation.is_empty() {
            Ok(())
        } else {
            Err(anyhow::anyhow!(
                "expected empty attestation, got {:?}",
                attestation
            ))
        }
    }
}

impl<G: AttestationGenerator + Clone, V: AttestationVerifier> AttestationBehavior<G, V> {
    pub fn create(generator: G, verifier: V) -> Self {
        Self {
            generator,
            verifier,
        }
    }
}

/// Convenience struct for managing protocol transcripts.
///
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

/// Compute data to be attested based on the actual or expected parameters.
///
/// In particular, the concatenation of the ephemeral public key, and the signing public key.
///
/// For instance, a remotely attestable server would use this function to condense all data that
/// needs to be remotely attested into a single sequence of bytes; on the other side, the client
/// would reconstruct the same expected data (e.g. during a key exchange protocol), and confirm that
/// it was indeed correctly attested by the server.
pub fn attestation_data(
    ephemeral_public_key: &[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
    signing_public_key: &[u8; SIGNING_ALGORITHM_KEY_LENGTH],
) -> Vec<u8> {
    hash_concat_hash(&[ephemeral_public_key, signing_public_key]).to_vec()
}

/// Compute a hash over values of possibly different length.
///
/// It is necessary to first hash the individual values, then concatenate the hashes, and then hash
/// the concatenated result, in order to guarantee that it's not possible to create a collision by
/// moving elements from one value to another (see unit test for an example of this attack).
pub fn hash_concat_hash(values: &[&[u8]]) -> [u8; SHA256_HASH_LENGTH] {
    get_sha256(
        &values
            .iter()
            .flat_map(|v| get_sha256(v))
            .collect::<Vec<_>>(),
    )
}
