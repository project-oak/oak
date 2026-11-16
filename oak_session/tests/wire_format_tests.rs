//
// Copyright 2026 The Project Oak Authors
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

//! Pinned wire-format and golden-artifact tests for `oak_session`.
//!
//! These tests guard against unintended wire-protocol changes in `oak_session`
//! (protobuf framing, assertion binding token serialization, session binding
//! hash derivation, 2-message unidirectional and 3-message bidirectional Noise
//! handshakes, and encrypted transport framing) using real AMD SEV-SNP
//! hardware attestation artifacts (`Evidence` and `Endorsements`).

use std::{
    boxed::Box,
    collections::BTreeMap,
    convert::{TryFrom, TryInto},
    fs,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};

use anyhow::{Context, anyhow};
use googletest::prelude::*;
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification::create_amd_verifier;
use oak_attestation_verification_results::unique_session_binding_public_key;
use oak_attestation_verification_types::{
    assertion_verifier::{AssertionVerifier, AssertionVerifierError},
    verifier::AttestationVerifier,
};
use oak_crypto::{
    encryptor::{Encryptor, Payload},
    noise_handshake::{
        NONCE_LEN, OrderedCrypter, P256_X962_LEN, P256Scalar, SHA256_OUTPUT_LEN, SYMMETRIC_KEY_LEN,
        aes_256_gcm_open_in_place, aes_256_gcm_seal_in_place, hkdf_sha256, p256_scalar_mult,
        sha256_two_part,
    },
};
use oak_file_utils::data_path;
use oak_proto_rust::oak::{
    attestation::v1::{
        Assertion, AttestationResults, Endorsements, Evidence, ReferenceValues,
        attestation_results::Status,
    },
    session::v1::{
        AttestRequest, AttestResponse, EncryptedMessage, EndorsedEvidence, HandshakeRequest,
        HandshakeResponse, NoiseHandshakeMessage, PlaintextMessage, SessionBinding,
        SessionBindingKeyWrapperAssertion, SessionRequest, SessionResponse, handshake_request,
        handshake_response, session_request, session_response,
    },
};
use oak_session::{
    ClientSession, ProtocolEngine, ServerSession, Session,
    aggregators::All,
    attestation::{
        AttestationHandler, AttestationType, ClientAttestationHandler, ServerAttestationHandler,
    },
    config::{SessionConfig, SessionConfigBuilder},
    encryptors::OrderedChannelEncryptor,
    generator::{BindableAssertionGenerator, SessionKeyBindableAssertionGenerator},
    handshake::HandshakeType,
    session_binding::{
        SessionBinder, SessionBindingVerifier, SessionBindingVerifierProvider, SignatureBinder,
        SignatureBindingVerifierBuilder, create_session_binding_token,
    },
    verifier::{BoundAssertionVerifier, SessionKeyBoundAssertionVerifier},
};
use oak_session_endorsed_evidence::{
    EndorsedEvidenceBindableAssertionGenerator, EndorsedEvidenceBoundAssertionVerifier,
};
use oak_time::{Instant, clock::FixedClock, make_instant};
use p256::ecdsa::{
    Signature, SigningKey, VerifyingKey,
    signature::{Signer as EcdsaSigner, Verifier as EcdsaVerifier},
};
use prost::Message;
use sha2::Digest;

const OC_EVIDENCE_PATH: &str = "oak_session/testdata/milan_oc_release_evidence.binarypb";
const OC_ENDORSEMENTS_PATH: &str = "oak_session/testdata/milan_oc_release_endorsements.binarypb";
const OC_REFERENCE_VALUES_PATH: &str =
    "oak_session/testdata/milan_oc_release_reference_values.binarypb";

const RK_EVIDENCE_PATH: &str = "oak_session/testdata/milan_rk_release_evidence.binarypb";
const RK_ENDORSEMENTS_PATH: &str = "oak_session/testdata/milan_rk_release_endorsements.binarypb";
const RK_REFERENCE_VALUES_PATH: &str =
    "oak_session/testdata/milan_rk_release_reference_values.binarypb";

const GOLDEN_ATTEST_REQUEST_ASSERTIONS_PATH: &str =
    "oak_session/testdata/attest_request_assertions.binarypb";
const GOLDEN_ATTEST_RESPONSE_ASSERTIONS_PATH: &str =
    "oak_session/testdata/attest_response_assertions.binarypb";
const GOLDEN_ATTEST_REQUEST_LEGACY_PATH: &str =
    "oak_session/testdata/attest_request_legacy.binarypb";
const GOLDEN_ATTEST_RESPONSE_LEGACY_PATH: &str =
    "oak_session/testdata/attest_response_legacy.binarypb";
const GOLDEN_HANDSHAKE_REQUEST_NN_INIT_PATH: &str =
    "oak_session/testdata/handshake_request_nn_init.binarypb";
const GOLDEN_HANDSHAKE_FOLLOWUP_ASSERTIONS_PATH: &str =
    "oak_session/testdata/handshake_followup_assertions.binarypb";
const GOLDEN_ENCRYPTED_REQUEST_MSG0_PATH: &str =
    "oak_session/testdata/encrypted_request_msg0.binarypb";
const GOLDEN_ENCRYPTED_RESPONSE_MSG0_PATH: &str =
    "oak_session/testdata/encrypted_response_msg0.binarypb";
const GOLDEN_BIDI_ATTESTATION_BINDING_TOKEN_PATH: &str =
    "oak_session/testdata/bidi_attestation_binding_token.bin";
const GOLDEN_UNI_SERVER_ATTESTATION_BINDING_TOKEN_PATH: &str =
    "oak_session/testdata/uni_server_attestation_binding_token.bin";
const GOLDEN_UNI_CLIENT_ATTESTATION_BINDING_TOKEN_PATH: &str =
    "oak_session/testdata/uni_client_attestation_binding_token.bin";

const ENDORSED_EVIDENCE_ASSERTION_ID: &str = "oak_endorsed_evidence_v1";
const SESSION_KEY_WRAPPED_ASSERTION_ID: &str = "oak_session_key_wrapper_v1";
const LEGACY_ATTESTATION_ID: &str = "oak_legacy_endorsed_evidence_v1";

const CLIENT_EE_BINDING_KEY_BYTES: [u8; 32] = [0x11; 32];
const CLIENT_SK_BINDING_KEY_BYTES: [u8; 32] = [0x12; 32];
const SERVER_EE_BINDING_KEY_BYTES: [u8; 32] = [0x21; 32];
const SERVER_SK_BINDING_KEY_BYTES: [u8; 32] = [0x22; 32];
const CLIENT_LEGACY_BINDING_KEY_BYTES: [u8; 32] = [0x31; 32];
const SERVER_LEGACY_BINDING_KEY_BYTES: [u8; 32] = [0x32; 32];

const FROZEN_CLIENT_EPHEMERAL_SCALAR: [u8; 32] = [0x41; 32];
const FROZEN_SERVER_EPHEMERAL_SCALAR: [u8; 32] = [0x42; 32];
const PINNED_HANDSHAKE_HASH: [u8; 32] = [0x55; 32];
const PINNED_CLIENT_WRITE_KEY: [u8; 32] = [0x61; 32];
const PINNED_SERVER_WRITE_KEY: [u8; 32] = [0x62; 32];

const CHANNEL_BINDING_INFO: &[u8] = b"oak-session-wire-format-test-v1";

fn verification_time() -> Instant {
    make_instant!("2026-11-16T00:00:00Z")
}

fn read_testdata_bytes(path: &str) -> Vec<u8> {
    fs::read(data_path(path)).unwrap_or_else(|e| panic!("reading {}: {}", path, e))
}

#[derive(Clone)]
struct GoldenAttestationBundle {
    evidence: Evidence,
    endorsements: Endorsements,
    reference_values: ReferenceValues,
    expect_container_session_binding_key: bool,
}

impl GoldenAttestationBundle {
    fn load_oc_release() -> Self {
        Self {
            evidence: Evidence::decode(read_testdata_bytes(OC_EVIDENCE_PATH).as_slice())
                .expect("decoding OC evidence"),
            endorsements: Endorsements::decode(
                read_testdata_bytes(OC_ENDORSEMENTS_PATH).as_slice(),
            )
            .expect("decoding OC endorsements"),
            reference_values: ReferenceValues::decode(
                read_testdata_bytes(OC_REFERENCE_VALUES_PATH).as_slice(),
            )
            .expect("decoding OC reference values"),
            expect_container_session_binding_key: true,
        }
    }

    fn load_rk_release() -> Self {
        Self {
            evidence: Evidence::decode(read_testdata_bytes(RK_EVIDENCE_PATH).as_slice())
                .expect("decoding RK evidence"),
            endorsements: Endorsements::decode(
                read_testdata_bytes(RK_ENDORSEMENTS_PATH).as_slice(),
            )
            .expect("decoding RK endorsements"),
            reference_values: ReferenceValues::decode(
                read_testdata_bytes(RK_REFERENCE_VALUES_PATH).as_slice(),
            )
            .expect("decoding RK reference values"),
            expect_container_session_binding_key: false,
        }
    }

    fn endorsed_evidence(&self) -> EndorsedEvidence {
        EndorsedEvidence {
            evidence: Some(self.evidence.clone()),
            endorsements: Some(self.endorsements.clone()),
        }
    }

    fn create_verifier(&self) -> Arc<dyn AttestationVerifier> {
        let inner = create_amd_verifier(
            FixedClock::at_instant(verification_time()),
            &self.reference_values,
        )
        .expect("creating AMD SEV-SNP verifier");
        Arc::new(CheckedHardwareVerifier {
            inner: Box::new(inner),
            expect_container_session_binding_key: self.expect_container_session_binding_key,
        })
    }
}

struct PrebuiltAttester {
    evidence: Evidence,
}

impl Attester for PrebuiltAttester {
    fn extend(&mut self, _encoded_event: &[u8]) -> anyhow::Result<()> {
        Ok(())
    }

    fn quote(&self) -> anyhow::Result<Evidence> {
        Ok(self.evidence.clone())
    }
}

struct PrebuiltEndorser {
    endorsements: Endorsements,
}

impl Endorser for PrebuiltEndorser {
    fn endorse(&self, _evidence: Option<&Evidence>) -> anyhow::Result<Endorsements> {
        Ok(self.endorsements.clone())
    }
}

/// Wraps [`AmdSevSnpDiceAttestationVerifier`] and additionally asserts that Oak
/// Containers DICE verification extracts the enclave's session binding key.
struct CheckedHardwareVerifier {
    inner: Box<dyn AttestationVerifier>,
    expect_container_session_binding_key: bool,
}

impl AttestationVerifier for CheckedHardwareVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let results = self.inner.verify(evidence, endorsements)?;
        if results.status() == Status::Success && self.expect_container_session_binding_key {
            let enclave_binding_key = unique_session_binding_public_key(&results)
                .map_err(|msg| anyhow!("extracting enclave session binding key: {}", msg))?;
            anyhow::ensure!(
                !enclave_binding_key.is_empty(),
                "extracted enclave session binding public key is empty"
            );
        }
        Ok(results)
    }
}

/// Test-only [`AssertionVerifier`] that validates the captured hardware
/// [`EndorsedEvidence`] inside a [`SessionBindingKeyWrapperAssertion`].
///
/// NOTE: Do NOT copy this verifier into production code. It intentionally
/// ignores `_asserted_data` (the wrapper's `public_binding_key`) because the
/// ephemeral DICE private signing keys corresponding to the captured hardware
/// `Evidence` existed only in enclave memory during capture and are unavailable
/// offline; deterministic test keys are substituted to sign and verify live
/// session bindings, while [`CheckedHardwareVerifier`] separately verifies DICE
/// key extraction from the hardware evidence.
struct EndorsedEvidenceInnerAssertionVerifier {
    attestation_verifier: Arc<dyn AttestationVerifier>,
}

impl AssertionVerifier for EndorsedEvidenceInnerAssertionVerifier {
    fn verify(
        &self,
        assertion: &Assertion,
        _asserted_data: &[u8],
        _verification_time: Instant,
    ) -> core::result::Result<(), AssertionVerifierError> {
        let endorsed_evidence = EndorsedEvidence::decode(assertion.content.as_slice())?;
        let evidence = endorsed_evidence.evidence.as_ref().ok_or_else(|| {
            AssertionVerifierError::AssertionMissingExpectedFields {
                error_msg: "missing evidence".to_string(),
            }
        })?;
        let endorsements = endorsed_evidence.endorsements.as_ref().ok_or_else(|| {
            AssertionVerifierError::AssertionMissingExpectedFields {
                error_msg: "missing endorsements".to_string(),
            }
        })?;
        let results = self.attestation_verifier.verify(evidence, endorsements)?;
        if results.status() != Status::Success {
            return Err(AssertionVerifierError::Other(anyhow!(
                "verifying hardware attestation: {}",
                results.reason
            )));
        }
        Ok(())
    }
}

/// Test-only [`SessionBindingVerifierProvider`] backed by a deterministic test
/// [`VerifyingKey`].
///
/// NOTE: Do NOT copy this provider into production code. It intentionally
/// ignores the public key in `attestation_results` (which
/// [`CheckedHardwareVerifier`] separately checks for non-empty extraction)
/// because the enclave private key matching the captured hardware `Evidence`
/// only existed inside the enclave during capture; offline wire tests sign
/// live handshake bindings with deterministic test keys instead.
struct DeterministicBindingVerifierProvider {
    verifying_key: VerifyingKey,
}

impl SessionBindingVerifierProvider for DeterministicBindingVerifierProvider {
    fn create_session_binding_verifier(
        &self,
        attestation_results: &AttestationResults,
    ) -> anyhow::Result<Box<dyn SessionBindingVerifier>> {
        anyhow::ensure!(
            attestation_results.status() == Status::Success,
            "unexpected attestation status"
        );
        Ok(Box::new(
            SignatureBindingVerifierBuilder::default()
                .verifier(Box::new(self.verifying_key))
                .build()
                .map_err(|e| anyhow!("building SignatureBindingVerifier: {}", e))?,
        ))
    }
}

fn signing_key(bytes: &[u8; 32]) -> SigningKey {
    SigningKey::from_slice(bytes).expect("parsing P-256 secret key")
}

fn signature_binder(bytes: &[u8; 32]) -> Arc<dyn SessionBinder> {
    Arc::new(SignatureBinder::new(Box::new(signing_key(bytes))))
}

fn binding_verifier_provider(bytes: &[u8; 32]) -> Arc<dyn SessionBindingVerifierProvider> {
    let vk = *signing_key(bytes).verifying_key();
    Arc::new(DeterministicBindingVerifierProvider { verifying_key: vk })
}

fn create_ee_assertion_generator(
    bundle: &GoldenAttestationBundle,
    key_bytes: &[u8; 32],
) -> Box<dyn BindableAssertionGenerator> {
    Box::new(EndorsedEvidenceBindableAssertionGenerator::new(
        Arc::new(PrebuiltAttester { evidence: bundle.evidence.clone() }),
        Arc::new(PrebuiltEndorser { endorsements: bundle.endorsements.clone() }),
        signature_binder(key_bytes),
    ))
}

fn create_sk_wrapped_assertion_generator(
    bundle: &GoldenAttestationBundle,
    key_bytes: &[u8; 32],
) -> Box<dyn BindableAssertionGenerator> {
    let inner = Assertion { content: bundle.endorsed_evidence().encode_to_vec() };
    Box::new(SessionKeyBindableAssertionGenerator::create_with_assertion(
        inner,
        Arc::new(signing_key(key_bytes)),
    ))
}

fn create_ee_assertion_verifier(
    bundle: &GoldenAttestationBundle,
    key_bytes: &[u8; 32],
) -> Box<dyn BoundAssertionVerifier> {
    Box::new(EndorsedEvidenceBoundAssertionVerifier::new(
        bundle.create_verifier(),
        binding_verifier_provider(key_bytes),
    ))
}

fn create_sk_wrapped_assertion_verifier(
    bundle: &GoldenAttestationBundle,
) -> Box<dyn BoundAssertionVerifier> {
    Box::new(SessionKeyBoundAssertionVerifier {
        assertion_verifier: Arc::new(EndorsedEvidenceInnerAssertionVerifier {
            attestation_verifier: bundle.create_verifier(),
        }),
        clock: Arc::new(FixedClock::at_instant(verification_time())),
    })
}

fn add_self_assertions(
    builder: SessionConfigBuilder,
    bundle: &GoldenAttestationBundle,
    ee_key: &[u8; 32],
    sk_key: &[u8; 32],
) -> SessionConfigBuilder {
    builder
        .add_self_assertion_generator(
            ENDORSED_EVIDENCE_ASSERTION_ID.to_string(),
            create_ee_assertion_generator(bundle, ee_key),
        )
        .add_self_assertion_generator(
            SESSION_KEY_WRAPPED_ASSERTION_ID.to_string(),
            create_sk_wrapped_assertion_generator(bundle, sk_key),
        )
}

fn add_peer_assertion_verifiers(
    builder: SessionConfigBuilder,
    peer_bundle: &GoldenAttestationBundle,
    peer_ee_key: &[u8; 32],
) -> SessionConfigBuilder {
    builder
        .add_peer_assertion_verifier(
            ENDORSED_EVIDENCE_ASSERTION_ID.to_string(),
            create_ee_assertion_verifier(peer_bundle, peer_ee_key),
        )
        .add_peer_assertion_verifier(
            SESSION_KEY_WRAPPED_ASSERTION_ID.to_string(),
            create_sk_wrapped_assertion_verifier(peer_bundle),
        )
        .set_assertion_attestation_aggregator(Box::new(All {}))
}

// ============================================================================
// Independent Frozen Wire-Protocol Implementation
//
// None of the helpers below call `oak_session`'s internal serialization,
// binding-token, Noise-handshake, or session-encryptor implementations. Any
// wire-level change in `oak_session` will diverge from this frozen peer.
// ============================================================================

const FROZEN_SESSION_BINDING_INFO: &[u8; 36] = b"04abb564-eeb9-42b7-8091-4d67cdb4d536";
const FROZEN_MANDATORY_CHANNEL_TOKEN_INFO: &[u8; 20] = b"11947944922982068094";
const FROZEN_NOISE_NN_PROTOCOL_NAME: &[u8; 27] = b"Noise_NN_P256_AESGCM_SHA256";
const FROZEN_PADDING_GRANULARITY: usize = 32;

fn frozen_serialize_assertions(assertions: &BTreeMap<String, Assertion>) -> Vec<u8> {
    let mut out = (assertions.len() as u64).to_le_bytes().to_vec();
    for (id, assertion) in assertions {
        out.extend(id.encode_to_vec());
        out.push(b':');
        out.extend((assertion.content.len() as u64).to_le_bytes());
        out.extend_from_slice(assertion.content.as_slice());
        out.push(b'|');
    }
    out
}

fn frozen_legacy_unprefixed_serialize_assertions(
    assertions: &BTreeMap<String, Assertion>,
) -> Vec<u8> {
    let mut out = Vec::new();
    for (id, assertion) in assertions {
        out.extend_from_slice(id.as_bytes());
        out.push(b':');
        out.extend(assertion.encode_to_vec());
        out.push(b'|');
    }
    out
}

fn frozen_derive_session_binding_token(
    attestation_binding_token: &[u8],
    handshake_hash: &[u8],
) -> [u8; 32] {
    let mut hasher = sha2::Sha256::new();
    hasher.update(attestation_binding_token);
    hasher.update(handshake_hash);
    hasher.update(FROZEN_SESSION_BINDING_INFO);
    hasher.finalize().into()
}

fn frozen_derive_channel_binding_token(handshake_hash: &[u8], info: &[u8]) -> [u8; 32] {
    let info_hash = sha2::Sha256::digest(info);
    let mut hasher = sha2::Sha256::new();
    hasher.update(handshake_hash);
    hasher.update(info_hash);
    hasher.update(FROZEN_MANDATORY_CHANNEL_TOKEN_INFO);
    hasher.finalize().into()
}

fn frozen_build_assertions_map(
    bundle: &GoldenAttestationBundle,
    sk_key_bytes: &[u8; 32],
) -> BTreeMap<String, Assertion> {
    let ee_bytes = bundle.endorsed_evidence().encode_to_vec();
    let sk = signing_key(sk_key_bytes);
    let wrapper = SessionBindingKeyWrapperAssertion {
        public_binding_key: sk.verifying_key().to_sec1_bytes().to_vec(),
        inner_assertion: Some(Assertion { content: ee_bytes.clone() }),
    };
    let mut map = BTreeMap::new();
    map.insert(ENDORSED_EVIDENCE_ASSERTION_ID.to_string(), Assertion { content: ee_bytes });
    map.insert(
        SESSION_KEY_WRAPPED_ASSERTION_ID.to_string(),
        Assertion { content: wrapper.encode_to_vec() },
    );
    map
}

fn frozen_sign_assertion_bindings(
    ee_key_bytes: &[u8; 32],
    sk_key_bytes: &[u8; 32],
    bound_data: &[u8],
) -> BTreeMap<String, SessionBinding> {
    let ee_sig: Signature = signing_key(ee_key_bytes).sign(bound_data);
    let sk_sig: Signature = signing_key(sk_key_bytes).sign(bound_data);
    let mut bindings = BTreeMap::new();
    bindings.insert(
        ENDORSED_EVIDENCE_ASSERTION_ID.to_string(),
        SessionBinding { binding: ee_sig.to_vec() },
    );
    bindings.insert(
        SESSION_KEY_WRAPPED_ASSERTION_ID.to_string(),
        SessionBinding { binding: sk_sig.to_vec() },
    );
    bindings
}

fn frozen_verify_peer_assertion_bindings(
    peer_assertions: &BTreeMap<String, Assertion>,
    peer_bindings: &BTreeMap<String, SessionBinding>,
    peer_ee_key_bytes: &[u8; 32],
    bound_data: &[u8],
) -> anyhow::Result<()> {
    let ee_vk = *signing_key(peer_ee_key_bytes).verifying_key();
    let ee_binding = peer_bindings
        .get(ENDORSED_EVIDENCE_ASSERTION_ID)
        .context("missing peer endorsed_evidence binding")?;
    let ee_sig = Signature::from_slice(&ee_binding.binding)
        .map_err(|e| anyhow!("parsing endorsed_evidence signature: {}", e))?;
    ee_vk
        .verify(bound_data, &ee_sig)
        .map_err(|e| anyhow!("verifying endorsed_evidence signature: {}", e))?;

    let sk_assertion = peer_assertions
        .get(SESSION_KEY_WRAPPED_ASSERTION_ID)
        .context("missing peer session_key_wrapper assertion")?;
    let wrapper = SessionBindingKeyWrapperAssertion::decode(sk_assertion.content.as_slice())
        .context("decoding session_key_wrapper assertion")?;
    let sk_vk = VerifyingKey::from_sec1_bytes(&wrapper.public_binding_key)
        .map_err(|e| anyhow!("parsing wrapper public key: {}", e))?;
    let sk_binding = peer_bindings
        .get(SESSION_KEY_WRAPPED_ASSERTION_ID)
        .context("missing peer session_key_wrapper binding")?;
    let sk_sig = Signature::from_slice(&sk_binding.binding)
        .map_err(|e| anyhow!("parsing session_key_wrapper signature: {}", e))?;
    sk_vk
        .verify(bound_data, &sk_sig)
        .map_err(|e| anyhow!("verifying session_key_wrapper signature: {}", e))?;
    Ok(())
}

struct FrozenNoiseSymmetricState {
    ck: [u8; SYMMETRIC_KEY_LEN],
    h: [u8; SHA256_OUTPUT_LEN],
    k: [u8; SYMMETRIC_KEY_LEN],
    nonce: u32,
}

impl FrozenNoiseSymmetricState {
    fn new_nn() -> Self {
        let mut ck = [0u8; SYMMETRIC_KEY_LEN];
        ck[..FROZEN_NOISE_NN_PROTOCOL_NAME.len()].copy_from_slice(FROZEN_NOISE_NN_PROTOCOL_NAME);
        Self { ck, h: ck, k: [0u8; SYMMETRIC_KEY_LEN], nonce: 0 }
    }

    fn hkdf2(ck: &[u8; SYMMETRIC_KEY_LEN], ikm: &[u8]) -> ([u8; 32], [u8; 32]) {
        let mut out = [0u8; 64];
        hkdf_sha256(ikm, ck, &[], &mut out).expect("deriving hkdf2 keys");
        (out[..32].try_into().unwrap(), out[32..].try_into().unwrap())
    }

    fn mix_hash(&mut self, data: &[u8]) {
        self.h = sha256_two_part(&self.h, data);
    }

    fn mix_key(&mut self, ikm: &[u8]) {
        let (ck, k) = Self::hkdf2(&self.ck, ikm);
        self.ck = ck;
        self.k = k;
        self.nonce = 0;
    }

    fn next_handshake_nonce(&mut self) -> [u8; NONCE_LEN] {
        let mut n = [0u8; NONCE_LEN];
        n[..4].copy_from_slice(&self.nonce.to_be_bytes());
        self.nonce += 1;
        n
    }

    fn encrypt_and_hash(&mut self, plaintext: &[u8]) -> Vec<u8> {
        let mut buf = plaintext.to_vec();
        let nonce = self.next_handshake_nonce();
        aes_256_gcm_seal_in_place(&self.k, &nonce, &self.h, &mut buf);
        self.mix_hash(&buf);
        buf
    }

    fn decrypt_and_hash(&mut self, ciphertext: &[u8]) -> anyhow::Result<Vec<u8>> {
        let aad = self.h;
        self.mix_hash(ciphertext);
        let nonce = self.next_handshake_nonce();
        aes_256_gcm_open_in_place(&self.k, &nonce, &aad, ciphertext.to_vec())
            .map_err(|_| anyhow!("decrypting noise handshake payload"))
    }

    fn split(&self) -> ([u8; 32], [u8; 32]) {
        Self::hkdf2(&self.ck, &[])
    }
}

struct FrozenTransportCipher {
    read_key: [u8; SYMMETRIC_KEY_LEN],
    write_key: [u8; SYMMETRIC_KEY_LEN],
    read_seq: u32,
    write_seq: u32,
}

impl FrozenTransportCipher {
    fn new(read_key: [u8; 32], write_key: [u8; 32]) -> Self {
        Self { read_key, write_key, read_seq: 0, write_seq: 0 }
    }

    fn transport_nonce(seq: u32) -> [u8; NONCE_LEN] {
        let mut nonce = [0u8; NONCE_LEN];
        nonce[NONCE_LEN - 4..].copy_from_slice(&seq.to_be_bytes());
        nonce
    }

    fn encrypt_payload(&mut self, plaintext: &[u8]) -> EncryptedMessage {
        let mut padded_size = plaintext.len() + 1;
        padded_size =
            (padded_size + FROZEN_PADDING_GRANULARITY - 1) & !(FROZEN_PADDING_GRANULARITY - 1);
        let mut buf = Vec::with_capacity(padded_size + 16);
        buf.extend_from_slice(plaintext);
        buf.resize(padded_size, 0u8);
        buf[padded_size - 1] = (padded_size - plaintext.len() - 1) as u8;

        let nonce = Self::transport_nonce(self.write_seq);
        self.write_seq += 1;
        aes_256_gcm_seal_in_place(&self.write_key, &nonce, &[], &mut buf);
        EncryptedMessage { ciphertext: buf, nonce: None, associated_data: None }
    }

    fn decrypt_payload(&mut self, msg: &EncryptedMessage) -> anyhow::Result<Vec<u8>> {
        anyhow::ensure!(msg.nonce.is_none(), "ordered channel must omit explicit nonce");
        anyhow::ensure!(
            msg.associated_data.is_none(),
            "ordered channel must omit explicit associated_data"
        );
        let nonce = Self::transport_nonce(self.read_seq);
        let mut pt = aes_256_gcm_open_in_place(&self.read_key, &nonce, &[], msg.ciphertext.clone())
            .map_err(|_| anyhow!("decrypting transport payload"))?;
        self.read_seq += 1;
        let pad_len = *pt.last().context("missing padding length byte")? as usize;
        anyhow::ensure!(pad_len < pt.len(), "invalid padding length");
        let unpadded_len = pt.len() - pad_len - 1;
        pt.truncate(unpadded_len);
        Ok(pt)
    }
}

struct FrozenNoiseInitiator {
    state: FrozenNoiseSymmetricState,
    e_priv: P256Scalar,
}

impl FrozenNoiseInitiator {
    fn new_deterministic(scalar_bytes: [u8; 32]) -> Self {
        Self {
            state: FrozenNoiseSymmetricState::new_nn(),
            e_priv: P256Scalar::from_bytes(scalar_bytes),
        }
    }

    fn build_initial_handshake_request(&mut self) -> HandshakeRequest {
        self.state.mix_hash(&[0u8; 1]);
        let e_pub = self.e_priv.compute_public_key();
        self.state.mix_hash(&e_pub);
        self.state.mix_key(&e_pub);
        let ciphertext = self.state.encrypt_and_hash(&[]);
        HandshakeRequest {
            r#handshake_type: Some(handshake_request::HandshakeType::NoiseHandshakeMessage(
                NoiseHandshakeMessage {
                    ephemeral_public_key: e_pub.to_vec(),
                    static_public_key: Vec::new(),
                    ciphertext,
                },
            )),
            attestation_bindings: BTreeMap::new(),
            assertion_bindings: BTreeMap::new(),
        }
    }

    fn process_handshake_response(
        &mut self,
        resp: &NoiseHandshakeMessage,
    ) -> anyhow::Result<([u8; 32], FrozenTransportCipher)> {
        let peer_e_pub: &[u8; P256_X962_LEN] = resp
            .ephemeral_public_key
            .as_slice()
            .try_into()
            .map_err(|_| anyhow!("parsing responder ephemeral public key"))?;
        anyhow::ensure!(
            resp.static_public_key.is_empty(),
            "noise NN response must have empty static_public_key"
        );
        let ee = p256_scalar_mult(&self.e_priv, peer_e_pub)
            .map_err(|_| anyhow!("computing initiator ECDH shared secret"))?;
        self.state.mix_hash(&resp.ephemeral_public_key);
        self.state.mix_key(&resp.ephemeral_public_key);
        self.state.mix_key(&ee);
        let pt = self.state.decrypt_and_hash(&resp.ciphertext)?;
        anyhow::ensure!(pt.is_empty(), "noise NN handshake payload must be empty");
        let (write_key, read_key) = self.state.split();
        Ok((self.state.h, FrozenTransportCipher::new(read_key, write_key)))
    }
}

fn frozen_respond_nn_deterministic(
    scalar_bytes: [u8; 32],
    req: &NoiseHandshakeMessage,
) -> anyhow::Result<(NoiseHandshakeMessage, [u8; 32], FrozenTransportCipher)> {
    anyhow::ensure!(
        req.static_public_key.is_empty(),
        "noise NN request must have empty static_public_key"
    );
    let peer_e_pub: &[u8; P256_X962_LEN] = req
        .ephemeral_public_key
        .as_slice()
        .try_into()
        .map_err(|_| anyhow!("parsing initiator ephemeral public key"))?;

    let mut state = FrozenNoiseSymmetricState::new_nn();
    state.mix_hash(&[0u8; 1]);
    state.mix_hash(&req.ephemeral_public_key);
    state.mix_key(&req.ephemeral_public_key);
    let pt = state.decrypt_and_hash(&req.ciphertext)?;
    anyhow::ensure!(pt.is_empty(), "noise NN request payload must be empty");

    let e_priv = P256Scalar::from_bytes(scalar_bytes);
    let e_pub = e_priv.compute_public_key();
    state.mix_hash(&e_pub);
    state.mix_key(&e_pub);
    let ee = p256_scalar_mult(&e_priv, peer_e_pub)
        .map_err(|_| anyhow!("computing responder ECDH shared secret"))?;
    state.mix_key(&ee);
    let ciphertext = state.encrypt_and_hash(&[]);
    let (read_key, write_key) = state.split();
    Ok((
        NoiseHandshakeMessage {
            ephemeral_public_key: e_pub.to_vec(),
            static_public_key: Vec::new(),
            ciphertext,
        },
        state.h,
        FrozenTransportCipher::new(read_key, write_key),
    ))
}

fn wire_encode_req(req: &SessionRequest) -> Vec<u8> {
    req.encode_to_vec()
}

fn wire_decode_req(bytes: &[u8]) -> anyhow::Result<SessionRequest> {
    SessionRequest::decode(bytes).context("decoding SessionRequest")
}

fn wire_encode_resp(resp: &SessionResponse) -> Vec<u8> {
    resp.encode_to_vec()
}

fn wire_decode_resp(bytes: &[u8]) -> anyhow::Result<SessionResponse> {
    SessionResponse::decode(bytes).context("decoding SessionResponse")
}

fn verify_encrypted_exchange_with_server(
    server: &mut ServerSession,
    frozen_cipher: &mut FrozenTransportCipher,
) -> anyhow::Result<()> {
    assert_that!(server.is_open(), eq(true));

    for msg_text in &[b"hello from frozen client 0".as_slice(), b"second client frame 1"] {
        let wire_req = wire_encode_req(&SessionRequest {
            request: Some(session_request::Request::EncryptedMessage(
                frozen_cipher.encrypt_payload(msg_text),
            )),
        });
        server.put_incoming_message(wire_decode_req(&wire_req)?)?;
        let decrypted = server.read()?.context("missing decrypted message on server")?;
        assert_that!(decrypted.plaintext.as_slice(), eq(*msg_text));
    }

    for reply_text in &[b"ack from head server 0".as_slice(), b"second server frame 1"] {
        server.write(PlaintextMessage { plaintext: reply_text.to_vec() })?;
        let wire_resp = wire_encode_resp(
            &server.get_outgoing_message()?.context("getting server encrypted message")?,
        );
        let decoded_resp = wire_decode_resp(&wire_resp)?;
        match decoded_resp.response {
            Some(session_response::Response::EncryptedMessage(enc)) => {
                let pt = frozen_cipher.decrypt_payload(&enc)?;
                assert_that!(pt.as_slice(), eq(*reply_text));
            }
            other => anyhow::bail!("unexpected response variant: {:?}", other),
        }
    }
    Ok(())
}

fn verify_encrypted_exchange_with_client(
    client: &mut ClientSession,
    frozen_cipher: &mut FrozenTransportCipher,
) -> anyhow::Result<()> {
    assert_that!(client.is_open(), eq(true));

    for msg_text in &[b"hello from head client 0".as_slice(), b"second head client frame 1"] {
        client.write(PlaintextMessage { plaintext: msg_text.to_vec() })?;
        let wire_req = wire_encode_req(
            &client.get_outgoing_message()?.context("getting client encrypted message")?,
        );
        let decoded_req = wire_decode_req(&wire_req)?;
        match decoded_req.request {
            Some(session_request::Request::EncryptedMessage(enc)) => {
                let pt = frozen_cipher.decrypt_payload(&enc)?;
                assert_that!(pt.as_slice(), eq(*msg_text));
            }
            other => anyhow::bail!("unexpected request variant: {:?}", other),
        }
    }

    for reply_text in &[b"ack from frozen server 0".as_slice(), b"second frozen server 1"] {
        let wire_resp = wire_encode_resp(&SessionResponse {
            response: Some(session_response::Response::EncryptedMessage(
                frozen_cipher.encrypt_payload(reply_text),
            )),
        });
        client.put_incoming_message(wire_decode_resp(&wire_resp)?)?;
        let decrypted = client.read()?.context("missing decrypted message on client")?;
        assert_that!(decrypted.plaintext.as_slice(), eq(*reply_text));
    }
    Ok(())
}

fn build_head_assertion_bindings(
    bundle: &GoldenAttestationBundle,
    ee_key: &[u8; 32],
    sk_key: &[u8; 32],
    bound_data: &[u8],
) -> anyhow::Result<BTreeMap<String, SessionBinding>> {
    let ee_assertion = create_ee_assertion_generator(bundle, ee_key)
        .generate()
        .context("generating endorsed_evidence bindable assertion")?;
    let sk_assertion = create_sk_wrapped_assertion_generator(bundle, sk_key)
        .generate()
        .context("generating session_key_wrapper bindable assertion")?;

    let mut bindings = BTreeMap::new();
    bindings.insert(
        ENDORSED_EVIDENCE_ASSERTION_ID.to_string(),
        ee_assertion.bind(bound_data).context("binding endorsed_evidence assertion")?,
    );
    bindings.insert(
        SESSION_KEY_WRAPPED_ASSERTION_ID.to_string(),
        sk_assertion.bind(bound_data).context("binding session_key_wrapper assertion")?,
    );
    Ok(bindings)
}

// ============================================================================
// Group 1: Pinned Golden Wire-Byte & Cryptographic Token Tests
// ============================================================================

#[googletest::test]
fn golden_attest_messages_and_tokens_assertions() -> anyhow::Result<()> {
    let rk_bundle = GoldenAttestationBundle::load_rk_release();
    let oc_bundle = GoldenAttestationBundle::load_oc_release();

    let client_cfg = add_peer_assertion_verifiers(
        add_self_assertions(
            SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
            &rk_bundle,
            &CLIENT_EE_BINDING_KEY_BYTES,
            &CLIENT_SK_BINDING_KEY_BYTES,
        ),
        &oc_bundle,
        &SERVER_EE_BINDING_KEY_BYTES,
    )
    .build();
    let server_cfg = add_peer_assertion_verifiers(
        add_self_assertions(
            SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
            &oc_bundle,
            &SERVER_EE_BINDING_KEY_BYTES,
            &SERVER_SK_BINDING_KEY_BYTES,
        ),
        &rk_bundle,
        &CLIENT_EE_BINDING_KEY_BYTES,
    )
    .build();

    let mut client = ClientSession::create(client_cfg).context("creating client session")?;
    let mut server = ServerSession::create(server_cfg).context("creating server session")?;

    let golden_attest_req = read_testdata_bytes(GOLDEN_ATTEST_REQUEST_ASSERTIONS_PATH);
    let golden_attest_resp = read_testdata_bytes(GOLDEN_ATTEST_RESPONSE_ASSERTIONS_PATH);

    let actual_req_bytes =
        wire_encode_req(&client.get_outgoing_message()?.context("getting client attest request")?);
    assert_that!(actual_req_bytes, eq(&golden_attest_req));

    // Feed the golden AttestRequest wire bytes directly into ServerSession (runs
    // AMD SEV-SNP RK verification).
    server
        .put_incoming_message(wire_decode_req(&golden_attest_req)?)
        .context("putting golden attest request into server")?;

    let actual_resp_bytes = wire_encode_resp(
        &server.get_outgoing_message()?.context("getting server attest response")?,
    );
    assert_that!(actual_resp_bytes, eq(&golden_attest_resp));

    // Feed the golden AttestResponse wire bytes directly into ClientSession (runs
    // AMD SEV-SNP OC verification).
    client
        .put_incoming_message(wire_decode_resp(&golden_attest_resp)?)
        .context("putting golden attest response into client")?;

    // Pin oak_session's own AttestationHandler binding token accumulation (bidi and
    // both unidirectional directions) against the golden .bin files.
    let bidi_client_handler_cfg = add_peer_assertion_verifiers(
        add_self_assertions(
            SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
            &rk_bundle,
            &CLIENT_EE_BINDING_KEY_BYTES,
            &CLIENT_SK_BINDING_KEY_BYTES,
        ),
        &oc_bundle,
        &SERVER_EE_BINDING_KEY_BYTES,
    )
    .build()
    .attestation_handler_config;
    let mut bidi_client_attester = ClientAttestationHandler::create(bidi_client_handler_cfg)
        .context("creating bidi client attestation handler")?;
    let attest_req_proto = bidi_client_attester
        .get_outgoing_message()?
        .context("getting bidi client attest request")?;
    let bidi_server_handler_cfg = add_peer_assertion_verifiers(
        add_self_assertions(
            SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
            &oc_bundle,
            &SERVER_EE_BINDING_KEY_BYTES,
            &SERVER_SK_BINDING_KEY_BYTES,
        ),
        &rk_bundle,
        &CLIENT_EE_BINDING_KEY_BYTES,
    )
    .build()
    .attestation_handler_config;
    let mut bidi_server_attester = ServerAttestationHandler::create(bidi_server_handler_cfg)
        .context("creating bidi server attestation handler")?;
    bidi_server_attester
        .put_incoming_message(attest_req_proto)
        .context("putting bidi attest request into server handler")?;
    let attest_resp_proto = bidi_server_attester
        .get_outgoing_message()?
        .context("getting bidi server attest response")?;
    bidi_client_attester
        .put_incoming_message(attest_resp_proto)
        .context("putting bidi attest response into client handler")?;

    let head_bidi_client_token =
        bidi_client_attester.take_attestation_state()?.attestation_binding_token;
    let head_bidi_server_token =
        bidi_server_attester.take_attestation_state()?.attestation_binding_token;
    let golden_bidi_token = read_testdata_bytes(GOLDEN_BIDI_ATTESTATION_BINDING_TOKEN_PATH);
    assert_that!(head_bidi_client_token, eq(&golden_bidi_token));
    assert_that!(head_bidi_server_token, eq(&golden_bidi_token));

    let uni_server_handler_cfg = add_self_assertions(
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN),
        &oc_bundle,
        &SERVER_EE_BINDING_KEY_BYTES,
        &SERVER_SK_BINDING_KEY_BYTES,
    )
    .build()
    .attestation_handler_config;
    let mut uni_server_attester = ServerAttestationHandler::create(uni_server_handler_cfg)
        .context("creating unidirectional server attestation handler")?;
    uni_server_attester
        .put_incoming_message(AttestRequest::default())
        .context("putting empty attest request into server handler")?;
    let _ = uni_server_attester.get_outgoing_message()?;
    let head_uni_server_token =
        uni_server_attester.take_attestation_state()?.attestation_binding_token;
    assert_that!(
        head_uni_server_token,
        eq(&read_testdata_bytes(GOLDEN_UNI_SERVER_ATTESTATION_BINDING_TOKEN_PATH))
    );

    let uni_client_handler_cfg = add_self_assertions(
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN),
        &rk_bundle,
        &CLIENT_EE_BINDING_KEY_BYTES,
        &CLIENT_SK_BINDING_KEY_BYTES,
    )
    .build()
    .attestation_handler_config;
    let mut uni_client_attester = ClientAttestationHandler::create(uni_client_handler_cfg)
        .context("creating unidirectional client attestation handler")?;
    let _ = uni_client_attester.get_outgoing_message()?;
    uni_client_attester
        .put_incoming_message(AttestResponse::default())
        .context("putting empty attest response into client handler")?;
    let head_uni_client_token =
        uni_client_attester.take_attestation_state()?.attestation_binding_token;
    assert_that!(
        head_uni_client_token,
        eq(&read_testdata_bytes(GOLDEN_UNI_CLIENT_ATTESTATION_BINDING_TOKEN_PATH))
    );

    // Pin oak_session's create_session_binding_token and BindableAssertion::bind
    // outputs against the golden follow-up HandshakeRequest wire bytes.
    let head_bound_data = create_session_binding_token(&golden_bidi_token, &PINNED_HANDSHAKE_HASH);
    let frozen_bound_data =
        frozen_derive_session_binding_token(&golden_bidi_token, &PINNED_HANDSHAKE_HASH);
    assert_that!(head_bound_data.as_slice(), eq(frozen_bound_data.as_slice()));

    let head_followup = SessionRequest {
        request: Some(session_request::Request::HandshakeRequest(HandshakeRequest {
            r#handshake_type: None,
            attestation_bindings: BTreeMap::new(),
            assertion_bindings: build_head_assertion_bindings(
                &rk_bundle,
                &CLIENT_EE_BINDING_KEY_BYTES,
                &CLIENT_SK_BINDING_KEY_BYTES,
                &head_bound_data,
            )?,
        })),
    };
    assert_that!(
        wire_encode_req(&head_followup),
        eq(&read_testdata_bytes(GOLDEN_HANDSHAKE_FOLLOWUP_ASSERTIONS_PATH))
    );

    Ok(())
}

#[googletest::test]
fn golden_attest_messages_legacy_endorsed_evidence() -> anyhow::Result<()> {
    let rk_bundle = GoldenAttestationBundle::load_rk_release();
    let oc_bundle = GoldenAttestationBundle::load_oc_release();

    let client_cfg = SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
        .add_self_attester_ref(
            LEGACY_ATTESTATION_ID.to_string(),
            &(Arc::new(PrebuiltAttester { evidence: rk_bundle.evidence.clone() })
                as Arc<dyn Attester>),
        )
        .add_self_endorser_ref(
            LEGACY_ATTESTATION_ID.to_string(),
            &(Arc::new(PrebuiltEndorser { endorsements: rk_bundle.endorsements.clone() })
                as Arc<dyn Endorser>),
        )
        .add_session_binder_ref(
            LEGACY_ATTESTATION_ID.to_string(),
            &signature_binder(&CLIENT_LEGACY_BINDING_KEY_BYTES),
        )
        .add_peer_verifier_with_binding_verifier_provider_ref(
            LEGACY_ATTESTATION_ID.to_string(),
            &oc_bundle.create_verifier(),
            &binding_verifier_provider(&SERVER_LEGACY_BINDING_KEY_BYTES),
        )
        .build();
    let server_cfg = SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
        .add_self_attester_ref(
            LEGACY_ATTESTATION_ID.to_string(),
            &(Arc::new(PrebuiltAttester { evidence: oc_bundle.evidence.clone() })
                as Arc<dyn Attester>),
        )
        .add_self_endorser_ref(
            LEGACY_ATTESTATION_ID.to_string(),
            &(Arc::new(PrebuiltEndorser { endorsements: oc_bundle.endorsements.clone() })
                as Arc<dyn Endorser>),
        )
        .add_session_binder_ref(
            LEGACY_ATTESTATION_ID.to_string(),
            &signature_binder(&SERVER_LEGACY_BINDING_KEY_BYTES),
        )
        .add_peer_verifier_with_binding_verifier_provider_ref(
            LEGACY_ATTESTATION_ID.to_string(),
            &rk_bundle.create_verifier(),
            &binding_verifier_provider(&CLIENT_LEGACY_BINDING_KEY_BYTES),
        )
        .build();

    let mut client = ClientSession::create(client_cfg).context("creating legacy client session")?;
    let mut server = ServerSession::create(server_cfg).context("creating legacy server session")?;

    let golden_req = read_testdata_bytes(GOLDEN_ATTEST_REQUEST_LEGACY_PATH);
    let golden_resp = read_testdata_bytes(GOLDEN_ATTEST_RESPONSE_LEGACY_PATH);

    let actual_req = wire_encode_req(
        &client.get_outgoing_message()?.context("getting legacy client attest request")?,
    );
    assert_that!(actual_req, eq(&golden_req));

    server
        .put_incoming_message(wire_decode_req(&golden_req)?)
        .context("putting golden legacy attest request into server")?;
    let actual_resp = wire_encode_resp(
        &server.get_outgoing_message()?.context("getting legacy server attest response")?,
    );
    assert_that!(actual_resp, eq(&golden_resp));

    client
        .put_incoming_message(wire_decode_resp(&golden_resp)?)
        .context("putting golden legacy attest response into client")?;
    Ok(())
}

#[googletest::test]
fn golden_handshake_and_encrypted_transport_frames() -> anyhow::Result<()> {
    let mut initiator = FrozenNoiseInitiator::new_deterministic(FROZEN_CLIENT_EPHEMERAL_SCALAR);
    let hs_init = SessionRequest {
        request: Some(session_request::Request::HandshakeRequest(
            initiator.build_initial_handshake_request(),
        )),
    };
    assert_that!(
        wire_encode_req(&hs_init),
        eq(&read_testdata_bytes(GOLDEN_HANDSHAKE_REQUEST_NN_INIT_PATH))
    );

    let golden_enc_req_bytes = read_testdata_bytes(GOLDEN_ENCRYPTED_REQUEST_MSG0_PATH);
    let golden_enc_resp_bytes = read_testdata_bytes(GOLDEN_ENCRYPTED_RESPONSE_MSG0_PATH);

    // Check both OrderedChannelEncryptor and FrozenTransportCipher produce and
    // decrypt the exact golden encrypted frames.
    let mut head_client_enc = OrderedChannelEncryptor::try_from(OrderedCrypter::new(
        &PINNED_SERVER_WRITE_KEY,
        &PINNED_CLIENT_WRITE_KEY,
    ))
    .context("creating client OrderedChannelEncryptor")?;
    let mut head_server_enc = OrderedChannelEncryptor::try_from(OrderedCrypter::new(
        &PINNED_CLIENT_WRITE_KEY,
        &PINNED_SERVER_WRITE_KEY,
    ))
    .context("creating server OrderedChannelEncryptor")?;

    let mut frozen_client_cipher =
        FrozenTransportCipher::new(PINNED_SERVER_WRITE_KEY, PINNED_CLIENT_WRITE_KEY);
    let mut frozen_server_cipher =
        FrozenTransportCipher::new(PINNED_CLIENT_WRITE_KEY, PINNED_SERVER_WRITE_KEY);

    let actual_head_req = SessionRequest {
        request: Some(session_request::Request::EncryptedMessage(
            head_client_enc
                .encrypt(Payload::from(PlaintextMessage {
                    plaintext: b"pinned wire request 0".to_vec(),
                }))
                .context("encrypting pinned request with OrderedChannelEncryptor")?
                .into(),
        )),
    };
    let actual_frozen_req = SessionRequest {
        request: Some(session_request::Request::EncryptedMessage(
            frozen_client_cipher.encrypt_payload(b"pinned wire request 0"),
        )),
    };
    assert_that!(wire_encode_req(&actual_head_req), eq(&golden_enc_req_bytes));
    assert_that!(wire_encode_req(&actual_frozen_req), eq(&golden_enc_req_bytes));

    let actual_head_resp = SessionResponse {
        response: Some(session_response::Response::EncryptedMessage(
            head_server_enc
                .encrypt(Payload::from(PlaintextMessage {
                    plaintext: b"pinned wire response 0".to_vec(),
                }))
                .context("encrypting pinned response with OrderedChannelEncryptor")?
                .into(),
        )),
    };
    let actual_frozen_resp = SessionResponse {
        response: Some(session_response::Response::EncryptedMessage(
            frozen_server_cipher.encrypt_payload(b"pinned wire response 0"),
        )),
    };
    assert_that!(wire_encode_resp(&actual_head_resp), eq(&golden_enc_resp_bytes));
    assert_that!(wire_encode_resp(&actual_frozen_resp), eq(&golden_enc_resp_bytes));

    match wire_decode_req(&golden_enc_req_bytes)?.request {
        Some(session_request::Request::EncryptedMessage(enc)) => {
            let frozen_pt = frozen_server_cipher.decrypt_payload(&enc)?;
            assert_that!(frozen_pt.as_slice(), eq(b"pinned wire request 0".as_slice()));
            let head_pt: PlaintextMessage = head_server_enc
                .decrypt(Payload::from(enc))
                .context("decrypting golden request with OrderedChannelEncryptor")?
                .into();
            assert_that!(head_pt.plaintext.as_slice(), eq(b"pinned wire request 0".as_slice()));
        }
        other => anyhow::bail!("unexpected request variant: {:?}", other),
    }
    match wire_decode_resp(&golden_enc_resp_bytes)?.response {
        Some(session_response::Response::EncryptedMessage(enc)) => {
            let frozen_pt = frozen_client_cipher.decrypt_payload(&enc)?;
            assert_that!(frozen_pt.as_slice(), eq(b"pinned wire response 0".as_slice()));
            let head_pt: PlaintextMessage = head_client_enc
                .decrypt(Payload::from(enc))
                .context("decrypting golden response with OrderedChannelEncryptor")?
                .into();
            assert_that!(head_pt.plaintext.as_slice(), eq(b"pinned wire response 0".as_slice()));
        }
        other => anyhow::bail!("unexpected response variant: {:?}", other),
    }

    Ok(())
}

// ============================================================================
// Group 2: End-to-End Wire Protocol Interop (Unidirectional & Bidirectional)
// ============================================================================

#[googletest::test]
fn wire_unidirectional_server_attested_assertions_frozen_client_to_head_server()
-> anyhow::Result<()> {
    let oc_bundle = GoldenAttestationBundle::load_oc_release();
    let server_cfg = add_self_assertions(
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN),
        &oc_bundle,
        &SERVER_EE_BINDING_KEY_BYTES,
        &SERVER_SK_BINDING_KEY_BYTES,
    )
    .build();
    let mut server = ServerSession::create(server_cfg).context("creating server session")?;

    // Step 1: Frozen client sends empty AttestRequest on wire; ServerSession
    // replies with golden AttestResponse.
    let empty_req_wire = wire_encode_req(&SessionRequest {
        request: Some(session_request::Request::AttestRequest(AttestRequest::default())),
    });
    server
        .put_incoming_message(wire_decode_req(&empty_req_wire)?)
        .context("putting empty attest request into server")?;
    let attest_resp_wire = wire_encode_resp(
        &server.get_outgoing_message()?.context("getting server attest response")?,
    );
    assert_that!(
        attest_resp_wire,
        eq(&read_testdata_bytes(GOLDEN_ATTEST_RESPONSE_ASSERTIONS_PATH))
    );

    let server_assertions = match wire_decode_resp(&attest_resp_wire)?.response {
        Some(session_response::Response::AttestResponse(resp)) => resp.assertions,
        other => anyhow::bail!("unexpected response variant: {:?}", other),
    };

    // Step 2: Replay golden HandshakeRequest #1 from disk into ServerSession.
    let mut initiator = FrozenNoiseInitiator::new_deterministic(FROZEN_CLIENT_EPHEMERAL_SCALAR);
    let _ = initiator.build_initial_handshake_request();
    let golden_hs_init_wire = read_testdata_bytes(GOLDEN_HANDSHAKE_REQUEST_NN_INIT_PATH);
    server
        .put_incoming_message(wire_decode_req(&golden_hs_init_wire)?)
        .context("putting golden initial handshake request into server")?;

    let hs_resp_wire = wire_encode_resp(
        &server.get_outgoing_message()?.context("getting server handshake response")?,
    );
    let hs_resp = match wire_decode_resp(&hs_resp_wire)?.response {
        Some(session_response::Response::HandshakeResponse(r)) => r,
        other => anyhow::bail!("unexpected response variant: {:?}", other),
    };
    let noise_msg = match hs_resp.r#handshake_type {
        Some(handshake_response::HandshakeType::NoiseHandshakeMessage(m)) => m,
        None => anyhow::bail!("missing NoiseHandshakeMessage"),
    };
    let (handshake_hash, mut frozen_cipher) = initiator.process_handshake_response(&noise_msg)?;

    // Verify server's assertion bindings against pinned
    // uni_server_attestation_binding_token.bin.
    let uni_server_token = read_testdata_bytes(GOLDEN_UNI_SERVER_ATTESTATION_BINDING_TOKEN_PATH);
    let bound_data = frozen_derive_session_binding_token(&uni_server_token, &handshake_hash);
    frozen_verify_peer_assertion_bindings(
        &server_assertions,
        &hs_resp.assertion_bindings,
        &SERVER_EE_BINDING_KEY_BYTES,
        &bound_data,
    )?;

    // Unidirectional server-attested requires no 3rd handshake message; server is
    // immediately open.
    verify_encrypted_exchange_with_server(&mut server, &mut frozen_cipher)?;
    assert_that!(
        server.get_session_binding_token(CHANNEL_BINDING_INFO)?.as_slice(),
        eq(frozen_derive_channel_binding_token(&handshake_hash, CHANNEL_BINDING_INFO).as_slice())
    );
    Ok(())
}

#[googletest::test]
fn wire_unidirectional_server_attested_assertions_head_client_to_frozen_server()
-> anyhow::Result<()> {
    let oc_bundle = GoldenAttestationBundle::load_oc_release();
    let client_cfg = add_peer_assertion_verifiers(
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN),
        &oc_bundle,
        &SERVER_EE_BINDING_KEY_BYTES,
    )
    .build();
    let mut client = ClientSession::create(client_cfg).context("creating client session")?;

    // Step 1: ClientSession emits empty AttestRequest; Frozen server replays
    // golden AttestResponse from disk.
    let attest_req_wire =
        wire_encode_req(&client.get_outgoing_message()?.context("getting client attest request")?);
    let attest_req = match wire_decode_req(&attest_req_wire)?.request {
        Some(session_request::Request::AttestRequest(r)) => r,
        other => anyhow::bail!("unexpected request variant: {:?}", other),
    };
    assert_that!(attest_req.assertions, is_empty());
    assert_that!(attest_req.endorsed_evidence, is_empty());

    let golden_attest_resp_wire = read_testdata_bytes(GOLDEN_ATTEST_RESPONSE_ASSERTIONS_PATH);
    client
        .put_incoming_message(wire_decode_resp(&golden_attest_resp_wire)?)
        .context("putting golden attest response into client")?;

    // Step 2: ClientSession sends HandshakeRequest; Frozen server responds with
    // assertion_bindings.
    let hs_req_wire = wire_encode_req(
        &client.get_outgoing_message()?.context("getting client handshake request")?,
    );
    let hs_req = match wire_decode_req(&hs_req_wire)?.request {
        Some(session_request::Request::HandshakeRequest(r)) => r,
        other => anyhow::bail!("unexpected request variant: {:?}", other),
    };
    let noise_req = match hs_req.r#handshake_type {
        Some(handshake_request::HandshakeType::NoiseHandshakeMessage(m)) => m,
        None => anyhow::bail!("missing NoiseHandshakeMessage"),
    };
    let (noise_resp, handshake_hash, mut frozen_cipher) =
        frozen_respond_nn_deterministic(FROZEN_SERVER_EPHEMERAL_SCALAR, &noise_req)?;

    let uni_server_token = read_testdata_bytes(GOLDEN_UNI_SERVER_ATTESTATION_BINDING_TOKEN_PATH);
    let bound_data = frozen_derive_session_binding_token(&uni_server_token, &handshake_hash);
    let hs_resp_wire = wire_encode_resp(&SessionResponse {
        response: Some(session_response::Response::HandshakeResponse(HandshakeResponse {
            r#handshake_type: Some(handshake_response::HandshakeType::NoiseHandshakeMessage(
                noise_resp,
            )),
            attestation_bindings: BTreeMap::new(),
            assertion_bindings: frozen_sign_assertion_bindings(
                &SERVER_EE_BINDING_KEY_BYTES,
                &SERVER_SK_BINDING_KEY_BYTES,
                &bound_data,
            ),
        })),
    });
    client
        .put_incoming_message(wire_decode_resp(&hs_resp_wire)?)
        .context("putting handshake response into client")?;

    verify_encrypted_exchange_with_client(&mut client, &mut frozen_cipher)?;
    assert_that!(
        client.get_session_binding_token(CHANNEL_BINDING_INFO)?.as_slice(),
        eq(frozen_derive_channel_binding_token(&handshake_hash, CHANNEL_BINDING_INFO).as_slice())
    );
    Ok(())
}

#[googletest::test]
fn wire_unidirectional_client_attested_assertions_both_directions() -> anyhow::Result<()> {
    let rk_bundle = GoldenAttestationBundle::load_rk_release();

    // Direction A: Frozen client (replaying golden RK AttestRequest + golden
    // HandshakeRequest) -> HEAD ServerSession.
    {
        let server_cfg = add_peer_assertion_verifiers(
            SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN),
            &rk_bundle,
            &CLIENT_EE_BINDING_KEY_BYTES,
        )
        .build();
        let mut server = ServerSession::create(server_cfg).context("creating server session")?;

        let golden_req_wire = read_testdata_bytes(GOLDEN_ATTEST_REQUEST_ASSERTIONS_PATH);
        server
            .put_incoming_message(wire_decode_req(&golden_req_wire)?)
            .context("putting golden attest request into server")?;
        let attest_resp_wire = wire_encode_resp(
            &server.get_outgoing_message()?.context("getting empty server attest response")?,
        );
        match wire_decode_resp(&attest_resp_wire)?.response {
            Some(session_response::Response::AttestResponse(r)) => {
                assert_that!(r.assertions, is_empty());
                assert_that!(r.endorsed_evidence, is_empty());
            }
            other => anyhow::bail!("unexpected response variant: {:?}", other),
        }

        let mut initiator = FrozenNoiseInitiator::new_deterministic(FROZEN_CLIENT_EPHEMERAL_SCALAR);
        let _ = initiator.build_initial_handshake_request();
        server
            .put_incoming_message(wire_decode_req(&read_testdata_bytes(
                GOLDEN_HANDSHAKE_REQUEST_NN_INIT_PATH,
            ))?)
            .context("putting golden handshake request into server")?;

        let hs_resp_wire = wire_encode_resp(
            &server.get_outgoing_message()?.context("getting server handshake response")?,
        );
        assert_that!(server.is_open(), eq(false));
        let noise_resp = match wire_decode_resp(&hs_resp_wire)?.response {
            Some(session_response::Response::HandshakeResponse(HandshakeResponse {
                r#handshake_type: Some(handshake_response::HandshakeType::NoiseHandshakeMessage(m)),
                ..
            })) => m,
            other => anyhow::bail!("unexpected response variant: {:?}", other),
        };
        let (handshake_hash, mut frozen_cipher) =
            initiator.process_handshake_response(&noise_resp)?;

        let uni_client_token =
            read_testdata_bytes(GOLDEN_UNI_CLIENT_ATTESTATION_BINDING_TOKEN_PATH);
        let bound_data = frozen_derive_session_binding_token(&uni_client_token, &handshake_hash);
        let followup_wire = wire_encode_req(&SessionRequest {
            request: Some(session_request::Request::HandshakeRequest(HandshakeRequest {
                r#handshake_type: None,
                attestation_bindings: BTreeMap::new(),
                assertion_bindings: frozen_sign_assertion_bindings(
                    &CLIENT_EE_BINDING_KEY_BYTES,
                    &CLIENT_SK_BINDING_KEY_BYTES,
                    &bound_data,
                ),
            })),
        });
        server
            .put_incoming_message(wire_decode_req(&followup_wire)?)
            .context("putting client handshake followup into server")?;
        assert_that!(server.get_outgoing_message()?, none());
        verify_encrypted_exchange_with_server(&mut server, &mut frozen_cipher)?;
        assert_that!(
            server.get_session_binding_token(CHANNEL_BINDING_INFO)?.as_slice(),
            eq(frozen_derive_channel_binding_token(&handshake_hash, CHANNEL_BINDING_INFO)
                .as_slice())
        );
    }

    // Direction B: HEAD ClientSession (SelfUnidirectional) -> Frozen server.
    {
        let client_cfg = add_self_assertions(
            SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN),
            &rk_bundle,
            &CLIENT_EE_BINDING_KEY_BYTES,
            &CLIENT_SK_BINDING_KEY_BYTES,
        )
        .build();
        let mut client = ClientSession::create(client_cfg).context("creating client session")?;

        let req_wire = wire_encode_req(
            &client.get_outgoing_message()?.context("getting client attest request")?,
        );
        assert_that!(req_wire, eq(&read_testdata_bytes(GOLDEN_ATTEST_REQUEST_ASSERTIONS_PATH)));
        let client_assertions = match wire_decode_req(&req_wire)?.request {
            Some(session_request::Request::AttestRequest(r)) => r.assertions,
            other => anyhow::bail!("unexpected request variant: {:?}", other),
        };

        let empty_resp_wire = wire_encode_resp(&SessionResponse {
            response: Some(session_response::Response::AttestResponse(AttestResponse::default())),
        });
        client
            .put_incoming_message(wire_decode_resp(&empty_resp_wire)?)
            .context("putting empty attest response into client")?;

        let hs_req_wire = wire_encode_req(
            &client.get_outgoing_message()?.context("getting client handshake request")?,
        );
        let noise_req = match wire_decode_req(&hs_req_wire)?.request {
            Some(session_request::Request::HandshakeRequest(HandshakeRequest {
                r#handshake_type: Some(handshake_request::HandshakeType::NoiseHandshakeMessage(m)),
                ..
            })) => m,
            other => anyhow::bail!("unexpected request variant: {:?}", other),
        };
        let (noise_resp, handshake_hash, mut frozen_cipher) =
            frozen_respond_nn_deterministic(FROZEN_SERVER_EPHEMERAL_SCALAR, &noise_req)?;

        let hs_resp_wire = wire_encode_resp(&SessionResponse {
            response: Some(session_response::Response::HandshakeResponse(HandshakeResponse {
                r#handshake_type: Some(handshake_response::HandshakeType::NoiseHandshakeMessage(
                    noise_resp,
                )),
                attestation_bindings: BTreeMap::new(),
                assertion_bindings: BTreeMap::new(),
            })),
        });
        client
            .put_incoming_message(wire_decode_resp(&hs_resp_wire)?)
            .context("putting handshake response into client")?;
        assert_that!(client.is_open(), eq(false));

        let followup_wire = wire_encode_req(
            &client.get_outgoing_message()?.context("getting client handshake followup")?,
        );
        let followup = match wire_decode_req(&followup_wire)?.request {
            Some(session_request::Request::HandshakeRequest(r)) => r,
            other => anyhow::bail!("unexpected request variant: {:?}", other),
        };
        assert_that!(followup.r#handshake_type, none());
        assert_that!(followup.attestation_bindings, is_empty());

        let uni_client_token =
            read_testdata_bytes(GOLDEN_UNI_CLIENT_ATTESTATION_BINDING_TOKEN_PATH);
        let bound_data = frozen_derive_session_binding_token(&uni_client_token, &handshake_hash);
        frozen_verify_peer_assertion_bindings(
            &client_assertions,
            &followup.assertion_bindings,
            &CLIENT_EE_BINDING_KEY_BYTES,
            &bound_data,
        )?;

        verify_encrypted_exchange_with_client(&mut client, &mut frozen_cipher)?;
        assert_that!(
            client.get_session_binding_token(CHANNEL_BINDING_INFO)?.as_slice(),
            eq(frozen_derive_channel_binding_token(&handshake_hash, CHANNEL_BINDING_INFO)
                .as_slice())
        );
    }

    Ok(())
}

#[googletest::test]
fn wire_bidirectional_assertions_frozen_client_to_head_server() -> anyhow::Result<()> {
    let rk_bundle = GoldenAttestationBundle::load_rk_release();
    let oc_bundle = GoldenAttestationBundle::load_oc_release();

    let server_cfg = add_peer_assertion_verifiers(
        add_self_assertions(
            SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
            &oc_bundle,
            &SERVER_EE_BINDING_KEY_BYTES,
            &SERVER_SK_BINDING_KEY_BYTES,
        ),
        &rk_bundle,
        &CLIENT_EE_BINDING_KEY_BYTES,
    )
    .build();
    let mut server = ServerSession::create(server_cfg).context("creating bidi server session")?;

    // 1. Replay golden AttestRequest (RK client attestation) into ServerSession;
    //    check golden AttestResponse.
    let golden_req_wire = read_testdata_bytes(GOLDEN_ATTEST_REQUEST_ASSERTIONS_PATH);
    server
        .put_incoming_message(wire_decode_req(&golden_req_wire)?)
        .context("putting golden attest request into bidi server")?;
    let resp_wire = wire_encode_resp(
        &server.get_outgoing_message()?.context("getting bidi server attest response")?,
    );
    assert_that!(resp_wire, eq(&read_testdata_bytes(GOLDEN_ATTEST_RESPONSE_ASSERTIONS_PATH)));

    let server_assertions = match wire_decode_resp(&resp_wire)?.response {
        Some(session_response::Response::AttestResponse(r)) => r.assertions,
        other => anyhow::bail!("unexpected response variant: {:?}", other),
    };

    // 2. Replay golden initial HandshakeRequest into ServerSession.
    let mut initiator = FrozenNoiseInitiator::new_deterministic(FROZEN_CLIENT_EPHEMERAL_SCALAR);
    let _ = initiator.build_initial_handshake_request();
    server
        .put_incoming_message(wire_decode_req(&read_testdata_bytes(
            GOLDEN_HANDSHAKE_REQUEST_NN_INIT_PATH,
        ))?)
        .context("putting golden handshake request into bidi server")?;

    let hs_resp_wire = wire_encode_resp(
        &server.get_outgoing_message()?.context("getting bidi server handshake response")?,
    );
    assert_that!(server.is_open(), eq(false));
    let hs_resp = match wire_decode_resp(&hs_resp_wire)?.response {
        Some(session_response::Response::HandshakeResponse(r)) => r,
        other => anyhow::bail!("unexpected response variant: {:?}", other),
    };
    let noise_resp = match hs_resp.r#handshake_type {
        Some(handshake_response::HandshakeType::NoiseHandshakeMessage(m)) => m,
        None => anyhow::bail!("missing NoiseHandshakeMessage"),
    };
    let (handshake_hash, mut frozen_cipher) = initiator.process_handshake_response(&noise_resp)?;

    // Verify server's assertion bindings over bidi_attestation_binding_token
    // (client || server).
    let bidi_token = read_testdata_bytes(GOLDEN_BIDI_ATTESTATION_BINDING_TOKEN_PATH);
    let bound_data = frozen_derive_session_binding_token(&bidi_token, &handshake_hash);
    frozen_verify_peer_assertion_bindings(
        &server_assertions,
        &hs_resp.assertion_bindings,
        &SERVER_EE_BINDING_KEY_BYTES,
        &bound_data,
    )?;

    // 3. Frozen client sends 3rd handshake message (client assertion_bindings over
    //    same bidi_token).
    let followup_wire = wire_encode_req(&SessionRequest {
        request: Some(session_request::Request::HandshakeRequest(HandshakeRequest {
            r#handshake_type: None,
            attestation_bindings: BTreeMap::new(),
            assertion_bindings: frozen_sign_assertion_bindings(
                &CLIENT_EE_BINDING_KEY_BYTES,
                &CLIENT_SK_BINDING_KEY_BYTES,
                &bound_data,
            ),
        })),
    });
    server
        .put_incoming_message(wire_decode_req(&followup_wire)?)
        .context("putting client handshake followup into bidi server")?;
    assert_that!(server.get_outgoing_message()?, none());

    // 4. Encrypted bidirectional application data + channel binding token check.
    verify_encrypted_exchange_with_server(&mut server, &mut frozen_cipher)?;
    assert_that!(
        server.get_session_binding_token(CHANNEL_BINDING_INFO)?.as_slice(),
        eq(frozen_derive_channel_binding_token(&handshake_hash, CHANNEL_BINDING_INFO).as_slice())
    );
    Ok(())
}

#[googletest::test]
fn wire_bidirectional_assertions_head_client_to_frozen_server() -> anyhow::Result<()> {
    let rk_bundle = GoldenAttestationBundle::load_rk_release();
    let oc_bundle = GoldenAttestationBundle::load_oc_release();

    let client_cfg = add_peer_assertion_verifiers(
        add_self_assertions(
            SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
            &rk_bundle,
            &CLIENT_EE_BINDING_KEY_BYTES,
            &CLIENT_SK_BINDING_KEY_BYTES,
        ),
        &oc_bundle,
        &SERVER_EE_BINDING_KEY_BYTES,
    )
    .build();
    let mut client = ClientSession::create(client_cfg).context("creating bidi client session")?;

    // 1. ClientSession emits exact golden AttestRequest; Frozen server replies with
    //    golden AttestResponse.
    let req_wire = wire_encode_req(
        &client.get_outgoing_message()?.context("getting bidi client attest request")?,
    );
    assert_that!(req_wire, eq(&read_testdata_bytes(GOLDEN_ATTEST_REQUEST_ASSERTIONS_PATH)));
    let client_assertions = match wire_decode_req(&req_wire)?.request {
        Some(session_request::Request::AttestRequest(r)) => r.assertions,
        other => anyhow::bail!("unexpected request variant: {:?}", other),
    };

    client
        .put_incoming_message(wire_decode_resp(&read_testdata_bytes(
            GOLDEN_ATTEST_RESPONSE_ASSERTIONS_PATH,
        ))?)
        .context("putting golden attest response into bidi client")?;

    // 2. ClientSession sends initial HandshakeRequest; Frozen server replies with
    //    assertion_bindings.
    let hs_req_wire = wire_encode_req(
        &client.get_outgoing_message()?.context("getting bidi client handshake request")?,
    );
    let noise_req = match wire_decode_req(&hs_req_wire)?.request {
        Some(session_request::Request::HandshakeRequest(HandshakeRequest {
            r#handshake_type: Some(handshake_request::HandshakeType::NoiseHandshakeMessage(m)),
            attestation_bindings,
            assertion_bindings,
        })) => {
            assert_that!(attestation_bindings, is_empty());
            assert_that!(assertion_bindings, is_empty());
            m
        }
        other => anyhow::bail!("unexpected request variant: {:?}", other),
    };
    let (noise_resp, handshake_hash, mut frozen_cipher) =
        frozen_respond_nn_deterministic(FROZEN_SERVER_EPHEMERAL_SCALAR, &noise_req)?;

    let bidi_token = read_testdata_bytes(GOLDEN_BIDI_ATTESTATION_BINDING_TOKEN_PATH);
    let bound_data = frozen_derive_session_binding_token(&bidi_token, &handshake_hash);
    let hs_resp_wire = wire_encode_resp(&SessionResponse {
        response: Some(session_response::Response::HandshakeResponse(HandshakeResponse {
            r#handshake_type: Some(handshake_response::HandshakeType::NoiseHandshakeMessage(
                noise_resp,
            )),
            attestation_bindings: BTreeMap::new(),
            assertion_bindings: frozen_sign_assertion_bindings(
                &SERVER_EE_BINDING_KEY_BYTES,
                &SERVER_SK_BINDING_KEY_BYTES,
                &bound_data,
            ),
        })),
    });
    client
        .put_incoming_message(wire_decode_resp(&hs_resp_wire)?)
        .context("putting handshake response into bidi client")?;
    assert_that!(client.is_open(), eq(false));

    // 3. ClientSession emits 3rd handshake message (follow-up assertion_bindings);
    //    Frozen server verifies it.
    let followup_wire = wire_encode_req(
        &client.get_outgoing_message()?.context("getting bidi client handshake followup")?,
    );
    let followup = match wire_decode_req(&followup_wire)?.request {
        Some(session_request::Request::HandshakeRequest(r)) => r,
        other => anyhow::bail!("unexpected request variant: {:?}", other),
    };
    assert_that!(followup.r#handshake_type, none());
    assert_that!(followup.attestation_bindings, is_empty());
    frozen_verify_peer_assertion_bindings(
        &client_assertions,
        &followup.assertion_bindings,
        &CLIENT_EE_BINDING_KEY_BYTES,
        &bound_data,
    )?;

    // 4. Encrypted bidirectional application data + channel binding token check.
    verify_encrypted_exchange_with_client(&mut client, &mut frozen_cipher)?;
    assert_that!(
        client.get_session_binding_token(CHANNEL_BINDING_INFO)?.as_slice(),
        eq(frozen_derive_channel_binding_token(&handshake_hash, CHANNEL_BINDING_INFO).as_slice())
    );
    Ok(())
}

#[googletest::test]
fn wire_bidirectional_legacy_endorsed_evidence_both_directions() -> anyhow::Result<()> {
    let rk_bundle = GoldenAttestationBundle::load_rk_release();
    let oc_bundle = GoldenAttestationBundle::load_oc_release();

    // Direction A: Frozen legacy client -> HEAD ServerSession (legacy
    // attestation_bindings sign raw handshake_hash).
    {
        let server_cfg =
            SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
                .add_self_attester_ref(
                    LEGACY_ATTESTATION_ID.to_string(),
                    &(Arc::new(PrebuiltAttester { evidence: oc_bundle.evidence.clone() })
                        as Arc<dyn Attester>),
                )
                .add_self_endorser_ref(
                    LEGACY_ATTESTATION_ID.to_string(),
                    &(Arc::new(PrebuiltEndorser { endorsements: oc_bundle.endorsements.clone() })
                        as Arc<dyn Endorser>),
                )
                .add_session_binder_ref(
                    LEGACY_ATTESTATION_ID.to_string(),
                    &signature_binder(&SERVER_LEGACY_BINDING_KEY_BYTES),
                )
                .add_peer_verifier_with_binding_verifier_provider_ref(
                    LEGACY_ATTESTATION_ID.to_string(),
                    &rk_bundle.create_verifier(),
                    &binding_verifier_provider(&CLIENT_LEGACY_BINDING_KEY_BYTES),
                )
                .build();
        let mut server =
            ServerSession::create(server_cfg).context("creating legacy server session")?;

        server
            .put_incoming_message(wire_decode_req(&read_testdata_bytes(
                GOLDEN_ATTEST_REQUEST_LEGACY_PATH,
            ))?)
            .context("putting golden legacy attest request into server")?;
        let resp_wire = wire_encode_resp(
            &server.get_outgoing_message()?.context("getting legacy server attest response")?,
        );
        assert_that!(resp_wire, eq(&read_testdata_bytes(GOLDEN_ATTEST_RESPONSE_LEGACY_PATH)));

        let mut initiator = FrozenNoiseInitiator::new_deterministic(FROZEN_CLIENT_EPHEMERAL_SCALAR);
        let _ = initiator.build_initial_handshake_request();
        server
            .put_incoming_message(wire_decode_req(&read_testdata_bytes(
                GOLDEN_HANDSHAKE_REQUEST_NN_INIT_PATH,
            ))?)
            .context("putting golden handshake request into legacy server")?;

        let hs_resp = match wire_decode_resp(&wire_encode_resp(
            &server.get_outgoing_message()?.context("getting legacy server handshake response")?,
        ))?
        .response
        {
            Some(session_response::Response::HandshakeResponse(r)) => r,
            other => anyhow::bail!("unexpected response variant: {:?}", other),
        };
        let noise_resp = match hs_resp.r#handshake_type {
            Some(handshake_response::HandshakeType::NoiseHandshakeMessage(m)) => m,
            None => anyhow::bail!("missing NoiseHandshakeMessage"),
        };
        let (handshake_hash, mut frozen_cipher) =
            initiator.process_handshake_response(&noise_resp)?;

        // Legacy attestation_bindings sign raw handshake_hash directly.
        let server_legacy_sig = Signature::from_slice(
            &hs_resp
                .attestation_bindings
                .get(LEGACY_ATTESTATION_ID)
                .context("missing server legacy binding")?
                .binding,
        )
        .map_err(|e| anyhow!("parsing server legacy signature: {}", e))?;
        signing_key(&SERVER_LEGACY_BINDING_KEY_BYTES)
            .verifying_key()
            .verify(&handshake_hash, &server_legacy_sig)
            .map_err(|e| anyhow!("verifying server legacy signature: {}", e))?;

        let client_legacy_sig: Signature =
            signing_key(&CLIENT_LEGACY_BINDING_KEY_BYTES).sign(&handshake_hash);
        let mut client_legacy_bindings = BTreeMap::new();
        client_legacy_bindings.insert(
            LEGACY_ATTESTATION_ID.to_string(),
            SessionBinding { binding: client_legacy_sig.to_vec() },
        );
        let followup_wire = wire_encode_req(&SessionRequest {
            request: Some(session_request::Request::HandshakeRequest(HandshakeRequest {
                r#handshake_type: None,
                attestation_bindings: client_legacy_bindings,
                assertion_bindings: BTreeMap::new(),
            })),
        });
        server
            .put_incoming_message(wire_decode_req(&followup_wire)?)
            .context("putting legacy client followup into server")?;
        assert_that!(server.get_outgoing_message()?, none());
        verify_encrypted_exchange_with_server(&mut server, &mut frozen_cipher)?;
        assert_that!(
            server.get_session_binding_token(CHANNEL_BINDING_INFO)?.as_slice(),
            eq(frozen_derive_channel_binding_token(&handshake_hash, CHANNEL_BINDING_INFO)
                .as_slice())
        );
    }

    // Direction B: HEAD ClientSession (legacy) -> Frozen legacy server.
    {
        let client_cfg =
            SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
                .add_self_attester_ref(
                    LEGACY_ATTESTATION_ID.to_string(),
                    &(Arc::new(PrebuiltAttester { evidence: rk_bundle.evidence.clone() })
                        as Arc<dyn Attester>),
                )
                .add_self_endorser_ref(
                    LEGACY_ATTESTATION_ID.to_string(),
                    &(Arc::new(PrebuiltEndorser { endorsements: rk_bundle.endorsements.clone() })
                        as Arc<dyn Endorser>),
                )
                .add_session_binder_ref(
                    LEGACY_ATTESTATION_ID.to_string(),
                    &signature_binder(&CLIENT_LEGACY_BINDING_KEY_BYTES),
                )
                .add_peer_verifier_with_binding_verifier_provider_ref(
                    LEGACY_ATTESTATION_ID.to_string(),
                    &oc_bundle.create_verifier(),
                    &binding_verifier_provider(&SERVER_LEGACY_BINDING_KEY_BYTES),
                )
                .build();
        let mut client =
            ClientSession::create(client_cfg).context("creating legacy client session")?;

        let req_wire = wire_encode_req(
            &client.get_outgoing_message()?.context("getting legacy client attest request")?,
        );
        assert_that!(req_wire, eq(&read_testdata_bytes(GOLDEN_ATTEST_REQUEST_LEGACY_PATH)));
        client
            .put_incoming_message(wire_decode_resp(&read_testdata_bytes(
                GOLDEN_ATTEST_RESPONSE_LEGACY_PATH,
            ))?)
            .context("putting golden legacy attest response into client")?;

        let hs_req_wire = wire_encode_req(
            &client.get_outgoing_message()?.context("getting legacy client handshake request")?,
        );
        let noise_req = match wire_decode_req(&hs_req_wire)?.request {
            Some(session_request::Request::HandshakeRequest(HandshakeRequest {
                r#handshake_type: Some(handshake_request::HandshakeType::NoiseHandshakeMessage(m)),
                ..
            })) => m,
            other => anyhow::bail!("unexpected request variant: {:?}", other),
        };
        let (noise_resp, handshake_hash, mut frozen_cipher) =
            frozen_respond_nn_deterministic(FROZEN_SERVER_EPHEMERAL_SCALAR, &noise_req)?;

        let server_legacy_sig: Signature =
            signing_key(&SERVER_LEGACY_BINDING_KEY_BYTES).sign(&handshake_hash);
        let mut server_legacy_bindings = BTreeMap::new();
        server_legacy_bindings.insert(
            LEGACY_ATTESTATION_ID.to_string(),
            SessionBinding { binding: server_legacy_sig.to_vec() },
        );
        let hs_resp_wire = wire_encode_resp(&SessionResponse {
            response: Some(session_response::Response::HandshakeResponse(HandshakeResponse {
                r#handshake_type: Some(handshake_response::HandshakeType::NoiseHandshakeMessage(
                    noise_resp,
                )),
                attestation_bindings: server_legacy_bindings,
                assertion_bindings: BTreeMap::new(),
            })),
        });
        client
            .put_incoming_message(wire_decode_resp(&hs_resp_wire)?)
            .context("putting legacy handshake response into client")?;

        let followup = match wire_decode_req(&wire_encode_req(
            &client.get_outgoing_message()?.context("getting legacy client handshake followup")?,
        ))?
        .request
        {
            Some(session_request::Request::HandshakeRequest(r)) => r,
            other => anyhow::bail!("unexpected request variant: {:?}", other),
        };
        let client_sig = Signature::from_slice(
            &followup
                .attestation_bindings
                .get(LEGACY_ATTESTATION_ID)
                .context("missing client legacy binding")?
                .binding,
        )
        .map_err(|e| anyhow!("parsing client legacy signature: {}", e))?;
        signing_key(&CLIENT_LEGACY_BINDING_KEY_BYTES)
            .verifying_key()
            .verify(&handshake_hash, &client_sig)
            .map_err(|e| anyhow!("verifying client legacy signature: {}", e))?;

        verify_encrypted_exchange_with_client(&mut client, &mut frozen_cipher)?;
        assert_that!(
            client.get_session_binding_token(CHANNEL_BINDING_INFO)?.as_slice(),
            eq(frozen_derive_channel_binding_token(&handshake_hash, CHANNEL_BINDING_INFO)
                .as_slice())
        );
    }

    Ok(())
}

// ============================================================================
// Group 3: Negative Wire Tamper & Format-Regression Tripwire Tests
// ============================================================================

#[googletest::test]
fn wire_regression_legacy_unprefixed_binding_token_rejected() -> anyhow::Result<()> {
    let rk_bundle = GoldenAttestationBundle::load_rk_release();
    let oc_bundle = GoldenAttestationBundle::load_oc_release();

    let client_assertions = frozen_build_assertions_map(&rk_bundle, &CLIENT_SK_BINDING_KEY_BYTES);
    let server_assertions = frozen_build_assertions_map(&oc_bundle, &SERVER_SK_BINDING_KEY_BYTES);
    let mut legacy_unprefixed_bidi_token =
        frozen_legacy_unprefixed_serialize_assertions(&client_assertions);
    legacy_unprefixed_bidi_token
        .extend(frozen_legacy_unprefixed_serialize_assertions(&server_assertions));

    // 1. Frozen server signing the deprecated unprefixed token must be rejected by
    //    HEAD ClientSession.
    {
        let client_cfg = add_peer_assertion_verifiers(
            add_self_assertions(
                SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
                &rk_bundle,
                &CLIENT_EE_BINDING_KEY_BYTES,
                &CLIENT_SK_BINDING_KEY_BYTES,
            ),
            &oc_bundle,
            &SERVER_EE_BINDING_KEY_BYTES,
        )
        .build();
        let mut client = ClientSession::create(client_cfg).context("creating client session")?;
        let _ = client.get_outgoing_message()?;
        client
            .put_incoming_message(wire_decode_resp(&read_testdata_bytes(
                GOLDEN_ATTEST_RESPONSE_ASSERTIONS_PATH,
            ))?)
            .context("putting golden attest response into client")?;

        let hs_req =
            match client.get_outgoing_message()?.context("getting handshake request")?.request {
                Some(session_request::Request::HandshakeRequest(HandshakeRequest {
                    r#handshake_type:
                        Some(handshake_request::HandshakeType::NoiseHandshakeMessage(m)),
                    ..
                })) => m,
                other => anyhow::bail!("unexpected request variant: {:?}", other),
            };
        let (noise_resp, handshake_hash, _cipher) =
            frozen_respond_nn_deterministic(FROZEN_SERVER_EPHEMERAL_SCALAR, &hs_req)?;
        let wrong_bound_data =
            frozen_derive_session_binding_token(&legacy_unprefixed_bidi_token, &handshake_hash);

        client
            .put_incoming_message(SessionResponse {
                response: Some(session_response::Response::HandshakeResponse(HandshakeResponse {
                    r#handshake_type: Some(
                        handshake_response::HandshakeType::NoiseHandshakeMessage(noise_resp),
                    ),
                    attestation_bindings: BTreeMap::new(),
                    assertion_bindings: frozen_sign_assertion_bindings(
                        &SERVER_EE_BINDING_KEY_BYTES,
                        &SERVER_SK_BINDING_KEY_BYTES,
                        &wrong_bound_data,
                    ),
                })),
            })
            .context("putting handshake response with unprefixed binding into client")?;
        // ClientSession verifies server bindings when transitioning out of Handshake on
        // followup fetch.
        assert_that!(client.get_outgoing_message(), err(anything()));
    }

    // 2. Frozen client signing the deprecated unprefixed token in 3rd message must
    //    be rejected by HEAD ServerSession.
    {
        let server_cfg = add_peer_assertion_verifiers(
            add_self_assertions(
                SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
                &oc_bundle,
                &SERVER_EE_BINDING_KEY_BYTES,
                &SERVER_SK_BINDING_KEY_BYTES,
            ),
            &rk_bundle,
            &CLIENT_EE_BINDING_KEY_BYTES,
        )
        .build();
        let mut server = ServerSession::create(server_cfg).context("creating server session")?;
        server
            .put_incoming_message(wire_decode_req(&read_testdata_bytes(
                GOLDEN_ATTEST_REQUEST_ASSERTIONS_PATH,
            ))?)
            .context("putting golden attest request into server")?;
        let _ = server.get_outgoing_message()?;

        let mut initiator = FrozenNoiseInitiator::new_deterministic(FROZEN_CLIENT_EPHEMERAL_SCALAR);
        let _ = initiator.build_initial_handshake_request();
        server
            .put_incoming_message(wire_decode_req(&read_testdata_bytes(
                GOLDEN_HANDSHAKE_REQUEST_NN_INIT_PATH,
            ))?)
            .context("putting golden handshake request into server")?;
        let hs_resp =
            match server.get_outgoing_message()?.context("getting handshake response")?.response {
                Some(session_response::Response::HandshakeResponse(HandshakeResponse {
                    r#handshake_type:
                        Some(handshake_response::HandshakeType::NoiseHandshakeMessage(m)),
                    ..
                })) => m,
                other => anyhow::bail!("unexpected response variant: {:?}", other),
            };
        let (handshake_hash, _cipher) = initiator.process_handshake_response(&hs_resp)?;
        let wrong_bound_data =
            frozen_derive_session_binding_token(&legacy_unprefixed_bidi_token, &handshake_hash);

        server
            .put_incoming_message(SessionRequest {
                request: Some(session_request::Request::HandshakeRequest(HandshakeRequest {
                    r#handshake_type: None,
                    attestation_bindings: BTreeMap::new(),
                    assertion_bindings: frozen_sign_assertion_bindings(
                        &CLIENT_EE_BINDING_KEY_BYTES,
                        &CLIENT_SK_BINDING_KEY_BYTES,
                        &wrong_bound_data,
                    ),
                })),
            })
            .context("putting client followup with unprefixed binding into server")?;
        assert_that!(server.get_outgoing_message(), err(anything()));
    }

    Ok(())
}

#[googletest::test]
fn wire_tampered_assertion_or_binding_rejected() -> anyhow::Result<()> {
    let rk_bundle = GoldenAttestationBundle::load_rk_release();
    let oc_bundle = GoldenAttestationBundle::load_oc_release();

    // Case 1: MITM injects an extra unverified assertion into golden AttestRequest
    // (client -> server). ServerSession accepts AttestRequest (All aggregator
    // ignores Unverified), but ServerAttestationHandler's attestation_binding_token
    // diverges so handshake binding verification must fail.
    {
        let server_cfg = add_peer_assertion_verifiers(
            add_self_assertions(
                SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
                &oc_bundle,
                &SERVER_EE_BINDING_KEY_BYTES,
                &SERVER_SK_BINDING_KEY_BYTES,
            ),
            &rk_bundle,
            &CLIENT_EE_BINDING_KEY_BYTES,
        )
        .build();
        let mut server = ServerSession::create(server_cfg).context("creating server session")?;

        let mut tampered_req =
            wire_decode_req(&read_testdata_bytes(GOLDEN_ATTEST_REQUEST_ASSERTIONS_PATH))?;
        if let Some(session_request::Request::AttestRequest(ref mut r)) = tampered_req.request {
            r.assertions.insert(
                "injected_extra_assertion".to_string(),
                Assertion { content: b"mitm".to_vec() },
            );
        }
        server
            .put_incoming_message(tampered_req)
            .context("putting tampered attest request into server")?;
        let _ = server.get_outgoing_message()?;

        let mut initiator = FrozenNoiseInitiator::new_deterministic(FROZEN_CLIENT_EPHEMERAL_SCALAR);
        let _ = initiator.build_initial_handshake_request();
        server
            .put_incoming_message(wire_decode_req(&read_testdata_bytes(
                GOLDEN_HANDSHAKE_REQUEST_NN_INIT_PATH,
            ))?)
            .context("putting golden handshake request into server")?;
        let hs_resp =
            match server.get_outgoing_message()?.context("getting handshake response")?.response {
                Some(session_response::Response::HandshakeResponse(HandshakeResponse {
                    r#handshake_type:
                        Some(handshake_response::HandshakeType::NoiseHandshakeMessage(m)),
                    ..
                })) => m,
                other => anyhow::bail!("unexpected response variant: {:?}", other),
            };
        let (handshake_hash, _cipher) = initiator.process_handshake_response(&hs_resp)?;

        // Honest client signs over original bidi_token (without the MITM-injected
        // assertion).
        let honest_bidi_token = read_testdata_bytes(GOLDEN_BIDI_ATTESTATION_BINDING_TOKEN_PATH);
        let honest_bound_data =
            frozen_derive_session_binding_token(&honest_bidi_token, &handshake_hash);
        server
            .put_incoming_message(SessionRequest {
                request: Some(session_request::Request::HandshakeRequest(HandshakeRequest {
                    r#handshake_type: None,
                    attestation_bindings: BTreeMap::new(),
                    assertion_bindings: frozen_sign_assertion_bindings(
                        &CLIENT_EE_BINDING_KEY_BYTES,
                        &CLIENT_SK_BINDING_KEY_BYTES,
                        &honest_bound_data,
                    ),
                })),
            })
            .context("putting honest client followup into server")?;
        assert_that!(server.get_outgoing_message(), err(anything()));
    }

    // Case 2: Symmetric MITM injection of an extra unverified assertion into golden
    // AttestResponse (server -> client). ClientSession accepts AttestResponse (All
    // aggregator ignores Unverified), but ClientAttestationHandler's
    // attestation_binding_token diverges so verifying the honest server's binding
    // must fail.
    {
        let client_cfg = add_peer_assertion_verifiers(
            add_self_assertions(
                SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
                &rk_bundle,
                &CLIENT_EE_BINDING_KEY_BYTES,
                &CLIENT_SK_BINDING_KEY_BYTES,
            ),
            &oc_bundle,
            &SERVER_EE_BINDING_KEY_BYTES,
        )
        .build();
        let mut client = ClientSession::create(client_cfg).context("creating client session")?;
        let _ = client.get_outgoing_message()?;

        let mut tampered_resp =
            wire_decode_resp(&read_testdata_bytes(GOLDEN_ATTEST_RESPONSE_ASSERTIONS_PATH))?;
        if let Some(session_response::Response::AttestResponse(ref mut r)) = tampered_resp.response
        {
            r.assertions.insert(
                "injected_extra_assertion".to_string(),
                Assertion { content: b"mitm".to_vec() },
            );
        }
        client
            .put_incoming_message(tampered_resp)
            .context("putting tampered attest response into client")?;

        let hs_req =
            match client.get_outgoing_message()?.context("getting handshake request")?.request {
                Some(session_request::Request::HandshakeRequest(HandshakeRequest {
                    r#handshake_type:
                        Some(handshake_request::HandshakeType::NoiseHandshakeMessage(m)),
                    ..
                })) => m,
                other => anyhow::bail!("unexpected request variant: {:?}", other),
            };
        let (noise_resp, handshake_hash, _cipher) =
            frozen_respond_nn_deterministic(FROZEN_SERVER_EPHEMERAL_SCALAR, &hs_req)?;

        // Honest server signs over original bidi_token (without the MITM-injected
        // assertion).
        let honest_bidi_token = read_testdata_bytes(GOLDEN_BIDI_ATTESTATION_BINDING_TOKEN_PATH);
        let honest_bound_data =
            frozen_derive_session_binding_token(&honest_bidi_token, &handshake_hash);
        client
            .put_incoming_message(SessionResponse {
                response: Some(session_response::Response::HandshakeResponse(HandshakeResponse {
                    r#handshake_type: Some(
                        handshake_response::HandshakeType::NoiseHandshakeMessage(noise_resp),
                    ),
                    attestation_bindings: BTreeMap::new(),
                    assertion_bindings: frozen_sign_assertion_bindings(
                        &SERVER_EE_BINDING_KEY_BYTES,
                        &SERVER_SK_BINDING_KEY_BYTES,
                        &honest_bound_data,
                    ),
                })),
            })
            .context("putting honest server handshake response into client")?;
        assert_that!(client.get_outgoing_message(), err(anything()));
    }

    // Case 3: Corrupted hardware report byte inside golden AttestResponse must fail
    // the attestation step immediately.
    {
        let client_cfg = add_peer_assertion_verifiers(
            add_self_assertions(
                SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
                &rk_bundle,
                &CLIENT_EE_BINDING_KEY_BYTES,
                &CLIENT_SK_BINDING_KEY_BYTES,
            ),
            &oc_bundle,
            &SERVER_EE_BINDING_KEY_BYTES,
        )
        .build();
        let mut client = ClientSession::create(client_cfg).context("creating client session")?;
        let _ = client.get_outgoing_message()?;

        let mut corrupted_oc = oc_bundle.endorsed_evidence();
        corrupted_oc.evidence.as_mut().unwrap().root_layer.as_mut().unwrap().eca_public_key[10] ^=
            0xff;
        let mut tampered_resp =
            wire_decode_resp(&read_testdata_bytes(GOLDEN_ATTEST_RESPONSE_ASSERTIONS_PATH))?;
        if let Some(session_response::Response::AttestResponse(ref mut r)) = tampered_resp.response
        {
            r.assertions.insert(
                ENDORSED_EVIDENCE_ASSERTION_ID.to_string(),
                Assertion { content: corrupted_oc.encode_to_vec() },
            );
        }
        assert_that!(client.put_incoming_message(tampered_resp), err(anything()));
    }

    Ok(())
}

// ============================================================================
// Ignored Helper for Intentional Wire-Protocol Golden Regeneration
//
// See `oak_session/testdata/README.md` for instructions.
// ============================================================================

#[googletest::test]
#[ignore]
fn regenerate_wire_goldens() -> anyhow::Result<()> {
    let out_dir = std::env::var("TEST_UNDECLARED_OUTPUTS_DIR")
        .context("reading TEST_UNDECLARED_OUTPUTS_DIR")?;

    let rk_bundle = GoldenAttestationBundle::load_rk_release();
    let oc_bundle = GoldenAttestationBundle::load_oc_release();

    let client_cfg = add_peer_assertion_verifiers(
        add_self_assertions(
            SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
            &rk_bundle,
            &CLIENT_EE_BINDING_KEY_BYTES,
            &CLIENT_SK_BINDING_KEY_BYTES,
        ),
        &oc_bundle,
        &SERVER_EE_BINDING_KEY_BYTES,
    )
    .build();
    let server_cfg = add_peer_assertion_verifiers(
        add_self_assertions(
            SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN),
            &oc_bundle,
            &SERVER_EE_BINDING_KEY_BYTES,
            &SERVER_SK_BINDING_KEY_BYTES,
        ),
        &rk_bundle,
        &CLIENT_EE_BINDING_KEY_BYTES,
    )
    .build();

    let mut client = ClientSession::create(client_cfg).context("creating client session")?;
    let mut server = ServerSession::create(server_cfg).context("creating server session")?;

    let attest_req_assertions =
        client.get_outgoing_message()?.context("getting client attest request")?;
    fs::write(
        format!("{}/attest_request_assertions.binarypb", out_dir),
        attest_req_assertions.encode_to_vec(),
    )
    .context("writing attest_request_assertions.binarypb")?;
    server
        .put_incoming_message(attest_req_assertions)
        .context("putting attest request into server")?;
    let attest_resp_assertions =
        server.get_outgoing_message()?.context("getting server attest response")?;
    fs::write(
        format!("{}/attest_response_assertions.binarypb", out_dir),
        attest_resp_assertions.encode_to_vec(),
    )
    .context("writing attest_response_assertions.binarypb")?;

    let legacy_client_cfg =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester_ref(
                LEGACY_ATTESTATION_ID.to_string(),
                &(Arc::new(PrebuiltAttester { evidence: rk_bundle.evidence.clone() })
                    as Arc<dyn Attester>),
            )
            .add_self_endorser_ref(
                LEGACY_ATTESTATION_ID.to_string(),
                &(Arc::new(PrebuiltEndorser { endorsements: rk_bundle.endorsements.clone() })
                    as Arc<dyn Endorser>),
            )
            .add_session_binder_ref(
                LEGACY_ATTESTATION_ID.to_string(),
                &signature_binder(&CLIENT_LEGACY_BINDING_KEY_BYTES),
            )
            .add_peer_verifier_with_binding_verifier_provider_ref(
                LEGACY_ATTESTATION_ID.to_string(),
                &oc_bundle.create_verifier(),
                &binding_verifier_provider(&SERVER_LEGACY_BINDING_KEY_BYTES),
            )
            .build();
    let legacy_server_cfg =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester_ref(
                LEGACY_ATTESTATION_ID.to_string(),
                &(Arc::new(PrebuiltAttester { evidence: oc_bundle.evidence.clone() })
                    as Arc<dyn Attester>),
            )
            .add_self_endorser_ref(
                LEGACY_ATTESTATION_ID.to_string(),
                &(Arc::new(PrebuiltEndorser { endorsements: oc_bundle.endorsements.clone() })
                    as Arc<dyn Endorser>),
            )
            .add_session_binder_ref(
                LEGACY_ATTESTATION_ID.to_string(),
                &signature_binder(&SERVER_LEGACY_BINDING_KEY_BYTES),
            )
            .add_peer_verifier_with_binding_verifier_provider_ref(
                LEGACY_ATTESTATION_ID.to_string(),
                &rk_bundle.create_verifier(),
                &binding_verifier_provider(&CLIENT_LEGACY_BINDING_KEY_BYTES),
            )
            .build();
    let mut legacy_client =
        ClientSession::create(legacy_client_cfg).context("creating legacy client session")?;
    let mut legacy_server =
        ServerSession::create(legacy_server_cfg).context("creating legacy server session")?;
    let attest_req_legacy =
        legacy_client.get_outgoing_message()?.context("getting legacy client request")?;
    fs::write(
        format!("{}/attest_request_legacy.binarypb", out_dir),
        attest_req_legacy.encode_to_vec(),
    )
    .context("writing attest_request_legacy.binarypb")?;
    legacy_server
        .put_incoming_message(attest_req_legacy)
        .context("putting legacy request into server")?;
    let attest_resp_legacy =
        legacy_server.get_outgoing_message()?.context("getting legacy server response")?;
    fs::write(
        format!("{}/attest_response_legacy.binarypb", out_dir),
        attest_resp_legacy.encode_to_vec(),
    )
    .context("writing attest_response_legacy.binarypb")?;

    let client_assertions = frozen_build_assertions_map(&rk_bundle, &CLIENT_SK_BINDING_KEY_BYTES);
    let server_assertions = frozen_build_assertions_map(&oc_bundle, &SERVER_SK_BINDING_KEY_BYTES);
    let empty_assertions = BTreeMap::new();

    let mut bidi_token = frozen_serialize_assertions(&client_assertions);
    bidi_token.extend(frozen_serialize_assertions(&server_assertions));
    fs::write(format!("{}/bidi_attestation_binding_token.bin", out_dir), &bidi_token)
        .context("writing bidi_attestation_binding_token.bin")?;

    let mut uni_server_token = frozen_serialize_assertions(&empty_assertions);
    uni_server_token.extend(frozen_serialize_assertions(&server_assertions));
    fs::write(format!("{}/uni_server_attestation_binding_token.bin", out_dir), &uni_server_token)
        .context("writing uni_server_attestation_binding_token.bin")?;

    let mut uni_client_token = frozen_serialize_assertions(&client_assertions);
    uni_client_token.extend(frozen_serialize_assertions(&empty_assertions));
    fs::write(format!("{}/uni_client_attestation_binding_token.bin", out_dir), &uni_client_token)
        .context("writing uni_client_attestation_binding_token.bin")?;

    let mut initiator = FrozenNoiseInitiator::new_deterministic(FROZEN_CLIENT_EPHEMERAL_SCALAR);
    let hs_init = SessionRequest {
        request: Some(session_request::Request::HandshakeRequest(
            initiator.build_initial_handshake_request(),
        )),
    };
    fs::write(format!("{}/handshake_request_nn_init.binarypb", out_dir), hs_init.encode_to_vec())
        .context("writing handshake_request_nn_init.binarypb")?;

    let bound_data = create_session_binding_token(&bidi_token, &PINNED_HANDSHAKE_HASH);
    let followup = SessionRequest {
        request: Some(session_request::Request::HandshakeRequest(HandshakeRequest {
            r#handshake_type: None,
            attestation_bindings: BTreeMap::new(),
            assertion_bindings: build_head_assertion_bindings(
                &rk_bundle,
                &CLIENT_EE_BINDING_KEY_BYTES,
                &CLIENT_SK_BINDING_KEY_BYTES,
                &bound_data,
            )?,
        })),
    };
    fs::write(
        format!("{}/handshake_followup_assertions.binarypb", out_dir),
        followup.encode_to_vec(),
    )
    .context("writing handshake_followup_assertions.binarypb")?;

    let mut client_enc = OrderedChannelEncryptor::try_from(OrderedCrypter::new(
        &PINNED_SERVER_WRITE_KEY,
        &PINNED_CLIENT_WRITE_KEY,
    ))
    .context("creating client OrderedChannelEncryptor")?;
    let mut server_enc = OrderedChannelEncryptor::try_from(OrderedCrypter::new(
        &PINNED_CLIENT_WRITE_KEY,
        &PINNED_SERVER_WRITE_KEY,
    ))
    .context("creating server OrderedChannelEncryptor")?;
    let enc_req = SessionRequest {
        request: Some(session_request::Request::EncryptedMessage(
            client_enc
                .encrypt(Payload::from(PlaintextMessage {
                    plaintext: b"pinned wire request 0".to_vec(),
                }))
                .context("encrypting request")?
                .into(),
        )),
    };
    let enc_resp = SessionResponse {
        response: Some(session_response::Response::EncryptedMessage(
            server_enc
                .encrypt(Payload::from(PlaintextMessage {
                    plaintext: b"pinned wire response 0".to_vec(),
                }))
                .context("encrypting response")?
                .into(),
        )),
    };
    fs::write(format!("{}/encrypted_request_msg0.binarypb", out_dir), enc_req.encode_to_vec())
        .context("writing encrypted_request_msg0.binarypb")?;
    fs::write(format!("{}/encrypted_response_msg0.binarypb", out_dir), enc_resp.encode_to_vec())
        .context("writing encrypted_response_msg0.binarypb")?;

    Ok(())
}
