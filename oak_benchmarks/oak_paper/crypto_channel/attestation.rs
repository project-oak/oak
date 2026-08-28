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

//! Session configurations for the attested leg of the crypto-channel
//! benchmark.
//!
//! # What Oak's attested Noise actually is
//!
//! Oak does not use a Noise pattern with static keys (NK, KK, XX). It runs
//! plain `NoiseNN` — ephemeral keys only — and adds attestation as a *separate*
//! step that is stitched to the handshake by a signature over the Noise
//! handshake hash:
//!
//! 1. the responder returns its DICE [`Evidence`] and [`Endorsements`], which
//!    contain a *session binding* public key;
//! 2. both sides complete the `NoiseNN` handshake and derive the handshake
//!    hash;
//! 3. the responder signs the handshake hash with the private half of the
//!    binding key, and the initiator verifies that signature.
//!
//! Step 3 is what proves that the party that produced the evidence is the same
//! party that ran the handshake. Binding a transcript hash is part of the Noise
//! specification (<https://noiseprotocol.org/noise.html#channel-binding>), not
//! an Oak invention.
//!
//! # What the attested-versus-unattested delta measures
//!
//! The extra round trip is *not* part of the delta: `AttestationType::
//! Unattested` already exchanges an `AttestRequest`/`AttestResponse` pair, so
//! both legs have the same number of network round trips. The delta is
//! therefore almost purely attestation *cryptography and serialisation*:
//!
//! | cost                              | paid by | per session? |
//! | --------------------------------- | ------- | ------------ |
//! | generating the DICE evidence      | server  | no, at boot  |
//! | serialising evidence onto the wire| server  | yes          |
//! | signing the handshake hash        | server  | yes, 1 sign  |
//! | verifying the DICE chain          | client  | yes, 1 per layer |
//! | evaluating the event-log policies | client  | yes          |
//! | verifying the binding signature   | client  | yes, 1 verify |
//!
//! [`ServerAttestationMaterial::generate`] is therefore called once, before the
//! benchmark's timed region, exactly as a real server generates its evidence
//! once at boot.
//!
//! # What is substituted, and why
//!
//! The root of trust is software, not hardware: [`Standalone`] builds a genuine
//! multi-layer DICE chain with real P-256 keys, but its root layer holds a mock
//! attestation report rather than an AMD SEV-SNP one. This is deliberate and
//! unavoidable here — this benchmark runs on a machine with no TEE, and the
//! recorded SEV-SNP evidence in `oak_attestation_verification/testdata` cannot
//! be used because we do not hold the private half of its binding key, so no
//! session using it could ever complete.
//!
//! The consequence is that the client-side cost measured here **excludes**
//! verification of the hardware root: the SEV-SNP attestation report signature
//! and the VCEK certificate chain, all of which are ECDSA P-384 rather than
//! P-256. Everything above the root — the DICE layer certificates, the event
//! log, and the session binding signature — is real, and the server's signing
//! cost is exactly what a real server pays. Treat the numbers from this leg as
//! a lower bound on attestation cost, and see the README for the separately
//! measured root-layer cost.
//!
//! Reference values are [`SkipVerification`], so the policies parse and
//! traverse the event log but do not compare digests against expected values.
//! Digest comparison is a handful of `memcmp`s and is not where the time goes.

use std::sync::Arc;

use anyhow::Context;
use oak_attestation_verification::{
    ContainerPolicy, InsecureAttestationVerifier, KernelPolicy, SystemPolicy,
};
use oak_dice::cert::generate_ecdsa_key_pair;
use oak_proto_rust::oak::attestation::v1::{
    BinaryReferenceValue, ContainerLayerReferenceValues, Endorsements, Evidence,
    KernelBinaryReferenceValue, KernelLayerReferenceValues, SkipVerification,
    SystemLayerReferenceValues, TextReferenceValue, binary_reference_value,
    kernel_binary_reference_value, text_reference_value,
};
use oak_sdk_common::{StaticAttester, StaticEndorser};
use oak_sdk_standalone::Standalone;
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType,
    key_extractor::DefaultBindingKeyExtractor, session_binding::SignatureBinder,
};
use oak_time_std::clock::SystemTimeClock;
use p256::ecdsa::SigningKey;

/// Identifier used to match the server's evidence with the client's verifier.
///
/// A session config keys its attesters, endorsers, binders and verifiers by
/// this string, so the two sides must agree on it.
pub const ATTESTER_ID: &str = "crypto_channel_benchmark";

/// The evidence a server presents, plus the private key it binds sessions with.
///
/// Generate this once per process. Regenerating it per session would charge the
/// benchmark for work that a real deployment does at boot: an Oak server's DICE
/// chain is built as the layers of the stack measure each other, long before
/// any client connects.
pub struct ServerAttestationMaterial {
    evidence: Evidence,
    endorsements: Endorsements,
    session_binding_key: SigningKey,
}

impl ServerAttestationMaterial {
    /// Builds a software-rooted DICE chain and the matching binding key.
    ///
    /// The binding key pair is generated here rather than by [`Standalone`] so
    /// that the private half stays with us: it is what
    /// [`Self::session_config`] signs handshake hashes with, and its public
    /// half is what the client recovers from the verified evidence.
    pub fn generate() -> anyhow::Result<Self> {
        let (session_binding_key, session_binding_public_key) = generate_ecdsa_key_pair();
        let standalone = Standalone::builder()
            .session_binding_key_pair(Some((
                session_binding_key.clone(),
                session_binding_public_key,
            )))
            .build()
            .context("building standalone attestation material")?;
        let endorsed_evidence = standalone.endorsed_evidence();
        Ok(Self {
            evidence: endorsed_evidence.evidence.context("missing evidence")?,
            endorsements: endorsed_evidence.endorsements.context("missing endorsements")?,
            session_binding_key,
        })
    }

    /// A server config that attests to the peer and binds the handshake.
    ///
    /// `SelfUnidirectional` is the responder half of the scheme described in
    /// the module comment: this side proves who it is, and does not ask the
    /// client to prove anything.
    pub fn session_config(&self) -> SessionConfig {
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(
                ATTESTER_ID.into(),
                Box::new(StaticAttester::new(self.evidence.clone())),
            )
            .add_self_endorser(
                ATTESTER_ID.into(),
                Box::new(StaticEndorser::new(self.endorsements.clone())),
            )
            .add_session_binder(
                ATTESTER_ID.into(),
                Box::new(SignatureBinder::new(Box::new(self.session_binding_key.clone()))),
            )
            .build()
    }
}

/// A client config that verifies the server's evidence and binding signature.
///
/// [`DefaultBindingKeyExtractor`] rather than the default signing-key extractor
/// is required here: the policy-based verifiers report their findings in
/// `event_attestation_results` and leave the deprecated `extracted_evidence`
/// field empty, and it is the *binding* key, not the application signing key,
/// that signs the handshake hash.
pub fn client_session_config() -> SessionConfig {
    SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
        .add_peer_verifier_with_key_extractor(
            ATTESTER_ID.into(),
            Box::new(InsecureAttestationVerifier::new(
                Arc::new(SystemTimeClock {}),
                vec![
                    Box::new(KernelPolicy::new(&skip_kernel_reference_values())),
                    Box::new(SystemPolicy::new(&skip_system_reference_values())),
                    Box::new(ContainerPolicy::new(&skip_container_reference_values())),
                ],
            )),
            Box::new(DefaultBindingKeyExtractor {}),
        )
        .build()
}

fn skip_binary() -> BinaryReferenceValue {
    BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification::default())),
    }
}

fn skip_kernel_reference_values() -> KernelLayerReferenceValues {
    KernelLayerReferenceValues {
        kernel: Some(KernelBinaryReferenceValue {
            r#type: Some(kernel_binary_reference_value::Type::Skip(SkipVerification::default())),
        }),
        kernel_cmd_line_text: Some(TextReferenceValue {
            r#type: Some(text_reference_value::Type::Skip(SkipVerification::default())),
        }),
        init_ram_fs: Some(skip_binary()),
        memory_map: Some(skip_binary()),
        acpi: Some(skip_binary()),
    }
}

fn skip_system_reference_values() -> SystemLayerReferenceValues {
    SystemLayerReferenceValues { system_image: Some(skip_binary()) }
}

fn skip_container_reference_values() -> ContainerLayerReferenceValues {
    ContainerLayerReferenceValues {
        binary: Some(skip_binary()),
        configuration: Some(skip_binary()),
    }
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;
    use oak_proto_rust::oak::session::v1::PlaintextMessage;
    use oak_session::{ClientSession, ProtocolEngine, ServerSession, Session};

    use super::*;

    /// A handshake needs a handful of message exchanges; anything beyond this
    /// means the loop is not converging.
    const MAX_HANDSHAKE_STEPS: usize = 16;

    /// The point of this test is that the attestation is *real*: if the
    /// evidence did not verify, or if the binding signature did not match the
    /// key recovered from the evidence, the session would never open and the
    /// benchmark leg built on this config would be measuring nothing.
    #[test]
    fn attested_session_opens_and_carries_a_message() {
        let material =
            ServerAttestationMaterial::generate().expect("generating attestation material");
        let mut client =
            ClientSession::create(client_session_config()).expect("creating client session");
        let mut server =
            ServerSession::create(material.session_config()).expect("creating server session");

        let mut steps = 0;
        while !(client.is_open() && server.is_open()) {
            steps += 1;
            assert_that!(steps, le(MAX_HANDSHAKE_STEPS), "handshake did not converge");

            if let Some(request) =
                client.get_outgoing_message().expect("getting outgoing client message")
            {
                server.put_incoming_message(request).expect("putting incoming client message");
            }
            if let Some(response) =
                server.get_outgoing_message().expect("getting outgoing server message")
            {
                client.put_incoming_message(response).expect("putting incoming server message");
            }
        }

        client.write(PlaintextMessage { plaintext: b"hello".to_vec() }).expect("writing plaintext");
        let encrypted =
            client.get_outgoing_message().expect("encrypting").expect("expected a message");
        server.put_incoming_message(encrypted).expect("putting encrypted message");

        let received = server.read().expect("decrypting").expect("expected a decrypted message");
        assert_that!(received.plaintext, eq(&b"hello".to_vec()));
    }

    /// A negative control for the test above.
    ///
    /// The server keeps its real evidence but signs the handshake hash with a
    /// key the evidence does not vouch for. This is exactly the attack the
    /// binding signature exists to stop -- a party that replays somebody else's
    /// evidence -- so the session must not open. If it did, the attested leg
    /// would be measuring an unattested session wearing a costume.
    #[test]
    fn a_binding_key_the_evidence_does_not_vouch_for_is_rejected() {
        let material =
            ServerAttestationMaterial::generate().expect("generating attestation material");
        let (unvouched_key, _) = generate_ecdsa_key_pair();
        let impostor = ServerAttestationMaterial {
            evidence: material.evidence.clone(),
            endorsements: material.endorsements.clone(),
            session_binding_key: unvouched_key,
        };

        let mut client =
            ClientSession::create(client_session_config()).expect("creating client session");
        let mut server =
            ServerSession::create(impostor.session_config()).expect("creating server session");

        for _ in 0..MAX_HANDSHAKE_STEPS {
            if client.is_open() {
                break;
            }
            let Ok(Some(request)) = client.get_outgoing_message() else { break };
            if server.put_incoming_message(request).is_err() {
                break;
            }
            let Ok(Some(response)) = server.get_outgoing_message() else { break };
            if client.put_incoming_message(response).is_err() {
                break;
            }
        }

        assert_that!(client.is_open(), eq(false));
    }

    /// Pins the shape of the DICE chain, because the README decomposes the
    /// attested `Setup` cost as a count of signature verifications and that
    /// count is only meaningful if the number of certificates is known.
    ///
    /// A client verifies one signature per layer certificate, plus one per
    /// application-key certificate, plus one for the session binding. If this
    /// test fails the chain changed shape and the cost model in the README is
    /// stale.
    #[test]
    fn the_chain_has_the_shape_the_cost_model_assumes() {
        let material =
            ServerAttestationMaterial::generate().expect("generating attestation material");
        let application_keys =
            material.evidence.application_keys.as_ref().expect("missing application keys");

        // Three layers -- stage 0, the system image, and the container -- each
        // certified by the one below it, with the root layer's key certifying
        // the first. Verifying them costs one signature verification each.
        assert_that!(material.evidence.layers.len(), eq(3));
        assert_that!(application_keys.encryption_public_key_certificate, not(is_empty()));
        assert_that!(application_keys.signing_public_key_certificate, not(is_empty()));
        // Key provisioning is not in use here, so there are no group keys to
        // verify.
        assert_that!(application_keys.group_encryption_public_key_certificate, is_empty());
        assert_that!(application_keys.group_signing_public_key_certificate, is_empty());
    }
}
