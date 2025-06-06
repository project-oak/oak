//
// Copyright 2025 The Project Oak Authors
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

use std::{
    fs,
    sync::Arc,
    time::{SystemTime, UNIX_EPOCH},
};

use anyhow::Result;
use base64::{prelude::BASE64_STANDARD, Engine as _};
use clap::Parser;
use oak_attestation_verification::{
    policy::session_binding_public_key::SessionBindingPublicKeyPolicy, verifier::EventLogVerifier,
};
use oak_attestation_verification_types::{util::Clock, verifier::AttestationVerifier};
use oak_crypto::certificate::certificate_verifier::CertificateVerifier;
use oak_crypto_tink::signature_verifier::SignatureVerifier;
use oak_proto_rust::{
    attestation::SIGNATURE_BASED_ATTESTATION_ID,
    oak::{
        attestation::v1::{
            collected_attestation::RequestMetadata, AttestationResults, CollectedAttestation,
        },
        session::v1::EndorsedEvidence,
    },
};
use prost::Message;

static GOOGLE_IDENTITY_PUBLIC_KEY: &[u8; 459] =
    include_bytes!("../data/google_identity_public_key.pb");

#[derive(Parser, Debug)]
#[group(required = true)]
struct Flags {
    /// Path of the collected attestation.
    #[arg(long, value_parser = collected_attestation_parser)]
    attestation: CollectedAttestation,
}

fn collected_attestation_parser(s: &str) -> Result<CollectedAttestation> {
    Ok(CollectedAttestation::decode(BASE64_STANDARD.decode(fs::read(s)?)?.as_slice())?)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
struct FrozenClock {
    timestamp: SystemTime,
}

impl Clock for FrozenClock {
    fn get_milliseconds_since_epoch(&self) -> i64 {
        let time_since_epoch = self
            .timestamp
            .duration_since(UNIX_EPOCH)
            .expect("unable to calculate duration since epoch");
        time_since_epoch
            .as_millis()
            .try_into()
            .expect("unable to convert u128 millis since epoch to i64")
    }
}

fn main() {
    let Flags { attestation } = Flags::parse();

    // TODO: b/419209669 - push this loop (removing print statements) down into some
    // new attestation verification library function (with tests!); make it return
    // some combined result.
    for (attestation_type_id, endorsed_evidence) in attestation.endorsed_evidence.iter() {
        match attestation_type_id.as_str() {
            SIGNATURE_BASED_ATTESTATION_ID => {
                println!("Signature-based attestation:");
                match verify_signature_based_attestation(
                    &attestation.request_metadata.clone().unwrap_or_default(),
                    endorsed_evidence,
                ) {
                    Ok(_) => println!("Attestation verified successfully."),
                    Err(_) => println!("Attestation failed to verify"),
                }
            }
            &_ => println!("Unrecognized attestation type ID: {}", attestation_type_id),
        }
    }
}

fn verify_signature_based_attestation(
    request_metadata: &RequestMetadata,
    endorsed_evidence: &EndorsedEvidence,
) -> Result<AttestationResults> {
    let attestation_verifier = {
        // TODO: b/419209669 - update this to choose keys based on meaningful URI
        // values, once they are defined.
        let tink_public_keyset = GOOGLE_IDENTITY_PUBLIC_KEY;
        let signature_verifier = SignatureVerifier::new(tink_public_keyset);
        let certificate_verifier = CertificateVerifier::new(signature_verifier);
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
        EventLogVerifier::new(
            vec![Box::new(policy)],
            Arc::new(FrozenClock {
                timestamp: SystemTime::try_from(
                    request_metadata.request_time.clone().unwrap_or_default(),
                )?,
            }),
        )
    };
    attestation_verifier.verify(
        &endorsed_evidence.evidence.clone().unwrap_or_default(),
        &endorsed_evidence.endorsements.clone().unwrap_or_default(),
    )
}
