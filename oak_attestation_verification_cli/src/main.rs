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

#![feature(try_blocks)]

use std::{
    fs,
    time::{SystemTime, UNIX_EPOCH},
};

use anyhow::{anyhow, Result};
use clap::Parser;
use oak_attestation_gcp::{
    jwt::verification::{AttestationTokenVerificationReport, CertificateReport, IssuerReport},
    policy::{ConfidentialSpacePolicy, ConfidentialSpaceVerificationReport},
    CONFIDENTIAL_SPACE_ROOT_CERT_PEM,
};
use oak_attestation_verification::policy::session_binding_public_key::{
    SessionBindingPublicKeyPolicy, SessionBindingPublicKeyVerificationReport,
};
use oak_crypto::certificate::certificate_verifier::{
    CertificateVerificationReport, CertificateVerifier,
};
use oak_crypto_tink::signature_verifier::SignatureVerifier;
use oak_proto_rust::{
    attestation::{CERTIFICATE_BASED_ATTESTATION_ID, CONFIDENTIAL_SPACE_ATTESTATION_ID},
    oak::{
        attestation::v1::{
            reference_values, CertificateBasedReferenceValues, CollectedAttestation,
            ReferenceValues, ReferenceValuesCollection,
        },
        session::v1::{EndorsedEvidence, SessionBinding},
        Variant,
    },
};
use oak_session::session_binding::{SessionBindingVerifier, SignatureBindingVerifierBuilder};
use oak_time::Instant;
use p256::ecdsa::VerifyingKey;
use prost::Message;
use x509_cert::{der::DecodePem, Certificate};

#[derive(Parser, Debug)]
#[group(required = true)]
struct Flags {
    /// Path of the collected attestation, encoded as a binary protobuf.
    #[arg(long, value_parser = proto_parser::<CollectedAttestation>)]
    attestation: CollectedAttestation,

    #[arg(long, value_parser = proto_parser::<ReferenceValuesCollection>)]
    reference_values: ReferenceValuesCollection,
}

fn proto_parser<T: Message + std::default::Default>(s: &str) -> Result<T> {
    Ok(T::decode(fs::read(s)?.as_slice())?)
}

// Prints a format string with the given arguments, with the provided indent
// prefix. Defined as a macro to enable accepting a variable number of arguments
// to the format string.
macro_rules! print_indented {
    ($indent:expr, $fmt:expr $(, $args:expr)*) => {
        {
            let formatted_text = format!($fmt $(, $args)*);
            println!("{}{}", "\t".repeat($indent), formatted_text);
        }
    };
}

// Prints one of two format string options (dependent on the condition), with
// the provided indent prefix. Defined as a macro to enable accepting a variable
// number of arguments to the format strings.
macro_rules! print_indented_conditional {
    ($indent:expr, $condition:expr, ($($true_args:tt)+), ($($false_args:tt)+)) => {
        if $condition {
            print_indented!($indent, $($true_args)+);
        } else {
            print_indented!($indent, $($false_args)+);
        }
    };
}

fn main() {
    let Flags { attestation, reference_values: ReferenceValuesCollection { reference_values } } =
        Flags::parse();

    let attestation_timestamp = get_timestamp(&attestation);
    print_timestamp_report(&attestation_timestamp);
    let attestation_timestamp = attestation_timestamp.unwrap_or(Instant::UNIX_EPOCH);

    let handshake_hash = attestation.handshake_hash.clone();
    print_handshake_hash_report(&handshake_hash);

    // TODO: b/419209669 - push this loop (removing print statements) down into some
    // new attestation verification library function (with tests!); make it return
    // some combined result.
    for (attestation_type_id, endorsed_evidence) in attestation.endorsed_evidence.iter() {
        let session_binding = attestation.session_bindings.get(attestation_type_id);
        match attestation_type_id.as_str() {
            CONFIDENTIAL_SPACE_ATTESTATION_ID => {
                process_confidential_space_attestation(
                    attestation_timestamp,
                    &handshake_hash,
                    endorsed_evidence,
                    session_binding,
                );
            }
            CERTIFICATE_BASED_ATTESTATION_ID => {
                match reference_values.get(CERTIFICATE_BASED_ATTESTATION_ID) {
                    Some(ReferenceValues {
                        r#type:
                            Some(reference_values::Type::CertificateBased(
                                ref certificate_based_reference_values,
                            )),
                    }) => {
                        process_certificate_based_attestation(
                            certificate_based_reference_values,
                            attestation_timestamp,
                            &handshake_hash,
                            endorsed_evidence,
                            session_binding,
                        );
                    }
                    _ => {
                        println!(
                            "❓ Could not find reference values for certificate-based attestation"
                        );
                    }
                }
            }
            _ => {
                println!("❓ Unrecognized attestation type ID: {}", attestation_type_id);
            }
        };
    }
}

fn get_timestamp(attestation: &CollectedAttestation) -> anyhow::Result<Instant> {
    let request_time =
        attestation.request_metadata.clone().unwrap_or_default().request_time.unwrap_or_default();
    let system_time = SystemTime::try_from(request_time)?;
    let duration_since_epoch = system_time.duration_since(UNIX_EPOCH)?;
    Ok(Instant::from_unix_millis(duration_since_epoch.as_millis().try_into()?))
}

/// Prints out a report for the provided timestamp
fn print_timestamp_report(timestamp: &anyhow::Result<Instant>) {
    let indent = 0;
    print_indented!(indent, "🕠 Recorded timestamp:");
    match timestamp {
        Err(err) => {
            let indent = indent + 1;
            print_indented!(indent, "❌ is invalid: {:?}", err);
        }
        Ok(timestamp) => {
            let indent = indent + 1;
            print_indented_conditional!(
                indent,
                *timestamp != Instant::UNIX_EPOCH,
                ("✅ is valid: {}", *timestamp),
                ("❌ is unset")
            );
        }
    }
}

fn print_handshake_hash_report(handshake_hash: &[u8]) {
    let indent = 0;
    print_indented!(indent, "🤝 Session handshake:");
    let indent = indent + 1;
    if handshake_hash.is_empty() {
        print_indented!(indent, "❌ is missing");
    } else {
        print_indented!(indent, "✅ is present");
    }
}

fn process_confidential_space_attestation(
    attestation_timestamp: Instant,
    handshake_hash: &[u8],
    endorsed_evidence: &EndorsedEvidence,
    session_binding: Option<&SessionBinding>,
) {
    let indent = 0;
    print_indented!(indent, "🧾 Confidential Space attestation:");
    let indent = indent + 1;

    let event = find_single_event(endorsed_evidence);
    print_event_report(indent, &event);
    let endorsement = find_single_endorsement(endorsed_evidence);
    print_endorsement_report(indent, &endorsement);

    if let (Ok(event), Ok(endorsement)) = (event, endorsement) {
        let report = create_confidential_space_attestation_report(
            attestation_timestamp,
            &event,
            &endorsement,
        );
        print_confidential_space_attestation_report(indent, &report);
        print_session_binding_verification_report(
            handshake_hash,
            try { report?.session_binding_public_key },
            session_binding,
        );
    }
}

fn create_confidential_space_attestation_report(
    attestation_timestamp: Instant,
    event: &[u8],
    endorsement: &Variant,
) -> Result<ConfidentialSpaceVerificationReport> {
    let root_certificate =
        Certificate::from_pem(CONFIDENTIAL_SPACE_ROOT_CERT_PEM).map_err(anyhow::Error::msg)?;
    // TODO: b/434899976 - provide reference values for the workload endorsement.
    let policy = ConfidentialSpacePolicy::new_unendorsed(root_certificate);
    policy.report(attestation_timestamp, event, endorsement).map_err(anyhow::Error::msg)
}

fn print_confidential_space_attestation_report(
    indent: usize,
    report: &Result<ConfidentialSpaceVerificationReport>,
) {
    match report {
        Err(err) => {
            print_indented!(indent, "❌ is invalid: {}", err)
        }
        Ok(report) => {
            print_indented!(indent, "🔑 Public key:");
            {
                let indent = indent + 1;
                match &report.public_key_verification {
                    Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
                    Ok(()) => print_indented!(indent, "✅ verified successfully"),
                }
            }
            print_token_report(indent, &report.token_report);
            // TODO: b/434898491 - Print workload endorsement verification
        }
    }
}

fn print_token_report(indent: usize, report: &AttestationTokenVerificationReport) {
    print_indented!(indent, "🪙 Token verification:");
    let indent = indent + 1;
    let AttestationTokenVerificationReport { validity, verification, issuer_report } = report;
    match validity {
        Err(err) => print_indented!(indent, "❌ is invalid: {}", err),
        Ok(()) => print_indented!(indent, "✅ is valid"),
    }
    match verification {
        Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
        Ok(_) => print_indented!(indent, "✅ verified successfully"),
    }
    print_indented!(indent, "📜 Certificate chain:");
    print_certificate_chain(indent + 1, issuer_report);
}

fn print_certificate_chain(
    indent: usize,
    report: &Result<
        CertificateReport,
        oak_attestation_gcp::jwt::verification::AttestationVerificationError,
    >,
) {
    match report {
        Err(err) => print_indented!(indent, "❌ invalid: {}", err),
        Ok(report) => {
            print_indented!(indent, "📜 Certificate:");
            {
                let indent = indent + 1;
                match &report.validity {
                    Err(err) => print_indented!(indent, "❌ is invalid: {}", err),
                    Ok(()) => print_indented!(indent, "✅ is valid"),
                }
                match &report.verification {
                    Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
                    Ok(()) => print_indented!(indent, "✅ verified successfully"),
                }
            }
            match report.issuer_report.as_ref() {
                IssuerReport::OtherCertificate(report) => {
                    print_certificate_chain(indent, report);
                }
                IssuerReport::SelfSigned => {
                    print_indented!(indent + 1, "✍️ Self-signed");
                }
            }
        }
    }
}

fn process_certificate_based_attestation(
    reference_values: &CertificateBasedReferenceValues,
    attestation_timestamp: Instant,
    handshake_hash: &[u8],
    endorsed_evidence: &EndorsedEvidence,
    session_binding: Option<&SessionBinding>,
) {
    let indent = 0;
    print_indented!(indent, "🧾 Certificate-based attestation:");
    let indent = indent + 1;

    let event = find_single_event(endorsed_evidence);
    print_event_report(indent, &event);
    let endorsement = find_single_endorsement(endorsed_evidence);
    print_endorsement_report(indent, &endorsement);

    if let (Ok(event), Ok(endorsement)) = (event, endorsement) {
        let report = create_certificate_based_attestation_report(
            reference_values,
            attestation_timestamp,
            &event,
            &endorsement,
        );
        print_certificate_based_attestation_report(indent, &report);
        print_session_binding_verification_report(
            handshake_hash,
            try { report?.session_binding_public_key },
            session_binding,
        );
    }
}

fn create_certificate_based_attestation_report(
    reference_values: &CertificateBasedReferenceValues,
    attestation_timestamp: Instant,
    event: &[u8],
    endorsement: &Variant,
) -> Result<SessionBindingPublicKeyVerificationReport> {
    let policy = {
        let tink_public_keyset = reference_values.clone().ca.unwrap_or_default().tink_proto_keyset;
        let signature_verifier = SignatureVerifier::new(tink_public_keyset.as_slice());
        let certificate_verifier = CertificateVerifier::new(signature_verifier);
        SessionBindingPublicKeyPolicy::new(certificate_verifier)
    };
    policy.report(attestation_timestamp, event, endorsement).map_err(anyhow::Error::msg)
}

fn print_certificate_based_attestation_report(
    indent: usize,
    report: &Result<SessionBindingPublicKeyVerificationReport>,
) {
    match report {
        Err(err) => {
            print_indented!(indent, "❌ is invalid: {}", err)
        }
        Ok(session_binding_public_key_verification_report) => {
            match &session_binding_public_key_verification_report.endorsement {
                Err(err) => print_indented!(indent, "❌ is invalid: {}", err),
                Ok(certificate_verification_report) => {
                    print_certificate_verification_report(indent, certificate_verification_report)
                }
            }
        }
    }
}

fn print_certificate_verification_report(indent: usize, report: &CertificateVerificationReport) {
    print_indented!(indent, "📜 Certificate:");
    let indent = indent + 1;
    let CertificateVerificationReport { validity, verification, freshness: freshness_option } =
        report;
    match validity {
        Err(err) => print_indented!(indent, "❌ is invalid: {}", err),
        Ok(()) => print_indented!(indent, "✅ is valid"),
    }
    match verification {
        Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
        Ok(()) => print_indented!(indent, "✅ verified successfully"),
    }
    if let Some(freshness) = freshness_option {
        match freshness {
            Err(err) => print_indented!(indent, "❌ proof of freshness failed to verify: {}", err),
            Ok(()) => print_indented!(indent, "✅ is fresh"),
        }
    }
}

fn find_single_event(endorsed_evidence: &EndorsedEvidence) -> anyhow::Result<Vec<u8>> {
    let evidence = &endorsed_evidence.evidence.clone().ok_or(anyhow!("missing evidence"))?;
    let event_log = &evidence.event_log.clone().ok_or(anyhow!("missing event log"))?;
    let encoded_events = &event_log.encoded_events;
    if encoded_events.len() > 1 {
        Err(anyhow!("too many ({}) events (expected: 1)", encoded_events.len()))?;
    }
    Ok(encoded_events.iter().next().ok_or(anyhow!("missing event"))?.clone())
}

fn print_event_report(indent: usize, event: &anyhow::Result<Vec<u8>>) {
    match event {
        Err(ref err) => {
            print_indented!(indent, "❌ does not include usable evidence: {}", err);
        }
        Ok(_) => {
            print_indented!(indent, "✅ includes evidence");
        }
    }
}

fn find_single_endorsement(endorsed_evidence: &EndorsedEvidence) -> anyhow::Result<Variant> {
    let endorsements =
        &endorsed_evidence.endorsements.clone().ok_or(anyhow!("missing endorsements"))?;
    let events = &endorsements.events;
    if events.len() > 1 {
        Err(anyhow!("too many ({}) endorsements (expected: 1)", events.len()))?;
    }
    Ok(events.iter().next().ok_or(anyhow!("missing endorsement"))?.clone())
}

fn print_endorsement_report(indent: usize, endorsement: &anyhow::Result<Variant>) {
    match endorsement {
        Err(ref err) => {
            print_indented!(indent, "❌ does not include usable endorsement: {}", err);
        }
        Ok(_) => {
            print_indented!(indent, "✅ includes endorsement");
        }
    }
}

fn print_session_binding_verification_report(
    handshake_hash: &[u8],
    session_binding_public_key: Result<Vec<u8>>,
    session_binding: Option<&SessionBinding>,
) {
    let indent = 1;
    print_indented!(indent, "🔐 Session binding:");
    let indent = indent + 1;

    let session_binding_public_key = session_binding_public_key
        .inspect_err(|err| print_indented!(indent, "❌ key could not be obtained: {}", err))
        .ok();

    if session_binding.is_none() {
        print_indented!(indent, "❌ no binding found");
    }

    if let (Some(session_binding_public_key), Some(session_binding)) =
        (session_binding_public_key, session_binding)
    {
        match verify_session_binding(
            &session_binding_public_key,
            handshake_hash,
            &session_binding.binding,
        ) {
            Ok(()) => print_indented!(indent, "✅ verified successfully"),
            Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
        }
    }
}

fn verify_session_binding(
    session_binding_public_key: &[u8],
    handshake_hash: &[u8],
    binding: &[u8],
) -> anyhow::Result<()> {
    let verifying_key = VerifyingKey::from_sec1_bytes(session_binding_public_key)
        .map_err(|err| anyhow!("VerifyingKey construction failed: {}", err))?;
    let verifier = SignatureBindingVerifierBuilder::default()
        .verifier(Box::new(verifying_key))
        .build()
        .map_err(|err| anyhow!("SignatureBindingVerifier construction failed: {}", err))?;
    verifier.verify_binding(handshake_hash, binding)
}
