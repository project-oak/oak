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
    time::{SystemTime, UNIX_EPOCH},
};

use anyhow::Result;
use base64::{prelude::BASE64_STANDARD, Engine as _};
use clap::Parser;
use oak_attestation_verification::policy::session_binding_public_key::SessionBindingPublicKeyPolicy;
use oak_crypto::certificate::certificate_verifier::{
    CertificateVerificationReport, CertificateVerifier,
};
use oak_crypto_tink::signature_verifier::SignatureVerifier;
use oak_proto_rust::{
    attestation::SIGNATURE_BASED_ATTESTATION_ID,
    oak::{attestation::v1::CollectedAttestation, session::v1::EndorsedEvidence},
};
use oak_time::Instant;
use prost::Message;

static GOOGLE_IDENTITY_PUBLIC_KEYSET: &[u8; 459] =
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
    let Flags { attestation } = Flags::parse();

    let attestation_timestamp = print_timestamp_report(&attestation);

    // TODO: b/419209669 - push this loop (removing print statements) down into some
    // new attestation verification library function (with tests!); make it return
    // some combined result.
    for (attestation_type_id, endorsed_evidence) in attestation.endorsed_evidence.iter() {
        match attestation_type_id.as_str() {
            SIGNATURE_BASED_ATTESTATION_ID => {
                print_signature_based_attestation_report(attestation_timestamp, endorsed_evidence)
            }
            _ => println!("❓ Unrecognized attestation type ID: {}", attestation_type_id),
        }
    }
}

// Returns the timestamp at which the provided attestation was recorded.
// Prints out a report of any success/error states.
fn print_timestamp_report(attestation: &CollectedAttestation) -> Instant {
    let request_time =
        attestation.request_metadata.clone().unwrap_or_default().request_time.unwrap_or_default();
    match SystemTime::try_from(request_time) {
        Err(err) => {
            println!("❌ 🕠 Attestation timestamp is invalid: {:?}", err);
            Instant::UNIX_EPOCH
        }
        Ok(system_time) => match system_time.duration_since(UNIX_EPOCH) {
            Err(err) => {
                println!("❌ 🕠 Attestation timestamp is invalid: {:?}", err);
                Instant::UNIX_EPOCH
            }
            Ok(duration_since_epoch) => match duration_since_epoch.as_millis().try_into() {
                Err(err) => {
                    println!("❌ 🕠 Attestation timestamp is invalid: {:?}", err);
                    Instant::UNIX_EPOCH
                }
                Ok(millis) => {
                    print_indented_conditional!(
                        0,
                        millis != 0,
                        ("✅ 🕠 Attestation timestamp, in millis since epoch: {}", millis),
                        ("❌ 🕠 Attestation timestamp appears to be unset")
                    );
                    Instant::from_unix_millis(millis)
                }
            },
        },
    }
}

fn print_signature_based_attestation_report(
    attestation_timestamp: Instant,
    endorsed_evidence: &EndorsedEvidence,
) {
    let indent = 0;
    let event = match &endorsed_evidence.evidence {
        None => {
            print_indented!(indent, "❌ 🧾 Attestation is missing evidence");
            Option::None
        }
        Some(evidence) => {
            print_indented!(indent, "✅ 🧾 Attestation includes evidence");
            let indent = indent + 1;
            match &evidence.event_log {
                None => {
                    print_indented!(indent, "❌ 🧾 Attestation evidence is missing event log");
                    Option::None
                }
                Some(event_log) => {
                    print_indented!(indent, "✅ 🧾 Attestation evidence includes event log");
                    let encoded_events = &event_log.encoded_events;
                    if encoded_events.len() != 1 {
                        print_indented!(indent, "❌ 🧾 Attestation evidence event log must contain a single event, but contains {} event(s)", encoded_events.len());
                        Option::None
                    } else {
                        print_indented!(
                            indent,
                            "✅ Attestation evidence event log has single event"
                        );
                        encoded_events.iter().next()
                    }
                }
            }
        }
    };

    let endorsement = match &endorsed_evidence.endorsements {
        None => {
            print_indented!(indent, "❌ Attestation is missing endorsements");
            Option::None
        }
        Some(endorsements) => {
            print_indented!(indent, "✅ Attestation includes endorsements");
            let indent = indent + 1;
            let events = &endorsements.events;
            if events.len() != 1 {
                print_indented!(indent, "❌ Attestation must contain a single endorsement, but contains {} endorsement(s)", events.len());
                Option::None
            } else {
                print_indented!(indent, "✅ Attestation includes a single endorsement");
                events.iter().next()
            }
        }
    };

    if let (Some(event), Some(endorsement)) = (event, endorsement) {
        let report = {
            // TODO: b/419209669 - update this to choose keys based on meaningful URI
            // values, once they are defined.
            let tink_public_keyset = GOOGLE_IDENTITY_PUBLIC_KEYSET;
            let signature_verifier = SignatureVerifier::new(tink_public_keyset);
            let certificate_verifier = CertificateVerifier::new(signature_verifier);
            let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
            policy.report(attestation_timestamp, event, endorsement)
        };

        match report {
            Err(err) => {
                print_indented!(indent, "❌ Attestation verification failed: {}", err)
            }
            Ok(session_binding_public_key_verification_report) => {
                print_indented!(indent, "Attestation verification:");
                let indent = indent + 1;
                match session_binding_public_key_verification_report.endorsement {
                    Err(err) => {
                        print_indented!(
                            indent,
                            "❌ Endorsement certificate verification failed: {}",
                            err
                        );
                    }
                    Ok(CertificateVerificationReport { validity, verification }) => {
                        match validity {
                            Err(err) => {
                                print_indented!(
                                    indent,
                                    "❌ 📜 Endorsement certificate is invalid: {}",
                                    err
                                )
                            }
                            Ok(()) => {
                                print_indented!(indent, "✅ 📜 Endorsement certificate is valid")
                            }
                        }
                        match verification {
                            Err(err) => {
                                print_indented!(
                                    indent,
                                    "❌ 📜 Endorsement certificate verification failed: {}",
                                    err
                                )
                            }
                            Ok(()) => {
                                print_indented!(
                                    indent,
                                    "✅ 📜 Endorsement certificate verification succeeded"
                                )
                            }
                        }
                    }
                }
            }
        }
    }
}
