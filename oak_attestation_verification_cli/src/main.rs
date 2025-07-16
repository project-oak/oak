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
use base64::{prelude::BASE64_STANDARD, Engine as _};
use clap::Parser;
use oak_attestation_verification::policy::session_binding_public_key::SessionBindingPublicKeyPolicy;
use oak_crypto::certificate::certificate_verifier::{
    CertificateVerificationReport, CertificateVerifier,
};
use oak_crypto_tink::signature_verifier::SignatureVerifier;
use oak_proto_rust::{
    attestation::SIGNATURE_BASED_ATTESTATION_ID,
    oak::{attestation::v1::CollectedAttestation, session::v1::EndorsedEvidence, Variant},
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
    let timestamp: anyhow::Result<Instant> = try {
        let system_time = SystemTime::try_from(request_time)?;
        let duration_since_epoch = system_time.duration_since(UNIX_EPOCH)?;
        Instant::from_unix_millis(duration_since_epoch.as_millis().try_into()?)
    };
    let indent = 0;
    print_indented!(indent, "🕠 Recorded timestamp:");
    match timestamp {
        Err(err) => {
            let indent = indent + 1;
            print_indented!(indent, "❌ is invalid: {:?}", err);
            Instant::UNIX_EPOCH
        }
        Ok(timestamp) => {
            let indent = indent + 1;
            print_indented_conditional!(
                indent,
                timestamp != Instant::UNIX_EPOCH,
                ("✅ is valid: {:?}", timestamp),
                ("❌ is unset")
            );
            timestamp
        }
    }
}

fn print_signature_based_attestation_report(
    attestation_timestamp: Instant,
    endorsed_evidence: &EndorsedEvidence,
) {
    let indent = 0;
    print_indented!(indent, "🧾 Attestation contents:");

    let event: anyhow::Result<Vec<u8>> = try {
        let evidence = &endorsed_evidence.evidence.clone().ok_or(anyhow!("missing evidence"))?;
        let event_log = &evidence.event_log.clone().ok_or(anyhow!("missing event log"))?;
        let encoded_events = &event_log.encoded_events;
        if encoded_events.len() > 1 {
            Err(anyhow!("too many ({}) events (expected: 1)", encoded_events.len()))?;
        }
        encoded_events.iter().next().ok_or(anyhow!("missing event"))?.clone()
    };
    {
        let indent = indent + 1;
        match event {
            Err(ref err) => {
                print_indented!(indent, "❌ does not include usable evidence: {}", err);
            }
            Ok(_) => {
                print_indented!(indent, "✅ includes evidence");
            }
        }
    }

    let endorsement: anyhow::Result<Variant> = try {
        let endorsements =
            &endorsed_evidence.endorsements.clone().ok_or(anyhow!("missing endorsements"))?;
        let events = &endorsements.events;
        if events.len() > 1 {
            Err(anyhow!("too many ({}) endorsements (expected: 1)", events.len()))?;
        }
        events.iter().next().ok_or(anyhow!("missing endorsement"))?.clone()
    };
    {
        let indent = indent + 1;
        match endorsement {
            Err(ref err) => {
                print_indented!(indent, "❌ does not include usable endorsement: {}", err);
            }
            Ok(_) => {
                print_indented!(indent, "✅ includes endorsement");
            }
        }
    }

    if let (Ok(event), Ok(endorsement)) = (event, endorsement) {
        let report = {
            // TODO: b/419209669 - update this to choose keys based on meaningful URI
            // values, once they are defined.
            let tink_public_keyset = GOOGLE_IDENTITY_PUBLIC_KEYSET;
            let signature_verifier = SignatureVerifier::new(tink_public_keyset);
            let certificate_verifier = CertificateVerifier::new(signature_verifier);
            let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
            policy.report(attestation_timestamp, &event, &endorsement)
        };

        print_indented!(indent, "🛂 Attestation verification:");

        {
            let indent = indent + 1;
            match report {
                Err(err) => {
                    print_indented!(indent, "❌ failed: {}", err)
                }
                Ok(session_binding_public_key_verification_report) => {
                    match session_binding_public_key_verification_report.endorsement {
                        Err(err) => {
                            print_indented!(indent, "❌ failed: {}", err);
                        }
                        Ok(CertificateVerificationReport { validity, verification }) => {
                            print_indented!(indent, "📜 Certificate:");
                            {
                                let indent = indent + 1;
                                match validity {
                                    Err(err) => {
                                        print_indented!(indent, "❌ is invalid: {}", err)
                                    }
                                    Ok(()) => {
                                        print_indented!(indent, "✅ is valid")
                                    }
                                }
                                match verification {
                                    Err(err) => {
                                        print_indented!(indent, "❌ failed to verify: {}", err)
                                    }
                                    Ok(()) => {
                                        print_indented!(indent, "✅ verified successfully")
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
