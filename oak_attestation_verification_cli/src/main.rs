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

mod print;
mod report;

use std::{
    fmt::Write,
    fs,
    path::Path,
    time::{SystemTime, UNIX_EPOCH},
};

use anyhow::anyhow;
use clap::Parser;
use oak_proto_rust::{
    attestation::{CERTIFICATE_BASED_ATTESTATION_ID, CONFIDENTIAL_SPACE_ATTESTATION_ID},
    oak::{
        attestation::v1::{
            reference_values, CollectedAttestation, ReferenceValues, ReferenceValuesCollection,
        },
        session::v1::EndorsedEvidence,
        Variant,
    },
};
use oak_time::Instant;
use prost::Message;

use crate::{print::print_indented, report::VerificationReport};

#[derive(Parser, Debug)]
#[group(required = true)]
struct Flags {
    /// Path of the collected attestation, encoded as a binary protobuf.
    #[arg(long, value_parser = proto_decoder::<CollectedAttestation>)]
    attestation: CollectedAttestation,

    #[arg(long, value_parser = proto_decoder::<ReferenceValuesCollection>)]
    reference_values: ReferenceValuesCollection,
}

/// Decodes the (binary format) proto stored in the [path] file. [path] may be
/// an absolute or relative file path.
fn proto_decoder<T: Message + std::default::Default>(path: &str) -> anyhow::Result<T> {
    // https://bazel.build/docs/user-manual#running-executables
    let path = Path::new(&std::env::var("BUILD_WORKING_DIRECTORY").unwrap_or_default()).join(path);
    Ok(T::decode(fs::read(path)?.as_slice())?)
}

fn main() -> std::fmt::Result {
    let Flags { attestation, reference_values: ReferenceValuesCollection { reference_values } } =
        Flags::parse();

    let mut buffer = String::new();
    let indent = 0;

    let attestation_timestamp = get_timestamp(&attestation);
    print_report_header(
        &mut buffer,
        indent,
        &attestation.request_metadata.unwrap_or_default().uri,
        &attestation_timestamp,
    )?;
    let attestation_timestamp = attestation_timestamp.unwrap_or(Instant::UNIX_EPOCH);

    let handshake_hash = attestation.handshake_hash.clone();
    print_handshake_hash_report(&mut buffer, indent, &handshake_hash)?;

    for (attestation_type_id, endorsed_evidence) in attestation.endorsed_evidence.iter() {
        match process_attestation(
            attestation_type_id.clone(),
            endorsed_evidence,
            attestation_timestamp,
            reference_values.get(attestation_type_id),
        ) {
            Ok(ref report) => {
                report.print(
                    &mut buffer,
                    indent,
                    &handshake_hash,
                    attestation.session_bindings.get(attestation_type_id),
                )?;
            }
            Err(ref err) => {
                print_indented!(
                    &mut buffer,
                    indent,
                    "❌ Provided attestation is invalid: {}",
                    err
                )?;
            }
        }
    }
    println!("{}", buffer);
    Ok(())
}

// TODO: b/419209669 - add tests for process_attestation (or perhaps more
// correctly the VerificationReport constructors).
fn process_attestation(
    attestation_type_id: String,
    endorsed_evidence: &EndorsedEvidence,
    attestation_timestamp: Instant,
    reference_values: Option<&ReferenceValues>,
) -> anyhow::Result<VerificationReport> {
    match attestation_type_id.as_str() {
        CONFIDENTIAL_SPACE_ATTESTATION_ID => match reference_values {
            Some(ReferenceValues {
                r#type:
                    Some(reference_values::Type::ConfidentialSpace(
                        ref confidential_space_reference_values,
                    )),
            }) => VerificationReport::confidential_space(
                confidential_space_reference_values,
                attestation_timestamp,
                &find_single_event(endorsed_evidence)?,
                &find_single_endorsement(endorsed_evidence)?,
            ),
            _ => Err(anyhow!("Found no reference values")),
        },
        CERTIFICATE_BASED_ATTESTATION_ID => match reference_values {
            Some(ReferenceValues {
                r#type:
                    Some(reference_values::Type::CertificateBased(
                        ref certificate_based_reference_values,
                    )),
            }) => VerificationReport::certificate_based(
                certificate_based_reference_values,
                attestation_timestamp,
                &find_single_event(endorsed_evidence)?,
                &find_single_endorsement(endorsed_evidence)?,
            ),
            _ => Err(anyhow!("Found no reference values")),
        },
        _ => Err(anyhow!("Unrecognized attestation type ID: {}", attestation_type_id)),
    }
}

fn get_timestamp(attestation: &CollectedAttestation) -> anyhow::Result<Instant> {
    let request_time =
        attestation.request_metadata.clone().unwrap_or_default().request_time.unwrap_or_default();
    let system_time = SystemTime::try_from(request_time)?;
    let duration_since_epoch = system_time.duration_since(UNIX_EPOCH)?;
    Ok(Instant::from_unix_millis(duration_since_epoch.as_millis().try_into()?))
}

/// Prints out the report header.
fn print_report_header(
    writer: &mut impl Write,
    indent: usize,
    uri: &String,
    timestamp: &anyhow::Result<Instant>,
) -> std::fmt::Result {
    print_indented!(writer, indent, "🔗 {}", uri)?;
    print_indented!(writer, indent, "🕠 Recorded timestamp:")?;
    match timestamp {
        Err(err) => {
            let indent = indent + 1;
            print_indented!(writer, indent, "❌ is invalid: {:?}", err)?;
        }
        Ok(timestamp) => {
            let indent = indent + 1;
            if *timestamp != Instant::UNIX_EPOCH {
                print_indented!(writer, indent, "✅ is valid: {}", *timestamp)?;
            } else {
                print_indented!(writer, indent, "❌ is unset")?;
            }
        }
    }
    Ok(())
}

fn print_handshake_hash_report(
    writer: &mut impl Write,
    indent: usize,
    handshake_hash: &[u8],
) -> std::fmt::Result {
    print_indented!(writer, indent, "🤝 Session handshake:")?;
    let indent = indent + 1;
    if handshake_hash.is_empty() {
        print_indented!(writer, indent, "❌ is missing")?;
    } else {
        print_indented!(writer, indent, "✅ is present")?;
    }
    Ok(())
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

fn find_single_endorsement(endorsed_evidence: &EndorsedEvidence) -> anyhow::Result<Variant> {
    let endorsements =
        &endorsed_evidence.endorsements.clone().ok_or(anyhow!("missing endorsements"))?;
    let events = &endorsements.events;
    if events.len() > 1 {
        Err(anyhow!("too many ({}) endorsements (expected: 1)", events.len()))?;
    }
    Ok(events.iter().next().ok_or(anyhow!("missing endorsement"))?.clone())
}
