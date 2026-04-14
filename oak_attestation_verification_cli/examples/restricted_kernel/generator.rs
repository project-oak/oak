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
use std::{collections::BTreeMap, fs::File, io::Write, path::PathBuf};

use clap::Parser;
use oak_proto_rust::{
    attestation::RESTRICTED_KERNEL_ATTESTATION_ID,
    oak::{
        attestation::v1::{
            CollectedAttestation, Endorsements, Evidence, ReferenceValuesCollection,
            collected_attestation::RequestMetadata,
        },
        session::v1::EndorsedEvidence,
    },
};
use prost::Message;

#[derive(Parser, Debug)]
struct Flags {
    #[arg(long)]
    collected_attestation_out: PathBuf,
    #[arg(long)]
    reference_values_out: PathBuf,
}

const HANDSHAKE: &str = "handshake!";

fn main() -> anyhow::Result<()> {
    let Flags { collected_attestation_out, reference_values_out } = Flags::parse();

    let now = oak_time::Instant::from_unix_seconds(1757424000);

    // Load golden dumps to satisfy complex X.509 DER signature chains in
    // verify_root_attestation_signature.
    let evidence_bytes = include_bytes!("milan_rk_release_evidence.binarypb");
    let endorsements_bytes = include_bytes!("milan_rk_release_endorsements.binarypb");

    let evidence = Evidence::decode(evidence_bytes.as_slice())?;
    let endorsements = Endorsements::decode(endorsements_bytes.as_slice())?;

    let extracted = oak_attestation_verification::extract_evidence(&evidence)?;
    let rvs = test_util::create_reference_values_for_extracted_evidence(extracted);

    let collected_attestation = CollectedAttestation {
        request_metadata: Some(RequestMetadata {
            request_time: Some(now.into_timestamp()),
            uri: "some://golden".to_string(),
        }),
        endorsed_evidence: BTreeMap::from([(
            RESTRICTED_KERNEL_ATTESTATION_ID.to_string(),
            EndorsedEvidence { evidence: Some(evidence), endorsements: Some(endorsements) },
        )]),
        // Static offline golden evidence contains no live session bindings.
        session_bindings: BTreeMap::new(),
        handshake_hash: HANDSHAKE.as_bytes().to_vec(),
    };

    let reference_values_collection = ReferenceValuesCollection {
        reference_values: BTreeMap::from([(RESTRICTED_KERNEL_ATTESTATION_ID.to_string(), rvs)]),
    };

    // Write output files.
    let mut file = File::create(collected_attestation_out)?;
    file.write_all(&collected_attestation.encode_to_vec())?;
    let mut file = File::create(reference_values_out)?;
    file.write_all(&reference_values_collection.encode_to_vec())?;

    Ok(())
}
