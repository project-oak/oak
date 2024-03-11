//
// Copyright 2024 The Project Oak Authors
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

use std::{fs, path::PathBuf};

use clap::Parser;
use oak_attestation_verification::verifier::{to_attestation_results, verify};
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results::Status, binary_reference_value, reference_values,
        AmdSevReferenceValues, ApplicationLayerReferenceValues, BinaryReferenceValue, Digests,
        Endorsements, Evidence, KernelLayerReferenceValues, OakRestrictedKernelReferenceValues,
        ReferenceValues, RootLayerReferenceValues, SkipVerification,
    },
    RawDigest,
};
use prost::Message;

// Timestamp taken for the purpose of demo: 5 Mar 2024, 12:27 UTC.
const NOW_UTC_MILLIS: i64 = 1709641620000;

#[derive(Parser, Clone, Debug, PartialEq)]
pub struct Params {
    /// Path to the evidence to verify.
    #[arg(long, value_parser = path_exists)]
    pub evidence: PathBuf,

    /// Path endorsements.
    #[arg(long, value_parser = path_exists)]
    pub endorsements: PathBuf,

    /// Expected Sha2-384 hash of the initial measurement of the VM memory in the attestation
    /// report.
    #[arg(
        long,
        value_parser = parse_hex_sha2_384_hash
    )]
    pub initial_measurement: BinaryReferenceValue,

    /// Expected Sha2-256 hash of the Restricted Kernel.
    #[arg(
        long,
        value_parser = parse_hex_sha2_256_hash
    )]
    pub kernel_hash: BinaryReferenceValue,

    /// Expected Sha2-256 hash of the setup data for the Restricted Kernel.
    #[arg(
            long,
            value_parser = parse_hex_sha2_256_hash
        )]
    pub kernel_setup_data_hash: BinaryReferenceValue,

    /// Expected Sha2-256 hash of the Enclave Application.
    #[arg(
        long,
        value_parser = parse_hex_sha2_256_hash
    )]
    pub app_hash: BinaryReferenceValue,
}

pub fn path_exists(s: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(s);
    if !fs::metadata(s).map_err(|err| err.to_string())?.is_file() {
        Err(String::from("path does not represent a file"))
    } else {
        Ok(path)
    }
}

pub fn parse_hex_sha2_256_hash(hex_sha2_256_hash: &str) -> Result<BinaryReferenceValue, String> {
    let hash = {
        let parts: Vec<&str> = hex_sha2_256_hash.split(':').collect();
        if parts[0] != "sha2-256" || parts.len() != 2 {
            println!("Invalid input format");
            return Err("invalid hash".to_string());
        }
        parts[1]
    };
    let raw_digest = RawDigest {
        sha2_256: hex::decode(hash).map_err(|_| "failed to parse hash".to_string())?,
        ..Default::default()
    };
    let digests = [raw_digest].to_vec();
    Ok(BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Digests(Digests { digests })),
    })
}

pub fn parse_hex_sha2_384_hash(hex_sha2_384_hash: &str) -> Result<BinaryReferenceValue, String> {
    let hash = {
        let parts: Vec<&str> = hex_sha2_384_hash.split(':').collect();
        if parts[0] != "sha2-384" || parts.len() != 2 {
            println!("Invalid input format");
            return Err("invalid hash".to_string());
        }
        parts[1]
    };
    let raw_digest = RawDigest {
        sha2_384: hex::decode(hash).map_err(|_| "failed to parse hash".to_string())?,
        ..Default::default()
    };
    let digests = [raw_digest].to_vec();
    Ok(BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Digests(Digests { digests })),
    })
}

fn main() {
    let Params {
        evidence,
        endorsements,
        initial_measurement,
        kernel_hash,
        kernel_setup_data_hash,
        app_hash,
    } = Params::parse();

    let serialized_evidence = fs::read(evidence).expect("couldn't read evidence");
    let evidence =
        Evidence::decode(serialized_evidence.as_slice()).expect("couldn't decode evidence");

    let serialized_endorsements = fs::read(endorsements).expect("couldn't read endorsements");
    let endorsements = Endorsements::decode(serialized_endorsements.as_slice())
        .expect("couldn't decode endorsements");

    let reference_values = {
        let skip = BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Skip(
                SkipVerification::default(),
            )),
        };

        let amd_sev = AmdSevReferenceValues {
            // This field is empty, because it's outdated, and AMD certificates are currently
            // built-in the Attestation Verification Library itself:
            // https://github.com/project-oak/oak/blob/24a34be872de77f1b9109e1b1fd2b8236f4f5aa0/oak_attestation_verification/src/verifier.rs#L66
            amd_root_public_key: vec![],
            firmware_version: None,
            allow_debug: false,
            stage0: Some(initial_measurement),
        };

        let root_layer = RootLayerReferenceValues {
            amd_sev: Some(amd_sev),
            ..Default::default()
        };
        let kernel_layer = KernelLayerReferenceValues {
            kernel_image: Some(kernel_hash),
            kernel_cmd_line: Some(skip.clone()),
            kernel_setup_data: Some(kernel_setup_data_hash),
            init_ram_fs: Some(skip.clone()),
            memory_map: Some(skip.clone()),
            acpi: Some(skip.clone()),
        };

        let application_layer = ApplicationLayerReferenceValues {
            binary: Some(app_hash),
            configuration: Some(skip.clone()),
        };

        let reference_values = OakRestrictedKernelReferenceValues {
            root_layer: Some(root_layer),
            kernel_layer: Some(kernel_layer),
            application_layer: Some(application_layer),
        };
        ReferenceValues {
            r#type: Some(reference_values::Type::OakRestrictedKernel(
                reference_values,
            )),
        }
    };

    let extracted_evidence = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let attestation_results = to_attestation_results(&extracted_evidence);

    match attestation_results.status() {
        Status::Success => println!("Verification successful"),
        Status::GenericFailure => {
            eprintln!(
                "Couldn't verify endorsed evidence: code={} reason={}",
                attestation_results.status as i32, attestation_results.reason
            );
        }
        Status::Unspecified => eprintln!("Illegal status code in attestation results"),
    }
}
