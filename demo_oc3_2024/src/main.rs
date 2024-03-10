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

#[derive(clap::Parser, Clone, Debug, PartialEq)]
pub struct Params {
    /// Path to the evidence to verify.
    #[arg(long, value_parser = path_exists, default_value = "demo_oc3_2024/testdata/evidence.binarypb")]
    pub evidence: PathBuf,

    /// Path endorsements.
    #[arg(long, value_parser = path_exists, default_value = "demo_oc3_2024/testdata/endorsements.binarypb")]
    pub endorsements: PathBuf,

    /// Expected Sha2-384 hash of the initial measurement of the VM memory in the attestation
    /// report.
    #[arg(
        long,
        value_parser = parse_hex_sha2_384_hash,
        // Obtained by building stage0 and getting its measurement:
        // `just stage0_bin`
        // `cargo run -p snp_measurement -- --stage0-rom="./stage0_bin/target/x86_64-unknown-none/release/stage0_bin"`
        default_value = "f6df2054a387f3f829914196086d5992646b7cbd834270c4db205cd36879977ee06016c1e65c9ec453e334a1353e933a"
    )]
    pub initial_measurement: BinaryReferenceValue,

    /// Expected Sha2-256 hash of the Restricted Kernel.
    #[arg(
        long,
        value_parser = parse_hex_sha2_256_hash,
        // Obtained by building Restricted Kernel and getting its measurement:
        // `just oak_restricted_kernel_simple_io_wrapper`
        // `cargo run -p oak_kernel_measurement -- --kernel=./oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/oak_restricted_kernel_simple_io_wrapper_bin`
        default_value = "cc8ea3ca6ac5e0a773e25b1f0f7df56aeee077421b5286fde5424f630507fb4e"
    )]
    pub kernel_hash: BinaryReferenceValue,

    /// Expected Sha2-256 hash of the setup data for the Restricted Kernel.
    #[arg(
            long,
            value_parser = parse_hex_sha2_256_hash,
            // Obtained by building Restricted Kernel and getting its measurement:
            // `just oak_restricted_kernel_simple_io_wrapper`
            // `cargo run -p oak_kernel_measurement -- --kernel=./oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/oak_restricted_kernel_simple_io_wrapper_bin`
            default_value = "4cd020820da663063f4185ca14a7e803cd7c9ca1483c64e836db840604b6fac1"
        )]
    pub kernel_setup_data_hash: BinaryReferenceValue,

    /// Expected Sha2-256 hash of the Enclave Application.
    #[arg(
        long,
        value_parser = parse_hex_sha2_256_hash,
        // Obtained by building Oak Functions enclave application and getting its measurement:
        // `just oak_functions_enclave_app`
        // `sha256sum ./enclave_apps/target/x86_64-unknown-none/release/oak_functions_enclave_app`
        default_value = "adda5dc6e483ddb49bbb53d8d73b40486eb5fde2c41986074c6e2ea489e0f328"
    )]
    pub app_hash: BinaryReferenceValue,
}

pub fn path_exists(s: &str) -> Result<std::path::PathBuf, String> {
    let path = std::path::PathBuf::from(s);
    if !std::fs::metadata(s)
        .map_err(|err| err.to_string())?
        .is_file()
    {
        Err(String::from("path does not represent a file"))
    } else {
        Ok(path)
    }
}

pub fn parse_hex_sha2_256_hash(hex_sha2_256_hash: &str) -> Result<BinaryReferenceValue, String> {
    let mut raw_digest = RawDigest::default();
    raw_digest.sha2_256 =
        hex::decode(hex_sha2_256_hash).map_err(|_| "failed to parse hash".to_string())?;
    let digests = [raw_digest].to_vec();
    Ok(BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Digests(Digests { digests })),
    })
}

pub fn parse_hex_sha2_384_hash(hex_sha2_384_hash: &str) -> Result<BinaryReferenceValue, String> {
    let mut raw_digest = RawDigest::default();
    raw_digest.sha2_384 =
        hex::decode(hex_sha2_384_hash).map_err(|_| "failed to parse hash".to_string())?;
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
            amd_root_public_key: b"".to_vec(),
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
    println!("extrated evidence: {:?}", extracted_evidence);
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
