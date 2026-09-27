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

use std::{collections::BTreeMap, fs::File, io::Write, path::PathBuf};

use clap::Parser;
use oak_proto_rust::{
    attestation::CONFIDENTIAL_SPACE_ATTESTATION_ID,
    oak::attestation::v1::{
        ConfidentialSpaceReferenceValues, ReferenceValues, ReferenceValuesCollection,
        confidential_space_reference_values::ContainerImage, reference_values,
    },
};
use prost::Message;

#[derive(Parser, Debug)]
struct Flags {
    /// Path to the GCP Confidential Space root certificate PEM file.
    #[arg(long)]
    root_certificate_pem_path: PathBuf,

    /// Optional container image reference prefix to verify against.
    #[arg(long)]
    container_reference_prefix: Option<String>,

    /// Output path for the serialized ReferenceValuesCollection protobuf.
    #[arg(long)]
    output: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let flags = Flags::parse();

    let root_pem = std::fs::read_to_string(&flags.root_certificate_pem_path)?;

    let reference_values_collection = ReferenceValuesCollection {
        reference_values: BTreeMap::from([(
            CONFIDENTIAL_SPACE_ATTESTATION_ID.to_string(),
            ReferenceValues {
                r#type: Some(reference_values::Type::ConfidentialSpace(
                    ConfidentialSpaceReferenceValues {
                        root_certificate_pem: root_pem,
                        container_image: flags
                            .container_reference_prefix
                            .map(ContainerImage::ContainerImageReferencePrefix),
                    },
                )),
            },
        )]),
    };

    let mut file = File::create(&flags.output)?;
    file.write_all(&reference_values_collection.encode_to_vec())?;

    println!("ReferenceValuesCollection written to '{}'", flags.output.display());

    Ok(())
}
