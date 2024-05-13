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
//

use std::{fs, path::PathBuf};

use clap::Parser;
use oak_attestation_explain::{HumanReadableExplanation, HumanReadableTitle};
use oak_attestation_verification_test_utils::reference_values_from_evidence;
use oak_proto_rust::oak::attestation::v1::{
    extracted_evidence::EvidenceValues, Evidence, OakRestrictedKernelData,
};
use prost::Message;

#[derive(Parser, Debug)]
#[group(skip)]
pub struct Params {
    /// Path to the evidence to inspect.
    #[arg(long, value_parser = path_exists, default_value = "oak_attestation_explain/testdata/rk_evidence.binarypb")]
    pub evidence: PathBuf,
}

fn path_exists(s: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(s);
    if !fs::metadata(s).map_err(|err| err.to_string())?.is_file() {
        Err(String::from("path does not represent a file"))
    } else {
        Ok(path)
    }
}

fn title(title: &str) -> String {
    format!(
        "



# {}
",
        title
    )
}

fn segment_title(title: &str, description: &str) -> String {
    format!(
        "

## {}
{}
",
        title, description
    )
}

fn main() {
    let extracted_evidence = {
        let Params { evidence } = Params::parse();
        let evidence = {
            let serialized = fs::read(evidence).expect("could not read evidence");
            Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
        };

        oak_attestation_verification::verifier::extract_evidence(&evidence).unwrap()
    };

    print!("{}", title("Evidence:"));

    match extracted_evidence.evidence_values.clone().take() {
        Some(EvidenceValues::OakRestrictedKernel(restricted_kernel_evidence)) => {
            match restricted_kernel_evidence {
                OakRestrictedKernelData {
                    root_layer: Some(root_layer),
                    kernel_layer: Some(kernel_layer),
                    application_layer: Some(application_layer),
                } => {
                    print!(
                        "{}",
                        segment_title(
                            &root_layer.title().unwrap(),
                            &root_layer.description().unwrap()
                        )
                    );
                    print!(
                        "{}",
                        segment_title(
                            &kernel_layer.title().unwrap(),
                            &kernel_layer.description().unwrap(),
                        )
                    );
                    print!(
                        "{}",
                        segment_title(
                            &application_layer.title().unwrap(),
                            &application_layer.description().unwrap(),
                        )
                    );
                    println!();
                }
                _ => panic!("evidence values unexpectedly unset"),
            }
        }
        _ => panic!("not restricted kernel evidence"),
    };

    let reference_values = reference_values_from_evidence(extracted_evidence);

    print!("{}", title("Reference values that describe this evidence:"));

    print!(
        "{}
        ",
        reference_values.description().expect("could not get reference values description")
    )
}
