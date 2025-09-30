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

//! Sends a string to the enclave app and prints the return.

use std::{fs, sync::Arc};

use anyhow::Context;
use clap::{Parser, ValueEnum};
use oak_functions_standalone_client_lib::{
    default_oak_functions_standalone_reference_values, OakFunctionsClient,
};
use oak_proto_rust::oak::attestation::v1::ConfidentialSpaceReferenceValues;
use oak_session::attestation::AttestationType;
use oak_time::Clock;
use oak_time_std::clock::FrozenSystemTimeClock;
use prost::Message;

// Supported AttestationTypes for Google Cloud Platform, derived from
// oak/oak_session/src/attestation.rs.
#[derive(Debug, Clone, Eq, PartialEq, ValueEnum)]
enum AttestationTypeParam {
    Unattested,
    PeerUnidirectional,
}

#[derive(Parser, Clone, Debug)]
#[command(about = "Oak Functions Standalone Client")]
pub struct Opt {
    #[arg(
        long,
        help = "URI of the Oak Functions Standalone enclave application to connect to",
        default_value = "http://localhost:8080"
    )]
    uri: String,

    #[arg(long, help = "Request to send Oak Functions standalone")]
    request: String,

    #[arg(long, help = "Attestation type", value_enum, default_value_t = AttestationTypeParam::Unattested)]
    attestation_type: AttestationTypeParam,

    #[arg(
        long,
        help = "Path to save the attestation evidence to. If not specified, the attestation is not saved."
    )]
    attestation_evidence_path: Option<String>,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::parse();

    let attestation_type = match opt.attestation_type {
        AttestationTypeParam::Unattested => AttestationType::Unattested,
        AttestationTypeParam::PeerUnidirectional => AttestationType::PeerUnidirectional,
    };

    let clock: Arc<dyn Clock> = Arc::new(FrozenSystemTimeClock::default());

    let ref_values: ConfidentialSpaceReferenceValues =
        default_oak_functions_standalone_reference_values();
    let mut client =
        OakFunctionsClient::create(&opt.uri, attestation_type, clock.clone(), Some(&ref_values))
            .await
            .context("couldn't connect to server")?;

    if let Some(path) = opt.attestation_evidence_path {
        let attestation =
            client.fetch_attestation(opt.uri, clock).context("unable to parse attestation")?;
        fs::write(path, attestation.encode_to_vec())?;
    }

    println!("Request: {}", opt.request);
    let decrypted_response = String::from_utf8(
        client.invoke(opt.request.as_bytes()).await.context("couldn't send request")?,
    )
    .context("response is not valid UTF-8")?;
    println!("Response: {decrypted_response}");

    Ok(())
}
