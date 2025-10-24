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

//! A version of a gRPC Oak Verity service that runs on GCP Confidential Space
//! and provides an assertion that binds the Confidential Space Token to the
//! manifest.

#![macro_use]
extern crate maplit;

use std::collections::BTreeMap;

use anyhow::Result;
use maplit::btreemap;
use oak_attestation_gcp::assertions::GcpAssertionGenerator;
use oak_attestation_types::assertion_generator::AssertionGenerator;
use oak_verity_grpc::OakVerityService;
use tonic::transport::Server;

const OAK_VERITY_GCP_CONFIDENTIAL_SPACE_TOKEN_AUDIENCE: &str = "z00063450530956731445";
const OAK_VERITY_GCP_CONFIDENTIAL_SPACE_ASSERTION_ID: &str = "z10798025375578713722";

#[tokio::main]
async fn main() -> Result<()> {
    let assertion_generators: BTreeMap<String, Box<dyn AssertionGenerator>> = btreemap! {
        OAK_VERITY_GCP_CONFIDENTIAL_SPACE_ASSERTION_ID.to_string() => Box::new(
            GcpAssertionGenerator::new(OAK_VERITY_GCP_CONFIDENTIAL_SPACE_TOKEN_AUDIENCE.to_string(), None)
        ) as Box<dyn AssertionGenerator>,
    };

    let service = OakVerityService::new(assertion_generators);
    let addr = "[::]:8080".parse::<std::net::SocketAddr>()?;
    eprintln!("listening on address {addr}");
    Server::builder()
        .add_service(oak_grpc::oak::verity::oak_verity_service_server::OakVerityServiceServer::new(
            service,
        ))
        .serve(addr)
        .await?;
    Ok(())
}
