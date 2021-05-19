//
// Copyright 2021 The Project Oak Authors
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

//! gRPC Attestation Service implementation.
//!
//! gRPC Attestation Service performs remote attestation for each incoming streaming gRPC request.
//!
//! It is assumed that prior to the attestation workflow Service remotely attests its TEE platform
//! key with the TEE firmware Provider. Provider sends back a signature rooted in some well-known
//! root key (e.g. AMD root key), thus confirming the authenticity of the TEE platform key.
//!
//! Remote attestation is done as follows:
//! - Client generates an ephemeral (single-use) private/public key pair
//! - Client sends a streaming gRPC request with its public key to the Server
//! - Server generates an ephemeral (single-use) private/public key pair
//! - Server uses its and Client's public keys to generate a symmetric session key, which is shared
//!   between client and server
//! - Server puts the hash of its public key into the TEE report request
//!   - It means that when a TEE report is signed, the public key will also be signed
//! - Server requests a TEE report from the TEE firmware
//! - Server sends its public key, a TEE report and Provider's certificate to the Client
//! - Client checks the validity of the TEE report
//!   - It checks that the TEE report is signed by TEE Provider’s root key
//!   - It checks that the public key hash from the TEE report is equal to the hash of the public
//!     key presented in the server response
//!   - It also extracts the TEE measurement from the TEE report and compares it to the expected one
//!   - If the TEE report is not valid, then the Client closes the connection and aborts the
//!     protocol
//! - Client uses its and Server's public keys to generate a symmetric session key, which is shared
//!   between client and server
//! - Client uses the session key to encrypt further requests to the Server
//! - Server uses the session key to decrypt further requests from the Client and encrypt
//!   corresponding responses
//!
//! It's important to note that for each new gRPC stream both Client and Server generate new pairs
//! of private/public key pairs and negotiate new session keys.
//!
//! Key negotiation is done using [`ring::agreement`](https://briansmith.org/rustdoc/ring/agreement/index.html).
//!
//! Note: Current version of the gRPC Attestation Service doesn't have remote attestation.

mod attestation;

use crate::attestation::AttestationServer;
use anyhow::Context;
use futures::FutureExt;
use log::info;
use oak_grpc_attestation::proto::grpc_attestation_server::GrpcAttestationServer;
use structopt::StructOpt;
use tonic::transport::Server;

#[derive(StructOpt, Clone)]
#[structopt(about = "gRPC Attestation")]
pub struct Opt {
    #[structopt(
        long,
        help = "Address to listen on for the gRPC server.",
        default_value = "[::]:8888"
    )]
    grpc_listen_address: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 certificate that signs TEE firmware key.",
        default_value = "./examples/certs/local/ca.pem"
    )]
    tee_certificate: String,
}

// Example message sent to the client.
const EXAMPLE_MESSAGE: &str = "Example message";

fn request_handler(request: &[u8]) -> Vec<u8> {
    let parsed_request = String::from_utf8(request.to_vec()).expect("Couldn't parse request");
    info!("Server received data: {:?}", parsed_request);
    EXAMPLE_MESSAGE.as_bytes().to_vec()
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let grpc_listen_address = opt
        .grpc_listen_address
        .parse()
        .context("Couldn't parse address")?;
    let tee_certificate =
        std::fs::read(&opt.tee_certificate).context("Couldn't load certificate")?;

    info!(
        "Starting proxy attestation server at {:?}",
        grpc_listen_address
    );
    Server::builder()
        .add_service(GrpcAttestationServer::new(
            AttestationServer::create(tee_certificate, request_handler)
                .context("Couldn't create proxy")?,
        ))
        .serve_with_shutdown(
            grpc_listen_address,
            tokio::signal::ctrl_c().map(|r| r.unwrap()),
        )
        .await
        .context("Couldn't start server")?;

    Ok(())
}
