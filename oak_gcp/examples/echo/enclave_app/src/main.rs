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

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use oak_attestation_gcp::attestation::request_attestation_token;
use p256::ecdsa::{signature::rand_core::OsRng, SigningKey};
use sha2::Digest;
use tokio::net::TcpListener;

const ENCLAVE_APP_PORT: u16 = 8080;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("Logging!");

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), ENCLAVE_APP_PORT);
    let listener = TcpListener::bind(addr).await?;

    println!("Generating binding key...");
    let binding_key = SigningKey::random(&mut OsRng);
    let public_key_hash = sha2::Sha256::digest(binding_key.verifying_key().to_sec1_bytes());
    let public_key_hash = hex::encode(public_key_hash);

    println!("Requesting attestation token for {public_key_hash}...");
    let endorsement =
        request_attestation_token("oak://session/attestation", public_key_hash.as_str())?;

    println!("Received endorsement: {endorsement}");

    println!("Starting enclave echo app...");
    let join_handle = tokio::spawn(oak_gcp_examples_echo_enclave_app::app_service::create(
        listener,
        oak_gcp_examples_echo_enclave_app::app::EchoHandler,
        binding_key,
        endorsement,
    ));
    println!("Enclave echo app now serving!");
    join_handle.await??;
    Ok(())
}
