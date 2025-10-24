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

use anyhow::Context;
use oak_attestation_gcp::{attestation::request_attestation_token, OAK_SESSION_NOISE_V1_AUDIENCE};
use oak_gcp_examples_echo_enclave_app::{app, app_service, gcp};
use oak_proto_rust::oak::attestation::v1::ConfidentialSpaceEndorsement;
use oci_client::{client::ClientConfig, secrets::RegistryAuth, Client, Reference};
use p256::ecdsa::{signature::rand_core::OsRng, SigningKey};
use rekor::log_entry::LogEntry;
use sha2::Digest;
use sigstore_client::cosign::pull_payload;
use tokio::net::TcpListener;
use verify_endorsement::create_signed_endorsement;

const ENCLAVE_APP_PORT: u16 = 8080;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    println!("Logging!");

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), ENCLAVE_APP_PORT);
    let listener = TcpListener::bind(addr).await?;

    println!("Generating binding key...");
    let binding_key = SigningKey::random(&mut OsRng);
    let public_key_hash = sha2::Sha256::digest(binding_key.verifying_key().to_sec1_bytes());
    let public_key_hash = hex::encode(public_key_hash);

    println!("Requesting attestation token for {public_key_hash}...");
    let jwt_token =
        request_attestation_token(OAK_SESSION_NOISE_V1_AUDIENCE, public_key_hash.as_str())?;

    println!("Received evidence: {jwt_token}");

    // We have to fetch this image's own identity. Confidential Space does not
    // provide an easy way to do this other than parsing the JWT. Requesting the
    // identity directly from the metadata server is a viable alternative. See
    // https://cloud.google.com/confidential-computing/confidential-space/docs/deploy-workloads#metadata-variables
    let image_reference = gcp::get_metadata_value("instance/attributes/tee-image-reference")
        .await
        .expect("Could not read tee-image-reference, are we running in Confidential Space?");
    let image_reference: Reference = image_reference
        .parse()
        .context("Could not parse tee-image-reference into an OCI image reference")?;
    anyhow::ensure!(
        image_reference.digest().is_some(),
        "Only images with digests are supported, not {image_reference}"
    );

    println!("Getting bearer token...");
    let token = gcp::get_bearer_token().await?;

    println!("Fetching endorsement for {image_reference}...");
    let client = Client::new(ClientConfig::default());
    let auth = RegistryAuth::Bearer(token);
    let (statement, rekor_bundle) = pull_payload(&client, &auth, &image_reference).await?;
    println!("Received statement: {statement:?}");
    println!("Received Rekor bundle: {rekor_bundle:?}");

    let log_entry: LogEntry = LogEntry::from_cosign_bundle(rekor_bundle.raw_data())?;
    let serialized_log_entry: Vec<u8> = serde_json::to_vec(&log_entry)?;
    println!("Converted Rekor log entry: {serialized_log_entry:?}");

    let endorsement = ConfidentialSpaceEndorsement {
        jwt_token,
        workload_endorsement: Some(create_signed_endorsement(
            statement.unverified_message(),
            statement.signature(),
            0,   // The key ID is not used here.
            &[], // The subject is not needed for verification.
            &serialized_log_entry,
        )),
    };

    println!("Starting enclave echo app...");
    let join_handle =
        tokio::spawn(app_service::create(listener, app::EchoHandler, binding_key, endorsement));
    println!("Enclave echo app now serving!");
    join_handle.await??;

    Ok(())
}
