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

//! TLS Attestation Service implementation.
//!
//! TLS Attestation Service works as an HTTPS proxy for a TEE application that runs inside the same
//! TEE as the application.
//!
//! TLS Attestation Service attests the TEE application to clients by creating a self-signed
//! certificate that is cryptographically bound to the TEE. It is done by requesting a TEE report
//! with a public key hash inside it and putting it into a custom X.509 certificate extension,
//! which clients need to verify.
//!
//! It is assumed that prior to the attestation workflow Service remotely attests its TEE platform
//! key with the TEE firmware Provider. Provider sends back a signature rooted in some well-known
//! root key (e.g. AMD root key), thus confirming the authenticity of the TEE platform key.
//!
//! The workflow of the TLS Attestation Service looks as follows:
//! - Service generates a private/public key pair
//! - Service puts the hash of the public key into the TEE report request
//!   - It means that when firmware signs a TEE report, it will also sign the public key
//! - Service requests a TEE report from the TEE firmware
//! - Service generates a self-signed X.509 certificate (using previously generated private key) and
//!   puts the signed TEE report and a certificate signed by the Provider’s root key in a custom
//!   X.509 extension
//!   - Service can now use this certificate for all incoming client connections without the need to
//!     communicate with the Provider again
//!   - Provider’s certificate is required for checking the validity of TEE reports and TEE firmware
//!     keys used to sign them
//! - Client starts a TLS handshake with the Service
//! - Service sends a self-signed certificate as a part of the handshake
//! - Client checks the validity of the TEE report from a custom X.509 extension
//!   - It checks that the TEE report is signed by TEE firmware Provider’s root key
//!     - The corresponding TEE Provider’s certificate is sent alongside the TEE report
//!   - It checks that the public key hash from the TEE report is equal to the hash of the public
//!     key presented in the self-signed X.509 certificate
//!   - It also extracts the TEE measurement from the TEE report and compares it to the expected one
//!   - If the TEE report is not valid, then the Client closes the connection and aborts the
//!     protocol
//! - Service redirects all client requests to the TEE application (that listens to HTTP
//!   connections)
//!
//! Note: Current version of the TLS Attestation Service doesn't have remote attestation.

mod server;

use anyhow::Context;
use log::info;
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
#[structopt(about = "TLS Attestation")]
pub struct Opt {
    #[structopt(
        long,
        help = "Address to listen on for the HTTPS server.",
        default_value = "[::]:8888"
    )]
    https_listen_address: String,
    #[structopt(
        long,
        help = "URI of the backend application to proxy HTTP requests to",
        default_value = "http://localhost:8081"
    )]
    backend_uri: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 certificate that signs TEE firmware key.",
        default_value = "./examples/certs/local/ca.pem"
    )]
    tee_certificate: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let backend_uri = opt
        .backend_uri
        .parse()
        .context("Couldn't parse application URI")?;
    let tee_certificate =
        std::fs::read(&opt.tee_certificate).context("Couldn't load certificate")?;

    info!(
        "TLS Attestation Service is listening on https://{}",
        &opt.https_listen_address
    );
    server::run_server(&opt.https_listen_address, backend_uri, tee_certificate)
        .await
        .context("Server error")?;

    Ok(())
}
