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

//! HTTPS Attestation Service implementation.
//!
//! HTTPS Attestation Service works as an HTTPS proxy for a TEE application that runs inside the
//! same TEE as the application.
//!
//! HTTPS Attestation Service allows to perform bidirectional remote attestation via TLS by
//! cryptographically binding assertions to a TLS session, using
//! [Exported Keying Material](https://tools.ietf.org/html/rfc5705) from an already established TLS
//! session and producing an assertion based on it, e.g. signing it with a TEE key.
//!
//! HTTPS Attestation Service description is provided in the
//! [TLS Remote Attestation RFC](https://github.com/project-oak/oak/pull/1929).
//!
//! Note: Current version of the HTTPS Attestation Service doesn't have remote attestation and
//! client assertion generation.

mod server;

use anyhow::{anyhow, Context};
use futures::FutureExt;
use log::info;
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
#[structopt(about = "HTTPS Attestation")]
pub struct Opt {
    #[structopt(
        long,
        help = "Address to listen on for the HTTPS server.",
        default_value = "[::]:8888"
    )]
    https_listen_address: String,
    #[structopt(
        long,
        help = "Private RSA key file used by HTTPS server.",
        default_value = "./examples/certs/local/local.key"
    )]
    https_private_key: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS certificate file used by HTTPS server.",
        default_value = "./examples/certs/local/local.pem"
    )]
    https_certificate: String,
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

// Load private key from file.
fn load_private_key(filename: &str) -> anyhow::Result<rustls::PrivateKey> {
    let private_key_file = std::fs::File::open(filename)
        .map_err(|error| anyhow!("Couldn't open file {}: {}", filename, error))?;
    let mut reader = std::io::BufReader::new(private_key_file);

    let private_keys = rustls::internal::pemfile::rsa_private_keys(&mut reader)
        .map_err(|error| anyhow!("Couldn't parse private key: {:?}", error))?;
    if private_keys.len() == 1 {
        Ok(private_keys[0].clone())
    } else {
        Err(anyhow!(
            "Incorrect number of private keys provided: {}, expected 1",
            private_keys.len()
        ))
    }
}

// Load certificate from file.
fn load_certificate(filename: &str) -> anyhow::Result<rustls::Certificate> {
    let certificate_file = std::fs::File::open(filename)
        .map_err(|error| anyhow!("Couldn't open file {}: {}", filename, error))?;
    let mut reader = std::io::BufReader::new(certificate_file);

    let certificates = rustls::internal::pemfile::certs(&mut reader)
        .map_err(|error| anyhow!("Couldn't parse certificate: {:?}", error))?;
    if certificates.len() == 1 {
        Ok(certificates[0].clone())
    } else {
        Err(anyhow!(
            "Incorrect number of certificates provided: {}, expected 1",
            certificates.len()
        ))
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let private_key =
        load_private_key(&opt.https_private_key).context("Couldn't load private key")?;
    let certificate =
        load_certificate(&opt.https_certificate).context("Couldn't load HTTPS certificate")?;
    let tee_certificate =
        std::fs::read(&opt.tee_certificate).context("Couldn't load TEE certificate")?;
    let backend_uri = opt
        .backend_uri
        .parse()
        .context("Couldn't parse application URI")?;

    info!(
        "HTTPS Attestation Service is listening on https://{}",
        &opt.https_listen_address
    );
    let server = server::run_server(
        &opt.https_listen_address,
        private_key,
        certificate,
        tee_certificate,
        backend_uri,
    );
    tokio::select!(
        result = server => {
            result.context("Couldn't run server")?;
        },
        () = tokio::signal::ctrl_c().map(|r| r.unwrap()) => {
            info!("Stopping HTTPS Attestation Service");
        },
    );

    Ok(())
}
