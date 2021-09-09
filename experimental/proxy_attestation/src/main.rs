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

//! Proxy Attestation Service implementation.
//!
//! Proxy Attestation Service works as a Certificate Authority for TEE applications. It attests
//! applications and creates signed certificates for TEE applications, which they use to create TLS
//! connections with clients.
//!
//! The work cycle of the proxy is represented in 2 stages.
//! First stage corresponds to the backend server attestation:
//! - TEE application connects to the proxy
//! - Proxy attests the application using a corresponding remote attestation protocol
//! - Application sends the proxy a certificate signing request
//! - Proxy creates a signed certificate and sends it back to the application
//!     - The certificate contains application's TEE measurements
//!
//! Second stage corresponds to the client connection:
//! - Client remotely attests the proxy using a corresponding attestation protocol
//! - Proxy sends the client its root certificate
//!     - Client trusts that this is a correct certificate, since it was sent via a secure channel
//!       created during the attestation process
//! - Client connects to the application using TLS, and the application uses a TLS certificate
//!   previously signed by the proxy
//! - Client checks that the certificate was signed by the root certificate and also checks TEE
//!   measurements
//! - If all checks were successful, client establishes a secure connection
//!
//! Note: Current version of Remote Attestation Service doesn't have remote attestation.

use anyhow::Context;
use futures::future::FutureExt;
use log::{error, info};
use oak_attestation_common::certificate::{AddTeeExtension, CertificateAuthority};
use oak_proxy_attestation::proto::{
    proxy_attestation_server::{ProxyAttestation, ProxyAttestationServer},
    GetRootCertificateRequest, GetRootCertificateResponse, GetSignedCertificateRequest,
    GetSignedCertificateResponse,
};
use openssl::x509::X509Req;
use structopt::StructOpt;
use tonic::{
    transport::{Identity, Server, ServerTlsConfig},
    Request, Response, Status,
};

#[derive(StructOpt, Clone)]
#[structopt(about = "Proxy Attestation")]
pub struct Opt {
    #[structopt(
        long,
        help = "Address to listen on for the gRPC server.",
        default_value = "[::]:8888"
    )]
    grpc_listen_address: String,
    #[structopt(long, help = "Private RSA key PEM encoded file used by gRPC server.")]
    grpc_tls_private_key: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS certificate file used by gRPC server."
    )]
    grpc_tls_certificate: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 certificate that signs TEE firmware key.",
        default_value = "./examples/certs/local/ca.pem"
    )]
    tee_certificate: String,
}

pub struct Proxy {
    certificate_authority: CertificateAuthority,
    tee_certificate: Vec<u8>,
}

impl Proxy {
    fn create(tee_certificate: Vec<u8>) -> anyhow::Result<Self> {
        let certificate_authority = CertificateAuthority::create(AddTeeExtension::No)
            .context("Couldn't create certificate authority")?;
        Ok(Self {
            certificate_authority,
            tee_certificate,
        })
    }
}

#[tonic::async_trait]
impl ProxyAttestation for Proxy {
    /// Creates a signed X.509 certificate based on the certificate signing request.
    async fn get_signed_certificate(
        &self,
        req: Request<GetSignedCertificateRequest>,
    ) -> Result<Response<GetSignedCertificateResponse>, Status> {
        info!("Received certificate sign request");
        let certificate_request = X509Req::from_pem(&req.into_inner().certificate_request)
            .map_err(|error| {
                let msg = "Certificate deserialize certificate request";
                error!("{}: {}", msg, error);
                Status::invalid_argument(msg)
            })?;
        match self.certificate_authority.sign_certificate(
            certificate_request,
            AddTeeExtension::Yes(self.tee_certificate.to_vec()),
        ) {
            Ok(certificate) => match certificate.to_pem() {
                Ok(serialized_certificate) => {
                    info!("Sending signed certificate");
                    let res = GetSignedCertificateResponse {
                        certificate: serialized_certificate,
                    };
                    Ok(Response::new(res))
                }
                Err(error) => {
                    let msg = "Certificate serialization error";
                    error!("{}: {}", msg, error);
                    Err(Status::internal(msg))
                }
            },
            Err(error) => {
                let msg = "Certificate signing error";
                error!("{}: {}", msg, error);
                Err(Status::internal(msg))
            }
        }
    }

    /// Sends back root X.509 certificate in PEM format.
    /// https://tools.ietf.org/html/rfc7468
    async fn get_root_certificate(
        &self,
        _req: Request<GetRootCertificateRequest>,
    ) -> Result<Response<GetRootCertificateResponse>, Status> {
        info!("Received root certificate request");
        match self.certificate_authority.root_certificate.to_pem() {
            Ok(serialized_certificate) => {
                info!("Sending root certificate");
                let res = GetRootCertificateResponse {
                    root_certificate: serialized_certificate,
                };
                Ok(Response::new(res))
            }
            Err(error) => {
                let msg = "Certificate serialization error";
                error!("{}: {}", msg, error);
                Err(Status::internal(msg))
            }
        }
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let grpc_tls_private_key =
        std::fs::read(&opt.grpc_tls_private_key).context("Couldn't load private key")?;
    let grpc_tls_certificate =
        std::fs::read(&opt.grpc_tls_certificate).context("Couldn't load certificate")?;
    let tee_certificate =
        std::fs::read(&opt.tee_certificate).context("Couldn't load certificate")?;

    let identity = Identity::from_pem(grpc_tls_certificate, grpc_tls_private_key);
    let address = opt
        .grpc_listen_address
        .parse()
        .context("Couldn't parse address")?;

    // Create proxy attestation gRPC server.
    info!("Starting proxy attestation server at {:?}", address);
    Server::builder()
        .tls_config(ServerTlsConfig::new().identity(identity))
        .context("Couldn't create TLS configuration")?
        .add_service(ProxyAttestationServer::new(
            Proxy::create(tee_certificate).context("Couldn't create proxy")?,
        ))
        .serve_with_shutdown(address, tokio::signal::ctrl_c().map(|r| r.unwrap()))
        .await
        .context("Couldn't start server")?;

    Ok(())
}
