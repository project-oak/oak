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

use std::{
    net::{IpAddr, Ipv4Addr, SocketAddr},
    sync::Arc,
};

use anyhow::Context;
use oak_grpc::oak::containers::v1::orchestrator_crypto_client::OrchestratorCryptoClient;
use oak_proto_rust::oak::containers::v1::{KeyOrigin, SignRequest};
use oak_sdk_containers::{default_orchestrator_channel, OrchestratorClient};
use p256::ecdsa::{signature::SignatureEncoding, Signature};
use rand::{rngs::StdRng, CryptoRng, RngCore, SeedableRng};
use sha2::{Digest, Sha256};
use tokio::{net::TcpListener, sync::Mutex};
use tonic::{transport::Server, Request, Response, Status};
use tonic_service::oak::ctf_sha2::enclave::{
    flag_digest_service_server::{FlagDigestService, FlagDigestServiceServer},
    GenerateFlagDigestRequest, GenerateFlagDigestResponse,
};

const ENCLAVE_APP_PORT: u16 = 8080;

struct FlagDigestServiceImpl {
    orchestrator_client: Arc<Mutex<OrchestratorClient>>,
    crypto_client: OrchestratorCryptoClient<tonic::transport::Channel>,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("CTF SHA2 enclave app starting");
    let orchestrator_channel =
        default_orchestrator_channel().await.context("failed to create orchestrator channel")?;

    let mut orchestrator_client = OrchestratorClient::create(&orchestrator_channel);
    let crypto_client = OrchestratorCryptoClient::new(orchestrator_channel);

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), ENCLAVE_APP_PORT);
    let listener = TcpListener::bind(addr).await?;

    orchestrator_client.notify_app_ready().await.context("failed to notify that app is ready")?;

    let service = FlagDigestServiceImpl {
        orchestrator_client: Arc::new(Mutex::new(orchestrator_client)),
        crypto_client,
    };

    let server_handle = tokio::spawn(
        Server::builder()
            .add_service(FlagDigestServiceServer::new(service))
            .serve_with_incoming(tokio_stream::wrappers::TcpListenerStream::new(listener)),
    );

    println!("CTF SHA2 enclave app now serving");
    server_handle.await??;
    Ok(())
}

#[tonic::async_trait]
impl FlagDigestService for FlagDigestServiceImpl {
    async fn generate_flag_digest(
        &self,
        _request: Request<GenerateFlagDigestRequest>,
    ) -> Result<Response<GenerateFlagDigestResponse>, Status> {
        // Generate a secret flag.
        let flag_digest = {
            let flag = generate_flag(&mut StdRng::from_entropy());
            let mut hasher = Sha256::new();
            hasher.update(flag);
            hasher.finalize().to_vec()
        };

        // Sign the flag digest.
        let signature = {
            let sign_req = SignRequest {
                key_origin: KeyOrigin::Instance as i32,
                message: flag_digest.clone(),
            };
            let sign_response = self
                .crypto_client
                .clone()
                .sign(sign_req)
                .await
                .map_err(|e| Status::internal(format!("failed to sign: {:?}", e)))?;
            let signature = sign_response
                .into_inner()
                .signature
                .ok_or_else(|| Status::internal("missing signature"))?
                .signature;
            Signature::from_slice(signature.as_slice())
                .map_err(|e| Status::internal(format!("failed to parse signature: {:?}", e)))?
        };

        // Fetch enclave app Evidence.
        let evidence =
            {
                let endorsed_evidence =
                    self.orchestrator_client.lock().await.get_endorsed_evidence().await.map_err(
                        |e| Status::internal(format!("failed to get evidence: {:?}", e)),
                    )?;
                endorsed_evidence.evidence.ok_or_else(|| Status::internal("missing evidence"))?
            };

        Ok(Response::new(GenerateFlagDigestResponse {
            flag_digest,
            signature: signature.to_der().to_vec(),
            evidence: Some(evidence),
        }))
    }
}

// We must use a cryptographically secure RNG.
// See <https://rust-random.github.io/book/guide-gen.html#cryptographically-secure-pseudo-random-number-generator>.
fn generate_flag<T: CryptoRng + RngCore>(rng: &mut T) -> [u8; 64] {
    let mut flag = [0; 64];
    rng.fill_bytes(&mut flag);
    flag
}
