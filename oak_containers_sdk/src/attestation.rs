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

use anyhow::Context;
use oak_grpc::oak::containers::orchestrator_client::OrchestratorClient as GrpcOrchestratorClient;
use oak_proto_rust::oak::session::v1::EndorsedEvidence;
use oak_session::attestation::Attester;
use tonic::transport::{Endpoint, Uri};
use tower::service_fn;

use crate::{IGNORED_ENDPOINT_URI, IPC_SOCKET};

#[derive(Clone)]
pub struct InstanceAttester {
    endorsed_evidence: EndorsedEvidence,
}

impl InstanceAttester {
    pub async fn create() -> anyhow::Result<Self> {
        // TODO: b/370474308 - Use a dedicated attestation gRPC client once
        // attestation is provided by a separate interface.
        let mut grpc_client: GrpcOrchestratorClient<tonic::transport::channel::Channel> = {
            let channel = Endpoint::try_from(IGNORED_ENDPOINT_URI)
                .context("couldn't form endpoint")?
                .connect_with_connector(service_fn(move |_: Uri| {
                    tokio::net::UnixStream::connect(IPC_SOCKET)
                }))
                .await
                .context("couldn't connect to UDS socket")?;

            GrpcOrchestratorClient::new(channel)
        };
        let endorsed_evidence = grpc_client.get_endorsed_evidence(()).await?.into_inner();
        Ok(Self { endorsed_evidence })
    }
}

impl Attester for InstanceAttester {
    /// Retrieves the endorsed evidence from the Orchestrator.
    /// This evidence is used to prove the authenticity and integrity of the
    /// application.
    fn get_endorsed_evidence(&self) -> anyhow::Result<EndorsedEvidence> {
        Ok(self.endorsed_evidence.clone())
    }
}
