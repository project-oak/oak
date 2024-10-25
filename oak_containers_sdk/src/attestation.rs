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
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_grpc::oak::containers::orchestrator_client::OrchestratorClient as GrpcOrchestratorClient;
use oak_proto_rust::oak::{
    attestation::v1::{Endorsements, Evidence},
    session::v1::EndorsedEvidence,
};
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
    fn extend(&mut self, _encoded_event: &[u8]) -> anyhow::Result<()> {
        anyhow::bail!("evidence extension is not currently supported in Oak Containers");
    }

    /// Retrieves the evidence from the Orchestrator.
    /// The evidence is used to prove the authenticity and integrity of the
    /// application.
    fn quote(&self) -> anyhow::Result<Evidence> {
        // TODO: b/370474308 - Currently we receive [`EndorsedEvidence`] from the
        // Orchestrator, and have to split before returning to the Noise SDK.
        // But we'll need make both Attester and Endorser request Evidence and
        // Endorsements from the Attestation Agent separately.
        self.endorsed_evidence
            .evidence
            .clone()
            .context("evidence is not present in the EndorsedEvidence")
    }
}

#[derive(Clone)]
pub struct InstanceEndorser {
    endorsed_evidence: EndorsedEvidence,
}

impl InstanceEndorser {
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

impl Endorser for InstanceEndorser {
    /// Retrieves the endorsements from the Orchestrator.
    fn endorse(&self, _evidence: Option<&Evidence>) -> anyhow::Result<Endorsements> {
        // TODO: b/370474308 - Currently we receive [`EndorsedEvidence`] from the
        // Orchestrator, and have to split before returning to the Noise SDK.
        // But we'll need make both Attester and Endorser request Evidence and
        // Endorsements from the Attestation Agent separately.
        self.endorsed_evidence
            .endorsements
            .clone()
            .context("endorsements are not present in the EndorsedEvidence")
    }
}
