//
// Copyright 2023 The Project Oak Authors
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

use anyhow::Context;
use oak_containers_channel::{buffer::Buffer, create_channel};
use oak_grpc::oak::containers::{
    launcher_client::LauncherClient as GrpcLauncherClient,
    v1::hostlib_key_provisioning_client::HostlibKeyProvisioningClient,
};
use oak_proto_rust::oak::{
    attestation::v1::{Endorsements, Evidence},
    containers::{SendAttestationEvidenceRequest, v1::KeyProvisioningRole},
    key_provisioning::v1::GroupKeys,
};
use tonic::transport::Channel;

/// Utility struct used to interface with the launcher
pub struct LauncherClient {
    channel: tonic::transport::Channel,
    inner: GrpcLauncherClient<Channel>,
    hostlib_key_provisioning_client: HostlibKeyProvisioningClient<Channel>,
}

impl LauncherClient {
    pub async fn create(addr: tonic::transport::Uri) -> Result<Self, Box<dyn std::error::Error>> {
        let channel = create_channel(addr).await?;
        let inner = GrpcLauncherClient::new(channel.clone());
        let hostlib_key_provisioning_client = HostlibKeyProvisioningClient::new(channel.clone());
        Ok(Self { channel, inner, hostlib_key_provisioning_client })
    }

    pub async fn get_container_bundle(&self) -> Result<Buffer, Box<dyn std::error::Error>> {
        let mut stream = self
            .inner
            .clone()
            .get_container_bundle(())
            .await
            .context("couldn't form streaming connection")?
            .into_inner();

        let mut container_buf = Buffer::new();
        while let Some(load_response) =
            stream.message().await.context("couldn't load message from stream")?
        {
            container_buf.push_back(load_response.image_chunk);
        }

        Ok(container_buf)
    }

    pub async fn get_application_config(&self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let application_config = self
            .inner
            .clone()
            .get_application_config(())
            .await
            .context("couldn't form get response")?
            .into_inner()
            .config;

        Ok(application_config)
    }
    pub async fn get_endorsements(&self) -> Result<Endorsements, Box<dyn std::error::Error>> {
        Ok(self
            .inner
            .clone()
            .get_endorsements(())
            .await
            .context("couldn't get response from launcher")?
            .into_inner())
    }

    pub async fn send_attestation_evidence(
        &self,
        evidence: Evidence,
    ) -> Result<(), Box<dyn std::error::Error>> {
        #[allow(deprecated)]
        let request =
            tonic::Request::new(SendAttestationEvidenceRequest { dice_evidence: Some(evidence) });
        self.inner
            .clone()
            .send_attestation_evidence(request)
            .await
            .context("couldn't form get response")?;

        Ok(())
    }

    pub async fn notify_app_ready(&self) -> Result<(), Box<dyn std::error::Error>> {
        let request = tonic::Request::new(());
        self.inner.clone().notify_app_ready(request).await.context("couldn't send notification")?;
        Ok(())
    }

    pub async fn get_key_provisioning_role(&self) -> anyhow::Result<KeyProvisioningRole> {
        let key_provisioning_role = self
            .hostlib_key_provisioning_client
            .clone()
            .get_key_provisioning_role(tonic::Request::new(()))
            .await
            .context("couldn't get key provisioning role")?
            .into_inner()
            .role;
        KeyProvisioningRole::try_from(key_provisioning_role)
            .context("unknown key provisioning role")
    }

    pub async fn get_group_keys(&self) -> anyhow::Result<GroupKeys> {
        self.hostlib_key_provisioning_client
            .clone()
            .get_group_keys(tonic::Request::new(()))
            .await
            .context("couldn't get group keys")?
            .into_inner()
            .group_keys
            .context("get group keys weren't provided")
    }

    pub fn channel(&self) -> tonic::transport::Channel {
        self.channel.clone()
    }
}
