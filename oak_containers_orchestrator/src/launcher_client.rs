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
use opentelemetry_otlp::{TonicExporterBuilder, WithExportConfig};
use tonic::transport::Channel;

use crate::proto::oak::{
    attestation::v1::Evidence,
    containers::{
        launcher_client::LauncherClient as GrpcLauncherClient,
        v1::{hostlib_key_provisioning_client::HostlibKeyProvisioningClient, KeyProvisioningRole},
        SendAttestationEvidenceRequest,
    },
    key_provisioning::v1::GroupKeys,
};

/// Utility struct used to interface with the launcher
pub struct LauncherClient {
    addr: tonic::transport::Uri,
    inner: GrpcLauncherClient<Channel>,
    hostlib_key_provisioning_client: HostlibKeyProvisioningClient<Channel>,
}

impl LauncherClient {
    pub async fn create(addr: tonic::transport::Uri) -> Result<Self, Box<dyn std::error::Error>> {
        let channel = Channel::builder(addr.clone()).connect().await?;
        let inner = GrpcLauncherClient::new(channel.clone());
        let hostlib_key_provisioning_client = HostlibKeyProvisioningClient::new(channel);
        Ok(Self {
            addr,
            inner,
            hostlib_key_provisioning_client,
        })
    }

    pub async fn get_container_bundle(&self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let mut stream = self
            .inner
            .clone()
            .get_container_bundle(())
            .await
            .context("couldn't form streaming connection")?
            .into_inner();

        let mut container_buf: Vec<u8> = Vec::new();
        while let Some(mut load_response) = stream
            .message()
            .await
            .context("couldn't load message from stream")?
        {
            container_buf.append(&mut load_response.image_chunk);
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

    pub async fn send_attestation_evidence(
        &self,
        evidence: Evidence,
    ) -> Result<(), Box<dyn std::error::Error>> {
        #[allow(deprecated)]
        let request = tonic::Request::new(SendAttestationEvidenceRequest {
            dice_evidence: Some(evidence),
        });
        self.inner
            .clone()
            .send_attestation_evidence(request)
            .await
            .context("couldn't form get response")?;

        Ok(())
    }

    pub async fn notify_app_ready(&self) -> Result<(), Box<dyn std::error::Error>> {
        let request = tonic::Request::new(());
        self.inner
            .clone()
            .notify_app_ready(request)
            .await
            .context("couldn't send notification")?;
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

    pub fn openmetrics_builder(&self) -> TonicExporterBuilder {
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint(self.addr.clone().to_string())
    }
}
