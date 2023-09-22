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

pub mod proto {
    pub mod oak {
        pub mod containers {
            tonic::include_proto!("oak.containers");
        }
        pub use oak_crypto::proto::oak::crypto;
        pub use oak_remote_attestation::proto::oak::session;
    }
}

use self::proto::oak::{
    containers::SendAttestationEvidenceRequest, session::v1::AttestationEvidence,
};
use anyhow::Context;
use proto::oak::containers::{launcher_client::LauncherClient as GrpcLauncherClient, LogEntry};
use std::collections::HashMap;
use tokio_stream::{Stream, StreamExt};
use tonic::transport::Channel;

/// Utility struct used to interface with the launcher
pub struct LauncherClient {
    inner: GrpcLauncherClient<tonic::transport::channel::Channel>,
}

impl LauncherClient {
    pub async fn create(addr: tonic::transport::Uri) -> Result<Self, Box<dyn std::error::Error>> {
        let inner = GrpcLauncherClient::<Channel>::connect(addr).await?;
        Ok(Self { inner })
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
        evidence: AttestationEvidence,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let request = tonic::Request::new(SendAttestationEvidenceRequest {
            evidence: Some(evidence),
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

    pub async fn log<I>(&self, entry: I) -> Result<(), Box<dyn std::error::Error>>
    where
        I: Stream<Item = HashMap<String, String>> + Send + 'static,
    {
        let request = tonic::Request::new(entry.map(|fields| LogEntry { fields }));
        self.inner
            .clone()
            .log(request)
            .await
            .context("couldn't stream log messages")?;
        Ok(())
    }
}
