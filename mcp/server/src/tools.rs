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
//

use std::sync::Arc;

use anyhow::Context;
use log::info;
use oak_functions_standalone_client_lib::{
    default_oak_functions_standalone_reference_values, OakFunctionsClient,
};
use oak_proto_rust::oak::attestation::v1::ConfidentialSpaceReferenceValues;
use oak_session::attestation::AttestationType;
use oak_time::Clock;
use oak_time_std::clock::FrozenSystemTimeClock;

#[derive(Clone)]
pub struct OakFunctionsTool {
    url: String,
    attestation: AttestationType,
    reference_values: ConfidentialSpaceReferenceValues,
}

impl OakFunctionsTool {
    pub fn new(url: &str, attestation: bool) -> Self {
        let attestation_type = if attestation {
            AttestationType::PeerUnidirectional
        } else {
            AttestationType::Unattested
        };
        let reference_values: ConfidentialSpaceReferenceValues =
            default_oak_functions_standalone_reference_values();

        Self { url: url.to_string(), attestation: attestation_type, reference_values }
    }

    pub async fn invoke(&self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        info!("Connecting to Oak Functions at: {}", self.url);

        let clock: Arc<dyn Clock> = Arc::new(FrozenSystemTimeClock::default());

        let mut client = OakFunctionsClient::create(
            &self.url,
            self.attestation,
            clock.clone(),
            Some(&self.reference_values),
        )
        .await
        .context("couldn't connect to Oak Functions")?;

        client.invoke(request_bytes).await.context("couldn't send request")
    }
}
