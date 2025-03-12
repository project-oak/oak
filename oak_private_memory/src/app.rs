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

use oak_sdk_server_v1::ApplicationHandler;

/// The actual business logic for the hello world application.
pub struct HelloWorldApplicationHandler {
    pub application_config: Vec<u8>,
}

#[async_trait::async_trait]
impl ApplicationHandler for HelloWorldApplicationHandler {
    /// This implementation is quite simple, since there's just a single request
    /// that is a string. In a real implementation, we'd probably
    /// deserialize into a proto, and dispatch to various handlers from
    /// there.
    async fn handle(&self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        let name = String::from_utf8_lossy(request_bytes);
        let config_len = self.application_config.len();
        Ok(
            format!(
                "Hello from the enclave, {name}! Btw, the app has a config with a length of {config_len} bytes.",
            ).into_bytes()
        )
    }
}
