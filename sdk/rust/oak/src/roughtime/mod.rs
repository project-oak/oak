//
// Copyright 2019 The Project Oak Authors
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

//! Helper library for accessing the Oak Roughtime service.

use crate::{
    grpc,
    proto::oak::roughtime::{GetRoughtimeRequest, RoughtimeServiceClient},
};
use oak_services::proto::oak::application::{
    node_configuration::ConfigType, NodeConfiguration, RoughtimeClientConfiguration,
};

/// Local representation of the connection to an external Roughtime service.
pub struct Roughtime {
    client: RoughtimeServiceClient,
}

impl Roughtime {
    /// Creates a [`Roughtime`] instance using the given configuration.
    pub fn new(config: &RoughtimeClientConfiguration) -> Option<Roughtime> {
        let config = NodeConfiguration {
            name: "roughtime".to_string(),
            config_type: Some(ConfigType::RoughtimeClientConfig(config.clone())),
        };
        crate::grpc::client::Client::new(&config).map(|client| Roughtime {
            client: RoughtimeServiceClient(client),
        })
    }

    /// Get the current Roughtime value as a Duration since UNIX epoch.
    /// Note that leap seconds are linearly smeared over 24h.
    pub fn get_roughtime(&self) -> grpc::Result<std::time::Duration> {
        let rsp = self.client.get_roughtime(GetRoughtimeRequest {})?;
        Ok(std::time::Duration::from_micros(rsp.roughtime_usec))
    }
}
