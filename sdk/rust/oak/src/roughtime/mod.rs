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
    proto::oak::roughtime::{RoughTimeRequest, RoughtimeServiceClient},
};

/// Default name for predefined Node config that corresponds to a Roughtime
/// pseudo-Node.
pub const DEFAULT_CONFIG_NAME: &str = "roughtime";

/// Local representation of the connection to an external Roughtime service.
pub struct Roughtime {
    client: RoughtimeServiceClient,
}

impl Roughtime {
    /// Create a default `Roughtime` instance assuming the default pre-defined
    /// name (`"roughtime"`) identifying Roughtime pseudo-Node config.
    pub fn default() -> Option<Roughtime> {
        Roughtime::new(DEFAULT_CONFIG_NAME)
    }

    /// Create a `Roughtime` instance using the given name identifying Roughtime
    /// pseudo-Node configuration.
    pub fn new(config: &str) -> Option<Roughtime> {
        crate::grpc::client::Client::new(config, "oak_main").map(|client| Roughtime {
            client: RoughtimeServiceClient(client),
        })
    }

    /// Get the current Roughtime value as a Duration since UNIX epoch.
    /// Note that leap seconds are linearly smeared over 24h.
    pub fn get_roughtime(&self) -> grpc::Result<std::time::Duration> {
        let rsp = self.client.get_rough_time(RoughTimeRequest {})?;
        Ok(std::time::Duration::from_micros(rsp.rough_time_usec))
    }
}
