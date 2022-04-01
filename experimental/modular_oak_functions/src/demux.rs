//
// Copyright 2022 The Project Oak Authors
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

use crate::{ConfigServiceType, Service, ServiceProxy};
use alloc::{collections::BTreeMap, sync::Arc};

/// A stream demultiplexer.
pub struct Demux {
    /// The services that can be configured from control frames.
    config_services: BTreeMap<ConfigServiceType, Arc<dyn Service>>,
    /// The service that will receive the split requests.
    next: Arc<dyn Service>,
}

impl Demux {
    pub fn new(
        config_services: BTreeMap<ConfigServiceType, Arc<dyn Service>>,
        next: Arc<dyn Service>,
    ) -> Self {
        Self {
            config_services,
            next,
        }
    }

    /// Handles a single control frame from a multiplexed stream.
    ///
    /// This will likely be part of `handle_frame` in a real implementation, just with different
    /// frame types, but it is split out here for clarity.
    pub fn handle_control_frame(&self, data: &[u8]) -> anyhow::Result<()> {
        eprintln!("control frame decapsulated");
        // Placeholder implementation to make sure that `configure` is called on every configurable
        // service. A real implementation will route the configuration data to the appropriate
        // service based on an identifier in the configuration frame.
        for (_, service) in self.config_services.iter() {
            service.configure(data)?;
        }
        Ok(())
    }

    /// Handles a single data frame from a multiplexed stream.
    pub fn handle_data_frame(&self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        eprintln!("request frame decapsulated");
        // For now, just create a single request proxy and call it with the raw frame. A real
        // implementation would decapsulate the frame to reconstruct the individual streams
        // and re-encapsulate the results as frames to return into the multiplexed stream.
        let response = self.next.clone().create_proxy().call(data)?;
        eprintln!("response frame encapsulated");
        Ok(response)
    }
}

impl Service for Demux {
    fn create_proxy(self: Arc<Self>) -> Box<dyn ServiceProxy> {
        // We don't have Demux proxies.
        unimplemented!();
    }

    fn configure(&self, _data: &[u8]) -> anyhow::Result<()> {
        // We do not expect the Demux service to be configured.
        unimplemented!();
    }

    fn call(&self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        // A real implemenation would decode and decapsulate the frame to determine the frame type.
        // For now we just assume that an empty frame is a control frame, and all non-empty
        // frames are data frames.
        if data.len() == 0 {
            self.handle_control_frame(data).map(|_| Vec::new())
        } else {
            self.handle_data_frame(data)
        }
    }
}
