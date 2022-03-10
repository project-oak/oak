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

use crate::{Service, ServiceType};
use std::{collections::BTreeMap, sync::Arc};

/// A stream demultiplexer.
pub struct Demux {
    config_services: BTreeMap<ServiceType, Arc<Box<dyn Service>>>,
    next: Arc<Box<dyn Service>>,
}

impl Demux {
    pub fn new(
        config_services: BTreeMap<ServiceType, Arc<Box<dyn Service>>>,
        next: Arc<Box<dyn Service>>,
    ) -> Self {
        Self {
            config_services,
            next,
        }
    }

    /// Handles a single admin frame from a multiplexed stream.
    ///
    /// This will likely be part of `handle_frame` in a real implementation, just with different
    /// frametypes, but it is split out here for clarity.
    pub fn handle_admin_frame(&self, data: &[u8]) -> anyhow::Result<()> {
        eprintln!("config frame decapsulated");
        for (_, service) in self.config_services.iter() {
            service.configure(data)?;
        }
        Ok(())
    }

    /// Handles a single frame from a multiplexed stream.
    pub fn handle_frame(&self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        eprintln!("request frame decapsulated");
        // For now, just create a single request proxy and call it with the raw fram. A real
        // implementation would decapsulate the frame to reconstruct the individual streams
        // and re-encapsulate the results as frames to return in the main stream.
        let response = self.next.create_proxy().call(data)?;
        eprintln!("response frame encapsulated");
        Ok(response)
    }
}
