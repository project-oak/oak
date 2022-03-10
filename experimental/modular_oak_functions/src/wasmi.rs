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

use crate::{Service, ServiceProxy, ServiceType};
use std::{collections::BTreeMap, sync::Arc};

/// Container for the Wasm business logic code, in future to be implemented using Wasmi.
pub struct WasmiService {
    services: BTreeMap<ServiceType, Arc<Box<dyn Service>>>,
}

impl WasmiService {
    pub fn new(services: BTreeMap<ServiceType, Arc<Box<dyn Service>>>) -> Self {
        Self { services }
    }
}

impl Service for WasmiService {
    fn create_proxy(&self) -> Box<dyn ServiceProxy> {
        let proxies: BTreeMap<ServiceType, Box<dyn ServiceProxy>> = self
            .services
            .iter()
            .map(|(&service_type, service)| (service_type, service.create_proxy()))
            .collect();
        Box::new(WasmiProxy::new(proxies))
    }
    fn configure(&self, _data: &[u8]) -> anyhow::Result<()> {
        Ok(())
    }
}

/// Provides the per-request Wasm sandbox execution.
pub struct WasmiProxy {
    proxies: BTreeMap<ServiceType, Box<dyn ServiceProxy>>,
}

impl WasmiProxy {
    fn new(proxies: BTreeMap<ServiceType, Box<dyn ServiceProxy>>) -> Self {
        Self { proxies }
    }
}

impl ServiceProxy for WasmiProxy {
    fn call(&self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        let mut result = data.to_vec();
        // The real implemenation will execute the Wasm business logic and call the appropriate
        // service proxies based on ABI calls. For now, just call each proxy and replace the
        // previous result every time.
        for (_, proxy) in self.proxies.iter() {
            result = proxy.call(&result)?;
        }
        Ok(result)
    }
}
