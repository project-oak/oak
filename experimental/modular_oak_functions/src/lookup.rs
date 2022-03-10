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

use crate::{Service, ServiceProxy};

/// Container for the shared lookup data.
pub struct LookupService {
    // Lookup data will be stored here in future.
}

impl LookupService {
    pub fn new() -> Self {
        Self {}
    }
}

impl Service for LookupService {
    fn create_proxy(&self) -> Box<dyn ServiceProxy> {
        Box::new(LookupProxy::new())
    }
    fn configure(&self, _data: &[u8]) -> anyhow::Result<()> {
        // Ignore configuration for now. In future this will be used to refresh the lookup data.
        Ok(())
    }
}

impl Default for LookupService {
    fn default() -> Self {
        Self::new()
    }
}

/// Provides the per-request access to lookup data.
pub struct LookupProxy {
    // Reference to lookup data will be stored here in future.
}

impl LookupProxy {
    fn new() -> Self {
        Self {}
    }
}

impl ServiceProxy for LookupProxy {
    fn call(&self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        // The real implementation will to the lookup, but for now we just echo the data back.
        Ok(data.to_vec())
    }
}
