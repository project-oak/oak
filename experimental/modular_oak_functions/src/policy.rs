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
use std::sync::Arc;

/// Policy enforcement service.
///
/// Note: it might not be possible to enforce the fixed time policy using this service. It might
/// have to be moved into the demux or io service.
pub struct PolicyService {
    // Policy configuration will also be stored here in future.
    next: Arc<Box<dyn Service>>,
}

impl PolicyService {
    pub fn new(next: Arc<Box<dyn Service>>) -> Self {
        Self { next }
    }
}

impl Service for PolicyService {
    fn create_proxy(&self) -> Box<dyn ServiceProxy> {
        Box::new(PolicyProxy::new(self.next.create_proxy()))
    }
    fn configure(&self, _data: &[u8]) -> anyhow::Result<()> {
        // Ignore configuration for now. In future this will set the policy to use.
        Ok(())
    }
}

/// Enforcer of the response policies
pub struct PolicyProxy {
    // Reference to policy configuration will also be stored here in future.
    next: Box<dyn ServiceProxy>,
}

impl PolicyProxy {
    fn new(next: Box<dyn ServiceProxy>) -> Self {
        Self { next }
    }
}

impl ServiceProxy for PolicyProxy {
    fn call(&self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        // The real implementation will to the lookup, but for now we just pass through.
        self.next.call(data)
    }
}
