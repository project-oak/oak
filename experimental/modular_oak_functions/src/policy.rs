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
use alloc::sync::Arc;

/// Policy enforcement service.
///
/// Note: it might not be possible to enforce the fixed time policy using this service. It might
/// have to be moved into the demux or io service.
pub struct PolicyService {
    /// The service where the incoming request will be sent and that will supply the response to
    /// which the policy will be applied.
    next: Arc<dyn Service>,
    // Policy configuration will also be stored here in future.
}

impl PolicyService {
    pub fn new(next: Arc<dyn Service>) -> Self {
        Self { next }
    }
}

impl Service for PolicyService {
    fn create_proxy(self: Arc<Self>) -> Box<dyn ServiceProxy> {
        Box::new(PolicyProxy::new(self.next.clone().create_proxy()))
    }

    fn configure(&self, _data: &[u8]) -> anyhow::Result<()> {
        eprintln!("policy configured");
        // Ignore configuration for now. In future this will set the policy to use.
        Ok(())
    }

    fn call(&self, _data: &[u8]) -> anyhow::Result<Vec<u8>> {
        unimplemented!();
    }
}

/// Enforces the response policies.
pub struct PolicyProxy {
    next: Box<dyn ServiceProxy>,
    // Reference to policy configuration will also be stored here in future.
}

impl PolicyProxy {
    fn new(next: Box<dyn ServiceProxy>) -> Self {
        Self { next }
    }
}

impl ServiceProxy for PolicyProxy {
    fn call(&self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        // The real implementation will enforce the policy, but for now we just pass through.
        let result = self.next.call(data)?;
        eprintln!("policy applied");
        Ok(result)
    }
}
