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

/// Session state service.
pub struct SessionService {
    // Per-session state will also be stored here, likely in a LRU cache.
    next: Arc<Box<dyn Service>>,
}

impl SessionService {
    pub fn new(next: Arc<Box<dyn Service>>) -> Self {
        Self { next }
    }
}

impl Service for SessionService {
    fn create_proxy(&self) -> Box<dyn ServiceProxy> {
        Box::new(SessionProxy::new(self.next.create_proxy()))
    }
    fn configure(&self, _data: &[u8]) -> anyhow::Result<()> {
        eprintln!("session configured");
        // Ignore configuration for now.
        Ok(())
    }
}

/// Per session state handler.
///
/// This proxy will also handle the remote attestation handshake and encrypting/decypting session
/// traffic.
pub struct SessionProxy {
    // Reference to policy configuration will also be stored here in future.
    next: Box<dyn ServiceProxy>,
}

impl SessionProxy {
    fn new(next: Box<dyn ServiceProxy>) -> Self {
        Self { next }
    }
}

impl ServiceProxy for SessionProxy {
    fn call(&self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        eprintln!("data decrypted");
        // The real implementation will do the remote attesation handshake and encrypt/decrypt using
        // the session keys, but for now we just pass through.
        let result = self.next.call(data)?;
        eprintln!("data encrypted");
        Ok(result)
    }
}
