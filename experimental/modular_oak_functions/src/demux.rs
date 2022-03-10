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

use crate::Service;
use std::sync::Arc;

/// A stream demultiplexer.
pub struct Demux {
    next: Arc<Box<dyn Service>>,
}

impl Demux {
    pub fn new(next: Arc<Box<dyn Service>>) -> Self {
        Self { next }
    }

    /// Handles a single frame from a multiplexed stream.
    pub fn handle_frame(&self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        eprintln!("decapsulated");
        // For now, just create a single request proxy and call it with the raw fram. A real
        // implementation would decapsulate the frame to reconstruct the individual streams
        // and re-encapsulate the results as frames to return in the main stream.
        let response = self.next.create_proxy().call(data)?;
        eprintln!("encapsulated");
        Ok(response)
    }
}
