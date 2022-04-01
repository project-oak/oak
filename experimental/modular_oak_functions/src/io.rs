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
use alloc::sync::Arc;

/// A fake IO Listener.
///
/// In the real implementation we will have different IO listeners for different environments (e.g.
/// vsock listener for Linux environments, serial listener for UEFI, etc.)
pub struct IoListener {
    /// The service where the incoming frames will be sent and that will supply the responses.
    next: Arc<dyn Service>,
}

impl IoListener {
    pub fn new(next: Arc<dyn Service>) -> Self {
        Self { next }
    }

    /// Listens for new messages on the incoming stream.
    pub fn listen(&self) -> anyhow::Result<()> {
        eprintln!("starting");
        // Create a fake configuration frame first to simulate the initial configuration. A real
        // implementation would have create a serialised frame, but for now we just treat empty
        // frames as controls frames and non-empty ones as data frames.
        self.next.call(b"")?;
        eprintln!("runtime configured");

        eprintln!("listening");
        // In a real implementation it would listen on an IO stream here handle the incoming
        // frames, but for now we just create a fake data frame, send it into the rest of the system
        // and print the response.
        let response = self.next.call(b"test")?;
        println!("response: {}", core::str::from_utf8(&response)?);
        Ok(())
    }
}
