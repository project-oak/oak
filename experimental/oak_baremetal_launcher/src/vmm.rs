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

use anyhow::Result;
use async_trait::async_trait;
use std::{os::unix::net::UnixStream, path::PathBuf};

#[derive(Debug)]
pub struct Params {
    /// Path to the VMM binary to execute.
    pub binary: PathBuf,

    /// Path to the binary to load into the VM.
    pub app: PathBuf,

    /// Stream to connect to the console of the VM.
    pub console: UnixStream,

    /// Port to use for debugging with gdb
    pub gdb: Option<u16>,
}

#[async_trait]
pub trait Vmm {
    /// Waits for the guest VM to finish.
    async fn wait(&mut self) -> Result<std::process::ExitStatus>;

    /// Kills the guest VM.
    async fn kill(self: Box<Self>) -> Result<std::process::ExitStatus>;

    /// Creates a channel to communicate with the VM.
    ///
    /// Since different VMMs might use different comms channels, we leave it up to the VMM to create
    /// the channel rather than passing it in as part of the parameters.
    async fn create_comms_channel(
        &self,
    ) -> Result<Box<dyn oak_baremetal_communication_channel::Channel>>;
}
