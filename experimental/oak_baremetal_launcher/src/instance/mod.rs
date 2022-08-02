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

pub mod crosvm;
pub mod native;

use anyhow::Result;
use async_trait::async_trait;

/// Defines the interface of a launched runtime instance. Standardizes the interface of different
/// implementations, e.g. a VM in which the runtime is running or the runtime running directly as a
/// unix binary.
#[async_trait]
pub trait LaunchedInstance {
    /// Wait for the runtime instance process to finish.
    async fn wait(&mut self) -> Result<std::process::ExitStatus>;

    /// Kill the runtime instance.
    async fn kill(self: Box<Self>) -> Result<std::process::ExitStatus>;

    /// Creates a channel to communicate with the runtime instance.
    ///
    /// Since different VMMs might use different comms channels, we leave it up to the VMM to create
    /// the channel rather than passing it in as part of the parameters.
    async fn create_comms_channel(
        &self,
    ) -> Result<Box<dyn oak_baremetal_communication_channel::Channel>>;
}
