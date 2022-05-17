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
    pub binary: PathBuf,
    pub firmware: Option<PathBuf>,
    pub app: PathBuf,

    pub console: UnixStream,
    pub comms: UnixStream,
}

#[async_trait]
pub trait Vmm {
    async fn wait(&mut self) -> Result<std::process::ExitStatus>;
    async fn kill(self: Box<Self>) -> Result<std::process::ExitStatus>;
}
