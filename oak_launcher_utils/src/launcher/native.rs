//
// Copyright 2023 The Project Oak Authors
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

use crate::launcher::GuestInstance;
use anyhow::Result;
use async_trait::async_trait;
use clap::Parser;
use command_fds::tokio::CommandFdAsyncExt;
use log::info;
use std::{
    net::Shutdown,
    os::unix::{io::AsRawFd, net::UnixStream},
    path::PathBuf,
};

use std::fs;

/// Parameters used for launching the enclave as a native binary
#[derive(Parser, Clone, Debug, PartialEq)]
pub struct Params {
    /// Path to the enclave binary.
    #[arg(long, value_parser = Params::path_exists)]
    pub enclave_binary: PathBuf,
}

impl Params {
    /// Checks if file with a given path exists.
    fn path_exists(s: &str) -> Result<PathBuf, String> {
        let path = PathBuf::from(s);
        if !fs::metadata(s).map_err(|err| err.to_string())?.is_file() {
            Err(String::from("path does not represent a file"))
        } else {
            Ok(path)
        }
    }
}

/// An instance of the enclave running directly as a linux binary
pub struct Instance {
    host_socket: UnixStream,
    instance: tokio::process::Child,
}

impl Instance {
    pub fn start(params: Params) -> Result<Self> {
        let (guest_socket, host_socket) = UnixStream::pair()?;

        let mut cmd = tokio::process::Command::new(params.enclave_binary);

        // Print any logs & errors
        cmd.stdout(std::process::Stdio::inherit());
        cmd.stderr(std::process::Stdio::inherit());

        cmd.preserved_fds(vec![guest_socket.as_raw_fd()]);
        cmd.args(["--comms-fd", &guest_socket.as_raw_fd().to_string()]);

        let instance = cmd.spawn()?;

        Ok(Self {
            instance,
            host_socket,
        })
    }
}

#[async_trait]
impl GuestInstance for Instance {
    async fn wait(&mut self) -> Result<std::process::ExitStatus> {
        self.instance.wait().await.map_err(anyhow::Error::from)
    }

    async fn kill(mut self: Box<Self>) -> Result<std::process::ExitStatus> {
        info!("Cleaning up and shutting down.");
        self.host_socket.shutdown(Shutdown::Both)?;
        self.instance.start_kill()?;
        self.wait().await
    }

    async fn connect(&self) -> Result<Box<dyn oak_channel::Channel>> {
        let host_socket = self.host_socket.try_clone()?;
        Ok(Box::new(host_socket))
    }
}
