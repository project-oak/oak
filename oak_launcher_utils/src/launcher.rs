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

use crate::channel::{Connector, ConnectorHandle};
use anyhow::Result;
use async_trait::async_trait;
use std::{
    io::{BufRead, BufReader},
    os::unix::net::UnixStream,
};

pub mod virtualized;

/// Defines the interface of a launched guest instance. Standardizes the interface of different
/// implementations, e.g. a VM in which the guest is running or the guest running directly as a
/// unix binary.
#[async_trait]
pub trait GuestInstance {
    /// Wait for the guest instance process to finish.
    async fn wait(&mut self) -> Result<std::process::ExitStatus>;

    /// Kill the guest instance.
    async fn kill(self: Box<Self>) -> Result<std::process::ExitStatus>;

    /// Creates a channel to communicate with the guest instance.
    async fn connect(&self) -> Result<Box<dyn oak_channel::Channel>>;
}

/// Launches a new guest instance in given mode.
pub async fn launch(
    params: virtualized::Params,
) -> Result<(Box<dyn GuestInstance>, ConnectorHandle), Box<dyn std::error::Error>> {
    // Provide a way for the launched instance to send logs
    let guest_writer: UnixStream = {
        // Create two linked consoles. Technically both can read/write, but we'll
        // use them as a one way channel.
        let (console_writer, console_receiver) = UnixStream::pair()?;

        // Log everything sent by the writer.
        tokio::spawn(async {
            let mut reader = BufReader::new(console_receiver);

            let mut line = String::new();
            while reader.read_line(&mut line).expect("couldn't read line") > 0 {
                log::info!("console: {:?}", line);
                line.clear();
            }
        });

        console_writer
    };

    log::info!("launching instance");

    let guest_instance = Box::new(virtualized::Instance::start(params, guest_writer)?);

    let channel = guest_instance.connect().await?;
    let connector_handle = Connector::spawn(channel);

    Ok((guest_instance, connector_handle))
}
