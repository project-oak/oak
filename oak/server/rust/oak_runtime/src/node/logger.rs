//
// Copyright 2020 The Project Oak Authors
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

use std::string::String;

use log::{error, info};

use oak_abi::OakStatus;
use std::{
    thread,
    thread::{spawn, JoinHandle},
};

use crate::proto::log::{Level, LogMessage};
use crate::runtime::ChannelRef;
use crate::RuntimeRef;
use prost::Message;

/// A simple logger loop.
fn logger(pretty_name: &str, runtime: RuntimeRef, reader: ChannelRef) -> Result<(), OakStatus> {
    loop {
        // An error indicates the runtime is terminating. We ignore it here and keep trying to read
        // in case a Wasm node wants to emit remaining messages. We will return once the channel is
        // closed.

        // TODO(#646): Temporarily don't wait for messages when terminating. Renable when channels
        // track their channels and make sure all channels are closed.
        // let _ = runtime.wait_on_channels(&[Some(&reader)]);
        runtime.wait_on_channels(&[Some(reader)])?;

        if let Some(message) = runtime.channel_read(reader)? {
            match LogMessage::decode(&*message.data) {
                Ok(msg) => info!(
                    "{} LOG: {} {}:{}: {}",
                    pretty_name,
                    to_level_name(msg.level),
                    msg.file,
                    msg.line,
                    msg.message
                ),
                Err(error) => error!("{} Could not parse LogMessage: {}", pretty_name, error),
            }
        }
    }
}

fn to_level_name(level: i32) -> String {
    format!(
        "{:?}",
        Level::from_i32(level).unwrap_or(Level::UnknownLevel)
    )
    .to_ascii_uppercase()
}

/// Create a new instance of a logger node.
pub fn new_instance(
    config_name: &str,
    runtime: RuntimeRef,
    initial_reader: ChannelRef,
) -> Result<JoinHandle<()>, OakStatus> {
    let pretty_name = format!("{}-{:?}:", config_name, thread::current());
    Ok(spawn(move || {
        let result = logger(&pretty_name, runtime, initial_reader);
        info!("{} LOG: exiting log thread {:?}", pretty_name, result);
    }))
}
