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

use std::prelude::v1::*;

use std::string::String;

use log::info;

use oak_abi::OakStatus;
use oak_platform::{current_thread, spawn, JoinHandle};

use crate::channel::{wait_on_channels, ChannelReader};
use crate::RuntimeRef;

/// A simple logger loop.
fn logger(pretty_name: &str, runtime: RuntimeRef, reader: ChannelReader) -> Result<(), OakStatus> {
    loop {
        // An error indicates the runtime is terminating. We ignore it here and keep trying to read
        // in case a Wasm node wants to emit remaining messages. We will return once the channel is
        // closed.
        let _ = wait_on_channels(&runtime, &[Some(&reader)]);

        if let Some(message) = reader.read()? {
            let message = String::from_utf8_lossy(&message.data);
            info!("{} LOG: {}", pretty_name, message);
        }
    }
}

/// Create a new instance of a logger node.
pub fn new_instance(
    config_name: &str,
    runtime: RuntimeRef,
    initial_reader: ChannelReader,
) -> Result<JoinHandle, OakStatus> {
    let pretty_name = format!("{}-{:?}:", config_name, current_thread());
    Ok(spawn(move || {
        let result = logger(&pretty_name, runtime, initial_reader);
        info!("{} LOG: exiting log thread {:?}", pretty_name, result);
    }))
}
