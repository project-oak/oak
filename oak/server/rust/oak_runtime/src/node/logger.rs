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

use crate::channel::ChannelReader;
use crate::platform;
use crate::RuntimeRef;

/// Create a new instance of a logger node.
pub fn new_instance(
    config_name: &str,
    _runtime: RuntimeRef,
    initial_reader: ChannelReader,
) -> Result<crate::JoinHandle, OakStatus> {
    let config_name = config_name.to_owned();
    Ok(platform::thread::spawn(move || {
        let pretty_name = format!("{}-{:?}:", config_name, platform::thread::current().id());
        loop {
            match initial_reader.read() {
                // Received message
                Ok(Some(message)) => {
                    let message = String::from_utf8_lossy(&message.data);
                    info!("{} LOG: {}", pretty_name, message);
                }
                // No message ready, yield thread
                Ok(None) => {
                    crate::yield_thread();
                }
                Err(OakStatus::ERR_CHANNEL_CLOSED) => {
                    return;
                }
                Err(e) => {
                    panic!("Unexpected error! {:?}", e);
                }
            }
        }
    }))
}
