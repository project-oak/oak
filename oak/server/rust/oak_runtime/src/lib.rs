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

pub mod proto;

pub mod config;
pub mod message;
pub mod node;
pub mod runtime;

#[cfg(test)]
mod tests;

pub use config::application_configuration;
pub use config::configure_and_run;

pub use message::Message;
pub use runtime::{ChannelHalfId, NodeId, Runtime};

use std::thread::Thread;

/// Formats the thread for logging. Threads should be given a name with
/// [`std::thread::Builder::name`] to make the output more readable.
fn pretty_name_for_thread(thread_handle: &Thread) -> String {
    format!(
        "{:?}:{}",
        thread_handle.id(),
        // Note: Use "<unnamed>" to make it stand out in the logs (and
        // hopefully fixed).
        thread_handle.name().unwrap_or("<unnamed>")
    )
}
