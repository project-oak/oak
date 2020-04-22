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

//! Oak Runtime implementation
//!
//! # Features
//!
//! The `oak_debug` feature enables various debugging features, including
//! data structure introspection functionality. This feature should only
//! be enabled in development, as it destroys the privacy guarantees of the
//! platform by providing easy channels for the exfiltration of private data.

pub mod proto;

pub mod config;
pub mod message;
pub mod metrics;
pub mod node;
pub mod runtime;

pub use config::{application_configuration, configure_and_run};

pub use message::{Message, NodeMessage};
pub use runtime::{HandleDirection, NodeId, Runtime};

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

/// Configuration options that govern the behaviour of the Runtime itself.
#[derive(Debug)]
pub struct RuntimeConfiguration {
    /// Port to run a metrics server on, if provided.
    pub metrics_port: Option<u16>,
    /// Port to run an introspection server on, if provided.
    pub introspect_port: Option<u16>,
}

impl Default for RuntimeConfiguration {
    fn default() -> Self {
        RuntimeConfiguration {
            metrics_port: None,
            introspect_port: None,
        }
    }
}
