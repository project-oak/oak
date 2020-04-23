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

use crate::{NodeId, RuntimeProxy};
use lazy_static::lazy_static;
use log::info;
use oak_abi::OakStatus;
use std::{sync::RwLock, thread, thread::JoinHandle};

// TODO(#724): shift to a more explicit external pseudo-Node creation
// mechanism when the runtime's main() is in Rust.
pub type NodeFactory = fn(config_name: &str, node_id: NodeId, handle: oak_abi::Handle);

lazy_static! {
    static ref FACTORY: RwLock<Option<NodeFactory>> = RwLock::new(None);
}

pub fn register_factory(factory: NodeFactory) {
    info!("register external node factory");
    *FACTORY.write().unwrap() = Some(factory);
}

pub struct PseudoNode {
    config_name: String,
    runtime: RuntimeProxy,
    reader: oak_abi::Handle,
}

impl PseudoNode {
    pub fn new(config_name: &str, runtime: RuntimeProxy, reader: oak_abi::Handle) -> Self {
        Self {
            config_name: config_name.to_string(),
            runtime,
            reader,
        }
    }

    /// Main node worker thread.
    fn worker_thread(self) {
        let pretty_name = format!("{}-{:?}:", self.config_name, thread::current());
        let factory_fn: NodeFactory = FACTORY
            .read()
            .expect("unlock failed")
            .expect("no registered factory");
        info!(
            "invoke external node factory with '{}', reader={:?} on thread {:?}",
            self.config_name,
            self.reader,
            thread::current(),
        );
        factory_fn(&self.config_name, self.runtime.node_id, self.reader);

        info!(
            "{} LOG: exiting pseudo-Node thread {:?}",
            pretty_name,
            thread::current()
        );
        self.runtime.exit_node();
    }
}

impl super::Node for PseudoNode {
    fn start(self: Box<Self>) -> Result<JoinHandle<()>, OakStatus> {
        // Clone or copy all the captured values and move them into the closure, for simplicity.
        let thread_handle = thread::Builder::new()
            .name(format!("external={}", self.config_name))
            .spawn(move || self.worker_thread())
            .expect("failed to spawn thread");
        info!("external node started on thread {:?}", thread_handle);
        Ok(thread_handle)
    }
}
