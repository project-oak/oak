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

use crate::{
    runtime::{Handle, RuntimeProxy},
    NodeId,
};
use lazy_static::lazy_static;
use log::{error, info};
use oak_abi::OakStatus;
use std::{sync::RwLock, thread, thread::JoinHandle};

// TODO(#724): shift to a more explicit external pseudo-Node creation
// mechanism when the runtime's main() is in Rust.
pub type NodeFactory = fn(config_name: &str, node_id: NodeId, handle: Handle);

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
    reader: Handle,
    thread_handle: Option<JoinHandle<()>>,
}

impl PseudoNode {
    pub fn new(config_name: &str, runtime: RuntimeProxy, reader: Handle) -> Self {
        Self {
            config_name: config_name.to_string(),
            runtime,
            reader,
            thread_handle: None,
        }
    }
}

impl super::Node for PseudoNode {
    fn start(&mut self) -> Result<(), OakStatus> {
        // Clone or copy all the captured values and move them into the closure, for simplicity.
        let config_name = self.config_name.clone();
        let runtime = self.runtime.clone();
        let reader = self.reader;
        let thread_handle = thread::Builder::new()
            .name(format!("external={}", config_name))
            .spawn(move || {
                let pretty_name = format!("{}-{:?}:", config_name, thread::current());
                let factory_fn: NodeFactory = FACTORY
                    .read()
                    .expect("unlock failed")
                    .expect("no registered factory");
                info!(
                    "invoke external node factory with '{}', reader={:?} on thread {:?}",
                    config_name,
                    reader,
                    thread::current(),
                );
                factory_fn(&config_name, runtime.node_id, reader);

                info!(
                    "{} LOG: exiting pseudo-Node thread {:?}",
                    pretty_name,
                    thread::current()
                );
                runtime.exit_node();
            })
            .expect("failed to spawn thread");
        info!("external node started on thread {:?}", thread_handle);
        self.thread_handle = Some(thread_handle);
        Ok(())
    }

    fn stop(&mut self) {
        if let Some(join_handle) = self.thread_handle.take() {
            if let Err(err) = join_handle.join() {
                error!("error while stopping external node: {:?}", err);
            }
        }
    }
}
