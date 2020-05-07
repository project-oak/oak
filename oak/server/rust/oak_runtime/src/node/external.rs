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
use std::{sync::RwLock, thread};

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
    node_name: String,
    config_name: String,
    runtime: RuntimeProxy,
    reader: oak_abi::Handle,
}

impl PseudoNode {
    pub fn new(
        node_name: &str,
        runtime: RuntimeProxy,
        config_name: &str,
        reader: oak_abi::Handle,
    ) -> Self {
        Self {
            node_name: node_name.to_string(),
            config_name: config_name.to_string(),
            runtime,
            reader,
        }
    }
}

impl super::Node for PseudoNode {
    fn run(self: Box<Self>) {
        let factory_fn: NodeFactory = FACTORY
            .read()
            .expect("unlock failed")
            .expect("no registered factory");
        info!(
            "{}: invoke external node factory with reader={:?} on thread {:?}",
            self.node_name,
            self.reader,
            thread::current(),
        );
        factory_fn(&self.config_name, self.runtime.node_id, self.reader);

        info!("{} pseudo-Node execution complete", self.node_name);
        let _ = self.runtime.channel_close(self.reader);
    }
}
