//
// Copyright 2019 The Project Oak Authors
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

//! Private Set Intersection example for Project Oak.
//!
//! Clients invoke the module by providing their own private set, and the module keeps track of the
//! intersection of all the provided sets from all the clients that have interacted with it.
//! The number of contributed private sets is limited and defined by [`SET_THRESHOLD`].
//!
//! The (common) intersection can then be retrieved by each client by a separate invocation.
//! After the first client retrieves the intersection it becomes locked, and new contributions are
//! discarded.
//!
//! Each client request should be provided with a set ID. This is necessary for allowing multiple
//! sets of clients to compute their own intersections.
//!
//! It's important to note that in the current implementation of the application labels, specifying
//! a different set ID does not provide guarantees that data from different clients is kept
//! separate.

pub mod proto {
    include!(concat!(
        env!("OUT_DIR"),
        "/oak.examples.private_set_intersection.rs"
    ));
}

use anyhow::Context;
use oak::{grpc, Label};
use oak_abi::proto::oak::application::ConfigMap;
use proto::{
    GetIntersectionRequest, GetIntersectionResponse, PrivateSetIntersection,
    PrivateSetIntersectionDispatcher, SubmitSetRequest,
};
use std::collections::{HashMap, HashSet};

#[derive(Default)]
struct Main;

oak::entrypoint_command_handler!(oak_main => Main);

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: ConfigMap) -> anyhow::Result<()> {
        let handler_sender = oak::io::entrypoint_node_create::<
            PrivateSetIntersectionDispatcher<Handler>,
        >("handler", &Label::public_untrusted(), "app")
        .context("could not create handler node")?;
        oak::grpc::server::init_with_sender("[::]:8080", handler_sender)
            .context("could not create gRPC server pseudo-Node")?;
        Ok(())
    }
}

/// Maximum number of contributed private sets.
pub const SET_THRESHOLD: u64 = 2;

#[derive(Default)]
struct SetIntersection {
    /// Current intersection of contributed private sets.
    values: HashSet<String>,
    /// Number of contributed private sets.
    set_count: u64,
    /// The intersection is locked and new contributions are discarded.
    locked: bool,
}

#[derive(Default)]
struct Handler {
    /// Map from set ID to `SetIntersection`.
    ///
    /// this allows multiple sets of clients to compute their own intersections, also explain what
    /// the security characteristics are
    sets: HashMap<String, SetIntersection>,
}

oak::entrypoint_command_handler!(handler => PrivateSetIntersectionDispatcher<Handler>);

impl PrivateSetIntersection for Handler {
    fn submit_set(&mut self, req: SubmitSetRequest) -> grpc::Result<()> {
        let mut current_set = self.sets.entry(req.set_id).or_default();

        if current_set.locked {
            return Err(grpc::build_status(
                grpc::Code::FailedPrecondition,
                "Set contributions are no longer available",
            ));
        }

        if current_set.set_count < SET_THRESHOLD {
            let submitted_set = req.values.iter().cloned().collect::<HashSet<_>>();
            current_set.values = if current_set.values.is_empty() {
                submitted_set
            } else {
                current_set
                    .values
                    .intersection(&submitted_set)
                    .cloned()
                    .collect()
            };
            current_set.set_count += 1;
            Ok(())
        } else {
            Err(grpc::build_status(
                grpc::Code::FailedPrecondition,
                "Maximum number of contributed private sets is reached",
            ))
        }
    }

    fn get_intersection(
        &mut self,
        req: GetIntersectionRequest,
    ) -> grpc::Result<GetIntersectionResponse> {
        match self.sets.get_mut(&req.set_id) {
            Some(ref mut set) => {
                set.locked = true;
                Ok(GetIntersectionResponse {
                    values: set.values.iter().cloned().collect(),
                })
            }
            None => Err(grpc::build_status(
                grpc::Code::FailedPrecondition,
                "Incorrect set ID",
            )),
        }
    }
}
