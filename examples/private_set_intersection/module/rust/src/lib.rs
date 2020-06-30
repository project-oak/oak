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
//! The number of contributed private sets is limited and defined by [`CONTRIBUTION_THRESHOLD`].
//!
//! The (common) intersection can then be retrieved by each client by a separate invocation.
//! After the first client retrieves the intersection it becomes locked, and new contributions are
//! discarded.

pub mod proto {
    include!(concat!(
        env!("OUT_DIR"),
        "/oak.examples.private_set_intersection.rs"
    ));
}

use oak::grpc;
use proto::{
    GetIntersectionResponse, PrivateSetIntersection, PrivateSetIntersectionDispatcher,
    SubmitSetRequest,
};
use std::collections::HashSet;

oak::entrypoint!(oak_main => |_in_channel| {
    let dispatcher = PrivateSetIntersectionDispatcher::new(Node::default());
    let grpc_channel =
        oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
    oak::run_event_loop(dispatcher, grpc_channel);
});

/// Maximum number of contributed private sets.
pub const SET_THRESHOLD: u64 = 2;

#[derive(Default)]
struct Node {
    /// Current intersection of contributed private sets.
    values: Option<HashSet<String>>,
    /// Number of contributed private sets.
    set_count: u64,
    /// The intersection is locked and new contributions are discarded.
    locked: bool,
}

impl PrivateSetIntersection for Node {
    fn submit_set(&mut self, req: SubmitSetRequest) -> grpc::Result<()> {
        if self.locked {
            return Err(grpc::build_status(
                grpc::Code::FailedPrecondition,
                "Set contributions are no longer available",
            ));
        }

        if self.set_count < SET_THRESHOLD {
            let set = req.values.iter().cloned().collect::<HashSet<_>>();
            let next = match self.values {
                Some(ref previous) => previous.intersection(&set).cloned().collect(),
                None => set,
            };
            self.values = Some(next);
            self.set_count += 1;
            Ok(())
        } else {
            Err(grpc::build_status(
                grpc::Code::FailedPrecondition,
                "Maximum number of contributed private sets is reached",
            ))
        }
    }

    fn get_intersection(&mut self, _req: ()) -> grpc::Result<GetIntersectionResponse> {
        let mut res = GetIntersectionResponse::default();
        if let Some(ref set) = self.values {
            res.values = set.iter().cloned().collect();
        };
        self.locked = true;
        Ok(res)
    }
}
