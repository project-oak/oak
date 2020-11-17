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

use crate::proto::{
    GetIntersectionRequest, GetIntersectionResponse, PrivateSetIntersection,
    PrivateSetIntersectionDispatcher, SubmitSetRequest,
};
use oak::grpc;
use std::collections::{HashMap, HashSet};

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

oak::impl_dispatcher!(impl Handler : PrivateSetIntersectionDispatcher);

oak::entrypoint_command_handler!(handler => Handler);

#[derive(Default)]
pub struct Handler {
    /// Map from set ID to `SetIntersection`.
    sets: HashMap<String, SetIntersection>,
}

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
