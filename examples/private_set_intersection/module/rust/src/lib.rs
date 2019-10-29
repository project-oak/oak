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
//!
//! The (common) intersection can then be retrieved by each client by a separate invocation.
//!
//! TODO: Limit number of clients / sets that may contribute to the intersection.
//! TODO: Consider stopping accepting contributions after the first client retrieves the
//! intersection.

extern crate oak;
extern crate oak_derive;
extern crate protobuf;

mod proto;

use oak::grpc;
use oak::grpc::OakNode;
use oak_derive::OakExports;
use proto::private_set_intersection::{GetIntersectionResponse, SubmitSetRequest};
use proto::private_set_intersection_grpc::{dispatch, PrivateSetIntersectionNode};
use protobuf::well_known_types::Empty;
use protobuf::ProtobufEnum;
use std::collections::HashSet;

#[derive(Default, OakExports)]
struct Node {
    values: Option<HashSet<String>>,
}

impl oak::grpc::OakNode for Node {
    fn new() -> Self {
        Node::default()
    }
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

impl PrivateSetIntersectionNode for Node {
    fn submit_set(&mut self, req: SubmitSetRequest) -> grpc::Result<Empty> {
        let set = req.values.iter().cloned().collect::<HashSet<_>>();
        let next = match self.values {
            Some(ref previous) => previous.intersection(&set).cloned().collect(),
            None => set,
        };
        self.values = Some(next);
        Ok(Empty::new())
    }

    fn get_intersection(&mut self, _req: Empty) -> grpc::Result<GetIntersectionResponse> {
        let mut res = GetIntersectionResponse::new();
        if let Some(ref set) = self.values {
            res.values = set.iter().cloned().collect();
        };
        Ok(res)
    }
}
