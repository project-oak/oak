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

use crate::{grpc::Invocation, OakStatus};
use oak_abi::label::Label;
use oak_io::Sender;

/// Initializes a gRPC client pseudo-Node connecting to the provided address.
///
/// Returns a [`Sender`] to write gRPC [`Invocation`]s to.
pub fn init(address: &str) -> Result<Sender<Invocation>, OakStatus> {
    let config = crate::node_config::grpc_client(address);
    // TODO(#1669): Assign an appropriate label to the newly created node, based on the provided
    // address. If the label is higher (more confidential) than what the newly created gRPC
    // pseudo-node is able to declassify, the Runtime should return an error at node creation time.
    crate::io::node_create::<Invocation>("grpc_client", &Label::public_untrusted(), &config)
}
