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

//! Functionality for gRPC pseudo-Nodes.

use oak_abi::proto::google::rpc;
pub mod client;
mod codec;
mod invocation;
pub mod server;

/// Converts [`oak_abi::proto::google::rpc::Status`] to [`tonic::Status`].
fn to_tonic_status(status: rpc::Status) -> tonic::Status {
    tonic::Status::new(tonic::Code::from_i32(status.code), status.message)
}
