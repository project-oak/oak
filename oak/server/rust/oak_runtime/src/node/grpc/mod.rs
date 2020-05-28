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

use oak_abi::proto::google::rpc;
pub mod client;
mod codec;
mod invocation;
pub mod server;

/// Converts [`tonic::Status`] to [`oak_abi::proto::google::rpc::Status`].
fn from_tonic_status(status: tonic::Status) -> oak_abi::proto::google::rpc::Status {
    oak_abi::proto::google::rpc::Status {
        code: status.code() as i32,
        message: status.message().to_string(),
        details: vec![prost_types::Any {
            // `type_url` parameter is not used by Oak Nodes.
            type_url: "".to_string(),
            // Request status details that have been sent back by an external gRPC service, are
            // propagated to an Oak Node that has created this request.
            value: status.details().to_vec(),
        }],
    }
}

/// Converts [`oak_abi::proto::google::rpc::Status`] to [`tonic::Status`].
fn to_tonic_status(status: oak_abi::proto::google::rpc::Status) -> tonic::Status {
    tonic::Status::new(tonic::Code::from_i32(status.code), status.message)
}

/// Converts [`oak_abi::OakStatus`] to [`oak_abi::proto::google::rpc::Status`].
fn from_abi_status(status: oak_abi::OakStatus) -> oak_abi::proto::google::rpc::Status {
    oak_abi::proto::google::rpc::Status {
        code: rpc::Code::Internal as i32,
        message: format!("Operation failed: {:?}", status),
        details: vec![],
    }
}
