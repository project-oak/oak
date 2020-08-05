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

use crate::proto::oak_abi::encap::GrpcRequest;
use log::warn;

/// Encapsulate a protocol buffer message in a GrpcRequest wrapper using the
/// given method name.
pub fn encap_request<T: prost::Message>(req: &T, method_name: &str) -> Option<GrpcRequest> {
    // Put the request in a GrpcRequest wrapper and serialize it.
    let mut bytes = Vec::new();
    if let Err(e) = req.encode(&mut bytes) {
        warn!("failed to serialize gRPC request: {}", e);
        return None;
    };
    let grpc_req = GrpcRequest {
        method_name: method_name.to_string(),
        req_msg: bytes,
        last: true,
    };
    Some(grpc_req)
}
