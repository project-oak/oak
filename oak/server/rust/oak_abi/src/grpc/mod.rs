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

use crate::proto::oak::encap::GrpcRequest;
use log::warn;

/// Encapsulate a protocol buffer message in a GrpcRequest wrapper using the
/// given method name.
pub fn encap_request<T: prost::Message>(
    req: &T,
    req_type_url: Option<&str>,
    method_name: &str,
) -> Option<GrpcRequest> {
    // Put the request in a GrpcRequest wrapper and serialize it.
    let mut grpc_req = GrpcRequest::default();
    grpc_req.method_name = method_name.to_string();
    let mut any = prost_types::Any::default();
    if let Err(e) = req.encode(&mut any.value) {
        warn!("failed to serialize gRPC request: {}", e);
        return None;
    };
    if let Some(type_url) = req_type_url {
        any.type_url = type_url.to_string();
    }
    grpc_req.req_msg = Some(any);
    grpc_req.last = true;
    Some(grpc_req)
}
