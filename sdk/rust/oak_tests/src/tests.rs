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

use oak::grpc::OakNode;
use protobuf::{Message, ProtobufEnum};

#[derive(oak_derive::OakExports)]
struct PanicNode;

impl oak::grpc::OakNode for PanicNode {
    fn new() -> Self {
        PanicNode
    }
    fn invoke(&mut self, _method: &str, _req: &[u8], _writer: oak::grpc::ChannelResponseWriter) {
        println!("PanicNode invoked, about to panic");
        panic!("PanicNode invoked!");
    }
}

#[test]
fn test_panic_catch() {
    crate::reset();
    crate::init_logging();
    let (write_handle, read_handle) = oak::channel_create().unwrap();

    // Mock up a GrpcRequest to trigger invoke()
    let mut grpc_req = oak::proto::grpc_encap::GrpcRequest::new();
    grpc_req.set_method_name("TestMethod".to_string());
    grpc_req.set_req_msg(protobuf::well_known_types::Any::new());
    grpc_req.set_last(true);

    // Serialize the request and send it with a handle.
    let mut req_data = Vec::new();
    grpc_req.write_to_writer(&mut req_data).unwrap();
    oak::channel_write(write_handle, &req_data, &[write_handle.handle]);

    assert_eq!(
        oak::OakStatus::ERR_INTERNAL.value(),
        oak_main(read_handle.handle)
    );
}
