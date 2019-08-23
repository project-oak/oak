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

extern crate oak;
extern crate oak_derive;

use oak::OakNode;
use protobuf::{Message, ProtobufEnum};

#[derive(oak_derive::OakExports)]
struct PanicNode;

impl oak::OakNode for PanicNode {
    fn new() -> Self {
        PanicNode
    }
    fn invoke(&mut self, _method: &str, _req: &[u8], _out: &mut oak::SendChannelHalf) {
        println!("PanicNode invoked, about to panic");
        panic!("PanicNode invoked!");
    }
}

#[test]
fn test_panic_catch() {
    crate::reset_channels();

    // Mock up a GrpcRequest to trigger invoke()
    let mut grpc_req = oak::proto::grpc_encap::GrpcRequest::new();
    grpc_req.set_method_name("TestMethod".to_string());
    grpc_req.set_req_msg(protobuf::well_known_types::Any::new());
    grpc_req.set_last(true);

    // Serialize the request into a channel.
    let mut channel = oak::SendChannelHalf::new(2);
    grpc_req.write_to_writer(&mut channel).unwrap();

    assert_eq!(
        oak::proto::oak_api::OakStatus::ERR_INTERNAL.value(),
        oak_main()
    );
}
