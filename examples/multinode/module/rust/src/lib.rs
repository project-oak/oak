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

#[macro_use]
extern crate log;
extern crate multinode_common;
extern crate oak;
extern crate oak_log;
extern crate protobuf;
extern crate serde;

mod proto;

use multinode_common::InternalMessage;
use oak::{GrpcResult, OakNode};
use proto::multinode::{ExampleRequest, ExampleResponse};
use proto::multinode_grpc::{dispatch, ExampleServiceNode};
use protobuf::ProtobufEnum;
use std::io::Write;

struct FrontendNode {
    grpc_in: oak::Handle,
    grpc_out: oak::Handle,
    backend_out: oak::SendChannelHalf,
    read_handles: Vec<oak::Handle>,
    backend_in: oak::ReceiveChannelHalf,
}

#[no_mangle]
pub extern "C" fn oak_main() -> i32 {
    match std::panic::catch_unwind(|| {
        let node = FrontendNode::new();
        let grpc_in = node.grpc_in;
        let grpc_out = node.grpc_out;
        oak::grpc_event_loop(node, grpc_in, grpc_out)
    }) {
        Ok(rc) => rc,
        Err(_) => oak::proto::oak_api::OakStatus::ERR_INTERNAL.value(),
    }
}

impl oak::OakNode for FrontendNode {
    fn new() -> Self {
        oak_log::init(log::Level::Debug, oak::channel_find("logging_port")).unwrap();
        let backend_in = oak::channel_find("from_backend");
        FrontendNode {
            grpc_in: oak::channel_find("gRPC_input"),
            grpc_out: oak::channel_find("gRPC_output"),
            backend_out: oak::SendChannelHalf::new(oak::channel_find("to_backend")),
            read_handles: vec![backend_in],
            backend_in: oak::ReceiveChannelHalf::new(backend_in),
        }
    }
    fn invoke(&mut self, method: &str, req: &[u8], out: &mut oak::SendChannelHalf) {
        dispatch(self, method, req, out)
    }
}

impl ExampleServiceNode for FrontendNode {
    fn example_method(&mut self, req: ExampleRequest) -> GrpcResult<ExampleResponse> {
        info!("Say hello to {}", req.greeting);

        // Ask the backend to transmute the greeting.
        let internal_req = InternalMessage { msg: req.greeting };
        let serialized_req = serde_json::to_string(&internal_req).unwrap();
        info!("send serialized message to backend: {}", serialized_req);
        self.backend_out
            .write_all(&serialized_req.into_bytes())
            .unwrap();

        // Block until there is a response from the backend available.
        match oak::wait_on_channels(&self.read_handles) {
            Ok(_ready_handles) => (),
            Err(err) => {
                let mut status = oak::proto::status::Status::new();
                status.set_code(13); // INTERNAL
                status.set_message(format!("Wait failure {}", err.value()));
                return Err(status);
            }
        }

        let mut buffer = Vec::<u8>::with_capacity(256);
        let mut handles = Vec::with_capacity(1);
        self.backend_in
            .read_message(&mut buffer, &mut handles)
            .unwrap();
        let serialized_rsp = String::from_utf8(buffer).unwrap();
        let internal_rsp: InternalMessage = serde_json::from_str(&serialized_rsp).unwrap();
        info!("received backend response: {:?}", internal_rsp);

        let mut res = ExampleResponse::new();
        res.reply = format!("HELLO {}!", internal_rsp.msg);
        Ok(res)
    }
}
