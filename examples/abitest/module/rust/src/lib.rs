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
extern crate abitest_common;
extern crate oak;
extern crate oak_log;
extern crate protobuf;
extern crate regex;
extern crate serde;

mod proto;

use abitest_common::InternalMessage;
use oak::{GrpcResult, OakNode};
use proto::abitest::{ABITestRequest, ABITestResponse, ABITestResponse_TestResult};
use proto::abitest_grpc::{dispatch, OakABITestServiceNode};
use protobuf::ProtobufEnum;
use std::collections::HashMap;
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

impl OakABITestServiceNode for FrontendNode {
    fn run_tests(&mut self, req: ABITestRequest) -> GrpcResult<ABITestResponse> {
        info!("Run tests matching {}", req.filter);
        let filter = regex::Regex::new(&req.filter).unwrap();
        let mut results = protobuf::RepeatedField::<ABITestResponse_TestResult>::new();

        // Manual registry of all tests.
        // TODO: Add some macro wizardry for registering test methods based on an attribute
        type TestFn = fn(&mut FrontendNode) -> std::io::Result<()>;
        let mut tests: HashMap<&str, TestFn> = HashMap::new();
        tests.insert("BackendRoundtrip", FrontendNode::test_backend_roundtrip);

        for (&name, &testfn) in &tests {
            if !filter.is_match(name) {
                continue;
            }
            info!("running test {}", name);
            let mut result = ABITestResponse_TestResult::new();
            result.set_name(name.to_string());
            match testfn(self) {
                Ok(()) => result.set_success(true),
                Err(err) => {
                    result.set_success(false);
                    result.set_details(format!("Error: {}", err));
                }
            }
            results.push(result);
        }

        let mut res = ABITestResponse::new();
        res.set_results(results);
        Ok(res)
    }
}

impl FrontendNode {
    fn test_backend_roundtrip(&mut self) -> std::io::Result<()> {
        // Ask the backend node to transmute something.
        let internal_req = InternalMessage {
            msg: "aaa".to_string(),
        };
        let serialized_req = serde_json::to_string(&internal_req)?;
        info!("send serialized message to backend: {}", serialized_req);
        self.backend_out.write_all(&serialized_req.into_bytes())?;

        // Block until there is a response from the backend available.
        match oak::wait_on_channels(&self.read_handles) {
            Ok(_ready_handles) => (),
            Err(status) => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    format!("Wait failure {:?}", status),
                ));
            }
        }

        let mut buffer = Vec::<u8>::with_capacity(256);
        let mut handles = Vec::with_capacity(1);
        self.backend_in.read_message(&mut buffer, &mut handles)?;

        // Expect to receive a channel read handle.
        // Read the actual response from the new channel.
        let mut new_in_channel = oak::ReceiveChannelHalf::new(handles[0]);
        new_in_channel.read_message(&mut buffer, &mut vec![])?;
        let serialized_rsp = String::from_utf8(buffer).unwrap();
        let internal_rsp: InternalMessage = serde_json::from_str(&serialized_rsp)?;
        info!(
            "received backend response via {}: {:?}",
            handles[0], internal_rsp
        );

        // Drop the new read channel now we have got the response.
        oak::channel_close(handles[0]);
        Ok(())
    }
}
