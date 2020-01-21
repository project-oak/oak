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

mod proto;

use oak::grpc;
use oak::grpc::OakGrpcServerNode;
use oak_derive::OakGrpcEntrypoint;
use proto::rustfmt::{FormatRequest, FormatResponse};
use proto::rustfmt_grpc::{dispatch, FormatServiceNode};
use protobuf::ProtobufEnum;

#[derive(OakGrpcEntrypoint)]
struct Node;

impl OakGrpcServerNode for Node {
    fn new() -> Self {
        oak_log::init_default();
        Node
    }
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

impl FormatServiceNode for Node {
    fn format(&mut self, req: FormatRequest) -> grpc::Result<FormatResponse> {
        let mut output = Vec::new();
        {
            let mut config = rustfmt_nightly::Config::default();
            config.set().emit_mode(rustfmt_nightly::EmitMode::Stdout);
            let mut session = rustfmt_nightly::Session::new(config, Some(&mut output));
            let input = rustfmt_nightly::Input::Text(req.code.clone());
            session.format(input).expect("could not format input");
        }
        let mut res = FormatResponse::new();
        res.code = String::from_utf8(output).expect("could not parse UTF8");
        Ok(res)
    }
}
