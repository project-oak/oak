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

mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.rustfmt.rs"));
}

use oak::grpc;
use proto::{FormatRequest, FormatResponse, FormatService, FormatServiceDispatcher};

oak::entrypoint!(oak_main => |in_channel| {
    oak::logger::init_default();
    let dispatcher = FormatServiceDispatcher::new(Node);
    oak::run_event_loop(dispatcher, in_channel);
});

oak::entrypoint!(grpc_oak_main => |_in_channel| {
    oak::logger::init_default();
    let dispatcher = FormatServiceDispatcher::new(Node);
    let grpc_channel = oak::grpc::server::init_default();
    oak::run_event_loop(dispatcher, grpc_channel);
});

struct Node;

impl FormatService for Node {
    fn format(&mut self, req: FormatRequest) -> grpc::Result<FormatResponse> {
        let mut output = Vec::new();
        {
            let mut config = rustfmt_nightly::Config::default();
            config.set().emit_mode(rustfmt_nightly::EmitMode::Stdout);
            let mut session = rustfmt_nightly::Session::new(config, Some(&mut output));
            let input = rustfmt_nightly::Input::Text(req.code);
            session.format(input).expect("could not format input");
        }
        let mut res = FormatResponse::default();
        res.code = String::from_utf8(output).expect("could not parse UTF8");
        Ok(res)
    }
}
