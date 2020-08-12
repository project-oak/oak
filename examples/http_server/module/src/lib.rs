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

//! Simple example starting an Oak Application serving a static page over HTTP.

use log::info;
use maplit::hashmap;
use oak::{http::Invocation, Node, OakError};
use oak_abi::proto::oak::encap::HttpResponse;

oak::entrypoint!(oak_main => |_in_channel| {
    oak::logger::init_default();
    let node = StaticHttpServer{};
    info!("Starting HTTP server pseudo-node on port 8080.");
    let http_channel =
        oak::http::init("[::]:8080").expect("Could not create HTTP server pseudo-Node!");

    oak::run_event_loop(node, http_channel);
});

struct StaticHttpServer;

impl Node<Invocation> for StaticHttpServer {
    fn handle_command(&mut self, invocation: Invocation) -> Result<(), OakError> {
        let request = invocation.receive()?;

        info!("Handling a request to {}.", request.path);

        let http_response = HttpResponse {
            body: "Hello from HTTP server!\n".to_string().into_bytes(),
            status: 200,
            headers: hashmap! {},
        };

        let res = invocation.send(&http_response);
        invocation.close_channels();
        res
    }
}
