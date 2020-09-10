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

use log::{info, warn};
use maplit::hashmap;
use oak::{http::Invocation, Node, OakError};
use oak_services::proto::oak::encap::HttpResponse;

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

        info!("Handling a request to {}.", request.uri);

        // Workaround for https://rust-lang.github.io/rust-clippy/master/index.html#borrow_interior_mutable_const.
        static CONTENT_TYPE: http::header::HeaderName = http::header::CONTENT_TYPE;

        let response = match request.uri.parse::<http::Uri>() {
            Ok(uri) => match uri.path().as_ref() {
                "/" => HttpResponse {
                    body: include_bytes!("../static/index.html").to_vec(),
                    status: http::StatusCode::OK.as_u16() as i32,
                    headers: hashmap! {
                        CONTENT_TYPE.as_str().to_string() => "text/html; charset=UTF-8".to_string().into_bytes(),
                    },
                },
                _ => HttpResponse {
                    body: "not found".to_string().into_bytes(),
                    status: http::StatusCode::NOT_FOUND.as_u16() as i32,
                    headers: hashmap! {},
                },
            },
            Err(err) => {
                warn!("could not parse URI: {}", err);
                HttpResponse {
                    body: "invalid URI".to_string().into_bytes(),
                    status: http::StatusCode::BAD_REQUEST.as_u16() as i32,
                    headers: hashmap! {},
                }
            }
        };

        let res = invocation.send(&response);
        invocation.close_channels();
        res
    }
}
