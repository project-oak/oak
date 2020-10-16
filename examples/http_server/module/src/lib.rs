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
use oak::{http::Invocation, CommandHandler, OakError, OakStatus};
use oak_abi::proto::oak::application::ConfigMap;

oak::entrypoint!(oak_main<ConfigMap> => |_receiver| {
    oak::logger::init_default();
    let node = StaticHttpServer;
    info!("Starting HTTP server pseudo-node on port 8080.");
    let http_channel =
        oak::http::init("[::]:8080").expect("Could not create HTTP server pseudo-Node!");

    oak::run_command_loop(node, http_channel);
});

/// A simple HTTP server that responds with `OK` (200) to every request sent to `/`, and with
/// `NOT_FOUND` (400) to any other request. It is used in the `abitest`. So its functionality
/// should be modified with care!
pub struct StaticHttpServer;

impl CommandHandler<Invocation> for StaticHttpServer {
    fn handle_command(&mut self, invocation: Invocation) -> Result<(), OakError> {
        let request = invocation.receive()?;

        info!("Handling a request to {}.", request.uri());

        let response = match request.uri().path().as_ref() {
            "/" => http::response::Builder::new()
                .status(http::StatusCode::OK)
                .header(http::header::CONTENT_TYPE, "text/html; charset=UTF-8")
                .body(include_bytes!("../static/index.html").to_vec()),
            _ => http::response::Builder::new()
                .status(http::StatusCode::NOT_FOUND)
                .body("not found".to_string().into_bytes()),
        };
        let response = response.map_err(|err| {
            warn!("Could not build response: {}", err);
            OakError::OakStatus(OakStatus::ErrInternal)
        })?;

        let res = invocation.send(&response);
        invocation.close_channels();
        res
    }
}
