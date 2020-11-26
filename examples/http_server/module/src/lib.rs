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

use anyhow::Context;
use log::info;
use oak::{http::Invocation, CommandHandler, Label};
use oak_abi::proto::oak::application::ConfigMap;
use oak_services::proto::oak::log::LogInit;

oak::entrypoint_command_handler!(oak_main => Main);

#[derive(Default)]
struct Main;

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: ConfigMap) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;
        let http_handler_sender = oak::io::entrypoint_node_create::<StaticHttpHandler, _, _>(
            "handler",
            &Label::public_untrusted(),
            "app",
            LogInit {
                log_sender: Some(log_sender),
            },
        )
        .expect("could not create handler node");
        oak::http::server::init_with_sender("[::]:8080", http_handler_sender)
            .expect("could not create HTTP server pseudo-Node");
        Ok(())
    }
}

oak::entrypoint_command_handler_init!(http_handler => StaticHttpHandler);

/// A simple HTTP handler that responds with `OK` (200) to every request sent to `/`; with a
/// response from `http://www.google.com` for every request sent to `/test_google`; and with
/// `NOT_FOUND` (400) to any other request. It is used in the `abitest`. So its functionality
/// should be modified with care!
#[derive(Default)]
pub struct StaticHttpHandler;

impl oak::WithInit for StaticHttpHandler {
    type Init = LogInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        StaticHttpHandler::default()
    }
}

impl CommandHandler for StaticHttpHandler {
    type Command = Invocation;

    fn handle_command(&mut self, invocation: Invocation) -> anyhow::Result<()> {
        let request = invocation.receive()?;

        info!("Handling a request to {}.", request.uri());

        let response = match request.uri().path().as_ref() {
            "/" => http::response::Builder::new()
                .status(http::StatusCode::OK)
                .header(http::header::CONTENT_TYPE, "text/html; charset=UTF-8")
                .body(include_bytes!("../static/index.html").to_vec())
                .context("Could not build response"),
            "/test_google" => {
                // create a public HTTP client pseudo-node
                let http_client = oak::http::client::init("")
                    .context("Could not create HttpClient pseudo-node")?;
                let request = http::Request::builder()
                    .method(http::Method::GET)
                    .uri("http://www.google.com")
                    .body(vec![])
                    .context("Could not build request")?;
                http_client
                    .send_request(request, &Label::public_untrusted())
                    .context("Could not get response")
            }
            _ => http::response::Builder::new()
                .status(http::StatusCode::NOT_FOUND)
                .body("not found".to_string().into_bytes())
                .context("Could not build response"),
        }?;

        let res = invocation.send(&response);
        invocation.close_channels();
        res?;
        Ok(())
    }
}
