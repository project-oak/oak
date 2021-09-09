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
//! In addition, there is a redirect server that redirects the requests sent to it to the static
//! server. This is done using an HTTP client pseudo-Node. So, in addition to the `Main` node and
//! the `Log` node, this example has three Oak nodes, and three pseudo-Nodes.

pub mod proto {
    pub mod oak {
        pub use oak::proto::oak::invocation;
        pub use oak_services::proto::oak::log;
        pub mod examples {
            pub mod http_server {
                include!(concat!(
                    env!("OUT_DIR"),
                    "/oak.examples.http_server_init.rs"
                ));
            }
        }
    }
}

use crate::proto::oak::examples::http_server::{RedirectHandlerInit, RedirectInvocation};
use anyhow::Context;
use log::info;
use oak::{
    http::{create_http_invocation, HttpInvocation},
    io::{ReceiverExt, Sender, SenderExt},
    CommandHandler, Label,
};
use oak_abi::{
    label::{confidentiality_label, tls_endpoint_tag},
    proto::oak::application::ConfigMap,
};
use oak_services::proto::oak::log::{LogInit, LogMessage};

oak::entrypoint_command_handler!(oak_main => Main);

#[derive(Default)]
struct Main;

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: ConfigMap) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;

        // Create a static server on port 8080, involving an Oak node and an HTTP server
        // pseudo-Node.
        create_static_server(log_sender.clone())?;

        // Create an Oak node for redirecting requests to an HTTP client node for "localhost:8080".
        let redirect_helper_sender = create_redirect_helper(log_sender.clone())?;

        // Create a redirect server on port 8081, involving an Oak node, an HTTP server
        // pseudo-Node, and an HTTP client pseudo-Node.
        create_redirect_server(log_sender, redirect_helper_sender)?;

        Ok(())
    }
}

oak::entrypoint_command_handler_init!(http_handler => StaticHttpHandler);
oak::entrypoint_command_handler_init!(redirect_handler => RedirectHandler);
oak::entrypoint_command_handler_init!(redirect_helper => RedirectHelper);

/// Creates a public Oak Node and an HTTP server pseudo-Node to serve requests sent to
/// `localhost:8080`.
fn create_static_server(log_sender: Sender<LogMessage>) -> anyhow::Result<()> {
    let static_handler_sender = oak::io::entrypoint_node_create::<StaticHttpHandler, _, _>(
        "static-handler",
        &Label::public_untrusted(),
        "app",
        LogInit {
            log_sender: Some(log_sender),
        },
    )
    .context("Couldn't create handler node")?;

    oak::http::server::init_with_sender("[::]:8080", static_handler_sender)
        .context("Couldn't create HTTP server pseudo-Node")?;
    Ok(())
}

/// Creates a public Oak Node and an HTTP server pseudo-Node to serve requests sent to
/// `localhost:8081`. Redirection requests are sent to a helper Oak Node (the handler to which is in
/// the input argument `redirect_helper_sender`) that redirects the requests to `localhost:8080`
/// using an HTTP client pseudo-Node, also created in this function.
fn create_redirect_server(
    log_sender: Sender<LogMessage>,
    redirect_helper_sender: Sender<RedirectInvocation>,
) -> anyhow::Result<()> {
    // create a non-public HTTP client pseudo-node
    let client_invocation_sender = oak::http::client::init("localhost:8080").unwrap();

    let redirect_handler_sender = oak::io::entrypoint_node_create::<RedirectHandler, _, _>(
        "redirect-handler",
        &Label::public_untrusted(),
        "app",
        RedirectHandlerInit {
            log_sender: Some(log_sender),
            helper_invocation_sender: Some(redirect_helper_sender),
            client_invocation_sender: Some(client_invocation_sender),
        },
    )
    .context("Couldn't create handler node")?;

    oak::http::server::init_with_sender("[::]:8081", redirect_handler_sender)
        .context("Couldn't create HTTP server pseudo-Node")?;
    Ok(())
}

/// Creates a non-public Oak node that sends requests to "localhost:8080" via a non-public HTTP
/// client pseudo-Node. Returns a handler for communication with the `redirect-handler` node.
fn create_redirect_helper(
    log_sender: Sender<LogMessage>,
) -> anyhow::Result<Sender<RedirectInvocation>> {
    let label = confidentiality_label(tls_endpoint_tag("localhost:8080"));

    oak::io::entrypoint_node_create::<RedirectHelper, _, _>(
        "redirect-helper",
        &label,
        "app",
        LogInit {
            log_sender: Some(log_sender),
        },
    )
    .context("Couldn't create handler node")
}

/// A simple HTTP handler that responds with `OK` (200) to every request sent to `/`, and with
/// `NOT_FOUND` (400) to any other request. This struct is used in the `abitest`. So its
/// functionality should be modified with care!
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
    type Command = HttpInvocation;

    fn handle_command(&mut self, invocation: HttpInvocation) -> anyhow::Result<()> {
        let request = invocation.receive()?;

        info!("Handling a request to {}.", request.uri());

        let response = match request.uri().path() {
            "/" => http::response::Builder::new()
                .status(http::StatusCode::OK)
                .header(http::header::CONTENT_TYPE, "text/html; charset=UTF-8")
                .body(include_bytes!("../static/index.html").to_vec())
                .context("Couldn't build response"),
            _ => http::response::Builder::new()
                .status(http::StatusCode::NOT_FOUND)
                .body("not found".to_string().into_bytes())
                .context("Couldn't build response"),
        };

        let response = match response {
            Ok(rsp) => rsp,
            Err(err) => http::response::Builder::new()
                .status(http::StatusCode::INTERNAL_SERVER_ERROR)
                .body(err.to_string().into_bytes())
                .context("Couldn't build response")?,
        };

        info!("Sending the response on the invocation channel");
        invocation.send(&response).context("Couldn't send response")
    }
}

/// A handler corresponding to an HTTP server that redirects every request to
/// `https://localhost:8080` and responds with `OK` (200) if the redirect is successful.
pub struct RedirectHandler {
    helper_invocation_sender: Sender<RedirectInvocation>,
    client_invocation_sender: Sender<HttpInvocation>,
}

impl oak::WithInit for RedirectHandler {
    type Init = RedirectHandlerInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        RedirectHandler {
            helper_invocation_sender: init.helper_invocation_sender.unwrap(),
            client_invocation_sender: init.client_invocation_sender.unwrap(),
        }
    }
}

impl CommandHandler for RedirectHandler {
    type Command = HttpInvocation;

    fn handle_command(&mut self, invocation: HttpInvocation) -> anyhow::Result<()> {
        info!("Redirecting the request");

        let label = confidentiality_label(tls_endpoint_tag("localhost:8080"));

        // Create invocations for passing HTTP requests to the HTTP Client node and collecting HTTP
        // responses from it.
        let (client_invocation, client_invocation_source) = create_http_invocation(&label)?;

        // Send the request-receiver channel, together with the new invocation source for
        // communication with the HTTP client pseudo-Node, to the RedirectHelper node in a
        // RedirectInvocation.
        let helper_invocation = RedirectInvocation {
            request_receiver: Some(invocation.receiver.clone().unwrap()),
            http_invocation_source: Some(client_invocation_source),
        };
        self.helper_invocation_sender.send(&helper_invocation)?;

        // Send the other end of the invocation to the HTTP client pseudo-Node.
        self.client_invocation_sender.send(&client_invocation)?;

        // Response with OK(200).
        let response = http::response::Builder::new()
            .status(http::StatusCode::OK)
            .body("Successfully sent request".to_string().into_bytes())
            .context("Couldn't build response")?;

        // Send a response to the caller.
        invocation
            .send(&response)
            .context("Couldn't send HTTP response")
    }
}

/// A helper node that sends request to an HTTP client pseudo-Node, collects the response and logs
/// the status in the response. To be able to interact with the HTTP client pseudo-Node, this node
/// expects to receive an [`oak::http::HttpInvocationSource`] in the invocation it receives for each
/// command.
pub struct RedirectHelper;

impl oak::WithInit for RedirectHelper {
    type Init = LogInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self {}
    }
}

impl CommandHandler for RedirectHelper {
    type Command = RedirectInvocation;

    fn handle_command(&mut self, invocation: RedirectInvocation) -> anyhow::Result<()> {
        let request = invocation.request_receiver.as_ref().unwrap().receive()?;
        invocation.request_receiver.unwrap().close()?;
        let client_invocation = invocation.http_invocation_source.unwrap();
        let uri = request.uri.parse::<http::Uri>()?;

        info!("Handling a request to {}", uri);

        // Create redirection request. Nothing from the original request is relevant here
        let label = Label::public_untrusted();
        let label_bytes = serde_json::to_string(&label)
            .context("Could not serialize public/untrusted label to JSON")?
            .into_bytes();
        let request = http::Request::builder()
            .method(http::Method::GET)
            .uri("https://localhost:8080")
            .header(oak_abi::OAK_LABEL_HTTP_JSON_KEY, label_bytes)
            .body(vec![])
            .context("Couldn't build request")?;

        // Send the request to the HTTP client pseudo-Node
        client_invocation
            .send(request)
            .context("Couldn't send the request to the HTTP client")?;

        // Collect the response from the HTTP client pseudo-Node
        let response = client_invocation
            .receive()
            .context("Couldn't receive the response from the HTTP client")?;

        info!("Got a response with status: {}", response.status());
        Ok(())
    }
}
