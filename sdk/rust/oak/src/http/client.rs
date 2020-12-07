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

use crate::{
    http::{util::Pipe, Invocation},
    OakError,
};
use http::{Request, Response};
use oak_abi::label::{confidentiality_label, tls_endpoint_tag, Label};
use oak_io::Sender;
use oak_services::proto::oak::encap::HttpRequest;
use std::convert::TryInto;

/// Initializes an HTTP client pseudo-Node serving requests that have the given authority in their
/// URIs. If the authority is empty, the node is public and can handle any incoming request.
/// Otherwise, the node is created with the `authority` as its confidentially tag. In this case, the
/// client can only serve HTTPS requests to the services indicated by the `authority`.
///
/// Returns an [`HttpClient`].
pub fn init(authority: &str) -> Result<HttpClient, OakError> {
    let config = crate::node_config::http_client(authority);
    let label = if authority.is_empty() {
        Label::public_untrusted()
    } else {
        confidentiality_label(tls_endpoint_tag(authority))
    };
    let sender = crate::io::node_create::<Invocation>("http_client", &label, &config)?;
    Ok(HttpClient {
        sender,
        authority: authority.to_string(),
    })
}

pub fn from_sender(sender: Sender<Invocation>, authority: String) -> HttpClient {
    HttpClient { sender, authority }
}

pub struct HttpClient {
    sender: Sender<Invocation>,
    authority: String,
}

impl HttpClient {
    /// Sends the given request via the HTTP client pseudo-node. The `response_label` should match
    /// the label of the Oak Node.
    pub fn send_request(
        &self,
        request: Request<Vec<u8>>,
        response_label: &Label,
    ) -> Result<Response<Vec<u8>>, OakError> {
        // Use the authority of the client node as the label of the request channel.
        let request_label = if self.authority.is_empty() {
            Label::public_untrusted()
        } else {
            confidentiality_label(tls_endpoint_tag(&self.authority))
        };
        // create a pipe with a request and a response channel
        let pipe = Pipe::new(&request_label, response_label)?;

        // insert the request into the request channel
        pipe.insert_message(HttpRequest::from(request))?;

        // wrap the request and response channels in an invocation, and send it to the HTTP client
        // pseudo-node
        pipe.send_invocation(&self.sender)?;

        // wait for the response to be received
        let rsp = pipe.get_response()?;

        // close all the channels in the pipe
        pipe.close();

        rsp.try_into().map_err(OakError::OakStatus)
    }
}
