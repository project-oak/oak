//
// Copyright 2024 The Project Oak Authors
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

use bytes::Bytes;
use http_body_util::{BodyExt, Full};
use hyper::{Method, Request, Uri};
use hyper_util::rt::TokioIo;
use oak_proto_rust::oak::{
    crypto::v1::{EncryptedRequest, EncryptedResponse},
    session::v1::{
        request_wrapper, response_wrapper, EndorsedEvidence, GetEndorsedEvidenceRequest,
        GetEndorsedEvidenceResponse, InvokeRequest, InvokeResponse, RequestWrapper,
        ResponseWrapper,
    },
};
use prost::Message;
use tokio::net::TcpStream;

/// A very rough http-based transport for demo purposes.
/// It can send either GET or POST requests, depending
/// on the [MakeRequest] type you parameterize it with.
#[derive(Debug, Clone)]
pub struct DemoTransport {
    addr: String,
}

impl DemoTransport {
    /// Create a new [DemoHttpTransport] for the provided `addr`.
    /// Requests will be formed by adding a query string to the end of the
    /// provided address.
    pub fn new(addr: String) -> Self {
        Self { addr }
    }

    pub fn addr(&self) -> &str {
        &self.addr
    }

    async fn make_request(
        &self,
        request_wrapper: &RequestWrapper,
    ) -> anyhow::Result<ResponseWrapper> {
        let serialized = request_wrapper.encode_to_vec();
        let result = self.hyper_post_request(&serialized).await?;
        Ok(ResponseWrapper::decode(&result[..])?)
    }

    // Helper method for making client requests with hyper, which is not trivial.
    // Using a library like reqwest would simplify this, but it introduces way too
    // many dependencies to be worth it.
    // See: https://hyper.rs/guides/1/client/basic/
    async fn hyper_post_request(&self, body: &[u8]) -> anyhow::Result<Vec<u8>> {
        let url = self.addr.parse::<Uri>()?;
        let host = url.host().expect("uri has no host");
        let port = url.port_u16().unwrap_or(80);
        let addr = format!("{}:{}", host, port);
        let stream = TcpStream::connect(addr).await?;
        let io = TokioIo::new(stream);

        let (mut sender, conn) = hyper::client::conn::http1::handshake(io).await?;
        tokio::task::spawn(async move {
            if let Err(err) = conn.await {
                println!("Connection failed: {:?}", err);
            }
        });

        let authority = url.authority().unwrap().clone();

        let req = Request::builder()
            .uri(url.path())
            .method(Method::POST)
            .header(hyper::header::HOST, authority.as_str())
            .body(Full::<Bytes>::from(Bytes::from(body.to_vec())))?;

        Ok(sender.send_request(req).await?.into_body().collect().await?.to_bytes().to_vec())
    }
}

#[async_trait::async_trait(?Send)]
impl oak_client::transport::Transport for DemoTransport {
    async fn invoke(
        &mut self,
        encrypted_request: &EncryptedRequest,
    ) -> anyhow::Result<EncryptedResponse> {
        let wrapper = RequestWrapper {
            request: Some(request_wrapper::Request::InvokeRequest(InvokeRequest {
                encrypted_request: Some(encrypted_request.clone()),
            })),
        };

        let response_wrapper = self.make_request(&wrapper).await?;

        match response_wrapper.response {
            Some(response_wrapper::Response::InvokeResponse(InvokeResponse {
                encrypted_response: Some(encrypted_response),
            })) => Ok(encrypted_response),
            _ => anyhow::bail!("response_wrapper contained wrong message type"),
        }
    }
}

#[async_trait::async_trait(?Send)]
impl oak_client::transport::EvidenceProvider for DemoTransport {
    async fn get_endorsed_evidence(&mut self) -> anyhow::Result<EndorsedEvidence> {
        let wrapper = RequestWrapper {
            request: Some(request_wrapper::Request::GetEndorsedEvidenceRequest(
                GetEndorsedEvidenceRequest {},
            )),
        };

        let response_wrapper = self.make_request(&wrapper).await?;

        match response_wrapper.response {
            Some(response_wrapper::Response::GetEndorsedEvidenceResponse(
                GetEndorsedEvidenceResponse { endorsed_evidence: Some(endorsed_evidence) },
            )) => Ok(endorsed_evidence),
            _ => anyhow::bail!("response_wrapper contained wrong message type"),
        }
    }
}
