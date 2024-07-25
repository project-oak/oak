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
//

use anyhow::Context;
use base64::{prelude::BASE64_STANDARD, Engine as _};
use oak_client::{
    client::OakClient,
    transport::{EvidenceProvider, Transport},
    verifier::InsecureAttestationVerifier,
};
use oak_proto_rust::oak::{
    crypto::v1::{EncryptedRequest, EncryptedResponse},
    session::v1::{
        request_wrapper, response_wrapper, EndorsedEvidence, GetEndorsedEvidenceRequest,
        GetEndorsedEvidenceResponse, InvokeRequest, InvokeResponse, RequestWrapper,
        ResponseWrapper,
    },
};
use prost::Message;
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, RequestMode, Response};

/// This transport implements interfacing with a simple demo API:
/// GET localhost:port/<base64encodedserializedRequestWrapper>
///
/// The request is sent as a GET request, and the response body contains the
/// response. This simplified transport is adopted for the purposes of a web
/// client demo only.
pub struct DemoRestBasedTransport {
    port: u16,
}

impl DemoRestBasedTransport {
    pub fn new(port: u16) -> Self {
        Self { port }
    }

    async fn send_and_receive(
        &self,
        request: request_wrapper::Request,
    ) -> anyhow::Result<ResponseWrapper> {
        let request_wrapper = RequestWrapper { request: Some(request) };
        let serialized = request_wrapper.encode_to_vec();
        let encoded = BASE64_STANDARD.encode(&serialized);

        let url = format!("http://localhost:{}/{}", self.port, encoded);

        let mut opts = RequestInit::new();
        opts.method("GET");
        opts.mode(RequestMode::Cors);

        let request = Request::new_with_str_and_init(&url, &opts)
            .map_err(|e| anyhow::anyhow!("Error creating request: {:?}", e))?;

        let window = web_sys::window().unwrap();
        let resp_value = JsFuture::from(window.fetch_with_request(&request))
            .await
            .map_err(|e| anyhow::anyhow!("Error fetching: {:?}", e))?;

        let resp: Response = resp_value.dyn_into().unwrap();

        let body = JsFuture::from(resp.array_buffer().unwrap())
            .await
            .map_err(|e| anyhow::anyhow!("Error getting response body: {:?}", e))?;

        let uint8_array = js_sys::Uint8Array::new(&body);
        let bytes = uint8_array.to_vec();

        ResponseWrapper::decode(&bytes[..]).context("Failed to decode response")
    }
}

#[async_trait::async_trait(?Send)]
impl Transport for DemoRestBasedTransport {
    async fn invoke(
        &mut self,
        encrypted_request: &EncryptedRequest,
    ) -> anyhow::Result<EncryptedResponse> {
        let response_wrapper = self
            .send_and_receive(request_wrapper::Request::InvokeRequest(InvokeRequest {
                encrypted_request: Some(encrypted_request.clone()),
            }))
            .await
            .context("Sending invoke request")?;

        match response_wrapper.response {
            Some(response_wrapper::Response::InvokeResponse(InvokeResponse {
                encrypted_response: Some(encrypted_response),
            })) => Ok(encrypted_response),
            _ => Err(anyhow::anyhow!(
                "response_wrapper does not have a valid invoke_response message"
            )),
        }
    }
}

#[async_trait::async_trait(?Send)]
impl EvidenceProvider for DemoRestBasedTransport {
    async fn get_endorsed_evidence(&mut self) -> anyhow::Result<EndorsedEvidence> {
        let response_wrapper = self
            .send_and_receive(request_wrapper::Request::GetEndorsedEvidenceRequest(
                GetEndorsedEvidenceRequest {},
            ))
            .await
            .context("Sending get_endorsed_evidence request")?;

        match response_wrapper.response {
            Some(response_wrapper::Response::GetEndorsedEvidenceResponse(
                GetEndorsedEvidenceResponse { endorsed_evidence: Some(endorsed_evidence) },
            )) => Ok(endorsed_evidence),
            _ => Err(anyhow::anyhow!(
                "response_wrapper does not have a valid invoke_response message"
            )),
        }
    }
}

pub struct GreeterClient {
    oak_client: OakClient<DemoRestBasedTransport>,
}

impl GreeterClient {
    pub async fn new(port: u16) -> anyhow::Result<Self> {
        let transport = DemoRestBasedTransport::new(port);
        let verifier = InsecureAttestationVerifier;
        let oak_client = OakClient::create(transport, &verifier).await?;
        Ok(Self { oak_client })
    }

    pub async fn greet(&mut self, name: &str) -> anyhow::Result<String> {
        let request = name.as_bytes().to_vec();
        let response = self.oak_client.invoke(&request).await?;
        String::from_utf8(response).context("Failed to decode response as UTF-8")
    }
}

#[wasm_bindgen]
pub async fn greet(port: u16, name: String) -> Result<String, JsValue> {
    let mut client = GreeterClient::new(port)
        .await
        .map_err(|e| JsValue::from_str(&format!("Failed to create client: {:?}", e)))?;

    client.greet(&name).await.map_err(|e| JsValue::from_str(&format!("Failed to greet: {:?}", e)))
}
