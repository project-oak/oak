//
// Copyright 2022 The Project Oak Authors
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

#![feature(async_closure)]

extern crate web_sys;

use crate::proto::{UnaryRequest, UnaryResponse};
use anyhow::Context;
use async_trait::async_trait;
use oak_functions_abi::Response;
use oak_remote_attestation::handshaker::{AttestationBehavior, EmptyAttestationGenerator};
use oak_remote_attestation_amd::PlaceholderAmdAttestationVerifier;
use oak_remote_attestation_sessions::SessionId;
use oak_remote_attestation_sessions_client::{GenericAttestationClient, UnaryClient};
use std::rc::Rc;
use wasm_bindgen::prelude::*;

mod grpc_web;

#[cfg(test)]
mod tests;

mod proto {
    #![allow(clippy::return_self_not_must_use)]
    include!(concat!(env!("OUT_DIR"), "/oak.session.unary.v1.rs"));
}

/// gRPC-web implementation of a [`UnaryClient`].
struct GrpcWebClient {
    uri: String,
}

impl GrpcWebClient {
    pub fn create(uri: &str) -> Self {
        Self {
            uri: format!("{}/oak.session.unary.v1.UnarySession/Message", uri),
        }
    }
}

// Not marked as [`Send`], as the underlying client uses JavaScript APIs for
// networking, which are not [`Send`].
#[async_trait(?Send)]
impl UnaryClient for GrpcWebClient {
    async fn message(&mut self, session_id: SessionId, body: Vec<u8>) -> anyhow::Result<Vec<u8>> {
        let reply = grpc_web::grpc_web_unary::<UnaryRequest, UnaryResponse>(
            &self.uri,
            UnaryRequest {
                session_id: session_id.to_vec(),
                body,
            },
        )
        .await?;
        Ok(reply.body)
    }
}

// The underlying [`GenericAttestationClient`] is held in a [`wasm_mutex::Mutex`],
// which provides a queue of invocations. Ref: https://lib.rs/crates/wasm_mutex
// TODO(#2908): Support concurrent invocations.
type WebClientInner = Rc<wasm_mutex::Mutex<GenericAttestationClient<GrpcWebClient>>>;

#[wasm_bindgen]
pub struct WebClient {
    inner: WebClientInner,
}

#[wasm_bindgen]
impl WebClient {
    #[wasm_bindgen(constructor)]
    pub async fn new(uri: String) -> Result<WebClient, String> {
        let grpc_web_client = GrpcWebClient::create(&uri);
        let inner = GenericAttestationClient::create(
            grpc_web_client,
            AttestationBehavior::create(
                EmptyAttestationGenerator,
                PlaceholderAmdAttestationVerifier,
            ),
        )
        .await
        .context("Could not create Oak Functions client")
        .map_err(|error| error.to_string())?;
        let inner = Rc::new(wasm_mutex::Mutex::new(inner));
        Ok(WebClient { inner })
    }

    // Typically this would be an async function. Instead it's a sync function
    // that returns a JS Promise (the JS equivalent of a Rust future).
    // The reason for this is that we cannot access the stack allocated self
    // inside a Rust future.
    // Ref: https://github.com/rustwasm/wasm-bindgen/issues/1858
    pub fn invoke(&self, request: Vec<u8>) -> js_sys::Promise {
        let inner = self.inner.clone();

        wasm_bindgen_futures::future_to_promise(async move {
            let response = WebClient::inner_invoke(inner, request)
                .await
                .map_err(|error| error.to_string())?;

            // Get the response body, while removing trailing empty space.
            let length = response
                .length
                .try_into()
                .map_err(|_| "Could not fit the response length into usize")?;
            let body = &response.body[0..length];

            // Construct a JavaScript object that contains the response status
            // and body.
            let js_response_object = js_sys::Object::new();
            js_sys::Reflect::set(
                &js_response_object,
                &"status".into(),
                &(response.status as u32).into(),
            )?;
            js_sys::Reflect::set(
                &js_response_object,
                &"body".into(),
                &js_sys::Uint8Array::from(body),
            )?;

            Ok(JsValue::from(js_response_object))
        })
    }
    async fn inner_invoke(inner: WebClientInner, request: Vec<u8>) -> anyhow::Result<Response> {
        let encoded_response = inner
            .lock()
            .await
            .message(&request)
            .await
            .context("Error invoking Oak Functions instance")?;

        Response::decode(encoded_response.as_ref())
            .map_err(anyhow::Error::msg)
            .context("Couldn't decode response")
    }
}

// Executed automtically
#[cfg(not(test))]
#[wasm_bindgen(start)]
pub fn main() {
    // Register panic handler to output more detailed error messages to the console
    // Ref: https://github.com/rustwasm/console_error_panic_hook#readme
    console_error_panic_hook::set_once();
}
