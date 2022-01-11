//
// Copyright 2021 The Project Oak Authors
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

pub mod proto {
    // Suppress warning: `large size difference between variants`.
    #![allow(clippy::large_enum_variant)]
    #![allow(clippy::return_self_not_must_use)]
    tonic::include_proto!("tensorflow");
    pub mod serving {
        tonic::include_proto!("tensorflow.serving");
    }
}

use anyhow::Context;
use futures::task::Poll;
use pin_project_lite::pin_project;
use prost::Message;
pub use proto::serving::{prediction_service_client::PredictionServiceClient, PredictRequest};
use std::{future::Future, pin::Pin};
use sync_wrapper::SyncWrapper;
use tokio::net::UnixStream;
use tonic::transport::{Channel, Endpoint, Uri};
use tower::service_fn;

/// Connection to the prediction service that can be used for creating new clients.
pub struct BackendConnection {
    channel: Channel,
}

impl BackendConnection {
    /// Connects to the prediction service over UDS and returns the wrapped channel.
    pub async fn connect(socket: &'static str) -> Self {
        // Ignore this uri because UDS do not use it, but Endpoint requires a valid uri.
        let channel = Endpoint::try_from("http://[::]:50051")
            .expect("invalid uri")
            .connect_with_connector(service_fn(move |_: Uri| {
                // Connect to a Unix Domain Socket
                UnixStream::connect(socket)
            }))
            .await
            .expect("couldn't connect to backend socket");
        Self { channel }
    }

    /// Creates a new client.
    pub fn create_client(&self) -> PredictionServiceClient<Channel> {
        PredictionServiceClient::new(self.channel.clone())
    }
}

pub async fn handle_request(
    mut client: PredictionServiceClient<Channel>,
    cleartext_request: Vec<u8>,
) -> anyhow::Result<Vec<u8>> {
    let predict_request =
        PredictRequest::decode(&*cleartext_request).context("couldn't parse decrypted request")?;
    // Wrap the gRPC client call to make it `Sync`.
    let sync_predict = FutureSyncWrapper {
        inner: SyncWrapper::new(client.predict(predict_request)),
    };
    let response = sync_predict
        .await
        .context("couldn't execute prediction")?
        .into_inner();

    let wrapped_response = oak_functions_abi::proto::Response::create(
        oak_functions_abi::proto::StatusCode::Success,
        response.encode_to_vec(),
    );
    Ok(wrapped_response.encode_to_vec())
}

pin_project! {
    /// Utility wrapper to implement `Sync` for `Future`s by wrapping the inner Future in a
    /// `SyncWrapper`.
    struct FutureSyncWrapper<F> {
        #[pin]
        inner: SyncWrapper<F>,
    }
}

impl<F: Future> Future for FutureSyncWrapper<F> {
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context) -> Poll<Self::Output> {
        self.project().inner.get_pin_mut().poll(cx)
    }
}
