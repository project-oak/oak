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

use crate::proto::oak::encap::GrpcRequest;
use anyhow::Context;
use bytes::{Buf, BufMut};
use futures::task::Poll;
use pin_project_lite::pin_project;
use prost::Message;
use std::{future::Future, io::copy, pin::Pin};
use sync_wrapper::SyncWrapper;
use tokio::net::UnixStream;
use tonic::{
    client::Grpc,
    codec::{Codec, DecodeBuf, Decoder, EncodeBuf, Encoder},
    transport::{Channel, Endpoint, Uri},
    Request,
};
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
    pub fn create_client(&self) -> Grpc<Channel> {
        Grpc::new(self.channel.clone())
    }
}

pub async fn handle_request(
    mut client: Grpc<Channel>,
    cleartext_request: Vec<u8>,
) -> anyhow::Result<Vec<u8>> {
    let encapsulated_request =
        GrpcRequest::decode(&*cleartext_request).context("couldn't decode encapsulated request")?;
    let bytes = Request::new(encapsulated_request.req_msg.clone());
    let codec = BytesCodec::default();
    let path = encapsulated_request
        .method_name
        .parse()
        .context("couldn't parse method name")?;
    client.ready().await.context("connection not ready")?;
    // Forward the bytes from the encapsulated request to the backend. We wrap the resulting future
    // to make it `Sync`, as required by the trait bounds for the request handler.
    let sync_unary = FutureSyncWrapper {
        inner: SyncWrapper::new(client.unary(bytes, path, codec)),
    };
    let response = sync_unary
        .await
        .context("couldn't execute prediction")?
        .into_inner();

    let wrapped_response =
        oak_functions_abi::Response::create(oak_functions_abi::StatusCode::Success, response);
    Ok(wrapped_response.encode_to_vec())
}

// TODO(#2476): Remove when upgrading Tonic from v0.5 to v0.6.
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

/// A Codec for encoding and decoding byte vectors to and from Tonic buffers.
///
/// This allows us to pass through the client encoding of the request to the backend and the backend
/// response to the client without requiring knowlege of the specific protos involved.
#[derive(Default)]
struct BytesCodec;

impl Codec for BytesCodec {
    type Encode = Vec<u8>;
    type Decode = Vec<u8>;

    type Encoder = BytesEncoder;
    type Decoder = BytesDecoder;

    fn encoder(&mut self) -> Self::Encoder {
        BytesEncoder {}
    }

    fn decoder(&mut self) -> Self::Decoder {
        BytesDecoder {}
    }
}

/// Passthrough encoder for encoding a byte vector to an [`tonic::codec::EncodeBuf`].
pub struct BytesEncoder;

impl Encoder for BytesEncoder {
    type Item = Vec<u8>;
    type Error = tonic::Status;

    fn encode(&mut self, item: Self::Item, dst: &mut EncodeBuf<'_>) -> Result<(), Self::Error> {
        copy(&mut item.reader(), &mut dst.writer()).map_err(|error| {
            tonic::Status::internal(format!("Couln't encode bytes: {:?}", error))
        })?;
        Ok(())
    }
}

/// Passthrough decoder for decoding a [`tonic::codec::DecodeBuf`] to a byte vector.
pub struct BytesDecoder;

impl Decoder for BytesDecoder {
    type Item = Vec<u8>;
    type Error = tonic::Status;

    fn decode(&mut self, src: &mut DecodeBuf<'_>) -> Result<Option<Self::Item>, Self::Error> {
        let mut item = vec![];
        copy(&mut src.reader(), &mut item).map_err(|error| {
            tonic::Status::internal(format!("Couln't decode bytes: {:?}", error))
        })?;
        Ok(Some(item))
    }
}
