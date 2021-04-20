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

mod proto {
    tonic::include_proto!("oak.functions.server");
}

use crate::proto::grpc_handler_client::GrpcHandlerClient;
use anyhow::Context;
use http::uri::Uri;
use oak_functions_abi::proto::{Request, Response};
use tonic::transport::Channel;

pub struct Client {
    inner: GrpcHandlerClient<Channel>,
}

impl Client {
    pub async fn new(uri: &Uri) -> anyhow::Result<Self> {
        let channel = Channel::builder(uri.clone()).connect().await?;
        let inner = GrpcHandlerClient::new(channel);
        Ok(Client { inner })
    }
    pub async fn invoke(&mut self, request_body: &[u8]) -> anyhow::Result<Response> {
        let request = tonic::Request::new(Request {
            body: request_body.to_vec(),
        });
        let response = self
            .inner
            .invoke(request)
            .await
            .context("Error invoking Oak Functions instance")?;
        Ok(response.into_inner())
    }
}
