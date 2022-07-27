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

use anyhow::{anyhow, Context};
use echo::{echo_client::EchoClient, EchoRequest};
use http::{Request, Response};
use hyper::{Body, Client, Method};

// TODO(mschett): similar functionality to send_http_request, refactor.
// differences:
// * client is http2_only
// * the request is given, not built
// * returns the whole response, not only the body.
pub async fn send_with_request(request: Request<Body>) -> anyhow::Result<Response<Body>> {
    let client = Client::builder().http2_only(true).build_http();

    let response = client
        .request(request)
        .await
        .context("Couldn't send request")?;
    if response.status() != http::StatusCode::OK {
        return Err(anyhow!("Non-OK status: {:?}", response.status()));
    }

    Ok(response)
}

pub async fn send_http_request(uri: &str, method: Method, body: &[u8]) -> anyhow::Result<Vec<u8>> {
    let client = Client::builder().http2_only(true).build_http();

    let request = hyper::Request::builder()
        .method(method)
        .uri(uri)
        .body(Body::from(body.to_vec()))
        .context("Couldn't create request")?;

    let response = client
        .request(request)
        .await
        .context("Couldn't send request")?;
    if response.status() != http::StatusCode::OK {
        return Err(anyhow!("Non-OK status: {:?}", response.status()));
    }

    let response_body = hyper::body::to_bytes(response.into_body())
        .await
        .context("Couldn't read response body")?
        .to_vec();
    Ok(response_body)
}

pub mod echo {
    tonic::include_proto!("experimental.trusted_shuffler.echo");
}

pub async fn send_grpc_request(uri: String, body: &[u8]) -> anyhow::Result<Vec<u8>> {
    let mut client = EchoClient::connect(uri).await?;
    let request = tonic::Request::new(EchoRequest {
        value_to_echo: body.to_vec(),
    });
    let response = client.echo(request).await?.into_inner();
    Ok(response.echoed_value)
}
