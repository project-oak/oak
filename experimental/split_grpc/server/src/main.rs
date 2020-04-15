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

use futures_core::Stream;
use std::pin::Pin;
use tonic::{
    transport::{Identity, Server, ServerTlsConfig},
    Request, Response, Status, Streaming,
};

use proto::{
    hello_world_server::{HelloWorld, HelloWorldServer},
    HelloRequest, HelloResponse,
};

pub mod proto {
    tonic::include_proto!("oak.examples.hello_world");
}

#[derive(Debug, Default)]
pub struct HelloWorldHandler;

#[tonic::async_trait]
impl HelloWorld for HelloWorldHandler {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloResponse>, Status> {
        let reply = HelloResponse {
            reply: format!("Hello {}!", request.into_inner().greeting),
        };

        Ok(Response::new(reply))
    }

    // Server streaming response type for the LotsOfReplies method.
    type LotsOfRepliesStream =
        Pin<Box<dyn Stream<Item = Result<HelloResponse, Status>> + Send + Sync + 'static>>;

    async fn lots_of_replies(
        &self,
        _request: Request<HelloRequest>,
    ) -> Result<Response<Self::LotsOfRepliesStream>, Status> {
        unimplemented!()
    }

    async fn lots_of_greetings(
        &self,
        _request: Request<Streaming<HelloRequest>>,
    ) -> Result<Response<HelloResponse>, Status> {
        unimplemented!()
    }

    // Server streaming response type for the BidiHello method.
    type BidiHelloStream =
        Pin<Box<dyn Stream<Item = Result<HelloResponse, Status>> + Send + Sync + 'static>>;
    async fn bidi_hello(
        &self,
        _request: Request<Streaming<HelloRequest>>,
    ) -> Result<Response<Self::BidiHelloStream>, Status> {
        unimplemented!()
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cert = tokio::fs::read("examples/certs/local/local.pem").await?;
    let key = tokio::fs::read("examples/certs/local/local.key").await?;
    let identity = Identity::from_pem(cert, key);
    let address = "[::1]:50052".parse()?;
    let handler = HelloWorldHandler::default();

    Server::builder()
        .tls_config(ServerTlsConfig::new().identity(identity))
        .add_service(HelloWorldServer::new(handler))
        .serve(address)
        .await?;

    Ok(())
}
