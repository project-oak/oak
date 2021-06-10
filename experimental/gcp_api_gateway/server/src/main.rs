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
use futures_util::StreamExt;
use std::pin::Pin;
use tokio::sync::mpsc;
use tokio_stream::wrappers::ReceiverStream;
use tonic::{transport::Server, Request, Response, Status, Streaming};

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
        request: Request<HelloRequest>,
    ) -> Result<Response<Self::LotsOfRepliesStream>, Status> {
        let (sender, receiver) = mpsc::channel(4);
        let greeting = request.into_inner().greeting;

        tokio::spawn(async move {
            sender
                .send(Ok(HelloResponse {
                    reply: format!("Hi {}!", greeting),
                }))
                .await
                .unwrap();
            sender
                .send(Ok(HelloResponse {
                    reply: format!("Hey {}!", greeting),
                }))
                .await
                .unwrap();
        });

        Ok(Response::new(Box::pin(ReceiverStream::new(receiver))))
    }

    async fn lots_of_greetings(
        &self,
        request: Request<Streaming<HelloRequest>>,
    ) -> Result<Response<HelloResponse>, Status> {
        let mut stream = request.into_inner();

        let mut reply = String::new();
        reply.push_str("Hello ");

        let mut first = true;
        while let Some(greeting) = stream.next().await {
            if !first {
                reply.push_str(", ");
            }
            reply.push_str(&greeting?.greeting);
            first = false;
        }

        reply.push('!');

        Ok(Response::new(HelloResponse { reply }))
    }

    // Server streaming response type for the BidiHello method.
    type BidiHelloStream =
        Pin<Box<dyn Stream<Item = Result<HelloResponse, Status>> + Send + Sync + 'static>>;

    async fn bidi_hello(
        &self,
        request: Request<Streaming<HelloRequest>>,
    ) -> Result<Response<Self::BidiHelloStream>, Status> {
        let mut stream = request.into_inner();

        let output = async_stream::try_stream! {
            while let Some(greeting) = stream.next().await {
                let greeting = greeting?;
                let response = HelloResponse {
                    reply: format!("Hello {}!", greeting.greeting),
                };
                yield response;
            }
        };

        Ok(Response::new(Box::pin(output) as Self::BidiHelloStream))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let address = "[::]:8080".parse()?;
    let handler = HelloWorldHandler::default();
    Server::builder()
        .add_service(HelloWorldServer::new(handler))
        .serve(address)
        .await?;

    Ok(())
}
