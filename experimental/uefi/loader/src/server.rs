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

use std::{net::SocketAddr, sync::Arc};

use futures::{stream::StreamExt, Future, SinkExt};
use log::error;
use tokio::{net::UnixStream, sync::Mutex};
use tokio_serde_cbor::Codec;
use tokio_util::codec::Framed;
use tonic::{transport::Server, Request, Response, Status};

use pb::{
    echo_server::{Echo, EchoServer},
    EchoRequest, EchoResponse,
};

pub mod pb {
    tonic::include_proto!("oak.experimental.uefi");
}

pub struct EchoImpl {
    channel: Arc<Mutex<Framed<UnixStream, Codec<String, String>>>>,
}

#[tonic::async_trait]
impl Echo for EchoImpl {
    async fn echo(&self, request: Request<EchoRequest>) -> Result<Response<EchoResponse>, Status> {
        let request = request.into_inner();

        let mut channel = self.channel.lock().await;

        if let Err(err) = channel.send(request.message).await {
            error!("Error sending message over channel: {:?}", err);
            Err(Status::internal(""))
        } else {
            Ok(())
        }?;
        // Sometimes next() gives us a None. Figure out what's going on in there.
        let mut response;
        loop {
            response = channel.next().await;
            if response.is_some() {
                break;
            }
        }
        let response = response.unwrap().map_err(|err| {
            error!("Error reading from channel: {:?}", err);
            Status::internal("")
        })?;

        Ok(Response::new(EchoResponse { message: response }))
    }
}

pub fn server(
    addr: SocketAddr,
    channel: Framed<UnixStream, Codec<String, String>>,
) -> impl Future<Output = Result<(), tonic::transport::Error>> {
    let server_impl = EchoImpl {
        channel: Arc::new(Mutex::new(channel)),
    };
    Server::builder()
        .add_service(EchoServer::new(server_impl))
        .serve(addr)
}
