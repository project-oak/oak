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

use bmrng::unbounded::UnboundedRequestSender;
use futures::Future;
use std::net::SocketAddr;
use tonic::{transport::Server, Request, Response, Status};

pub mod proto {
    tonic::include_proto!("oak.experimental.uefi");
}

use proto::{
    echo_server::{Echo, EchoServer},
    EchoRequest, EchoResponse,
};

pub struct EchoImpl {
    channel: UnboundedRequestSender<String, anyhow::Result<String>>,
}

#[tonic::async_trait]
impl Echo for EchoImpl {
    async fn echo(&self, request: Request<EchoRequest>) -> Result<Response<EchoResponse>, Status> {
        let request = request.into_inner();

        // There's two nested errors: one for communicating over the channel, and one for
        // communicating over the serial port with the UEFI app.
        // We probably want to log the error in the future and serve something more
        // ambiguous to the end user, but for now that'll do.
        let message = self
            .channel
            .send_receive(request.message)
            .await
            .map_err(|err| Status::internal(format!("{:?}", err)))?
            .map_err(|err| Status::internal(format!("{:?}", err)))?;

        Ok(Response::new(EchoResponse { message }))
    }
}

pub fn server(
    addr: SocketAddr,
    channel: UnboundedRequestSender<String, anyhow::Result<String>>,
) -> impl Future<Output = Result<(), tonic::transport::Error>> {
    let server_impl = EchoImpl { channel };
    Server::builder()
        .add_service(EchoServer::new(server_impl))
        .serve(addr)
}
