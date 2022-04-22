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
    tonic::include_proto!("oak.session.unary.v1");
}

use proto::{
    unary_session_server::{UnarySession, UnarySessionServer},
    UnaryRequest, UnaryResponse,
};

pub struct EchoImpl {
    channel: UnboundedRequestSender<Vec<u8>, anyhow::Result<Vec<u8>>>,
}

#[tonic::async_trait]
impl UnarySession for EchoImpl {
    async fn message(
        &self,
        request: Request<UnaryRequest>,
    ) -> Result<Response<UnaryResponse>, Status> {
        let request = request.into_inner();

        // There's two nested errors: one for communicating over the channel, and one for
        // communicating over the serial port with the UEFI app.
        // We probably want to log the error in the future and serve something more
        // ambiguous to the end user, but for now that'll do.
        let body = self
            .channel
            .send_receive(request.body)
            .await
            .map_err(|err| Status::internal(format!("{:?}", err)))?
            .map_err(|err| Status::internal(format!("{:?}", err)))?;

        Ok(Response::new(UnaryResponse { body }))
    }
}

pub fn server(
    addr: SocketAddr,
    channel: UnboundedRequestSender<Vec<u8>, anyhow::Result<Vec<u8>>>,
) -> impl Future<Output = Result<(), tonic::transport::Error>> {
    let server_impl = EchoImpl { channel };
    Server::builder()
        .add_service(UnarySessionServer::new(server_impl))
        .serve(addr)
}
