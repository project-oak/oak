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

use anyhow::bail;
use bmrng::unbounded::UnboundedRequestSender;
use futures::Future;
use oak_remote_attestation_sessions::{SessionId, SessionRequest, SESSION_ID_LENGTH};
use std::net::SocketAddr;
use tonic::{transport::Server, Request, Response, Status};

pub mod proto {
    tonic::include_proto!("oak.session.unary.v1");
}

use proto::{
    unary_session_server::{UnarySession, UnarySessionServer},
    UnaryRequest, UnaryResponse,
};

// Since the SerializeableRequest struct essentially mirrors the UnaryRequest
// proto message conversion between them is simple. We do not use
// proto serialization directly to avoid creating a dependecy on protobuf in
// the trusted runtime.
impl TryFrom<UnaryRequest> for SessionRequest {
    type Error = anyhow::Error;

    fn try_from(unary_request: UnaryRequest) -> Result<Self, Self::Error> {
        let mut session_id: SessionId = [0; SESSION_ID_LENGTH];

        if unary_request.session_id.len() != SESSION_ID_LENGTH {
            bail!(
                "session_id must be {} bytes in length, found a length of {} bytes instead",
                SESSION_ID_LENGTH,
                unary_request.session_id.len()
            );
        }

        session_id.copy_from_slice(&unary_request.session_id);

        Ok(Self {
            session_id,
            body: unary_request.body,
        })
    }
}

pub struct EchoImpl {
    channel: UnboundedRequestSender<SessionRequest, Result<Vec<u8>, oak_idl::Error>>,
}

#[tonic::async_trait]
impl UnarySession for EchoImpl {
    async fn message(
        &self,
        request: Request<UnaryRequest>,
    ) -> Result<Response<UnaryResponse>, Status> {
        let request = request.into_inner();
        let session_request = SessionRequest::try_from(request)
            .map_err(|err| Status::invalid_argument(format!("{:?}", err)))?;

        // There's two nested errors: one for communicating over the channel, and one for
        // communicating over the serial port with the UEFI app.
        // We probably want to log the error in the future and serve something more
        // ambiguous to the end user, but for now that'll do.
        let body = self
            .channel
            .send_receive(session_request)
            .await
            .map_err(|err| Status::internal(format!("{:?}", err)))?
            .map_err(|err| Status::internal(format!("{:?}", err)))?;

        Ok(Response::new(UnaryResponse { body }))
    }
}

pub fn server(
    addr: SocketAddr,
    channel: UnboundedRequestSender<SessionRequest, Result<Vec<u8>, oak_idl::Error>>,
) -> impl Future<Output = Result<(), tonic::transport::Error>> {
    let server_impl = EchoImpl { channel };
    Server::builder()
        .add_service(UnarySessionServer::new(server_impl))
        .serve(addr)
}
