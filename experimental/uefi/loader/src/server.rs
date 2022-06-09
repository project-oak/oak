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
use channel::schema;
use futures::Future;
use oak_remote_attestation_sessions::{SessionId, SESSION_ID_LENGTH};
use std::net::SocketAddr;
use tonic::{transport::Server, Request, Response, Status};

pub mod proto {
    tonic::include_proto!("oak.session.unary.v1");
}

use proto::{
    unary_session_server::{UnarySession, UnarySessionServer},
    UnaryRequest, UnaryResponse,
};

fn encode_request(unary_request: UnaryRequest) -> Result<Vec<u8>, oak_idl::Error> {
    let mut session_id: SessionId = [0; SESSION_ID_LENGTH];
    if unary_request.session_id.len() != SESSION_ID_LENGTH {
        return Err(oak_idl::Error::new_with_message(
            oak_idl::ErrorCode::InvalidRequest,
            format!(
                "session_id must be {} bytes in length, found a length of {} bytes instead",
                SESSION_ID_LENGTH,
                unary_request.session_id.len()
            ),
        ));
    }
    session_id.copy_from_slice(&unary_request.session_id);

    // Create the flatbuffer message (containing an implicit lifetime)
    let request_message = {
        let mut builder = oak_idl::utils::MessageBuilder::default();
        let session_id = &schema::SessionId::new(&session_id);
        let body = builder.create_vector::<u8>(&unary_request.body);
        let message = schema::UserRequest::create(
            &mut builder,
            &schema::UserRequestArgs {
                session_id: Some(session_id),
                body: Some(body),
            },
        );
        builder.finish(message).map_err(|err| {
            oak_idl::Error::new_with_message(oak_idl::ErrorCode::InvalidRequest, err.to_string())
        })?
    };

    // Return the underlying owned buffer
    Ok(request_message.into_vec())
}

pub struct EchoImpl {
    channel: UnboundedRequestSender<Vec<u8>, Result<Vec<u8>, oak_idl::Error>>,
}

#[tonic::async_trait]
impl UnarySession for EchoImpl {
    async fn message(
        &self,
        request: Request<UnaryRequest>,
    ) -> Result<Response<UnaryResponse>, Status> {
        let request = request.into_inner();
        let session_request = encode_request(request)
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
    channel: UnboundedRequestSender<Vec<u8>, Result<Vec<u8>, oak_idl::Error>>,
) -> impl Future<Output = Result<(), tonic::transport::Error>> {
    let server_impl = EchoImpl { channel };
    Server::builder()
        .add_service(UnarySessionServer::new(server_impl))
        .serve(addr)
}
