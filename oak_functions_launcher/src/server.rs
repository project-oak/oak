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

use crate::{channel::ConnectorHandle, schema};
use futures::Future;
use oak_remote_attestation_sessions::{SessionId, SESSION_ID_LENGTH};
use std::net::SocketAddr;
use tonic::{transport::Server, Request, Response};

pub mod proto {
    tonic::include_proto!("oak.session.unary.v1");
}

use proto::{
    unary_session_server::{UnarySession, UnarySessionServer},
    PublicKeyInfo, UnaryRequest, UnaryResponse,
};

fn encode_request(unary_request: UnaryRequest) -> Result<schema::UserRequest, oak_idl::Status> {
    let mut session_id: SessionId = [0; SESSION_ID_LENGTH];
    if unary_request.session_id.len() != SESSION_ID_LENGTH {
        return Err(oak_idl::Status::new_with_message(
            oak_idl::StatusCode::Internal,
            format!(
                "session_id must be {} bytes in length, found a length of {} bytes instead",
                SESSION_ID_LENGTH,
                unary_request.session_id.len()
            ),
        ));
    }
    session_id.copy_from_slice(&unary_request.session_id);

    // Return the underlying owned buffer
    Ok(schema::UserRequest {
        session_id: Some(schema::SessionId {
            value: session_id.to_vec(),
        }),
        body: unary_request.body,
    })
}

pub struct SessionProxy {
    connector_handle: ConnectorHandle,
    signing_public_key: Vec<u8>,
    attestation: Vec<u8>,
}

#[tonic::async_trait]
impl UnarySession for SessionProxy {
    async fn message(
        &self,
        request: Request<UnaryRequest>,
    ) -> Result<Response<UnaryResponse>, tonic::Status> {
        log::debug!("handling client request");
        let request = request.into_inner();
        let encoded_request = encode_request(request)
            .map_err(|err| tonic::Status::invalid_argument(format!("{:?}", err)))?;

        let mut client = schema::TrustedRuntimeAsyncClient::new(self.connector_handle.clone());

        let response = client
            .handle_user_request(&encoded_request)
            .await
            .flatten()
            .map_err(|err| {
                tonic::Status::internal(format!("error handling client request: {:?}", err))
            })?;

        Ok(Response::new(UnaryResponse {
            body: response.body,
        }))
    }

    async fn get_public_key_info(
        &self,
        _request: Request<()>,
    ) -> Result<Response<PublicKeyInfo>, tonic::Status> {
        Ok(Response::new(PublicKeyInfo {
            public_key: self.signing_public_key.clone(),
            attestation: self.attestation.clone(),
        }))
    }
}

pub fn server(
    addr: SocketAddr,
    connector_handle: ConnectorHandle,
    signing_public_key: Vec<u8>,
    attestation: Vec<u8>,
) -> impl Future<Output = Result<(), tonic::transport::Error>> {
    let server_impl = SessionProxy {
        connector_handle,
        signing_public_key,
        attestation,
    };

    #[cfg(feature = "grpc-web")]
    return Server::builder()
        .add_service(tonic_web::enable(UnarySessionServer::new(server_impl)))
        .serve(addr);

    #[cfg(not(feature = "grpc-web"))]
    return Server::builder()
        .add_service(UnarySessionServer::new(server_impl))
        .serve(addr);
}
