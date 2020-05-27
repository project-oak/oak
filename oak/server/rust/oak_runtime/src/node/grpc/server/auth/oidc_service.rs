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

//! gRPC service implementation for handling OpenID Connect authentication requests from clients.

use crate::{
    auth::oidc_utils::exchange_code_for_token,
    proto::oak::authentication::{
        authentication_server::{Authentication, AuthenticationServer},
        AuthParameters, IdentityTokenRequest, IdentityTokenResponse,
    },
};
use tonic::{Request, Response, Status};

pub fn build_service(
    client_id: &str,
    client_secret: &str,
) -> AuthenticationServer<AuthenticationHandler> {
    AuthenticationServer::new(AuthenticationHandler::new(client_id, client_secret))
}

/// Service implementation to handle authentication requests.
#[derive(Default)]
pub struct AuthenticationHandler {
    client_id: String,
    client_secret: String,
    /* TODO(#922): Add a state storage mechanism to be able to match a client request to the
     * nonce and code challenge. */
}

impl AuthenticationHandler {
    pub fn new(client_id: &str, client_secret: &str) -> AuthenticationHandler {
        AuthenticationHandler {
            client_id: client_id.to_owned(),
            client_secret: client_secret.to_owned(),
        }
    }
}

#[tonic::async_trait]
impl Authentication for AuthenticationHandler {
    /// Gets the authentication parameters needed by the client to send authorisation code
    /// requests to the authentication endpoint.
    async fn get_auth_parameters(
        &self,
        _req: Request<()>,
    ) -> Result<Response<AuthParameters>, Status> {
        Ok(Response::new(AuthParameters {
            client_id: self.client_id.clone(),
            // Using Google Identity Platform endpoint for this example.
            // See https://developers.google.com/identity/protocols/oauth2/openid-connect
            // TODO(#923): The endpoint should be read from the discovery document.
            auth_endpoint: "https://accounts.google.com/o/oauth2/v2/auth".to_string(),
        }))
    }

    /// Exchanges an authorization code for an identity token.
    async fn get_token_from_code(
        &self,
        request: Request<IdentityTokenRequest>,
    ) -> Result<Response<IdentityTokenResponse>, Status> {
        match exchange_code_for_token(
            &request.into_inner().auth_code,
            &self.client_id,
            &self.client_secret,
        )
        .await
        {
            Ok(token) => Ok(Response::new(IdentityTokenResponse { token })),
            Err(error) => Err(Status::internal(format!("Unexpected error: {}", error))),
        }
    }
}
