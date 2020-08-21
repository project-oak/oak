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

use proto::{authentication_client::AuthenticationClient, IdentityTokenRequest};
use tonic::transport::{Certificate, Channel, ClientTlsConfig};
use url::Url;

pub mod proto {
    tonic::include_proto!("oak.authentication");
}

/// Creates an `AuthenticationClient` that trusts certificates signed by the root certificate stored
/// at `ca_cert` for TLS and connects to `auth_server`.
pub async fn build_auth_client(
    ca_cert: &str,
    auth_server: &str,
) -> Result<AuthenticationClient<Channel>, Box<dyn std::error::Error>> {
    let root_cert = tokio::fs::read(ca_cert).await?;
    let root_cert = Certificate::from_pem(root_cert);
    let tls_config = ClientTlsConfig::new().ca_certificate(root_cert);

    let channel = Channel::from_shared(auth_server.to_owned())?
        .tls_config(tls_config)
        .expect("Couldn't create TLS configuration")
        .connect()
        .await?;

    Ok(AuthenticationClient::new(channel))
}

/// Gets the URL for authentication requests.
///
/// See: https://developers.google.com/identity/protocols/oauth2/openid-connect#sendauthrequest
/// for more details on the request URL for the Google Identity Platform.
pub async fn get_authentication_request_url(
    auth_client: &mut AuthenticationClient<Channel>,
    redirect_address: &str,
) -> Result<String, Box<dyn std::error::Error>> {
    let request = tonic::Request::new(());
    let response = auth_client.get_auth_parameters(request).await?.into_inner();

    let mut auth_endpoint = Url::parse(&response.auth_endpoint).unwrap();
    // TODO(#922): Consider retrieving scope from server.
    let scope = "openid email";
    let redirect_url = format!("http://{}", redirect_address);
    // TODO(#922): Retrieve state and code challenge from server and add to request.
    auth_endpoint
        .query_pairs_mut()
        .append_pair("scope", scope)
        .append_pair("response_type", "code")
        .append_pair("redirect_uri", &redirect_url)
        .append_pair("client_id", &response.client_id);
    Ok(auth_endpoint.to_string())
}

/// Exchanges the authorisation code for an identity token.
pub async fn get_identity_token(
    auth_client: &mut AuthenticationClient<Channel>,
    code: &str,
) -> Result<String, Box<dyn std::error::Error>> {
    let request = tonic::Request::new(IdentityTokenRequest {
        auth_code: code.to_owned(),
    });
    let response = auth_client.get_token_from_code(request).await?.into_inner();
    Ok(response.token)
}
