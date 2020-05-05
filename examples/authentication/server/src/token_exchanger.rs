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

//! Utilities for exchanging authorisation codes for identity tokens and validating the resulting
//! tokens.
//!
//! For reference, see:
//! https://developers.google.com/identity/protocols/oauth2/openid-connect#exchangecode

use jsonwebtoken::{decode, decode_header, Algorithm, DecodingKey, Header, Validation};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::{error, fmt};

/// Claims encoded into the identity token. Reference:
/// https://developers.google.com/identity/protocols/oauth2/openid-connect#an-id-tokens-payload
#[derive(Debug, Deserialize)]
pub struct Claims {
    /// The intended audience for the token (will be a client id).
    #[serde(rename = "aud")]
    audience: String,
    /// The expiration time for the token in Unix time (seconds).
    #[serde(rename = "exp")]
    expiry: usize,
    /// The time that the token was issued in Unix time (seconds).
    #[serde(rename = "iat")]
    issued_at: usize,
    /// The issuer identifier (https://accounts.google.com or accounts.google.com).
    #[serde(rename = "iss")]
    issuer: String,
    /// The unique identifier for the account.
    #[serde(rename = "sub")]
    subject: String,
    /// The email address used for logging into the account.
    email: String,
    // TODO(#922): Add nonce
}

/// The request paramters for the token service. Reference:
/// https://developers.google.com/identity/protocols/oauth2/openid-connect#exchangecode
#[derive(Serialize, Debug)]
struct TokenRequest {
    /// The authorisation code to exchange for an ID token.
    code: String,
    /// The OAuth client ID used for requesting the authorisation code.
    client_id: String,
    /// The secret associated with the OAuth client ID.
    client_secret: String,
    /// The redirect URI that was used when requesting the authorisation code.
    redirect_uri: String,
    /// The grant type. This should always be 'authorization_code' when exchaning an authorisation
    /// code.
    grant_type: String,
}

/// The response from the token service. Reference:
/// https://developers.google.com/identity/protocols/oauth2/openid-connect#exchangecode
#[derive(Deserialize, Debug)]
struct TokenResponse {
    expires_in: usize,
    id_token: String,
}

/// Container for the JSON Web Key Set containing the signing keys.
/// Reference: https://auth0.com/docs/tokens/references/jwks-properties
#[derive(Deserialize, Debug)]
struct KeySet {
    /// The keys contained in the key set.
    keys: Vec<Key>,
}

/// A JSON Web Key potentially used for signing the identity tokens.
/// Reference: https://auth0.com/docs/tokens/references/jwks-properties
///
/// The Gooogle Identity Platform keys always seem to use RSA:
/// https://www.googleapis.com/oauth2/v3/certs
#[derive(Clone, Deserialize, Debug)]
struct Key {
    /// The signing algorithm for the key.
    #[serde(rename = "alg")]
    algorithm: String,
    /// Base64 encoded RSA exponent.
    #[serde(rename = "e")]
    exponent: String,
    /// The key ID.
    #[serde(rename = "kid")]
    key_id: String,
    /// Base64 encoded RSA modulus.
    #[serde(rename = "n")]
    modulus: String,
}

/// Exchanges an authorisation code for an ID token and validates the token.
pub async fn exchange_code_for_token(
    code: &str,
    client_id: &str,
    client_secret: &str,
) -> Result<String, Box<dyn error::Error>> {
    let body = TokenRequest {
        code: code.to_owned(),
        client_id: client_id.to_owned(),
        client_secret: client_secret.to_owned(),
        // TODO(#922): Pass the actual redirect URI from the client app.
        redirect_uri: "http://127.0.0.1:8089".to_owned(),
        grant_type: "authorization_code".to_owned(),
    };
    // TODO(#923): Get the token service URL from the discovery document.
    let token_service = "https://oauth2.googleapis.com/token";
    let client = Client::new();
    let response = client
        .post(token_service)
        .form(&body)
        .send()
        .await?
        .text()
        .await?;
    let result: TokenResponse = serde_json::from_str(&response)?;
    // Validate token.
    decode_identity_token(&result.id_token).await?;
    Ok(result.id_token)
}

// Decodes and validates the identity token.
async fn decode_identity_token(token: &str) -> Result<Claims, Box<dyn error::Error>> {
    let key = get_key(decode_header(token)?).await?;
    let validation = Validation::new(key.algorithm.parse()?);
    let key = DecodingKey::from_rsa_components(&key.modulus, &key.exponent);
    let data = decode::<Claims>(&token, &key, &validation)?;
    Ok(data.claims)
}

/// Gets the public key that matches the header's key ID and algorithm.
async fn get_key(header: Header) -> Result<Key, Box<dyn std::error::Error>> {
    // TODO(#923): Get certificate location from the discovery document.
    let cert_location = "https://www.googleapis.com/oauth2/v3/certs";
    // TODO(#924): Cache certificates based on the max-age value of the cache-control response
    // header.
    let response = reqwest::get(cert_location).await?.text().await?;
    let key_list: KeySet = serde_json::from_str(&response)?;
    match key_list.keys.iter().find(|key| {
        key.algorithm.parse::<Algorithm>().unwrap() == header.alg
            && key.key_id[..] == header.kid.as_ref().unwrap()[..]
    }) {
        Some(key) => Ok(key.clone()),
        None => Err(Box::new(TokenError::new("No matching key found."))),
    }
}

/// Represents a token validation error.
#[derive(Debug, Clone)]
pub struct TokenError {
    message: String,
}

impl TokenError {
    pub fn new(message: &str) -> TokenError {
        TokenError {
            message: message.to_owned(),
        }
    }
}

impl fmt::Display for TokenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Token validation error: {}", &self.message)
    }
}

impl error::Error for TokenError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        // Source is not tracked.
        None
    }
}
