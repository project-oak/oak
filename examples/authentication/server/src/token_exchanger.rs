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
use log::info;
use serde::{Deserialize, Serialize};
use std::{error, fmt};
use url::form_urlencoded;

use crate::http_client;

/// Claims encoded into the identity token
#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    aud: String,
    exp: usize,
    iat: usize,
    iss: String,
    sub: String,
    email: String,
    // TODO(#922): Add nonce
}

#[derive(Deserialize, Debug)]
struct TokenResponse {
    expires_in: usize,
    id_token: String,
}

#[derive(Deserialize, Debug)]
struct KeyList {
    keys: Vec<Key>,
}

#[derive(Clone, Deserialize, Debug)]
struct Key {
    // The signing algorithm for the key.
    alg: String,
    // Base64 encoded RSA exponent.
    e: String,
    // The key ID.
    kid: String,
    // Base64 encoded RSA modulus.
    n: String,
}

pub async fn exchange_code_for_token(
    code: &str,
    client_id: &str,
    client_secret: &str,
) -> Result<String, Box<dyn error::Error>> {
    let body: String = form_urlencoded::Serializer::new(String::new())
        .append_pair("code", code)
        .append_pair("client_id", client_id)
        .append_pair("client_secret", client_secret)
        // TODO(#922): Pass the actual redirect URI from the client app.
        .append_pair("redirect_uri", "http://127.0.0.1:8089")
        .append_pair("grant_type", "authorization_code")
        .finish();

    // TODO(#923): Get the token URL from the discovery document.
    let token_uri = "https://oauth2.googleapis.com/token".parse()?;
    let response = http_client::post(token_uri, &body, "application/x-www-form-urlencoded").await?;
    let result: TokenResponse = serde_json::from_str(&response)?;
    // Validate token.
    let claims = decode_identity_token(&result.id_token).await?;
    info!(
        "Validated identity token with email '{}' and subject '{}'",
        &claims.email, &claims.sub
    );
    Ok(result.id_token)
}

// Decodes and validates the identity token.
pub async fn decode_identity_token(token: &str) -> Result<Claims, Box<dyn error::Error>> {
    let key = get_key(decode_header(token)?).await?;
    let validation = Validation::new(key.alg.parse()?);
    let key = DecodingKey::from_rsa_components(&key.n, &key.e);
    let data = decode::<Claims>(&token, &key, &validation)?;
    Ok(data.claims)
}

/// Gets the public key that matches the header's key ID and algorithm.
async fn get_key(header: Header) -> Result<Key, Box<dyn std::error::Error>> {
    // TODO(#923): Get certificate location from the discovery document.
    let cert_location = "https://www.googleapis.com/oauth2/v3/certs".parse()?;
    // TODO(#924): Cache certificates based on the max-age value of the cache-control response
    // header
    let response = http_client::get(cert_location).await?;
    let key_list: KeyList = serde_json::from_str(&response)?;
    match key_list.keys.iter().find(|key| {
        key.alg.parse::<Algorithm>().unwrap() == header.alg
            && key.kid[..] == header.kid.as_ref().unwrap()[..]
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
