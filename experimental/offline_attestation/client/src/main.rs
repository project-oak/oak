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

use anyhow::anyhow;
use clap::Parser;
use log::{debug, info};
use offline_attestation_shared::{
    decrypt, encrypt, generate_private_key, init, serialize_public_key, EncryptedRequest,
    EncryptedResponse, PublicKeyInfo,
};
use url::Url;

const ECHO_PATH: &str = "encrypted_echo";

const PUBLIC_KEY_INFO_PATH: &str = "public_key_info";

#[derive(Parser, Clone)]
#[clap(about = "Offline Attestation Client")]
pub struct Opt {
    #[clap(
        long,
        help = "URL of the server",
        default_value = "http://localhost:8080"
    )]
    url: String,
    #[clap(
        long,
        help = "The message to send to the server",
        default_value = "test"
    )]
    message: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    init();
    let opt = Opt::parse();
    let base_url = Url::parse(&opt.url)?;
    let echo_url = base_url.join(ECHO_PATH)?;
    let public_key_info_url = base_url.join(PUBLIC_KEY_INFO_PATH)?;

    let message = opt.message.as_bytes().to_vec();
    debug!("Cleartext message: {:?}", message);

    let client = reqwest::Client::new();

    // For this example we fetch and validate the server's public key. In a more reslistic
    // implementation this would happen out of band and be provided to the client.
    let public_key_response = client.get(public_key_info_url).send().await?;
    let public_key_info: PublicKeyInfo = public_key_response.json().await?;
    debug!(
        "Received server's public key: {:?}",
        serde_json::to_string(&public_key_info)?
    );
    public_key_info.validate()?;
    let request_public_key_handle = public_key_info.get_public_key_handle()?;

    // Encrypt the message with the server's public key.
    let ciphertext = encrypt(&request_public_key_handle, &message)?;

    // Generate a private key for decrypting the response.
    let private_key_handle = generate_private_key()?;
    // Get the associated public key so that the server can use it for encrypting the response.
    let response_public_key_handle = private_key_handle
        .public()
        .map_err(|error| anyhow!("Couldn't get public key: {}", error))?;
    let response_public_key = serialize_public_key(&response_public_key_handle)?;

    // Build the encrypted request to send to the server.
    let encrypted_request = EncryptedRequest {
        ciphertext,
        response_public_key,
    };

    debug!(
        "Encrypted request: {}",
        serde_json::to_string(&encrypted_request)?
    );

    // Post the JSON-encoded encrypted request to the server.
    let response = client
        .post(echo_url)
        .json(&encrypted_request)
        .send()
        .await?;
    let encrypted_response: EncryptedResponse = response.json().await?;
    debug!(
        "Encrypted response: {}",
        serde_json::to_string(&encrypted_response)?
    );

    // Decrypt the response.
    let response = decrypt(&private_key_handle, &encrypted_response.ciphertext)?;
    let result = String::from_utf8(response)?;
    info!("Result: {}", result);
    Ok(())
}
