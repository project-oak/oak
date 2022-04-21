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

#![feature(try_blocks)]

use anyhow::anyhow;
use clap::Parser;
use log::{debug, info};
use offline_attestation_shared::{
    decrypt, encrypt, generate_private_key, init, EncryptedRequest, EncryptedResponse, Handle,
    PublicKeyInfo,
};
use std::{
    net::{Ipv6Addr, SocketAddr},
    sync::Arc,
};
use warp::{hyper::StatusCode, reply::Response, Filter, Reply};

const ECHO_PATH: &str = "encrypted_echo";

const PUBLIC_KEY_INFO_PATH: &str = "public_key_info";

#[derive(Parser, Clone, Debug)]
#[clap(about = "Offline Attestation Server")]
pub struct Opt {
    #[clap(long, default_value = "8080", help = "Port number on which to listen.")]
    port: u16,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    init();
    let opt = Opt::parse();
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, opt.port));

    debug!("Generating private key");
    let private_key_handle = Arc::new(generate_private_key()?);
    let public_key_handle = private_key_handle
        .public()
        .map_err(|error| anyhow!("Couldn't get public key: {}", error))?;

    let public_key_info = Arc::new(PublicKeyInfo::new(&public_key_handle)?);
    debug!(
        "Constructed public key info: {}",
        serde_json::to_string(public_key_info.as_ref())?
    );

    let root_filer = create_root_filter(private_key_handle, public_key_info);

    warp::serve(root_filer).run(address).await;
    Ok(())
}

fn create_root_filter(
    private_key_handle: Arc<Handle>,
    public_key_info: Arc<PublicKeyInfo>,
) -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
    get_public_key_info(public_key_info).or(encrypted_echo(private_key_handle))
}

fn get_public_key_info(
    public_key_info: Arc<PublicKeyInfo>,
) -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
    // Path filer for "GET /public_key_info".
    warp::get()
        .and(warp::path(PUBLIC_KEY_INFO_PATH))
        .and(warp::path::end())
        .map(move || warp::reply::json(public_key_info.clone().as_ref()))
}

fn encrypted_echo(
    private_key_handle: Arc<Handle>,
) -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
    warp::post()
        .and(warp::path(ECHO_PATH))
        // Limit the maximum request body size to 4kb.
        .and(warp::body::content_length_limit(1024 * 4))
        .and(warp::body::json())
        .map(move |request: EncryptedRequest| handle(request, private_key_handle.clone()))
}

fn handle(encrypted_request: EncryptedRequest, private_key_handle: Arc<Handle>) -> Response {
    let result: anyhow::Result<EncryptedResponse> = try {
        debug!(
            "Received encrypted request: {}",
            serde_json::to_string(&encrypted_request)?
        );

        let clear_text = decrypt(private_key_handle.as_ref(), &encrypted_request.ciphertext)?;
        info!("Received cleartext: {:?}", clear_text);
        let ciphertext = encrypt(&encrypted_request.get_public_key_handle()?, &clear_text)?;
        let response = EncryptedResponse { ciphertext };

        debug!(
            "Sending encrypted respone: {}",
            serde_json::to_string(&response)?
        );

        response
    };
    match result {
        Ok(response) => warp::reply::json(&response).into_response(),
        Err(_) => StatusCode::INTERNAL_SERVER_ERROR.into_response(),
    }
}
