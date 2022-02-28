//
// Copyright 2021 The Project Oak Authors
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

#![feature(async_closure)]

pub mod proto {
    pub mod google {
        pub mod rpc {
            tonic::include_proto!("google.rpc");
        }
    }
    pub mod oak {
        pub mod encap {
            tonic::include_proto!("oak.encap");
        }
    }
}

use crate::grpc::handle_request;
use anyhow::Context;
use clap::Parser;
use grpc_streaming_attestation::{
    proto::streaming_session_server::StreamingSessionServer,
    server::{AttestationServer, LogError},
};
use log::warn;
use oak_functions_abi::proto::ConfigurationInfo;
use prost::Message;
use std::{
    fs::canonicalize,
    net::{Ipv6Addr, SocketAddr},
    path::PathBuf,
};
use tokio::time::{sleep, Duration};
use tonic::transport::Server;

pub mod grpc;

// The name of the UNIX domain socket for communicating with the TF model server.
static SOCKET: &str = "/tmp/serving_uds";

#[derive(Parser, Clone, Debug)]
pub struct Opt {
    #[clap(
        long,
        default_value = "8080",
        help = "Port number that the proxy listens on."
    )]
    port: u16,
    #[clap(
        long,
        default_value = "tensorflow_model_server",
        help = "Path to the TensorFlow model server binary to launch."
    )]
    tf_server_path: String,
    #[clap(
        long,
        default_value = "model/mnist",
        help = "Path to the base directory of the TensorFlow saved model to serve."
    )]
    tf_model_base_path: String,
    #[clap(
        long,
        default_value = "mnist",
        help = "The name of the TensorFlow saved model to serve."
    )]
    tf_model_name: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    cleanup_socket_temp_file()?;
    let opt = Opt::parse();
    launch_tf_model_server(&opt)?;
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, opt.port));
    wait_for_socket(SOCKET).await?;
    let backend = grpc::BackendConnection::connect(SOCKET).await;
    let client = backend.create_client();

    // Create fake configuration info for now, as it cannot be empty for the attestation
    // handshake.
    // TODO(#2420): Remove once Java client can work without the configuration info.
    let additional_info = ConfigurationInfo {
        wasm_hash: vec![0, 1, 2, 3],
        policy: None,
        ml_inference: false,
        metrics: None,
    }
    .encode_to_vec();

    let request_handler = async move |request| handle_request(client.clone(), request).await;

    Server::builder()
        .add_service(StreamingSessionServer::new(AttestationServer::create(
            Vec::new(),
            request_handler,
            additional_info,
            ErrorLogger {},
        )?))
        .serve(address)
        .await
        .context("error executing server")?;

    Ok(())
}

fn cleanup_socket_temp_file() -> anyhow::Result<()> {
    let path = std::path::Path::new(SOCKET);
    if path.exists() {
        std::fs::remove_file(path).context("couldn't remove temp file")?;
    }
    Ok(())
}

fn launch_tf_model_server(opt: &Opt) -> anyhow::Result<()> {
    let model_base_path = PathBuf::from(&opt.tf_model_base_path);
    let args = vec![
        format!("--grpc_socket_path={}", SOCKET),
        format!(
            "--model_base_path={}",
            canonicalize(model_base_path)
                .context("invalid model base path")?
                .display()
        ),
        format!("--model_name={}", opt.tf_model_name),
        "--port=0".to_owned(),
    ];
    tokio::process::Command::new(&opt.tf_server_path)
        .args(&args)
        .spawn()
        .context("couldn't spawn TF model server")?;
    Ok(())
}

async fn wait_for_socket(socket: &str) -> anyhow::Result<()> {
    // Wait for up to 5 seconds for the socket to become visible after the model server has been
    // started.
    for _ in 0..50 {
        if std::path::Path::new(socket).exists() {
            return Ok(());
        }
        sleep(Duration::from_millis(100)).await;
    }
    Err(anyhow::anyhow!("socket not available in time"))
}

#[derive(Clone)]
struct ErrorLogger {}

impl LogError for ErrorLogger {
    fn log_error(&self, error: &str) {
        warn!("{}", error);
    }
}
