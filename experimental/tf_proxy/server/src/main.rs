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

pub mod proto {
    tonic::include_proto!("oak.session.stream.v1");
}

use crate::attestation::AttestationServer;
use anyhow::Context;
use proto::streaming_session_server::StreamingSessionServer;
use std::{
    fs::canonicalize,
    net::{Ipv6Addr, SocketAddr},
    path::PathBuf,
};
use structopt::StructOpt;
use tokio::time::{sleep, Duration};
use tonic::transport::Server;

pub mod attestation;
pub mod grpc;

// The name of the UNIX domain socket for communicating with the TF model server.
static SOCKET: &str = "/tmp/serving_uds";

#[derive(StructOpt, Clone, Debug)]
pub struct Opt {
    #[structopt(
        long,
        default_value = "8080",
        help = "Port number that the proxy listens on."
    )]
    port: u16,
    #[structopt(
        long,
        default_value = "tensorflow_model_server",
        help = "Path to the TensorFlow model server binary to launch."
    )]
    tf_server_path: String,
    #[structopt(
        long,
        default_value = "model/mnist",
        help = "Path to the base directory of the TensorFlow saved model to serve."
    )]
    tf_model_base_path: String,
    #[structopt(
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
    let opt = Opt::from_args();
    launch_tf_model_server(&opt)?;
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, opt.port));
    wait_for_socket(SOCKET).await?;
    let backend = grpc::BackendConnection::connect(SOCKET).await;
    let handler = AttestationServer::create(Vec::new(), backend)?;
    Server::builder()
        .add_service(StreamingSessionServer::new(handler))
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
