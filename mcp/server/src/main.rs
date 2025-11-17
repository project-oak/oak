//
// Copyright 2025 The Project Oak Authors
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

use axum::Router;
use clap::Parser;
use log::info;
use mcp_server_lib::service::Service;
use rmcp::transport::streamable_http_server::{
    session::local::LocalSessionManager, StreamableHttpService,
};
use tokio::net::TcpListener;

#[derive(Parser, Debug)]
pub struct Args {
    #[arg(short, long, default_value = "0.0.0.0:8081")]
    listen_address: String,
    #[arg(short, long, env = "OAK_FUNCTIONS_URL")]
    oak_functions_url: String,
    #[arg(long, default_value_t = false)]
    attestation: bool,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "info")
    }
    env_logger::init();
    let args = Args::parse();

    info!("Starting MCP server");
    let service = Service::new(&args.oak_functions_url, args.attestation);
    let http_service = StreamableHttpService::new(
        move || Ok(service.clone()),
        LocalSessionManager::default().into(),
        Default::default(),
    );

    let router = Router::new().nest_service("/mcp", http_service);

    let tcp_listener = TcpListener::bind(&args.listen_address).await?;
    info!("Listening on {}", &args.listen_address);
    axum::serve(tcp_listener, router)
        .with_graceful_shutdown(async {
            tokio::signal::ctrl_c().await.unwrap();
        })
        .await?;
    info!("Stopping MCP server");
    Ok(())
}
