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
use oak_functions_mcp_lib::service::OakFunctionsMcpService;
use oak_functions_service::wasm::wasmtime::WasmtimeHandler;
use oak_proto_rust::oak::functions::{InitializeRequest, LookupDataChunk};
use prost::Message;
use rmcp::transport::streamable_http_server::{
    session::local::LocalSessionManager, StreamableHttpService,
};
use tokio::net::TcpListener;

#[derive(Parser, Debug)]
pub struct Args {
    #[arg(short, long, default_value = "0.0.0.0:8080")]
    listen_address: String,
    #[arg(long, help = "The URI for fetching the wasm logic")]
    wasm_uri: String,
    #[arg(
        long,
        help = "The URI for fetching the serialized LookupDataChunk data",
        default_value = ""
    )]
    lookup_data_uri: String,
}

fn fetch_data_from_uri(uri: &str) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    info!("fetching data from uri: {uri}");
    let response = ureq::get(uri).call()?;
    let mut buffer = Vec::new();
    response.into_reader().read_to_end(&mut buffer)?;
    Ok(buffer)
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // TODO: b/469747147 - configure logging flags at the level of VM config
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "info")
    }
    env_logger::init();
    let args = Args::parse();

    let wasm_module_bytes: Vec<u8> = if !args.wasm_uri.is_empty() {
        fetch_data_from_uri(&args.wasm_uri).expect("unable to fetch Wasm data")
    } else {
        panic!("--wasm_uri must be specified")
    };

    let lookup_data: Option<LookupDataChunk> = if !args.lookup_data_uri.is_empty() {
        let lookup_data_bytes =
            fetch_data_from_uri(&args.lookup_data_uri).expect("unable to fetch lookup data");
        Some(
            LookupDataChunk::decode(lookup_data_bytes.as_slice())
                .expect("couldn't decode lookup data"),
        )
    } else {
        None
    };

    let initialize_request =
        InitializeRequest { wasm_module: wasm_module_bytes, ..Default::default() };

    info!("Starting Oak Functions MCP server");
    let http_service = StreamableHttpService::new(
        move || {
            let service = OakFunctionsMcpService::<WasmtimeHandler>::new(Default::default());
            service.initialize(initialize_request.clone()).expect("could not initialize service");
            if let Some(lookup_data) = &lookup_data {
                service.load_lookup_data(lookup_data.clone()).expect("could not load lookup data");
            }
            Ok(service)
        },
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
    info!("Stopping Oak Functions MCP server");
    Ok(())
}
