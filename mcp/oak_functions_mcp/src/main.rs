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
use oak_functions_mcp_lib::service::{OakFunctionsMcpService, ToolConfig};
use oak_functions_service::wasm::wasmtime::WasmtimeHandler;
use oak_proto_rust::oak::functions::{InitializeRequest, LookupDataChunk};
use prost::Message;
use rmcp::transport::streamable_http_server::{
    StreamableHttpService, session::local::LocalSessionManager,
};
use tokio::net::TcpListener;

#[derive(Parser, Debug)]
pub struct Args {
    #[arg(short, long, default_value = "127.0.0.1:8080")]
    listen_address: String,
    #[arg(
        long,
        env = "WASM_URL",
        help = "The URL for fetching the wasm logic",
        default_value = "https://storage.googleapis.com/oak-functions-standalone-bucket/wasm/key_value_lookup_with_json.wasm"
    )]
    wasm_url: String,
    #[arg(
        long,
        env = "LOOKUP_DATA_URL",
        help = "The URL for fetching the serialized LookupDataChunk data",
        default_value = "https://storage.googleapis.com/oak-functions-standalone-bucket/lookup_data/double_lookup_data.binarypb"
    )]
    lookup_data_url: String,
    #[arg(
        long,
        env = "TOOL_CONFIG_URL",
        help = "The URL for fetching the ToolConfig JSON file",
        default_value = "https://storage.googleapis.com/oak-functions-standalone-bucket/tool_config/key_value_lookup.json"
    )]
    tool_config_url: String,
}

fn fetch_data_from_url(url: &str) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    info!("fetching data from url: {url}");
    let response = ureq::get(url).call()?;
    let mut buffer = Vec::new();
    response.into_reader().read_to_end(&mut buffer)?;
    Ok(buffer)
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // TODO: b/469747147 - configure logging flags at the level of VM config
    if std::env::var("RUST_LOG").is_err() {
        // Safety: this is a CLI tool.
        unsafe {
            std::env::set_var("RUST_LOG", "info");
        }
    }
    env_logger::init();
    let args = Args::parse();

    let wasm_module_bytes: Vec<u8> = if !args.wasm_url.is_empty() {
        fetch_data_from_url(&args.wasm_url).expect("unable to fetch Wasm data")
    } else {
        panic!("--wasm_url must be specified")
    };

    let lookup_data: Option<LookupDataChunk> = if !args.lookup_data_url.is_empty() {
        let lookup_data_bytes =
            fetch_data_from_url(&args.lookup_data_url).expect("unable to fetch lookup data");
        Some(
            LookupDataChunk::decode(lookup_data_bytes.as_slice())
                .expect("couldn't decode lookup data"),
        )
    } else {
        None
    };

    let tool_config: ToolConfig = if !args.tool_config_url.is_empty() {
        let config_bytes =
            fetch_data_from_url(&args.tool_config_url).expect("unable to fetch tool config");
        serde_json::from_slice(&config_bytes).expect("unable to parse tool config")
    } else {
        panic!("--tool_config_url must be specified")
    };

    let initialize_request =
        InitializeRequest { wasm_module: wasm_module_bytes, ..Default::default() };

    info!("Starting Oak Functions MCP server");
    let http_service = StreamableHttpService::new(
        move || {
            let service = OakFunctionsMcpService::<WasmtimeHandler>::new_with_config(
                Default::default(),
                tool_config.clone(),
            );
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
