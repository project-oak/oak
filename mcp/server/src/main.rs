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

use std::sync::Arc;

use anyhow::Context;
use axum::Router;
use clap::Parser;
use futures::Future;
use log::{info, warn};
use oak_functions_standalone_client_lib::{
    default_oak_functions_standalone_reference_values, OakFunctionsClient,
};
use oak_proto_rust::oak::attestation::v1::ConfidentialSpaceReferenceValues;
use oak_session::attestation::AttestationType;
use oak_time::Clock;
use oak_time_std::clock::FrozenSystemTimeClock;
use rmcp::{
    handler::server::{router::tool::ToolRouter, tool::Parameters},
    model::{
        CallToolResult, Content, Implementation, InitializeRequestParam, InitializeResult,
        ProtocolVersion, ServerCapabilities, ServerInfo,
    },
    schemars,
    serde_json::json,
    service::RequestContext,
    tool, tool_handler, tool_router,
    transport::streamable_http_server::{
        session::local::LocalSessionManager, StreamableHttpService,
    },
    ErrorData, RoleServer, ServerHandler,
};
use serde::Deserialize;
use tokio::net::TcpListener;

#[derive(Parser, Debug)]
pub struct Args {
    #[arg(short, long, default_value = "0.0.0.0:8081")]
    listen_address: String,
    #[arg(short, long, env = "OAK_FUNCTIONS_URL")]
    tool_url: String,
    #[arg(long, default_value_t = false)]
    insecure_attestation: bool,
}

#[derive(Clone)]
pub struct WeatherService {
    tool_url: String,
    insecure_attestation: bool,
    tool_router: ToolRouter<Self>,
}

#[derive(Deserialize, schemars::JsonSchema)]
struct GetWeatherRequest {
    #[schemars(description = "Latitude")]
    latitude: f32,
    #[schemars(description = "Longitude")]
    longitude: f32,
}

impl WeatherService {
    pub fn new(tool_url: &str, insecure_attestation: bool) -> Self {
        Self {
            tool_url: tool_url.to_string(),
            insecure_attestation,
            tool_router: Self::tool_router(),
        }
    }

    pub async fn send_tool_request(&self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        info!("Connecting to the weather tool at: {}", self.tool_url);

        let clock: Arc<dyn Clock> = Arc::new(FrozenSystemTimeClock::default());

        let ref_values: ConfidentialSpaceReferenceValues =
            default_oak_functions_standalone_reference_values();

        let mut client = OakFunctionsClient::create(
            &self.tool_url,
            if self.insecure_attestation {
                AttestationType::Unattested
            } else {
                AttestationType::PeerUnidirectional
            },
            clock.clone(),
            Some(&ref_values),
        )
        .await
        .context("couldn't connect to server")?;

        client.invoke(request_bytes).await.context("couldn't send request")
    }
}

#[tool_router]
impl WeatherService {
    #[tool(description = "Provides current user coordinates")]
    fn get_user_location(&self) -> Result<CallToolResult, ErrorData> {
        let result = json!({
            "status": "success",
            "coordinates": {
                "latitude": 45.51,
                "longitude": -122.68,
            },
        });
        let result = Content::json(result).expect("couldn't serialize JSON resuls");
        Ok(CallToolResult::success(vec![result]))
    }

    #[tool(
        description = "Provides current weather for specified coordinates. If the server connection fails, this means that the server is not trusted, and the user request will be leaked. And cannot risk leaking the request and compromise user's privacy! So please explain it to the user"
    )]
    async fn get_weather(
        &self,
        params: Parameters<GetWeatherRequest>,
    ) -> Result<CallToolResult, ErrorData> {
        let Parameters(GetWeatherRequest { latitude, longitude }) = params;
        info!("Requested weather for ({}, {})", latitude, longitude);

        info!("Sending a tool request at: {}", self.tool_url);
        let tool_result =
            self.send_tool_request(format!("({latitude},{longitude})").as_bytes()).await;
        info!("Tool result: {:?}", tool_result);
        let result = match tool_result {
            Ok(tool_response_bytes) => {
                let tool_response = String::from_utf8(tool_response_bytes)
                    .expect("unable to convert tool response bytes to string");
                info!("Received a tool response: {}", tool_response);
                json!({
                    "status": "success",
                    "weather": tool_response,
                })
            }
            Err(err) => {
                warn!("Received an error: {:?}", err);
                json!({
                    "status": "error",
                    "error_message": format!("Couldn't verify server attestation"),
                })
            }
        };

        let result = Content::json(result).expect("couldn't serialize JSON resuls");
        Ok(CallToolResult::success(vec![result]))
    }
}

#[tool_handler]
impl ServerHandler for WeatherService {
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: ProtocolVersion::V_2025_06_18,
            capabilities: ServerCapabilities::builder().enable_tools().build(),
            server_info: Implementation::from_build_env(),
            instructions: Some(
                "Weather server that can provide weather information based on coordinates".into(),
            ),
        }
    }

    async fn initialize(
        &self,
        _request: InitializeRequestParam,
        _context: RequestContext<RoleServer>,
    ) -> Result<InitializeResult, ErrorData> {
        Ok(self.get_info())
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "info")
    }
    env_logger::init();
    let args = Args::parse();

    info!("Starting weather service");
    let service = WeatherService::new(&args.tool_url, args.insecure_attestation);
    let http_service = StreamableHttpService::new(
        move || Ok(service.clone()),
        LocalSessionManager::default().into(),
        Default::default(),
    );

    let router = Router::new().nest_service("/mcp", http_service);

    let tcp_listener = TcpListener::bind(&args.listen_address).await?;
    info!("listening on {}", &args.listen_address);
    axum::serve(tcp_listener, router)
        .with_graceful_shutdown(async {
            tokio::signal::ctrl_c().await.unwrap();
        })
        .await?;
    info!("Stopping weather service");
    Ok(())
}
