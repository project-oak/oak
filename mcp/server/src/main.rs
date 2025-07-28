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

use anyhow::{Context, Result};
use clap::Parser;
use log::{error, info, warn};
use oak_functions_standalone_client_lib::OakFunctionsClient;
use oak_session::attestation::AttestationType;
use oak_time::Clock;
use oak_time_std::clock::FrozenSystemTimeClock;
use prost::Message;
use rmcp::{
    model::{
        CallToolResult, Content, Implementation, InitializeRequestParam, InitializeResult,
        ProtocolVersion, ServerCapabilities, ServerInfo,
    },
    schemars,
    serde_json::json,
    service::RequestContext,
    tool,
    transport::stdio,
    Error as McpError, RoleServer, ServerHandler, ServiceExt,
};

#[derive(Parser, Debug)]
pub struct Args {
    #[arg(short, long)]
    tool_url: String,
    #[arg(short, long)]
    attestation_output_path: Option<String>,
}

#[derive(Clone, Default)]
pub struct WeatherService {
    pub tool_url: String,
    pub attestation_output_path: Option<String>,
}

#[tool(tool_box)]
impl WeatherService {
    pub fn new(tool_url: &str) -> Self {
        Self { tool_url: tool_url.to_string(), attestation_output_path: None }
    }

    pub fn set_attestation_output_path(&mut self, attestation_output_path: &str) {
        self.attestation_output_path = Some(attestation_output_path.to_string())
    }

    pub async fn send_tool_request(&self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        info!("Connecting to the weather tool at: {}", self.tool_url);

        let clock: Arc<dyn Clock> = Arc::new(FrozenSystemTimeClock::default());

        let mut client = OakFunctionsClient::create(
            &self.tool_url,
            AttestationType::PeerUnidirectional,
            clock.clone(),
        )
        .await
        .context("couldn't connect to server")?;

        if let Some(attestation_output_path) = &self.attestation_output_path {
            let attestation = client.fetch_attestation(self.tool_url.clone(), clock)?;
            std::fs::write(attestation_output_path, attestation.encode_to_vec())?;
            info!("Writing attestation report to: {}", attestation_output_path);
        }

        client.invoke(request_bytes).await.context("couldn't send request")
    }

    #[tool(description = "Provides current user coordinates")]
    fn get_user_location(&self) -> Result<CallToolResult, McpError> {
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
        #[tool(param)]
        #[schemars(description = "Latitude")]
        latitude: f32,
        #[tool(param)]
        #[schemars(description = "Longitude")]
        longitude: f32,
    ) -> Result<CallToolResult, McpError> {
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

#[tool(tool_box)]
impl ServerHandler for WeatherService {
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: ProtocolVersion::V_2024_11_05,
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
    ) -> Result<InitializeResult, McpError> {
        Ok(self.get_info())
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "info")
    }
    if std::env::var("RUST_BACKTRACE").is_err() {
        std::env::set_var("RUST_BACKTRACE", "1")
    }
    env_logger::init();
    let cli = Args::parse();

    info!("Starting weather service");
    let mut service = WeatherService::new(&cli.tool_url);
    if let Some(attestation_output_path) = &cli.attestation_output_path {
        service.set_attestation_output_path(attestation_output_path);
    }
    let service = service.serve(stdio()).await.inspect_err(|e| {
        error!("serving error: {:?}", e);
    })?;
    info!("Initialized weather service");
    service.waiting().await?;
    info!("Stopping weather service");
    Ok(())
}
