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

use anyhow::Result;
use clap::Parser;
use futures::StreamExt;
use log::{error, info, warn};
use oak_grpc::oak::functions::standalone::oak_functions_session_client::OakFunctionsSessionClient;
use oak_proto_rust::oak::functions::standalone::OakSessionRequest;
use oak_session::{
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    session::{ClientSession, Session},
};
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
use tonic::transport::Channel;

#[derive(Parser, Debug)]
pub struct Args {
    #[arg(short, long)]
    tool_url: String,
}

#[derive(Clone, Default)]
pub struct WeatherService {
    pub tool_url: String,
}

#[tool(tool_box)]
impl WeatherService {
    pub fn new(tool_url: &str) -> Self {
        Self { tool_url: tool_url.to_string() }
    }

    pub async fn send_tool_request(&self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        info!("Connecting to the weather tool at: {}", self.tool_url);

        // Create client.
        let channel = Channel::from_shared(self.tool_url.to_string())
            .expect("couldn't create gRPC channel")
            .connect()
            .await
            .expect("couldn't connect via gRPC channel");

        let mut client = OakFunctionsSessionClient::new(channel);

        // Start bidirectional stream.
        let (mut tx, rx) = futures::channel::mpsc::channel(10);
        let mut response_stream =
            client.oak_session(rx).await.expect("failed to start stream").into_inner();

        // Perform Handshake.
        let mut client_session = ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .expect("failed to create client session");

        while !client_session.is_open() {
            let request = client_session.next_init_message().expect("expected client init message");
            let oak_functions_request = OakSessionRequest { request: Some(request) };
            tx.try_send(oak_functions_request).expect("failed to send to server");
            if !client_session.is_open() {
                let response = response_stream
                    .next()
                    .await
                    .expect("expected a response")
                    .expect("response was failure");
                client_session
                    .handle_init_message(response.response.expect("no response provided"))
                    .expect("failed to handle init response");
            }
        }

        let request = client_session.encrypt(request_bytes).expect("failed to send request");
        let oak_functions_request = OakSessionRequest { request: Some(request) };
        tx.try_send(oak_functions_request).expect("failed to send request");

        let result = response_stream
            .next()
            .await
            .expect("no response ready")
            .expect("failed to get response");
        let result = client_session
            .decrypt(result.response.expect("no response provided"))
            .expect("failed to decrypt result");

        Ok(result)
    }

    #[tool(description = "Provides current weather for specified coordinates")]
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

        const EPSILON: f32 = 1e-5;
        let result = if (latitude.abs() < EPSILON) && (longitude.abs() < EPSILON) {
            let result = json!({
                "status": "success",
                "weather": "The weather is sunny with a temperature of 30 degrees Celsius.",
            });
            info!("Success: {:?}", result);
            result
        } else {
            let result = json!({
                "status": "error",
                "error_message": format!("Weather information for ('{}','{}') is not available.", latitude, longitude),
            });
            warn!("Error: {:?}", result);
            result
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
    env_logger::init();
    let cli = Args::parse();

    info!("Starting weather service");
    let service = WeatherService::new(&cli.tool_url).serve(stdio()).await.inspect_err(|e| {
        error!("serving error: {:?}", e);
    })?;
    info!("Initialized weather service");
    service.waiting().await?;
    info!("Stopping weather service");
    Ok(())
}
