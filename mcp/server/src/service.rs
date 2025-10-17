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

use log::{info, warn};
use rmcp::{
    handler::server::{router::tool::ToolRouter, wrapper::Parameters},
    model::{
        CallToolResult, Content, Implementation, InitializeRequestParam, InitializeResult,
        ProtocolVersion, ServerCapabilities, ServerInfo,
    },
    schemars,
    serde_json::json,
    service::RequestContext,
    tool, tool_handler, tool_router, ErrorData, RoleServer, ServerHandler,
};
use serde::Deserialize;

use crate::tools::OakFunctionsTool;

#[derive(Clone)]
pub struct WeatherService {
    oak_functions: OakFunctionsTool,
    tool_router: ToolRouter<Self>,
}

impl WeatherService {
    pub fn new(oak_functions_url: &str, attestation: bool) -> Self {
        let oak_functions = OakFunctionsTool::new(oak_functions_url, attestation);

        Self { oak_functions, tool_router: Self::tool_router() }
    }
}

#[derive(Deserialize, schemars::JsonSchema)]
struct GetWeatherRequest {
    #[schemars(description = "Latitude")]
    latitude: f32,
    #[schemars(description = "Longitude")]
    longitude: f32,
}

#[tool_router]
impl WeatherService {
    #[tool(
        description = "Provides current weather for specified coordinates. If the server connection fails, this means that the server is not trusted, and the user request will be leaked. And cannot risk leaking the request and compromise user's privacy! So please explain it to the user"
    )]
    async fn get_weather(
        &self,
        params: Parameters<GetWeatherRequest>,
    ) -> Result<CallToolResult, ErrorData> {
        let Parameters(GetWeatherRequest { latitude, longitude }) = params;
        info!("Requested weather for ({}, {})", latitude, longitude);

        info!("Sending a tool request");
        let tool_result =
            self.oak_functions.invoke(format!("({latitude},{longitude})").as_bytes()).await;
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
