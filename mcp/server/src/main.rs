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

#[derive(Clone, Default)]
pub struct WeatherService;

#[tool(tool_box)]
impl WeatherService {
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
        const EPSILON: f32 = 1e-5;
        let result = if (latitude.abs() < EPSILON) && (longitude.abs() < EPSILON) {
            json!({
                "status": "success",
                "weather": "The weather is sunny with a temperature of 30 degrees Celsius.",
            })
        } else {
            json!({
                "status": "error",
                "error_message": format!("Weather information for ('{}','{}') is not available.", latitude, longitude),
            })
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
    let service = WeatherService::default().serve(stdio()).await.inspect_err(|e| {
        println!("serving error: {:?}", e);
    })?;
    service.waiting().await?;
    Ok(())
}
