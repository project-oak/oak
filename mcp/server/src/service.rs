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
    ErrorData, RoleServer, ServerHandler,
    handler::server::{router::tool::ToolRouter, wrapper::Parameters},
    model::{
        CallToolResult, Content, Implementation, InitializeRequestParam, InitializeResult,
        ProtocolVersion, ServerCapabilities, ServerInfo,
    },
    schemars,
    serde_json::json,
    service::RequestContext,
    tool, tool_handler, tool_router,
};
use serde::Deserialize;

use crate::tools::OakFunctionsTool;

const REQUEST_DESC: &str =
    "Get activity request. Needs to be formatted as a city name (e.g., LONDON).";
const INSTRUCTIONS: &str = "Activity server that can provide activity information based on a city.";

#[derive(Clone)]
pub struct Service {
    oak_functions: OakFunctionsTool,
    tool_router: ToolRouter<Self>,
}

impl Service {
    pub fn new(oak_functions_url: &str, attestation: bool) -> Self {
        let oak_functions = OakFunctionsTool::new(oak_functions_url, attestation);
        Self { oak_functions, tool_router: Self::tool_router() }
    }
}

#[derive(Deserialize, schemars::JsonSchema)]
struct GetRequest {
    #[schemars(description = REQUEST_DESC)]
    key: String,
}

#[tool_router]
impl Service {
    #[tool(description = "Provides activity information")]
    async fn get(&self, params: Parameters<GetRequest>) -> Result<CallToolResult, ErrorData> {
        let Parameters(GetRequest { key }) = params;
        info!("Requested the following key: {}", key);

        info!("Sending a tool request");
        let tool_result = self.oak_functions.invoke(key.as_bytes()).await;
        info!("Tool result: {:?}", tool_result);
        let result = match tool_result {
            Ok(tool_response_bytes) => {
                if !tool_response_bytes.is_empty() {
                    let tool_response = String::from_utf8(tool_response_bytes)
                        .expect("unable to convert tool response bytes to string");
                    info!("Received a tool response: {}", tool_response);
                    json!({
                        "status": "success",
                        "response": tool_response,
                    })
                } else {
                    json!({
                        "status": "error",
                        "response": format!("No entry with the key: {}", key),
                    })
                }
            }
            Err(err) => {
                warn!("Received an error: {:?}", err);
                json!({
                    "status": "error",
                    "error_message": "Couldn't verify server attestation",
                })
            }
        };

        let result = Content::json(result).expect("couldn't serialize JSON resuls");
        Ok(CallToolResult::success(vec![result]))
    }
}

#[tool_handler]
impl ServerHandler for Service {
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: ProtocolVersion::V_2025_06_18,
            capabilities: ServerCapabilities::builder().enable_tools().build(),
            server_info: Implementation::from_build_env(),
            instructions: Some(INSTRUCTIONS.into()),
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
