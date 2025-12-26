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

use rmcp::{
    model::{
        Implementation, InitializeRequestParam, InitializeResult, ProtocolVersion,
        ServerCapabilities, ServerInfo,
    },
    service::RequestContext,
    tool_handler, tool_router, ErrorData, RoleServer, ServerHandler,
};

const INSTRUCTIONS: &str = "An Oak Functions MCP server that provides sandboxing for arbitrary stateless logic that can be invoked via a tool call.";

use rmcp::handler::server::router::tool::ToolRouter;

#[derive(Clone)]
pub struct OakFunctionsMcpService {
    tool_router: ToolRouter<Self>,
}

impl OakFunctionsMcpService {
    pub fn new() -> Self {
        Self { tool_router: Self::tool_router() }
    }
}

impl Default for OakFunctionsMcpService {
    fn default() -> Self {
        Self::new()
    }
}

// TODO: b/469747147 - Provide an `invoke` method that invokes the underlying
// Oak Functions instance.
#[tool_router]
impl OakFunctionsMcpService {}

#[tool_handler]
impl ServerHandler for OakFunctionsMcpService {
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: ProtocolVersion::V_2025_06_18,
            capabilities: ServerCapabilities::builder().build(),
            server_info: Implementation::from_build_env(),
            instructions: Some(INSTRUCTIONS.into()),
        }
    }

    // TODO: b/469747147 - Initialize the Oak Functions instance.
    async fn initialize(
        &self,
        _request: InitializeRequestParam,
        _context: RequestContext<RoleServer>,
    ) -> Result<InitializeResult, ErrorData> {
        Ok(self.get_info())
    }
}
