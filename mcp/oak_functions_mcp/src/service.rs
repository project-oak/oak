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

use std::sync::OnceLock;

use anyhow::{Context, Result};
use log::info;
use oak_functions_service::{instance::OakFunctionsInstance, Handler};
use oak_proto_rust::oak::functions::{
    extend_next_lookup_data_request::Data, ExtendNextLookupDataRequest,
    FinishNextLookupDataRequest, InitializeRequest, LookupDataChunk, ReserveRequest,
};
use rmcp::{
    handler::server::wrapper::Parameters,
    model::{
        Implementation, InitializeRequestParam, InitializeResult, ServerCapabilities, ServerInfo,
    },
    schemars,
    schemars::JsonSchema,
    service::RequestContext,
    tool, tool_handler, tool_router, ErrorData, RoleServer, ServerHandler,
};
use serde::{Deserialize, Serialize};

const INSTRUCTIONS: &str = "An Oak Functions MCP server that provides sandboxing for arbitrary stateless logic that can be invoked via a tool call.";

use rmcp::handler::server::router::tool::ToolRouter;

// Request structure for invoking Oak Functions. Right now this is specially
// suited to key, value lookups where the keys are integers from 1-1000
// (inclusive). TODO: b/469747147 - Accept this as an arguement or config from
// the operator.
#[derive(Serialize, Deserialize, JsonSchema)]
#[schemars(description = "Request to invoke Oak Functions with a lookup key")]
struct OakFunctionsMcpRequest {
    /// The lookup key. Must be a string containing only an integer between 1
    /// and 1000 (inclusive).
    #[schemars(
        description = "The lookup key. Must be a string containing only an integer value between 1 and 1000 (inclusive). For example: \"1\", \"500\", \"1000\". Do not include any other characters."
    )]
    key: String,
}

#[derive(Serialize, Deserialize, JsonSchema)]
struct OakFunctionsMcpResponse {
    value: String,
}

pub struct OakFunctionsMcpService<H: Handler> {
    tool_router: ToolRouter<Self>,
    handler_config: H::HandlerConfig,
    oak_functions_instance: OnceLock<OakFunctionsInstance<H>>,
}

impl<H: Handler + 'static> OakFunctionsMcpService<H>
where
    H::HandlerType: Send + Sync,
{
    pub fn new(handler_config: H::HandlerConfig) -> Self {
        Self {
            tool_router: Self::tool_router(),
            handler_config,
            oak_functions_instance: OnceLock::new(),
        }
    }

    // Initializes the Oak Functions instance. This can only be done once; all
    // subsequent calls will fail.
    pub fn initialize(&self, initialize_request: InitializeRequest) -> Result<()> {
        info!("Initializing Oak Functions instance");
        if self.oak_functions_instance.get().is_some() {
            anyhow::bail!("instance already initialized");
        }
        let instance =
            OakFunctionsInstance::new(&initialize_request, None, self.handler_config.clone())
                .context("Failed to initialize Oak Function MCP server.")?;
        self.oak_functions_instance
            .set(instance)
            .map_err(|_| anyhow::anyhow!("instance already initialized"))?;
        Ok(())
    }

    // Loads lookup data into the initialized Oak Functions instance. Subsequent
    // calls to this function will overwrite any prior lookup data in the Oak
    // Functions instance.
    pub fn load_lookup_data(&self, lookup_data: LookupDataChunk) -> Result<()> {
        info!("Loading lookup data");
        let guard = self.oak_functions_instance.get();
        if let Some(instance) = guard.as_ref() {
            let entry_count = lookup_data.items.len() as u64;
            let lookup_data_request =
                ExtendNextLookupDataRequest { data: Some(Data::Chunk(lookup_data)) };
            instance
                .reserve(ReserveRequest { additional_entries: entry_count })
                .context("failed to reserve lookup data entries")?;
            instance
                .extend_next_lookup_data(lookup_data_request)
                .context("failed to extend next lookup data")?;
            instance
                .finish_next_lookup_data(FinishNextLookupDataRequest {})
                .context("failed to finish loading lookup data")?;
        } else {
            anyhow::bail!("instance not initialized");
        }
        Ok(())
    }
}

#[tool_router]
impl<H> OakFunctionsMcpService<H>
where
    H: Handler + 'static,
    H::HandlerType: Send + Sync,
{
    // TODO: b/469747147 - Create an rmcp::model::Tool at startup instead of
    // utilizing the tool Macro.
    #[tool(description = "Invoke Oak Functions with a key to look up a value")]
    async fn invoke(
        &self,
        params: Parameters<OakFunctionsMcpRequest>,
    ) -> Result<String, ErrorData> {
        info!("Invoking Oak Functions");
        let Parameters(OakFunctionsMcpRequest { key }) = params;
        let guard = self.oak_functions_instance.get();
        if let Some(instance) = guard.as_ref() {
            let response = instance.handle_user_request(key.as_bytes().to_vec()).map_err(|e| {
                ErrorData::internal_error(
                    format!("Invoke failed with microRpc status: {e:?}"),
                    None,
                )
            })?;
            let result = serde_json::to_string(&OakFunctionsMcpResponse {
                value: String::from_utf8(response).expect("unable to convert response to string"),
            })
            .map_err(|e| {
                ErrorData::internal_error(format!("JSON serialization failed: {e}"), None)
            })?;
            Ok(result)
        } else {
            Err(ErrorData::internal_error("instance is not initialized".to_string(), None))
        }
    }
}

#[tool_handler]
impl<H> ServerHandler for OakFunctionsMcpService<H>
where
    H: Handler + 'static,
    H::HandlerType: Send + Sync,
{
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            server_info: Implementation::from_build_env(),
            instructions: Some(INSTRUCTIONS.into()),
            capabilities: ServerCapabilities {
                tools: Some(rmcp::model::ToolsCapability::default()),
                ..Default::default()
            },
            // Note that this uses the latest protocol version.
            ..Default::default()
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
