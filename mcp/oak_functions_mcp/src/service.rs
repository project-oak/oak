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

use std::{
    result,
    sync::{Arc, OnceLock},
};

use anyhow::{Context, Result};
use futures::future::BoxFuture;
use log::info;
use oak_functions_service::{instance::OakFunctionsInstance, Handler};
use oak_proto_rust::oak::functions::{
    extend_next_lookup_data_request::Data, ExtendNextLookupDataRequest,
    FinishNextLookupDataRequest, InitializeRequest, LookupDataChunk, ReserveRequest,
};
use rmcp::{
    handler::server::{
        router::tool::{ToolRoute, ToolRouter},
        tool::ToolCallContext,
    },
    model::{
        CallToolResult, Content, Implementation, InitializeRequestParam, InitializeResult,
        JsonObject, ServerCapabilities, ServerInfo, Tool,
    },
    service::RequestContext,
    tool_handler, ErrorData, RoleServer, ServerHandler,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;

const INSTRUCTIONS: &str = "An Oak Functions MCP server that provides sandboxing for arbitrary stateless logic that can be invoked via a tool call.";

/// Configuration for the dynamically created MCP tool.
#[derive(Clone, Debug)]
pub struct ToolConfig {
    /// Description of the tool shown to MCP clients.
    pub description: String,
    /// JSON Schema defining the expected input parameters.
    pub input_schema: Value,
}

impl Default for ToolConfig {
    fn default() -> Self {
        Self {
            description: "Invoke Oak Functions with a key to look up a value".to_string(),
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "key": {
                        "type": "string",
                        "description": "The lookup key. Must be a string containing only an integer value between 1 and 1000 (inclusive)."
                    }
                },
                "required": ["key"]
            }),
        }
    }
}

#[derive(Serialize, Deserialize)]
struct OakFunctionsMcpResponse {
    value: String,
}

pub struct OakFunctionsMcpService<H: Handler> {
    tool_router: ToolRouter<Self>,
    handler_config: H::HandlerConfig,
    oak_functions_instance: Arc<OnceLock<OakFunctionsInstance<H>>>,
}

impl<H: Handler + 'static> OakFunctionsMcpService<H>
where
    H::HandlerType: Send + Sync,
{
    /// Creates a new service with the default tool configuration.
    // TODO: b/469747147 - This should be removed once we generalize this
    // service beyond the key-value lookup.
    pub fn new(handler_config: H::HandlerConfig) -> Self {
        Self::new_with_config(handler_config, ToolConfig::default())
    }

    /// Creates a new service with a custom tool configuration.
    pub fn new_with_config(handler_config: H::HandlerConfig, tool_config: ToolConfig) -> Self {
        let oak_functions_instance = Arc::new(OnceLock::new());
        let tool_router =
            Self::create_tool_router(tool_config, Arc::clone(&oak_functions_instance));
        Self { tool_router, handler_config, oak_functions_instance }
    }

    /// Creates the tool router with dynamically configured tool.
    fn create_tool_router(
        tool_config: ToolConfig,
        instance: Arc<OnceLock<OakFunctionsInstance<H>>>,
    ) -> ToolRouter<Self> {
        // Convert the input schema Value to JsonObject
        let input_schema: JsonObject = serde_json::from_value(tool_config.input_schema)
            .expect("input_schema must be a valid JSON object");

        // Create the Tool with dynamic description and schema
        let tool = Tool::new("invoke", tool_config.description, Arc::new(input_schema));

        // Create a dynamic route with a closure that handles tool calls
        let route = ToolRoute::<Self>::new_dyn(tool, move |ctx: ToolCallContext<'_, Self>| {
            let instance = Arc::clone(&instance);
            Box::pin(async move { Self::handle_invoke(ctx, instance).await })
                as BoxFuture<'_, result::Result<CallToolResult, ErrorData>>
        });

        let mut router = ToolRouter::new();
        router.add_route(route);
        router
    }

    /// Handles the invoke tool call.
    async fn handle_invoke(
        ctx: ToolCallContext<'_, Self>,
        instance: Arc<OnceLock<OakFunctionsInstance<H>>>,
    ) -> result::Result<CallToolResult, ErrorData> {
        info!("Invoking Oak Functions");

        // Extract the key from the request arguments
        // TODO: b/469747147 - Here we fetch the contents of 'key' but this should be
        // handled by the Wasm module in the future.
        let key = ctx
            .arguments
            .as_ref()
            .and_then(|args| args.get("key"))
            .and_then(|v| v.as_str())
            .ok_or_else(|| ErrorData::invalid_params("Missing required parameter: key", None))?
            .to_string();

        let guard = instance.get();
        if let Some(oak_instance) = guard.as_ref() {
            let response =
                oak_instance.handle_user_request(key.as_bytes().to_vec()).map_err(|e| {
                    ErrorData::internal_error(
                        format!("Invoke failed with microRpc status: {e:?}"),
                        None,
                    )
                })?;
            // TODO: b/469747147 - Response should be generic JSON which is specified by the
            // tool schema.
            let result = OakFunctionsMcpResponse {
                value: String::from_utf8(response).map_err(|e| {
                    ErrorData::internal_error(
                        format!("unable to convert response to string: {e}"),
                        None,
                    )
                })?,
            };
            let content = Content::json(result).map_err(|e| {
                ErrorData::internal_error(format!("JSON serialization failed: {e}"), None)
            })?;
            Ok(CallToolResult::success(vec![content]))
        } else {
            Err(ErrorData::internal_error("instance is not initialized".to_string(), None))
        }
    }

    /// Initializes the Oak Functions instance. This can only be done once; all
    /// subsequent calls will fail.
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

    /// Loads lookup data into the initialized Oak Functions instance.
    /// Subsequent calls to this function will overwrite any prior lookup
    /// data in the Oak Functions instance.
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
