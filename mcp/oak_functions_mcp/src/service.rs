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
use oak_functions_service::{instance::OakFunctionsInstance, Handler};
use oak_proto_rust::oak::functions::{
    extend_next_lookup_data_request::Data, ExtendNextLookupDataRequest,
    FinishNextLookupDataRequest, InitializeRequest, LookupDataChunk, ReserveRequest,
};
use rmcp::{
    model::{Implementation, ProtocolVersion, ServerCapabilities, ServerInfo},
    tool_handler, tool_router, ServerHandler,
};

const INSTRUCTIONS: &str = "An Oak Functions MCP server that provides sandboxing for arbitrary stateless logic that can be invoked via a tool call.";

use rmcp::handler::server::router::tool::ToolRouter;

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

// TODO: b/469747147 - Provide an `invoke` method that invokes the underlying
// Oak Functions instance.
#[tool_router]
impl<H> OakFunctionsMcpService<H>
where
    H: Handler + 'static,
    H::HandlerType: Send + Sync,
{
}

#[tool_handler]
impl<H> ServerHandler for OakFunctionsMcpService<H>
where
    H: Handler + 'static,
    H::HandlerType: Send + Sync,
{
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: ProtocolVersion::V_2025_06_18,
            capabilities: ServerCapabilities::builder().build(),
            server_info: Implementation::from_build_env(),
            instructions: Some(INSTRUCTIONS.into()),
        }
    }
}
