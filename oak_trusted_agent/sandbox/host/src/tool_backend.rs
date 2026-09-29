//
// Copyright 2026 The Project Oak Authors
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

//! Tool backends that serve the guest's `oak:agent/tools` imports.

use std::{
    collections::HashMap,
    io::{BufRead, BufReader},
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};

use anyhow::{Context, bail};
use serde_json::{Value, json};

use crate::ToolDescription;

/// MCP protocol version requested during initialization.
const MCP_PROTOCOL_VERSION: &str = "2025-06-18";

/// Lists and executes the tools exposed to the agent guest.
pub trait ToolBackend: Send + Sync {
    fn list_tools(&self) -> Vec<ToolDescription>;

    /// Calls tool `name` with JSON-encoded `arguments`, returning the result as
    /// a string (JSON when the tool returns structured content).
    fn call_tool(&self, name: &str, arguments: &str) -> anyhow::Result<String>;
}

/// Tool backend that exposes no tools.
pub struct NoTools;

impl ToolBackend for NoTools {
    fn list_tools(&self) -> Vec<ToolDescription> {
        Vec::new()
    }

    fn call_tool(&self, name: &str, _arguments: &str) -> anyhow::Result<String> {
        bail!("no tool backend is configured to handle tool `{name}`")
    }
}

/// Tool backend that combines the tools of several backends and routes each
/// call to the backend that exposes the tool.
pub struct MultiToolBackend {
    backends: Vec<Box<dyn ToolBackend>>,
    routes: HashMap<String, usize>,
    tools: Vec<ToolDescription>,
}

impl MultiToolBackend {
    /// Combines `backends`. Fails if more than one backend exposes a tool with
    /// the same name, because calls to it could not be routed unambiguously.
    pub fn new(backends: Vec<Box<dyn ToolBackend>>) -> anyhow::Result<Self> {
        let mut routes = HashMap::new();
        let mut tools = Vec::new();
        for (index, backend) in backends.iter().enumerate() {
            for tool in backend.list_tools() {
                if routes.insert(tool.name.clone(), index).is_some() {
                    bail!("tool `{}` is exposed by more than one tool backend", tool.name);
                }
                tools.push(tool);
            }
        }
        Ok(Self { backends, routes, tools })
    }
}

impl ToolBackend for MultiToolBackend {
    fn list_tools(&self) -> Vec<ToolDescription> {
        self.tools.clone()
    }

    fn call_tool(&self, name: &str, arguments: &str) -> anyhow::Result<String> {
        let index = *self.routes.get(name).with_context(|| format!("unknown tool `{name}`"))?;
        self.backends[index].call_tool(name, arguments)
    }
}

/// Tool backend for an MCP server using the Streamable HTTP transport, as
/// served behind an Oak Proxy client.
///
/// The tool list is fetched once when connecting and cached.
pub struct McpToolBackend {
    agent: ureq::Agent,
    url: String,
    session_id: Option<String>,
    protocol_version: String,
    next_id: AtomicU64,
    tools: Vec<ToolDescription>,
}

impl McpToolBackend {
    /// Initializes an MCP session with the server at `url` and fetches its
    /// tools.
    pub fn connect(url: &str, timeout: Duration) -> anyhow::Result<Self> {
        let mut backend = Self {
            agent: ureq::AgentBuilder::new().timeout(timeout).build(),
            url: url.to_string(),
            session_id: None,
            protocol_version: MCP_PROTOCOL_VERSION.to_string(),
            next_id: AtomicU64::new(1),
            tools: Vec::new(),
        };

        let id = backend.next_id.fetch_add(1, Ordering::Relaxed);
        let response = backend.post(&json!({
            "jsonrpc": "2.0",
            "id": id,
            "method": "initialize",
            "params": {
                "protocolVersion": MCP_PROTOCOL_VERSION,
                "capabilities": {},
                "clientInfo": {"name": "oak_trusted_agent", "version": "0.1.0"},
            },
        }))?;
        backend.session_id = response.header("mcp-session-id").map(str::to_string);
        let initialize_result =
            read_json_rpc_result(response, id).context("MCP `initialize` request failed")?;
        if let Some(version) = initialize_result["protocolVersion"].as_str() {
            backend.protocol_version = version.to_string();
        }
        backend.post(&json!({"jsonrpc": "2.0", "method": "notifications/initialized"}))?;

        let tools_result = backend.request("tools/list", json!({}))?;
        backend.tools = tools_result["tools"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|tool| {
                Ok(ToolDescription {
                    name: tool["name"].as_str().context("MCP tool is missing `name`")?.to_string(),
                    description: tool["description"].as_str().unwrap_or_default().to_string(),
                    input_schema: tool["inputSchema"].to_string(),
                })
            })
            .collect::<anyhow::Result<_>>()?;
        Ok(backend)
    }

    fn post(&self, body: &Value) -> anyhow::Result<ureq::Response> {
        let mut request = self
            .agent
            .post(&self.url)
            .set("Content-Type", "application/json")
            .set("Accept", "application/json, text/event-stream");
        if let Some(session_id) = &self.session_id {
            request = request
                .set("Mcp-Session-Id", session_id)
                .set("MCP-Protocol-Version", &self.protocol_version);
        }
        request.send_string(&body.to_string()).map_err(|e| match e {
            ureq::Error::Status(code, response) => anyhow::anyhow!(
                "MCP server returned HTTP {code}: {}",
                response.into_string().unwrap_or_default()
            ),
            other => anyhow::Error::new(other).context("failed to reach MCP server"),
        })
    }

    fn request(&self, method: &str, params: Value) -> anyhow::Result<Value> {
        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        let response =
            self.post(&json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}))?;
        read_json_rpc_result(response, id).with_context(|| format!("MCP `{method}` request failed"))
    }
}

impl ToolBackend for McpToolBackend {
    fn list_tools(&self) -> Vec<ToolDescription> {
        self.tools.clone()
    }

    fn call_tool(&self, name: &str, arguments: &str) -> anyhow::Result<String> {
        let arguments: Value =
            serde_json::from_str(arguments).context("tool arguments are not valid JSON")?;
        let result = self.request("tools/call", json!({"name": name, "arguments": arguments}))?;
        let text = result["content"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|content| content["text"].as_str())
            .collect::<Vec<_>>()
            .join("\n");
        if result["isError"].as_bool() == Some(true) {
            bail!("tool `{name}` failed: {text}");
        }
        match result.get("structuredContent") {
            Some(structured) if !structured.is_null() => Ok(structured.to_string()),
            _ => Ok(text),
        }
    }
}

/// Reads the JSON-RPC response with the given `id`, which the server may send
/// either as a JSON body or as an event in an SSE stream.
fn read_json_rpc_result(response: ureq::Response, id: u64) -> anyhow::Result<Value> {
    let message = if response.content_type() == "text/event-stream" {
        read_sse_message(BufReader::new(response.into_reader()), id)?
    } else {
        serde_json::from_str(&response.into_string()?).context("invalid JSON-RPC response")?
    };
    if let Some(error) = message.get("error") {
        bail!("JSON-RPC error: {error}");
    }
    message.get("result").cloned().context("JSON-RPC response is missing `result`")
}

/// Returns the first SSE event whose data is a JSON-RPC message with `id`.
fn read_sse_message(reader: impl BufRead, id: u64) -> anyhow::Result<Value> {
    let mut data = String::new();
    for line in reader.lines().chain(std::iter::once(Ok(String::new()))) {
        let line = line.context("failed to read SSE stream")?;
        if let Some(chunk) = line.strip_prefix("data:") {
            data.push_str(chunk.trim_start());
        } else if line.is_empty() && !data.is_empty() {
            let message: Value = serde_json::from_str(&data).context("invalid SSE event data")?;
            if message["id"] == json!(id) {
                return Ok(message);
            }
            data.clear();
        }
    }
    bail!("SSE stream ended without a response to request {id}")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tool backend exposing `names`, whose calls return `<backend>:<name>`.
    struct NamedTools {
        backend: &'static str,
        names: Vec<&'static str>,
    }

    impl ToolBackend for NamedTools {
        fn list_tools(&self) -> Vec<ToolDescription> {
            self.names
                .iter()
                .map(|name| ToolDescription {
                    name: name.to_string(),
                    description: String::new(),
                    input_schema: "{}".to_string(),
                })
                .collect()
        }

        fn call_tool(&self, name: &str, _arguments: &str) -> anyhow::Result<String> {
            Ok(format!("{}:{name}", self.backend))
        }
    }

    #[test]
    fn test_multi_tool_backend_routes_calls() {
        let backend = MultiToolBackend::new(vec![
            Box::new(NamedTools { backend: "a", names: vec!["lookup", "search"] }),
            Box::new(NamedTools { backend: "b", names: vec!["book"] }),
        ])
        .unwrap();

        let names: Vec<_> = backend.list_tools().into_iter().map(|tool| tool.name).collect();
        assert_eq!(names, ["lookup", "search", "book"]);
        assert_eq!(backend.call_tool("search", "{}").unwrap(), "a:search");
        assert_eq!(backend.call_tool("book", "{}").unwrap(), "b:book");
        assert!(backend.call_tool("missing", "{}").is_err());
    }

    #[test]
    fn test_multi_tool_backend_rejects_duplicate_tools() {
        let result = MultiToolBackend::new(vec![
            Box::new(NamedTools { backend: "a", names: vec!["lookup"] }),
            Box::new(NamedTools { backend: "b", names: vec!["lookup"] }),
        ]);

        assert!(result.is_err());
    }

    #[test]
    fn test_read_sse_message_skips_other_events() {
        let stream = "id: 0\nretry: 3000\ndata:\n\n\
                      data: {\"jsonrpc\":\"2.0\",\"method\":\"notifications/progress\"}\n\n\
                      data: {\"jsonrpc\":\"2.0\",\"id\":3,\"result\":{\"ok\":true}}\n\n";

        let message = read_sse_message(stream.as_bytes(), 3).unwrap();

        assert_eq!(message["result"], json!({"ok": true}));
    }

    #[test]
    fn test_read_sse_message_without_trailing_blank_line() {
        let stream = "data: {\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{}}";
        assert!(read_sse_message(stream.as_bytes(), 1).is_ok());
    }

    #[test]
    fn test_read_sse_message_missing_response() {
        let stream = "data: {\"jsonrpc\":\"2.0\",\"id\":2,\"result\":{}}\n\n";
        assert!(read_sse_message(stream.as_bytes(), 1).is_err());
    }
}
