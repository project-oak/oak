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

//! Proxy mesh orchestration and endpoint planning for the Oak Trusted Agent.
//!
//! An Oak Trusted Agent container runs inside Confidential Space and
//! communicates exclusively over hardware-attested Oak Session tunnels managed
//! by `oak_proxy`:
//! - One inbound `oak_proxy_server` instance accepts attested client
//!   connections (on `0.0.0.0:8080` by default) and forwards plaintext traffic
//!   to the local agent backend (`127.0.0.1:8081`).
//! - One outbound `oak_proxy_client` instance connects to the attested Model
//!   server (`MODEL_PROXY_URL`) and exposes a local HTTP endpoint
//!   (`127.0.0.1:11434`) for the sandboxed agent.
//! - Zero or more outbound `oak_proxy_client` instances connect to each
//!   attested MCP tool server in `MCP_PROXY_URLS`, dynamically allocating local
//!   ports starting at `base_port` (`127.0.0.1:8090`, `127.0.0.1:8091`, ...)
//!   and exposing Streamable HTTP MCP endpoints (`http://127.0.0.1:<port>/mcp`).

use core::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::path::{Path, PathBuf};

use url::Url;

/// Errors returned while planning or launching the agent's Oak Proxy mesh.
#[derive(thiserror::Error, Debug, PartialEq, Eq)]
pub enum AgentError {
    /// A proxy URL could not be parsed as a valid URL.
    #[error("invalid proxy url '{url}': {reason}")]
    InvalidProxyUrl { url: String, reason: String },

    /// A proxy URL does not use the `ws` or `wss` WebSocket scheme required by
    /// `oak_proxy_client`.
    #[error("unsupported scheme '{scheme}' in proxy url '{url}', expected 'ws' or 'wss'")]
    UnsupportedProxyScheme { url: String, scheme: String },

    /// Computing the local port `base_port + index` overflowed `u16::MAX`.
    #[error("mcp proxy port overflow at index {index} from base port {base_port}")]
    McpPortOverflow { base_port: u16, index: usize },

    /// Spawning an `oak_proxy` child process did not succeed.
    #[error("spawning process '{program}': {reason}")]
    ProcessSpawn { program: String, reason: String },

    /// The model configuration fetched from `MODEL_CONFIG_URL` is not valid.
    #[error("invalid model config: {reason}")]
    InvalidModelConfig { reason: String },
}

/// Configuration of the model exposed to the sandboxed agent.
///
/// Fetched as JSON from `MODEL_CONFIG_URL` at startup, for example:
///
/// ```json
/// {"name": "gemma4:e2b-it-qat", "provider": "ollama"}
/// ```
#[derive(Debug, Clone, PartialEq, Eq, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ModelConfig {
    /// Name of the model, as understood by `provider`.
    pub name: String,
    /// Provider serving the model.
    pub provider: ModelConfigProvider,
}

/// Provider serving the model described by a [`ModelConfig`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ModelConfigProvider {
    Ollama,
    Gemini,
}

impl ModelConfig {
    /// Parses and validates a JSON model configuration.
    ///
    /// Unknown fields are rejected so that a misspelled key fails at startup
    /// instead of being silently ignored.
    pub fn from_json(json: &[u8]) -> Result<Self, AgentError> {
        let config: Self = serde_json::from_slice(json)
            .map_err(|err| AgentError::InvalidModelConfig { reason: err.to_string() })?;
        if config.name.trim().is_empty() {
            return Err(AgentError::InvalidModelConfig {
                reason: "model name must not be empty".to_string(),
            });
        }
        Ok(config)
    }
}

/// Command-line specification for spawning an `oak_proxy` child process.
///
/// All flags use the `--flag=value` syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProxyProcessSpec {
    /// Path to the executable binary (e.g. `/bin/server` or `/bin/client`).
    pub program: PathBuf,
    /// Command-line arguments passed to `program`.
    pub args: Vec<String>,
}

/// Validated configuration for the outbound Model `oak_proxy_client` tunnel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModelProxyPlan {
    remote_proxy_url: Url,
    local_listen_address: SocketAddr,
    local_model_url: Url,
}

impl ModelProxyPlan {
    /// Creates a validated [`ModelProxyPlan`] connecting to `remote_url` and
    /// listening locally on `127.0.0.1:<local_port>`.
    pub fn new(remote_url: &str, local_port: u16) -> Result<Self, AgentError> {
        let remote_proxy_url = parse_websocket_url(remote_url)?;
        let local_listen_address = SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), local_port);
        let local_model_url = Url::parse(&format!("http://{local_listen_address}"))
            .expect("localhost socket address always forms a valid http url");
        Ok(Self { remote_proxy_url, local_listen_address, local_model_url })
    }

    /// Remote WebSocket URL (`ws://` or `wss://`) of the attested Model server.
    pub fn remote_proxy_url(&self) -> &Url {
        &self.remote_proxy_url
    }

    /// Local socket address where the Model `oak_proxy_client` listens.
    pub fn local_listen_address(&self) -> SocketAddr {
        self.local_listen_address
    }

    /// Local HTTP base URL (`http://127.0.0.1:<port>`) that the sandboxed agent
    /// uses to query the attested Model server.
    pub fn local_model_url(&self) -> &Url {
        &self.local_model_url
    }

    /// Builds the [`ProxyProcessSpec`] to launch the Model `oak_proxy_client`.
    pub fn to_process_spec(&self, client_bin: &Path, config_path: &Path) -> ProxyProcessSpec {
        ProxyProcessSpec {
            program: client_bin.to_path_buf(),
            args: vec![
                format!("--config={}", config_path.display()),
                format!("--listen-address={}", self.local_listen_address),
                format!("--server-proxy-url={}", self.remote_proxy_url),
            ],
        }
    }
}

/// Validated configuration for a single outbound MCP `oak_proxy_client` tunnel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct McpProxyPlan {
    index: usize,
    remote_proxy_url: Url,
    local_listen_address: SocketAddr,
    local_mcp_url: Url,
    attestation_output_file: PathBuf,
}

impl McpProxyPlan {
    /// Zero-based index of this MCP server in the configured `MCP_PROXY_URLS`
    /// list.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Remote WebSocket URL (`ws://` or `wss://`) of the attested MCP server.
    pub fn remote_proxy_url(&self) -> &Url {
        &self.remote_proxy_url
    }

    /// Local socket address (`127.0.0.1:<base_port + index>`) where this MCP
    /// `oak_proxy_client` instance listens.
    pub fn local_listen_address(&self) -> SocketAddr {
        self.local_listen_address
    }

    /// Local Streamable HTTP MCP endpoint (`http://127.0.0.1:<port>/mcp`)
    /// exposed to the sandboxed agent.
    pub fn local_mcp_url(&self) -> &Url {
        &self.local_mcp_url
    }

    /// Path where `oak_proxy_client` writes the peer MCP server's attestation
    /// evidence protobuf.
    pub fn attestation_output_file(&self) -> &Path {
        &self.attestation_output_file
    }

    /// Builds the [`ProxyProcessSpec`] to launch this MCP `oak_proxy_client`.
    pub fn to_process_spec(&self, client_bin: &Path, config_path: &Path) -> ProxyProcessSpec {
        ProxyProcessSpec {
            program: client_bin.to_path_buf(),
            args: vec![
                format!("--config={}", config_path.display()),
                format!("--listen-address={}", self.local_listen_address),
                format!("--server-proxy-url={}", self.remote_proxy_url),
                format!("--attestation-output-file={}", self.attestation_output_file.display()),
            ],
        }
    }
}

/// Plans outbound `oak_proxy_client` instances for a list of remote MCP server
/// WebSocket URLs, assigning sequential localhost ports starting from
/// `base_port`.
///
/// Empty or whitespace-only entries in `mcp_proxy_urls` are skipped so that an
/// empty `MCP_PROXY_URLS=""` environment variable cleanly produces zero MCP
/// proxy plans.
pub fn plan_mcp_proxies<S: AsRef<str>>(
    mcp_proxy_urls: &[S],
    base_port: u16,
    attestation_dir: &Path,
) -> Result<Vec<McpProxyPlan>, AgentError> {
    let mut plans = Vec::new();
    for raw_url in mcp_proxy_urls.iter().map(AsRef::as_ref).map(str::trim).filter(|s| !s.is_empty())
    {
        let index = plans.len();
        let offset =
            u16::try_from(index).map_err(|_| AgentError::McpPortOverflow { base_port, index })?;
        let port = base_port
            .checked_add(offset)
            .ok_or(AgentError::McpPortOverflow { base_port, index })?;

        let remote_proxy_url = parse_websocket_url(raw_url)?;
        let local_listen_address = SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), port);
        let local_mcp_url = Url::parse(&format!("http://{local_listen_address}/mcp"))
            .expect("localhost socket address always forms a valid http url");
        let attestation_output_file = attestation_dir.join(format!("mcp_{index}_attestation.pb"));

        plans.push(McpProxyPlan {
            index,
            remote_proxy_url,
            local_listen_address,
            local_mcp_url,
            attestation_output_file,
        });
    }
    Ok(plans)
}

/// Paths to the `oak_proxy` binaries and TOML configuration files used when
/// launching the agent's proxy mesh.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProxyBinaryPaths {
    /// Path to `oak_proxy_server` (typically `/bin/server`).
    pub server_bin: PathBuf,
    /// Path to the inbound server TOML config (typically
    /// `/etc/proxy_server.toml`).
    pub server_config: PathBuf,
    /// Path to `oak_proxy_client` (typically `/bin/client`).
    pub client_bin: PathBuf,
    /// Path to the outbound model client TOML config (typically
    /// `/etc/model_proxy_client.toml`).
    pub model_client_config: PathBuf,
    /// Path to the outbound MCP client TOML config template (typically
    /// `/etc/mcp_proxy_client.toml`).
    pub mcp_client_config: PathBuf,
}

impl ProxyBinaryPaths {
    /// Builds the [`ProxyProcessSpec`] for the inbound `oak_proxy_server`.
    pub fn inbound_server_spec(&self) -> ProxyProcessSpec {
        ProxyProcessSpec {
            program: self.server_bin.clone(),
            args: vec![format!("--config={}", self.server_config.display())],
        }
    }
}

/// Abstraction over process creation so [`start_proxy_mesh`] can be unit-tested
/// with a mock spawner without launching OS processes.
pub trait ProcessSpawner {
    /// Handle representing a running child process.
    type Handle;

    /// Spawns the process described by `spec`.
    fn spawn(&mut self, spec: &ProxyProcessSpec) -> Result<Self::Handle, AgentError>;
}

/// Spawns the complete Oak Proxy mesh for the agent:
/// 1. Inbound `oak_proxy_server` fronting the agent backend.
/// 2. Outbound `oak_proxy_client` connecting to the attested Model server.
/// 3. Outbound `oak_proxy_client` instances for each planned MCP server.
pub fn start_proxy_mesh<S: ProcessSpawner>(
    spawner: &mut S,
    paths: &ProxyBinaryPaths,
    model_plan: &ModelProxyPlan,
    mcp_plans: &[McpProxyPlan],
) -> Result<Vec<S::Handle>, AgentError> {
    let mut handles = Vec::with_capacity(2 + mcp_plans.len());

    let server_spec = paths.inbound_server_spec();
    log::info!("starting inbound oak_proxy_server with config {}", paths.server_config.display());
    handles.push(spawner.spawn(&server_spec)?);

    let model_spec = model_plan.to_process_spec(&paths.client_bin, &paths.model_client_config);
    log::info!(
        "starting model oak_proxy_client on {} -> {}",
        model_plan.local_listen_address(),
        model_plan.remote_proxy_url()
    );
    handles.push(spawner.spawn(&model_spec)?);

    for mcp_plan in mcp_plans {
        let mcp_spec = mcp_plan.to_process_spec(&paths.client_bin, &paths.mcp_client_config);
        log::info!(
            "starting mcp oak_proxy_client #{} on {} -> {}",
            mcp_plan.index(),
            mcp_plan.local_listen_address(),
            mcp_plan.remote_proxy_url()
        );
        handles.push(spawner.spawn(&mcp_spec)?);
    }

    Ok(handles)
}

fn parse_websocket_url(raw_url: &str) -> Result<Url, AgentError> {
    let parsed = Url::parse(raw_url.trim()).map_err(|err| AgentError::InvalidProxyUrl {
        url: raw_url.to_string(),
        reason: err.to_string(),
    })?;
    match parsed.scheme() {
        "ws" | "wss" => Ok(parsed),
        scheme => Err(AgentError::UnsupportedProxyScheme {
            url: raw_url.to_string(),
            scheme: scheme.to_string(),
        }),
    }
}

/// Adds the operator's system prompt to a `GenerateContent`-style model
/// request from the sandboxed agent.
///
/// The system prompt goes before any `systemInstruction` the agent set itself,
/// so that the deployment's prompt (e.g. the user context of a demo) and the
/// agent's own instruction both reach the model. `systemInstruction` may be a
/// plain string or a `Content` object with text `parts`, as in the Gemini API.
pub fn add_system_prompt(request: &str, system_prompt: &str) -> anyhow::Result<String> {
    use anyhow::Context;
    use serde_json::{Value, json};

    let mut request: Value = serde_json::from_str(request).context("invalid model request JSON")?;
    let object = request.as_object_mut().context("model request is not a JSON object")?;
    let instruction = match object.remove("systemInstruction") {
        None | Some(Value::Null) => json!(system_prompt),
        Some(Value::String(text)) => json!(format!("{system_prompt}\n\n{text}")),
        Some(Value::Object(mut content)) => {
            let mut parts = vec![json!({"text": system_prompt})];
            if let Some(Value::Array(existing)) = content.remove("parts") {
                parts.extend(existing);
            }
            content.insert("parts".to_string(), Value::Array(parts));
            Value::Object(content)
        }
        Some(other) => anyhow::bail!("unsupported systemInstruction: {other}"),
    };
    object.insert("systemInstruction".to_string(), instruction);
    Ok(request.to_string())
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;
    use oak_file_utils::data_path;
    use oak_proxy_lib::config::{ClientConfig, ServerConfig, load_toml};

    use super::*;

    #[derive(Default)]
    struct MockProcessSpawner {
        spawned_specs: Vec<ProxyProcessSpec>,
    }

    impl ProcessSpawner for MockProcessSpawner {
        type Handle = usize;

        fn spawn(&mut self, spec: &ProxyProcessSpec) -> Result<Self::Handle, AgentError> {
            let id = self.spawned_specs.len();
            self.spawned_specs.push(spec.clone());
            Ok(id)
        }
    }

    #[gtest]
    fn test_plan_mcp_proxies_scales_ports_and_urls() {
        let urls = vec!["ws://10.128.0.10:8080", "wss://10.128.0.11:8080", ""];
        let plans = plan_mcp_proxies(&urls, 8090, Path::new("/tmp")).unwrap();

        assert_that!(plans.len(), eq(2));

        expect_that!(plans[0].index(), eq(0));
        expect_that!(plans[0].local_listen_address().to_string(), eq("127.0.0.1:8090"));
        expect_that!(plans[0].local_mcp_url().as_str(), eq("http://127.0.0.1:8090/mcp"));
        expect_that!(
            plans[0].attestation_output_file(),
            eq(Path::new("/tmp/mcp_0_attestation.pb"))
        );

        expect_that!(plans[1].index(), eq(1));
        expect_that!(plans[1].local_listen_address().to_string(), eq("127.0.0.1:8091"));
        expect_that!(plans[1].local_mcp_url().as_str(), eq("http://127.0.0.1:8091/mcp"));
        expect_that!(
            plans[1].attestation_output_file(),
            eq(Path::new("/tmp/mcp_1_attestation.pb"))
        );
    }

    #[gtest]
    fn test_plan_mcp_proxies_rejects_non_websocket_scheme() {
        let urls = vec!["http://10.128.0.10:8080"];
        let result = plan_mcp_proxies(&urls, 8090, Path::new("/tmp"));

        assert_that!(
            result,
            err(eq(&AgentError::UnsupportedProxyScheme {
                url: "http://10.128.0.10:8080".to_string(),
                scheme: "http".to_string(),
            }))
        );
    }

    #[gtest]
    fn test_plan_mcp_proxies_detects_port_overflow() {
        let urls = vec!["ws://10.128.0.10:8080", "ws://10.128.0.11:8080"];
        let result = plan_mcp_proxies(&urls, u16::MAX, Path::new("/tmp"));

        assert_that!(
            result,
            err(eq(&AgentError::McpPortOverflow { base_port: u16::MAX, index: 1 }))
        );
    }

    #[gtest]
    fn test_start_proxy_mesh_spawns_expected_commands() {
        let paths = ProxyBinaryPaths {
            server_bin: PathBuf::from("/bin/server"),
            server_config: PathBuf::from("/etc/proxy_server.toml"),
            client_bin: PathBuf::from("/bin/client"),
            model_client_config: PathBuf::from("/etc/model_proxy_client.toml"),
            mcp_client_config: PathBuf::from("/etc/mcp_proxy_client.toml"),
        };
        let model_plan = ModelProxyPlan::new("ws://10.128.0.2:8080", 11434).unwrap();
        let mcp_plans = plan_mcp_proxies(
            &["ws://10.128.0.3:8080", "ws://10.128.0.4:8080"],
            8090,
            Path::new("/tmp"),
        )
        .unwrap();

        let mut spawner = MockProcessSpawner::default();
        let handles = start_proxy_mesh(&mut spawner, &paths, &model_plan, &mcp_plans).unwrap();

        assert_that!(handles, eq(&vec![0, 1, 2, 3]));
        assert_that!(spawner.spawned_specs.len(), eq(4));

        expect_that!(
            spawner.spawned_specs[0],
            eq(&ProxyProcessSpec {
                program: PathBuf::from("/bin/server"),
                args: vec!["--config=/etc/proxy_server.toml".to_string()],
            })
        );
        expect_that!(
            spawner.spawned_specs[1],
            eq(&ProxyProcessSpec {
                program: PathBuf::from("/bin/client"),
                args: vec![
                    "--config=/etc/model_proxy_client.toml".to_string(),
                    "--listen-address=127.0.0.1:11434".to_string(),
                    "--server-proxy-url=ws://10.128.0.2:8080/".to_string(),
                ],
            })
        );
        expect_that!(
            spawner.spawned_specs[2],
            eq(&ProxyProcessSpec {
                program: PathBuf::from("/bin/client"),
                args: vec![
                    "--config=/etc/mcp_proxy_client.toml".to_string(),
                    "--listen-address=127.0.0.1:8090".to_string(),
                    "--server-proxy-url=ws://10.128.0.3:8080/".to_string(),
                    "--attestation-output-file=/tmp/mcp_0_attestation.pb".to_string(),
                ],
            })
        );
        expect_that!(
            spawner.spawned_specs[3],
            eq(&ProxyProcessSpec {
                program: PathBuf::from("/bin/client"),
                args: vec![
                    "--config=/etc/mcp_proxy_client.toml".to_string(),
                    "--listen-address=127.0.0.1:8091".to_string(),
                    "--server-proxy-url=ws://10.128.0.4:8080/".to_string(),
                    "--attestation-output-file=/tmp/mcp_1_attestation.pb".to_string(),
                ],
            })
        );
    }

    #[gtest]
    fn test_checked_in_proxy_toml_configs_are_valid() {
        let server_path = data_path("oak_trusted_agent/agent/config/proxy_server.toml");
        let server_config: ServerConfig =
            load_toml(server_path.to_str().unwrap()).expect("proxy_server.toml should parse");
        expect_that!(server_config.listen_address.map(|a| a.to_string()), some(eq("0.0.0.0:8080")));
        expect_that!(
            server_config.backend_address.map(|a| a.to_string()),
            some(eq("127.0.0.1:8081"))
        );
        expect_that!(server_config.attestation_generators.len(), eq(1));
        expect_that!(server_config.attestation_verifiers.len(), eq(0));

        let model_path = data_path("oak_trusted_agent/agent/config/model_proxy_client.toml");
        let model_config: ClientConfig =
            load_toml(model_path.to_str().unwrap()).expect("model_proxy_client.toml should parse");
        expect_that!(
            model_config.listen_address.map(|a| a.to_string()),
            some(eq("127.0.0.1:11434"))
        );
        expect_that!(model_config.attestation_generators.len(), eq(0));
        expect_that!(model_config.attestation_verifiers.len(), eq(1));

        let mcp_path = data_path("oak_trusted_agent/agent/config/mcp_proxy_client.toml");
        let mcp_config: ClientConfig =
            load_toml(mcp_path.to_str().unwrap()).expect("mcp_proxy_client.toml should parse");
        expect_that!(mcp_config.listen_address.map(|a| a.to_string()), some(eq("127.0.0.1:8090")));
        expect_that!(mcp_config.attestation_generators.len(), eq(0));
        expect_that!(mcp_config.attestation_verifiers.len(), eq(1));
    }

    #[gtest]
    fn test_model_config_parses_valid_json() {
        let config =
            ModelConfig::from_json(br#"{"name": "gemma4:e2b-it-qat", "provider": "ollama"}"#)
                .unwrap();
        expect_that!(
            config,
            eq(&ModelConfig {
                name: "gemma4:e2b-it-qat".to_string(),
                provider: ModelConfigProvider::Ollama,
            })
        );
    }

    #[gtest]
    fn test_model_config_rejects_invalid_json() {
        let cases: [&[u8]; 6] = [
            b"not json",
            br#"{"name": "gemma"}"#,
            br#"{"provider": "ollama"}"#,
            br#"{"name": "gemma", "provider": "unknown"}"#,
            br#"{"name": "gemma", "provider": "ollama", "extra": 1}"#,
            br#"{"name": "  ", "provider": "ollama"}"#,
        ];
        for json in cases {
            expect_that!(
                ModelConfig::from_json(json),
                err(matches_pattern!(AgentError::InvalidModelConfig { .. })),
                "{}",
                String::from_utf8_lossy(json)
            );
        }
    }

    #[googletest::test]
    fn test_add_system_prompt_without_instruction() {
        let request = add_system_prompt(r#"{"model": "m", "contents": []}"#, "Be kind.").unwrap();
        let request: serde_json::Value = serde_json::from_str(&request).unwrap();
        expect_that!(request["systemInstruction"], eq(&serde_json::json!("Be kind.")));
        expect_that!(request["model"], eq(&serde_json::json!("m")));
    }

    #[googletest::test]
    fn test_add_system_prompt_before_string_instruction() {
        let request =
            add_system_prompt(r#"{"systemInstruction": "Use tools."}"#, "Be kind.").unwrap();
        let request: serde_json::Value = serde_json::from_str(&request).unwrap();
        expect_that!(
            request["systemInstruction"],
            eq(&serde_json::json!("Be kind.\n\nUse tools."))
        );
    }

    #[googletest::test]
    fn test_add_system_prompt_before_content_instruction() {
        let request = add_system_prompt(
            r#"{"systemInstruction": {"role": "system", "parts": [{"text": "Use tools."}]}}"#,
            "Be kind.",
        )
        .unwrap();
        let request: serde_json::Value = serde_json::from_str(&request).unwrap();
        expect_that!(
            request["systemInstruction"],
            eq(&serde_json::json!({
                "role": "system",
                "parts": [{"text": "Be kind."}, {"text": "Use tools."}],
            }))
        );
    }

    #[googletest::test]
    fn test_add_system_prompt_rejects_invalid_request() {
        expect_that!(add_system_prompt("not json", "Be kind."), err(anything()));
        expect_that!(add_system_prompt(r#"{"systemInstruction": 1}"#, "Be kind."), err(anything()));
    }
}
