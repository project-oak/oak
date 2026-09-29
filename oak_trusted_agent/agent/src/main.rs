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

//! Oak Trusted Agent container entrypoint and host.
//!
//! Fetches the agent Wasm component and model configuration from
//! operator-provided URLs, loads the component into an [`AgentSandbox`],
//! starts the Oak Proxy mesh and serves the `TrustedAgentService` streaming
//! gRPC interface behind the inbound `oak_proxy_server`.
//!
//! The gRPC interface is plaintext and unattested, so it only binds to a
//! loopback address. Clients reach it through the inbound `oak_proxy_server`,
//! which terminates the attested, end-to-end encrypted Oak Session and forwards
//! the decrypted byte stream to `--listen-address`.
//!
//! In the other direction, the sandbox's model calls go to the Ollama API
//! served by the model `oak_proxy_client`, and its tool calls go to the MCP
//! servers served by the MCP `oak_proxy_client`s. Both tunnel over attested Oak
//! Sessions to the remote backends.

use core::{net::SocketAddr, time::Duration};
use std::{io::Read, path::PathBuf, sync::Arc};

use anyhow::{Context, ensure};
use clap::Parser;
use oak_grpc::oak::trusted_agent::v1::trusted_agent_service_server::TrustedAgentServiceServer;
use oak_trusted_agent_lib::{
    AgentError, ModelConfig, ModelConfigProvider, ModelProxyPlan, ProcessSpawner, ProxyBinaryPaths,
    ProxyProcessSpec, plan_mcp_proxies, start_proxy_mesh,
};
use oak_trusted_agent_sandbox::{
    AgentSandbox, HostConfig, McpToolBackend, ModelInfo, ModelProvider, MultiToolBackend,
    OllamaModelBackend, ToolBackend,
};
use oak_trusted_agent_server::TrustedAgentServiceImpl;
use tokio::{
    net::TcpListener,
    process::{Child, Command},
    task::JoinSet,
};
use tokio_stream::wrappers::TcpListenerStream;
use tonic::transport::Server;

/// Upper bound on the time spent fetching each startup resource.
const FETCH_TIMEOUT: Duration = Duration::from_secs(60);

/// Timeout for each model and tool request. CPU-only model servers can take
/// minutes to answer.
const BACKEND_TIMEOUT: Duration = Duration::from_secs(300);

/// How long to keep retrying the initial connection to each MCP server. The
/// MCP `oak_proxy_client`s start concurrently with the agent and must complete
/// an attested handshake with the remote server first.
const MCP_CONNECT_DEADLINE: Duration = Duration::from_secs(120);
const MCP_CONNECT_RETRY_INTERVAL: Duration = Duration::from_secs(1);

#[derive(Parser, Debug)]
#[command(author, version, about = "Oak Trusted Agent container entrypoint and host")]
struct Args {
    /// Local socket address where the agent backend listens behind the inbound
    /// `oak_proxy_server`. Must be a loopback address.
    #[arg(long, env = "AGENT_LISTEN_ADDRESS", default_value = "127.0.0.1:8081")]
    listen_address: SocketAddr,

    /// URL (e.g. a GCS object URL) from which the agent Wasm component run in
    /// the sandbox is fetched at startup.
    #[arg(long, env = "WASM_URL")]
    wasm_url: String,

    /// URL from which the JSON model configuration is fetched at startup, e.g.
    /// `{"name": "gemma4:e2b-it-qat", "provider": "ollama"}`. Only the `ollama`
    /// provider has a backend so far.
    #[arg(long, env = "MODEL_CONFIG_URL")]
    model_config_url: String,

    /// Remote WebSocket URL (`ws://<ip>:<port>`) of the attested Model server's
    /// `oak_proxy_server`.
    #[arg(long, env = "MODEL_PROXY_URL")]
    model_proxy_url: String,

    /// Local port where the Model `oak_proxy_client` listens inside the
    /// container.
    #[arg(long, default_value_t = 11434)]
    model_local_port: u16,

    /// Comma-separated list of remote WebSocket URLs (`ws://<ip>:<port>`) for
    /// attested MCP tool servers.
    #[arg(long, env = "MCP_PROXY_URLS", value_delimiter = ',')]
    mcp_proxy_urls: Vec<String>,

    /// Starting local port (`8090`, `8091`, ...) allocated to outbound MCP
    /// `oak_proxy_client` instances.
    #[arg(long, default_value_t = 8090)]
    mcp_base_port: u16,

    /// Optional URL from which the agent host fetches the system prompt at
    /// startup.
    #[arg(long, env = "SYSTEM_PROMPT_URL")]
    system_prompt_url: Option<String>,

    /// Path to the `oak_proxy_server` binary.
    #[arg(long, default_value = "/bin/server")]
    proxy_server_bin: PathBuf,

    /// Path to the inbound `oak_proxy_server` TOML configuration file.
    #[arg(long, default_value = "/etc/proxy_server.toml")]
    proxy_server_config: PathBuf,

    /// Path to the `oak_proxy_client` binary.
    #[arg(long, default_value = "/bin/client")]
    proxy_client_bin: PathBuf,

    /// Path to the outbound Model `oak_proxy_client` TOML configuration file.
    #[arg(long, default_value = "/etc/model_proxy_client.toml")]
    model_proxy_client_config: PathBuf,

    /// Path to the outbound MCP `oak_proxy_client` TOML configuration template.
    #[arg(long, default_value = "/etc/mcp_proxy_client.toml")]
    mcp_proxy_client_config: PathBuf,

    /// Directory where `oak_proxy_client` instances write peer attestation
    /// evidence protobufs.
    #[arg(long, default_value = "/tmp")]
    attestation_dir: PathBuf,
}

/// Maps the provider of a fetched [`ModelConfig`] to the WIT `model-provider`
/// enum exposed to the sandbox.
fn to_sandbox_provider(provider: ModelConfigProvider) -> ModelProvider {
    match provider {
        ModelConfigProvider::Ollama => ModelProvider::Ollama,
        ModelConfigProvider::Gemini => ModelProvider::Gemini,
    }
}

/// Fetches the body of `url` over HTTP(S), e.g. an object in a GCS bucket.
///
/// This blocks the calling thread. It is only called at startup, before the
/// server and the proxy mesh run, so there are no other tasks to starve.
fn fetch_url(url: &str) -> anyhow::Result<Vec<u8>> {
    let fetch = || -> anyhow::Result<Vec<u8>> {
        let agent = ureq::AgentBuilder::new().timeout(FETCH_TIMEOUT).build();
        let response = agent.get(url).call()?;
        let mut bytes = Vec::new();
        response.into_reader().read_to_end(&mut bytes)?;
        Ok(bytes)
    };
    fetch().with_context(|| format!("fetching {url}"))
}

/// Connects to the MCP server at `url`, retrying until
/// [`MCP_CONNECT_DEADLINE`] while its `oak_proxy_client` comes up.
async fn connect_mcp_server(url: &str) -> anyhow::Result<McpToolBackend> {
    let deadline = tokio::time::Instant::now() + MCP_CONNECT_DEADLINE;
    loop {
        let attempt_url = url.to_string();
        // Connecting performs blocking HTTP requests.
        let result = tokio::task::spawn_blocking(move || {
            McpToolBackend::connect(&attempt_url, BACKEND_TIMEOUT)
        })
        .await?;
        match result {
            Ok(backend) => {
                let names: Vec<_> =
                    backend.list_tools().into_iter().map(|tool| tool.name).collect();
                log::info!("connected to MCP server at {url} with tools {names:?}");
                return Ok(backend);
            }
            Err(err) if tokio::time::Instant::now() < deadline => {
                log::warn!("connecting to MCP server at {url} failed, retrying: {err:#}");
                tokio::time::sleep(MCP_CONNECT_RETRY_INTERVAL).await;
            }
            Err(err) => return Err(err.context(format!("connecting to MCP server at {url}"))),
        }
    }
}

struct TokioProcessSpawner;

impl ProcessSpawner for TokioProcessSpawner {
    type Handle = (String, Child);

    fn spawn(&mut self, spec: &ProxyProcessSpec) -> Result<Self::Handle, AgentError> {
        let label = format!("{} {}", spec.program.display(), spec.args.join(" "));
        let mut command = Command::new(&spec.program);
        command.args(&spec.args).kill_on_drop(true);
        let child = command.spawn().map_err(|err| AgentError::ProcessSpawn {
            program: spec.program.display().to_string(),
            reason: err.to_string(),
        })?;
        Ok((label, child))
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let args = Args::parse();

    // Refuse to expose the plaintext interface beyond the host, so that the
    // only ingress path is the attested Oak Session terminated by the inbound
    // `oak_proxy_server`.
    ensure!(
        args.listen_address.ip().is_loopback(),
        "--listen-address must be a loopback address so that the agent is only reachable through \
         the inbound oak_proxy_server, got {}",
        args.listen_address
    );

    // Fetch the agent and its configuration, load the sandbox and bind the
    // backend port before starting the proxy mesh, so that configuration errors
    // fail fast without spawning children.
    let wasm_bytes = fetch_url(&args.wasm_url).context("loading agent Wasm component")?;
    log::info!("fetched agent Wasm component from {} ({} bytes)", args.wasm_url, wasm_bytes.len());
    let model_config_bytes = fetch_url(&args.model_config_url).context("loading model config")?;
    let model_config = ModelConfig::from_json(&model_config_bytes)
        .with_context(|| format!("parsing model config from {}", args.model_config_url))?;
    log::info!("fetched model config from {}: {:?}", args.model_config_url, model_config);
    ensure!(
        model_config.provider == ModelConfigProvider::Ollama,
        "model provider {:?} is not supported yet; only the Ollama backend is available",
        model_config.provider
    );

    let sandbox = AgentSandbox::new(&wasm_bytes).context("creating agent sandbox")?;
    let listener =
        TcpListener::bind(args.listen_address).await.context("binding agent backend listener")?;

    let model_plan = ModelProxyPlan::new(&args.model_proxy_url, args.model_local_port)
        .context("planning model oak_proxy_client")?;
    let mcp_plans =
        plan_mcp_proxies(&args.mcp_proxy_urls, args.mcp_base_port, &args.attestation_dir)
            .context("planning mcp oak_proxy_client instances")?;

    let paths = ProxyBinaryPaths {
        server_bin: args.proxy_server_bin,
        server_config: args.proxy_server_config,
        client_bin: args.proxy_client_bin,
        model_client_config: args.model_proxy_client_config,
        mcp_client_config: args.mcp_proxy_client_config,
    };

    let mut spawner = TokioProcessSpawner;
    let children = start_proxy_mesh(&mut spawner, &paths, &model_plan, &mcp_plans)
        .context("starting oak_proxy mesh")?;

    let local_mcp_urls: Vec<String> =
        mcp_plans.iter().map(|plan| plan.local_mcp_url().to_string()).collect();
    log::info!(
        "started oak_proxy mesh: model_url={}, local_mcp_urls=[{}], system_prompt_url={:?}",
        model_plan.local_model_url(),
        local_mcp_urls.join(", "),
        args.system_prompt_url
    );

    let mut proxy_tasks = JoinSet::new();
    for (label, mut child) in children {
        proxy_tasks.spawn(async move {
            let status = child.wait().await;
            (label, status)
        });
    }

    let mut tool_backends: Vec<Box<dyn ToolBackend>> = Vec::new();
    for url in &local_mcp_urls {
        tool_backends.push(Box::new(connect_mcp_server(url).await?));
    }
    let host_config = HostConfig {
        model_info: ModelInfo {
            name: model_config.name.clone(),
            provider: to_sandbox_provider(model_config.provider),
        },
        model_backend: Arc::new(OllamaModelBackend::new(
            model_plan.local_model_url().as_str(),
            BACKEND_TIMEOUT,
        )),
        tool_backend: Arc::new(MultiToolBackend::new(tool_backends)?),
    };
    let service = TrustedAgentServiceImpl::new(sandbox, host_config);

    log::info!(
        "serving TrustedAgentService on {} (model: {}, provider: {:?})",
        listener.local_addr()?,
        model_config.name,
        model_config.provider
    );
    let server = Server::builder()
        .add_service(TrustedAgentServiceServer::new(service))
        .serve_with_incoming(TcpListenerStream::new(listener));

    tokio::select! {
        Some(join_result) = proxy_tasks.join_next() => {
            let (label, status) = join_result.context("joining proxy child task")?;
            anyhow::bail!("proxy process '{label}' exited unexpectedly with status {status:?}");
        }
        serve_result = server => {
            serve_result.context("serving TrustedAgentService")
        }
    }
}
