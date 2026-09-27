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

use core::net::SocketAddr;
use std::path::PathBuf;

use anyhow::Context;
use clap::Parser;
use oak_trusted_agent_lib::{
    AgentError, ModelProxyPlan, ProcessSpawner, ProxyBinaryPaths, ProxyProcessSpec,
    plan_mcp_proxies, start_proxy_mesh,
};
use tokio::{
    net::TcpListener,
    process::{Child, Command},
    task::JoinSet,
};

#[derive(Parser, Debug)]
#[command(author, version, about = "Oak Trusted Agent container entrypoint and host")]
struct Args {
    /// Local socket address where the agent backend listens behind the inbound
    /// `oak_proxy_server`.
    #[arg(long, env = "AGENT_LISTEN_ADDRESS", default_value = "127.0.0.1:8081")]
    listen_address: SocketAddr,

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

    // Bind the local agent backend port behind `oak_proxy_server`.
    // TODO: b/429197818 - Replace placeholder listener with the Wasmtime host
    // executing `//oak_trusted_agent/sandbox:adk_agent_ts` against
    // `model_plan.local_model_url()` and `local_mcp_urls`.
    let listener =
        TcpListener::bind(args.listen_address).await.context("binding agent backend listener")?;
    log::info!("listening for inbound agent requests on {}", args.listen_address);

    tokio::select! {
        Some(join_result) = proxy_tasks.join_next() => {
            let (label, status) = join_result.context("joining proxy child task")?;
            anyhow::bail!("proxy process '{label}' exited unexpectedly with status {status:?}");
        }
        accept_result = run_placeholder_backend(listener) => {
            accept_result.context("running placeholder agent backend")
        }
    }
}

async fn run_placeholder_backend(listener: TcpListener) -> anyhow::Result<()> {
    loop {
        let (_stream, peer_addr) =
            listener.accept().await.context("accepting connection from oak_proxy_server")?;
        log::info!("accepted connection from oak_proxy_server at {peer_addr}");
    }
}
