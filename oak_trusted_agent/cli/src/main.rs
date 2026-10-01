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

//! Command-line client for an Oak Trusted Agent.
//!
//! `open` starts a `TrustedAgentService.Stream` RPC, which gets a dedicated
//! agent sandbox for as long as the stream is open, and then reads user
//! messages from stdin, one per line. Each message is a new turn on the same
//! stream, and the agent's reply is printed before the next prompt. Typing
//! `close`, or ending the input (Ctrl-D), closes the stream and ends the agent
//! session.
//!
//! Every `open` has its own stream and sandbox, so several can run at the same
//! time (e.g. in different terminals) without affecting each other.
//!
//! The agent is normally reached through a local Oak Proxy client, which
//! verifies the agent's attestation before forwarding any data. If the
//! attestation can't be verified, the proxy client closes the connection and
//! `open` fails.

use std::{io::Write, process::ExitCode, time::Duration};

use anyhow::{Context, anyhow};
use clap::{Parser, Subcommand};
use oak_grpc::oak::trusted_agent::v1::trusted_agent_service_client::TrustedAgentServiceClient;
use oak_proto_rust::oak::trusted_agent::v1::{
    AgentRequest, AgentResponse, UserMessage, agent_request, agent_response,
};
use tokio::{
    io::{AsyncBufReadExt, BufReader},
    sync::mpsc,
};
use tokio_stream::wrappers::ReceiverStream;
use tonic::{Streaming, transport::Channel};

/// Upper bound on opening a stream to the agent. Through an Oak Proxy client,
/// this includes the attested handshake with the agent's server proxy.
const OPEN_TIMEOUT: Duration = Duration::from_secs(60);

/// How long to wait for the agent to end the stream after it is closed.
const CLOSE_TIMEOUT: Duration = Duration::from_secs(10);

/// The input line that closes the stream.
const CLOSE_COMMAND: &str = "close";

/// Prompt shown before each user message.
const USER_PROMPT: &str = "user$ ";

/// Label printed before each agent reply.
const AGENT_LABEL: &str = "trusted-agent$ ";

#[derive(Parser, Debug)]
#[command(author, version, about = "Command-line client for an Oak Trusted Agent")]
struct Cli {
    #[command(subcommand)]
    command: CliCommand,
}

#[derive(Subcommand, Debug)]
enum CliCommand {
    /// Opens a stream to the agent and sends each line typed on stdin to it as
    /// a user message, until `close` is typed or the input ends.
    Open {
        /// URL of the agent's gRPC endpoint, usually the listen address of a
        /// local Oak Proxy client (e.g. "http://127.0.0.1:8080").
        #[arg(long, env = "OAK_TRUSTED_AGENT_URL")]
        agent_url: String,
    },
}

#[tokio::main]
async fn main() -> ExitCode {
    let cli = Cli::parse();
    let result = match cli.command {
        CliCommand::Open { agent_url } => open(&agent_url).await,
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("❌ {err:#}");
            ExitCode::FAILURE
        }
    }
}

async fn open(agent_url: &str) -> anyhow::Result<()> {
    let mut stream = tokio::time::timeout(OPEN_TIMEOUT, AgentStream::open(agent_url))
        .await
        .map_err(|_| anyhow!("timed out after {OPEN_TIMEOUT:?}"))
        .and_then(|result| result)
        .with_context(|| format!("failed to open a stream to {agent_url}"))?;
    println!("✅ Opened a stream to {agent_url}.");
    println!(
        "Type a message and press Enter to send it. Type `{CLOSE_COMMAND}` to end the session."
    );

    let mut lines = BufReader::new(tokio::io::stdin()).lines();
    loop {
        print!("{USER_PROMPT}");
        std::io::stdout().flush()?;
        let Some(line) = lines.next_line().await.context("failed to read stdin")? else {
            // The input ended (e.g. Ctrl-D): close the stream like `close` does.
            println!();
            break;
        };
        let text = line.trim();
        if text.is_empty() {
            continue;
        }
        if text == CLOSE_COMMAND {
            break;
        }
        let reply = stream.send(text.to_string()).await?;
        println!("{AGENT_LABEL}{reply}");
    }

    stream.close().await;
    println!("✅ Closed the stream.");
    Ok(())
}

/// An open `TrustedAgentService.Stream`.
struct AgentStream {
    requests: mpsc::Sender<AgentRequest>,
    responses: Streaming<AgentResponse>,
}

impl AgentStream {
    async fn open(agent_url: &str) -> anyhow::Result<Self> {
        let channel = Channel::from_shared(agent_url.to_string())
            .context("invalid agent URL")?
            .connect()
            .await
            .context("failed to connect to the agent")?;
        let (requests, receiver) = mpsc::channel(1);
        // The server starts a new agent session before accepting the stream.
        let responses = TrustedAgentServiceClient::new(channel)
            .stream(ReceiverStream::new(receiver))
            .await
            .map_err(|status| {
                anyhow!(
                    "failed to start the stream ({:?}): {}\n\
                     If the agent is reached through an Oak Proxy client, the agent's attestation \
                     may have failed verification: check the proxy client's log, and inspect the \
                     attestation it saved with oak_attestation_verification_cli.",
                    status.code(),
                    status.message()
                )
            })?
            .into_inner();
        Ok(Self { requests, responses })
    }

    /// Sends a user message and waits for the agent's reply. An error means
    /// that the stream has ended.
    async fn send(&mut self, text: String) -> anyhow::Result<String> {
        let request = AgentRequest {
            request: Some(agent_request::Request::UserMessage(UserMessage { text })),
        };
        // If the stream has ended, the error status is read below.
        let _ = self.requests.send(request).await;
        match self.responses.message().await {
            Ok(Some(AgentResponse {
                response: Some(agent_response::Response::AgentMessage(message)),
            })) => Ok(message.text),
            Ok(Some(AgentResponse { response: None })) => {
                Err(anyhow!("the agent sent an empty response"))
            }
            Ok(None) => Err(anyhow!("the agent closed the stream")),
            Err(status) => Err(anyhow!(
                "the agent ended the stream ({:?}): {}",
                status.code(),
                status.message()
            )),
        }
    }

    /// Half-closes the stream and waits for the agent to end it.
    async fn close(self) {
        let Self { requests, mut responses } = self;
        drop(requests);
        let _ = tokio::time::timeout(CLOSE_TIMEOUT, async {
            while let Ok(Some(_)) = responses.message().await {}
        })
        .await;
    }
}
