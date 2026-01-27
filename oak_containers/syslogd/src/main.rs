//
// Copyright 2023 The Project Oak Authors
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

#![feature(c_size_t)]

mod log_relay;
mod systemd_journal;

use std::sync::Arc;

use anyhow::anyhow;
use clap::Parser;
use oak_containers_orchestrator::launcher_client::LauncherClient;
use opentelemetry::global::set_error_handler;
use signal_hook::consts::signal::SIGTERM;
use signal_hook_tokio::Signals;
use tokio::sync::OnceCell;
use tokio_stream::StreamExt;

#[derive(Parser, Debug)]
struct Args {
    #[arg(env, default_value = "http://10.0.2.100:8080")]
    launcher_addr: String,
}

#[allow(clippy::never_loop)]
async fn signal_handler(mut signals: Signals, term: Arc<OnceCell<()>>) {
    while let Some(signal) = signals.next().await {
        match signal {
            SIGTERM => {
                // We don't care if it has already been initialized.
                let _ = term.set(());
                return;
            }
            _ => unreachable!(),
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    set_error_handler(|err| eprintln!("oak-syslogd: OTLP error: {}", err))?;

    let term = Arc::new(OnceCell::new());
    let launcher_client = LauncherClient::create(args.launcher_addr.parse()?)
        .await
        .map_err(|error| anyhow!("couldn't create client: {:?}", error))?;

    let signals = Signals::new([SIGTERM])?;
    let handle = signals.handle();
    let signals_task = tokio::spawn(signal_handler(signals, term.clone()));

    tokio::try_join!(log_relay::run(launcher_client, term))?;
    handle.close();
    signals_task.await?;

    Ok(())
}
