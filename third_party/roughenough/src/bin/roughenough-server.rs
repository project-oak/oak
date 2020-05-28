// Copyright 2017-2019 int08h LLC
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

//!
//! Roughtime server
//!
//! # Configuration
//! The server has multiple ways it can be configured, see
//! [`ServerConfig`](config/trait.ServerConfig.html) for details.
//!

#[macro_use]
extern crate log;

use std::env;
use std::process;
use std::sync::atomic::Ordering;

use roughenough::config;
use roughenough::config::ServerConfig;
use roughenough::roughenough_version;
use roughenough::server::Server;

use mio::Events;

macro_rules! check_ctrlc {
    ($keep_running:expr) => {
        if !$keep_running.load(Ordering::Acquire) {
            warn!("Ctrl-C caught, exiting...");
            return;
        }
    };
}

fn polling_loop(config: Box<dyn ServerConfig>) {
    let mut server = Server::new(config);
    let cfg = server.get_config(); // borrow config that was moved above

    info!("Long-term public key       : {}", server.get_public_key());
    info!("Online public key          : {}", server.get_online_key());
    info!("Max response batch size    : {}", cfg.batch_size());
    info!("Status updates every       : {} seconds", cfg.status_interval().as_secs());
    info!("Server listening on        : {}:{}", cfg.interface(), cfg.port());
    if let Some(hc_port) = cfg.health_check_port() {
        info!("TCP health check           : {}:{}", cfg.interface(), hc_port);
    } else {
        info!("TCP health check           : disabled");
    }
    info!("Client req/resp tracking   : {}",
          if cfg.client_stats_enabled() { "per-client" } else { "aggregated" }
    );
    if cfg.fault_percentage() > 0 {
        info!("Deliberate response errors : ~{}%", cfg.fault_percentage());
    } else {
        info!("Deliberate response errors : disabled");
    }

    let kr = server.get_keep_running();
    let kr_new = kr.clone();

    ctrlc::set_handler(move || kr.store(false, Ordering::Release))
        .expect("failed setting Ctrl-C handler");

    let mut events = Events::with_capacity(64);

    loop {
        check_ctrlc!(kr_new);
        if server.process_events(&mut events) {
            return;
        }
    }
}

pub fn main() {
    use log::Level;

    simple_logger::init_with_level(Level::Info).unwrap();

    info!("Roughenough server v{} starting", roughenough_version());

    let mut args = env::args();
    if args.len() != 2 {
        error!("Usage: server <ENV | /path/to/config.yaml>");
        process::exit(1);
    }

    let arg1 = args.nth(1).unwrap();
    let config = match config::make_config(&arg1) {
        Err(e) => {
            error!("{:?}", e);
            process::exit(1)
        }
        Ok(ref cfg) if !config::is_valid_config(cfg.as_ref()) => process::exit(1),
        Ok(cfg) => cfg,
    };

    polling_loop(config);

    info!("Done.");
    process::exit(0);
}
