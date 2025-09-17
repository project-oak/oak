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

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use anyhow::Result;
use private_memory_server_lib::{
    app,
    app::{run_persistence_service, ApplicationConfig},
};
use tokio::net::TcpListener;

fn init_logging() {
    let _ = env_logger::builder().is_test(true).try_init();
}

pub async fn start_server() -> Result<(
    SocketAddr,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<()>,
)> {
    init_logging();
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await?;
    let addr = listener.local_addr()?;

    let db_addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let db_listener = TcpListener::bind(db_addr).await?;
    let db_addr = db_listener.local_addr()?;

    let application_config = ApplicationConfig { database_service_host: db_addr };

    let metrics = private_memory_server_lib::metrics::get_global_metrics();
    let (persistence_tx, persistence_rx) = tokio::sync::mpsc::unbounded_channel();
    let persistence_join_handle = tokio::spawn(run_persistence_service(persistence_rx));
    Ok((
        addr,
        tokio::spawn(app::service::create(listener, application_config, metrics, persistence_tx)),
        tokio::spawn(private_memory_test_database_server_lib::service::create(db_listener)),
        persistence_join_handle,
    ))
}
