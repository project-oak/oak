//
// Copyright 2020 The Project Oak Authors
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

//! Trusted Database Benchmark.
//!
//! This benchmark measures average gRPC request time to a database that is either:
//! - A part of the Trusted Database Oak application
//!     - This version uses compiled Wasm modules and Oak IFC which both account for a nontrivial
//!       performance difference
//!     - Implemented in `oak::OakApplication`
//! - A `tonic` gRPC server without using Oak
//!     - Implemented in `native::NativeApplication`
//! Benchmark pseudo-randomly (but deterministically) generates a database and sends it both to Oak
//! and native application. Then it sends `REQUEST_NUMBER` of requests to each application and
//! computes the average response time. It also computes time needed to start Oak application (which
//! includes XML database deserialization).
//!
//! It's important to note that Wasm module for Trusted Database application is being compiled with
//! `--release`.
//!
//! Invoke with:
//!
//! ```shell
//! cargo run --release --manifest-path=experimental/benchmark/Cargo.toml -- --database-size 100
//! ```
//!
//! Where `--database-size` specifies the size (number of entries) of the generated database.

mod proto {
    tonic::include_proto!("oak.examples.trusted_database");
}

mod application;
mod database;

use crate::{
    application::{native::NativeApplication, oak::OakApplication, ApplicationClient},
    database::Database,
};
use log::{error, info};
use std::{
    ops::Range,
    time::{Duration, Instant},
};
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
#[structopt(about = "Trusted Database Client")]
pub struct Opt {
    #[structopt(long, help = "Database size (number of items)")]
    database_size: usize,
}

// Port for running a gRPC server for the native application.
const NATIVE_APPLICATION_GRPC_PORT: u16 = 8888;

// Number of requests to average request time on.
const REQUEST_NUMBER: usize = 1;

/// Measures average request time in milliseconds.
async fn measure_request_time(
    client: &mut dyn ApplicationClient,
    database_size: usize,
) -> Duration {
    use rand::{rngs::SmallRng, Rng, SeedableRng};
    let mut rng = SmallRng::seed_from_u64(0);

    let request_start = Instant::now();
    for _ in 0..REQUEST_NUMBER {
        let id = format!(
            "{}",
            rng.gen_range(Range {
                start: 0,
                end: database_size
            })
        );
        let _ = client.send_request(&id).await.map_err(|error| {
            error!("Couldn't send request: {}", error);
        });
    }
    request_start.elapsed().div_f32(REQUEST_NUMBER as f32)
}

#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn main() -> anyhow::Result<()> {
    // Set current dir to create `oak_tests` in the `experimental/benchmark` directory.
    std::env::set_current_dir("./experimental/benchmark")?;

    env_logger::init();
    let opt = Opt::from_args();

    let database = Database::new(opt.database_size);
    let serialized_database = database.serialize();
    let mut native_app = NativeApplication::start(&database, NATIVE_APPLICATION_GRPC_PORT).await;

    // Start Oak runtime.
    info!(
        "Loading Runtime: Sending database - size: {} entries ({} bytes)",
        database.points_of_interest.entries.len(),
        serialized_database.as_bytes().len()
    );
    let oak_loading_start = Instant::now();
    let mut oak_app = OakApplication::start(&serialized_database).await;
    let oak_loading_time = oak_loading_start.elapsed();
    info!("Runtime loaded: {:?}", oak_loading_time);

    // Measure native request durations.
    let average_native_request_time =
        measure_request_time(&mut native_app, opt.database_size).await;

    // Measure Oak request durations.
    let average_oak_request_time = measure_request_time(&mut oak_app, opt.database_size).await;

    oak_app.stop();
    native_app.stop()?;

    info!(
        "Database size: {} entries",
        database.points_of_interest.entries.len()
    );
    info!("Runtime loading time: {:?}", oak_loading_time);
    info!(
        "Average native request time: {:?}",
        average_native_request_time
    );
    info!("Average Oak request time: {:?}", average_oak_request_time);

    Ok(())
}
