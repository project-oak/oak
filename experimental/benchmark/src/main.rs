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
//! - Implemented as part of the Trusted Database Oak application (using `oak::OakApplication`)
//! - Implemented as a `tonic` gRPC server without using Oak (using `raw::RawApplication`)
//!
//! Benchmark randomly generates (with 0 seed) a database and sends it both to Oak and Raw
//! application. Then it sends `REQUEST_NUMBER` of requests to each application and computes the
//! average response time. It also computes time needed to start Oak application (which includes XML
//! database deserialization).
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
    application::{oak::OakApplication, raw::RawApplication, Application},
    database::Database,
};
use log::{error, info};
use std::time::Instant;
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
#[structopt(about = "Trusted Database Client")]
pub struct Opt {
    #[structopt(long, help = "Database size (number of items)")]
    database_size: usize,
}

// Port for running a gRPC server for the raw application.
const VANILLA_APP_PORT: u16 = 8888;

// Number of requests to average request time on.
const REQUEST_NUMBER: usize = 10;

/// Measures average request time in milliseconds.
async fn measure_request_time(app: &mut dyn Application, database_size: usize) -> f32 {
    use rand::{rngs::SmallRng, Rng, SeedableRng};
    let mut rng = SmallRng::seed_from_u64(0);

    let request_start = Instant::now();
    for _ in 0..REQUEST_NUMBER {
        let id = format!("{}", rng.gen_range(0, database_size));
        let _ = app.send_request(&id).await.map_err(|error| {
            error!("Couldn't send request: {}", error);
        });
    }
    let total_request_time = request_start.elapsed().as_millis();
    (total_request_time as f32) / (REQUEST_NUMBER as f32)
}

#[tokio::main(core_threads = 4)]
async fn main() -> anyhow::Result<()> {
    // Set current dir to create `oak_tests` in the `experimental/benchmark` directory.
    std::env::set_current_dir("./experimental/benchmark")?;

    env_logger::init();
    let opt = Opt::from_args();

    let database = Database::new(opt.database_size);
    let serialized_database = database.serialize();
    let mut raw_app = RawApplication::start(&database, VANILLA_APP_PORT).await;

    // Start Oak runtime.
    info!(
        "Loading Runtime: Sending database - size: {} entries ({} bytes)",
        database.points_of_interest.entries.len(),
        serialized_database.as_bytes().len()
    );
    let oak_loading_start = Instant::now();
    let mut oak_app = OakApplication::start(&serialized_database).await;
    let oak_loading_time = (oak_loading_start.elapsed().as_millis() as f64) / 1000.0;
    info!("Runtime loaded: {:.3}s", oak_loading_time);

    // Measure raw request durations.
    let average_raw_request_time = measure_request_time(&mut raw_app, opt.database_size).await;

    // Measure Oak request durations.
    let average_oak_request_time = measure_request_time(&mut oak_app, opt.database_size).await;

    oak_app.stop();

    info!(
        "Database size: {} entries",
        database.points_of_interest.entries.len()
    );
    info!("Runtime loading time: {:.3}s", oak_loading_time / 1000.0);
    info!(
        "Average raw request time: {:.3}s",
        average_raw_request_time / 1000.0
    );
    info!(
        "Average Oak request time: {:.3}s",
        average_oak_request_time / 1000.0
    );

    Ok(())
}
