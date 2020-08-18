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

//! A utility binary to run Oak Runtime.
//!
//! Invoke with:
//!
//! ```shell
//! cargo run --manifest-path=oak_loader/Cargo.toml -- \
//!     --application=<APP_CONFIG_PATH> \
//!     --grpc-tls-private-key=<PRIVATE_KEY_PATH> \
//!     --grpc-tls-certificate=<CERTIFICATE_PATH> \
//!     --root-tls-certificate=<CERTIFICATE_PATH>
//! ```

use anyhow::Context;
use log::info;
mod options;
use oak_runtime::config::configure_and_run;
use options::create_runtime_config;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

#[cfg(test)]
mod tests;

/// Main execution point for the Oak loader.
fn main() -> anyhow::Result<()> {
    if cfg!(feature = "oak_debug") {
        env_logger::init();
    } else {
        eprintln!("No debugging output configured at build time");
    }

    // Create Runtime config.
    let runtime_configuration = create_runtime_config()?;

    // Start the Runtime from the given config.
    info!("starting Runtime");
    let runtime = configure_and_run(runtime_configuration).context("could not start Runtime")?;
    info!("started Runtime");

    let done = Arc::new(AtomicBool::new(false));
    signal_hook::flag::register(signal_hook::SIGINT, Arc::clone(&done))
        .context("could not register signal handler")?;

    // The Runtime kicks off its own threads for the initial Node and any subsequently created
    // Nodes, so just block the current thread until a signal arrives.
    while !done.load(Ordering::Relaxed) {
        // There are few synchronization mechanisms that are allowed to be used in a signal
        // handler context, so use a primitive sleep loop to watch for the termination
        // notification (rather than something more accurate like `std::sync::Condvar`).
        // See e.g.: http://man7.org/linux/man-pages/man7/signal-safety.7.html
        std::thread::sleep(std::time::Duration::from_millis(100));
    }

    info!("stop Runtime");
    runtime.stop();

    info!("Runtime stopped");
    Ok(())
}
