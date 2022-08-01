//
// Copyright 2022 The Project Oak Authors
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

use clap::Parser;
use oak_remote_attestation::handshaker::{AttestationBehavior, EmptyAttestationVerifier};
use oak_remote_attestation_amd::PlaceholderAmdAttestationGenerator;
use std::os::unix::net::UnixStream;

#[derive(Parser, Clone, Debug)]
#[clap(about = "Oak Functions Loader Linux UDS")]
pub struct Opt {
    #[clap(long, help = "UDS address to use for the communication channel")]
    pub comms_address: std::path::PathBuf,
}

struct Logger {}

impl log::Log for Logger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    #[cfg(debug_assertions)]
    fn log(&self, record: &log::Record) {
        println!("{}: {}", record.level(), record.args());
    }

    #[cfg(not(debug_assertions))]
    fn log(&self, record: &log::Record) {}

    fn flush(&self) {}
}

static LOGGER: Logger = Logger {};

fn main() {
    let opt = Opt::parse();
    log::set_logger(&LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Debug);
    log::info!(
        "Connecting to the launcher via the socket on: {}",
        opt.comms_address.to_string_lossy()
    );
    let socket = UnixStream::connect(opt.comms_address)
        .expect("Could not connect to the communication socket");
    let attestation_behavior =
        AttestationBehavior::create(PlaceholderAmdAttestationGenerator, EmptyAttestationVerifier);
    let channel = Box::new(socket);
    oak_baremetal_runtime::framing::handle_frames(channel, attestation_behavior)
        .expect("Couldn't handle frames");
}
