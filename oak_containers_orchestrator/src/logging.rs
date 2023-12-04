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

extern crate log;

use log::LevelFilter;
use syslog::{BasicLogger, Facility, Formatter3164};

/// Setup logging to syslog.
pub fn setup() -> Result<(), Box<dyn std::error::Error>> {
    // Based on syslog's example of integrating with the log crate.
    // Ref: https://docs.rs/syslog/6.1.0/syslog/

    let formatter = Formatter3164 {
        facility: Facility::LOG_DAEMON,
        hostname: None,
        process: "oak_containers_orchestrator".into(),
        pid: std::process::id(),
    };

    let logger =
        syslog::unix(formatter).map_err(|e| format!("impossible to connect to syslog: {:?}", e))?;

    log::set_boxed_logger(Box::new(BasicLogger::new(logger)))
        .map(|()| log::set_max_level(LevelFilter::Debug))
        .map_err(|e| format!("failed to set logger: {:?}", e))?;

    Ok(())
}
