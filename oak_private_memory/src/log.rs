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

use std::io::Write;

use log::LevelFilter;
pub use log::{debug, error, info, warn};

/// Crate name prefixes for first-party code. Add new crates here when
/// they are introduced. `record.module_path()` always starts with the
/// crate name, so a `starts_with` check is sufficient.
const FIRST_PARTY_CRATES: &[&str] = &[
    "app",
    "attestation",
    "client",
    "encryption",
    "external_db_client",
    "metrics",
    "oak_private_memory_database",
    "private_memory_server",
    "private_memory_server_lib",
    "session_binder",
];

pub fn init_logging(enable_logging: bool) {
    if enable_logging {
        env_logger::Builder::new()
            .target(env_logger::Target::Stdout)
            .filter(None, LevelFilter::Info)
            .format(|buf, record| {
                // Only emit logs from first-party crates. All third-party
                // crate logs are suppressed.
                let is_first_party = record
                    .module_path()
                    .is_some_and(|m| FIRST_PARTY_CRATES.iter().any(|prefix| m.starts_with(prefix)));
                if !is_first_party {
                    return Ok(());
                }
                writeln!(
                    buf,
                    "{}:{} [{}] - {}",
                    record.file().unwrap_or("unknown"),
                    record.line().unwrap_or(0),
                    record.level(),
                    record.args()
                )
            })
            .init();
    } else {
        // Explicitly register a no-op logger so the global logger slot is
        // occupied. Any later attempt to register another logger will error,
        // surfacing accidental double-init bugs.
        env_logger::Builder::new().filter_level(LevelFilter::Off).init();
        disable_icing_logging();
    }
}

pub fn disable_icing_logging() {
    icing::set_logging(false);
}
