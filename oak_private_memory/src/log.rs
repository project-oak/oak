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

pub fn init_logging(enable_logging: bool) {
    if enable_logging {
        env_logger::Builder::new()
            .target(env_logger::Target::Stdout)
            .format(|buf, record| {
                writeln!(
                    buf,
                    "{}:{} [{}] - {}",
                    record.file().unwrap_or("unknown"),
                    record.line().unwrap_or(0),
                    record.level(),
                    record.args()
                )
            })
            .filter(None, LevelFilter::Info)
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
