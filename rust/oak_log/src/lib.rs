//
// Copyright 2019 The Project Oak Authors
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

//! A logger that send output to an Oak logging channel.

extern crate log;
extern crate oak;

#[cfg(test)]
mod tests;

use log::{Level, Log, Metadata, Record, SetLoggerError};
use std::io::Write;

struct OakChannelLogger;

impl Log for OakChannelLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= log::max_level()
    }
    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }
        writeln!(
            oak::logging_channel(),
            "{}  {} : {} : {}",
            record.level(),
            record.file().unwrap_or_default(),
            record.line().unwrap_or_default(),
            record.args()
        )
        .unwrap();
    }
    fn flush(&self) {}
}

pub fn init(level: Level) -> Result<(), SetLoggerError> {
    log::set_boxed_logger(Box::new(OakChannelLogger))?;
    log::set_max_level(level.to_level_filter());
    Ok(())
}
