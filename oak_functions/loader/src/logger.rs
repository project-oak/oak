//
// Copyright 2021 The Project Oak Authors
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

use chrono::{SecondsFormat, Utc};
use log::{Level, LevelFilter};
use oak_logger::OakLogger;
use std::default::Default;

/// A simple logger that splits logging between writing logs that contain only public, non-sensitive
/// content and writing logs that could potentially contain sensitive content.
///
/// Writing of potentially sensitive content will be ignored unless the "oak-unsafe" feature is
/// enabled.
#[derive(Clone)]
pub struct Logger {
    max_level: LevelFilter,
}

impl Logger {
    /// Creates a new logger with the specified maximum `LevelFilter`.
    pub fn new(max_level: LevelFilter) -> Self {
        Self { max_level }
    }

    /// Creates a new logger for testing using the debug `LevelFilter`.
    pub fn for_test() -> Self {
        Self::new(LevelFilter::Debug)
    }

    fn log(&self, level: Level, message: &str) {
        if level <= self.max_level {
            eprintln!(
                "{} {} - {}",
                Utc::now().to_rfc3339_opts(SecondsFormat::Secs, true),
                level,
                message,
            );
        }
    }
}

impl Default for Logger {
    fn default() -> Self {
        Logger::new(LevelFilter::Debug)
    }
}

impl OakLogger for Logger {
    #[cfg(feature = "oak-unsafe")]
    fn log_sensitive(&self, level: Level, message: &str) {
        self.log(level, message);
    }

    #[cfg(not(feature = "oak-unsafe"))]
    fn log_sensitive(&self, _level: Level, _message: &str) {}

    fn log_public(&self, level: Level, message: &str) {
        self.log(level, message);
    }
}
