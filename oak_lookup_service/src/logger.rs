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

use log::log;
use oak_logger::{Level, OakLogger};

/// Temporary OakLogger implementation using the `log` crate.
///
/// TODO(#2783): Replace with redesigned logger implementation.
#[derive(Clone, Default)]
pub struct StandaloneLogger {}

// TODO(#2783): Implement a logger that differentiates between public and sensitive loges.
impl OakLogger for StandaloneLogger {
    fn log_sensitive(&self, level: Level, message: &str) {
        log!(level, "{}", message,);
    }

    fn log_public(&self, level: Level, message: &str) {
        log!(level, "{}", message,);
    }
}
