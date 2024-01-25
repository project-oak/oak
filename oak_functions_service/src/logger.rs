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

pub use log::Level;

pub trait OakLogger: Send + Sync {
    /// Logs the message, which might contain sensitive information, at the specified `Level`.
    ///
    /// Only insecure debug-only implementations may provide a non-empty implementation. Production
    /// implementations must not do anything.
    fn log_sensitive(&self, level: Level, message: &str);

    /// Logs a message that contains only public, non-sensitive content at the specified `Level`.
    ///
    /// All code that uses this function must be inspected to ensure that the message can never
    /// contain any information that could have been derived from sensitive or non-public data.
    fn log_public(&self, level: Level, message: &str);
}

/// Temporary OakLogger implementation using the `log` crate.
///
/// TODO(#2783): Replace with redesigned logger implementation.
pub struct StandaloneLogger;

// TODO(#2783): Implement a logger that differentiates between public and sensitive loges.
impl OakLogger for StandaloneLogger {
    #[cfg(not(feature = "deny_sensitive_logging"))]
    fn log_sensitive(&self, level: Level, message: &str) {
        log::log!(level, "{}", message,);
    }

    #[cfg(feature = "deny_sensitive_logging")]
    fn log_sensitive(&self, _level: Level, _message: &str) {}

    fn log_public(&self, level: Level, message: &str) {
        log::log!(level, "{}", message,);
    }
}
