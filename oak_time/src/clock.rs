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
use crate::instant::Instant;

/// A trait for a time source that can provide the current time as an `Instant`.
///
/// This trait is designed to be object-safe, allowing it to be used as a trait
/// object (`Box<dyn Clock>`). This is useful for dependency injection,
/// especially in testing scenarios where a fixed or controlled time source is
/// needed.
pub trait Clock: Send + Sync {
    /// Returns the current time as an `Instant`.
    fn get_time(&self) -> Instant;
}

/// A `Clock` implementation that always returns a fixed, pre-configured time.
///
/// This is primarily useful for testing components that depend on the current
/// time.
pub struct FixedClock {
    time: Instant,
}

impl FixedClock {
    /// Creates a new `FixedClock` that will always return the given `Instant`.
    pub fn at_instant(time: Instant) -> Self {
        FixedClock { time }
    }
}

impl Clock for FixedClock {
    /// Returns the fixed time this `FixedClock` was created with.
    fn get_time(&self) -> Instant {
        self.time
    }
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;

    use super::*;

    #[googletest::test]
    fn test_fixed_clock() {
        let now = Instant::from_unix_millis(1234567890);
        let clock = FixedClock::at_instant(now);
        assert_that!(clock.get_time(), eq(now));
    }
}
