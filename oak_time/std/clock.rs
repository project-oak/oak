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

use std::time::SystemTime;

use oak_time::{Clock, Instant};

use crate::instant;

/// A `Clock` implementation that uses `std::time::SystemTime` as a time source.
///
/// This is the standard `Clock` implementation for environments where the Rust
/// standard library is available.
pub struct SystemTimeClock;

impl Clock for SystemTimeClock {
    fn get_time(&self) -> Instant {
        instant::from_system_time(SystemTime::now())
    }
}

pub struct FrozenSystemTimeClock {
    time: SystemTime,
}

impl Default for FrozenSystemTimeClock {
    fn default() -> Self {
        Self { time: SystemTime::now() }
    }
}

impl Clock for FrozenSystemTimeClock {
    fn get_time(&self) -> Instant {
        instant::from_system_time(self.time)
    }
}

#[cfg(test)]
mod tests {
    use std::time::SystemTime;

    use googletest::prelude::*;

    use super::*;
    use crate::instant::from_system_time;

    #[googletest::test]
    fn test_system_time_clock_returns_current_time() {
        let clock = SystemTimeClock;

        let now_before = from_system_time(SystemTime::now());
        let time_from_clock = clock.get_time();
        let now_after = from_system_time(SystemTime::now());

        assert_that!(time_from_clock, ge(now_before));
        assert_that!(time_from_clock, le(now_after));
    }
}
