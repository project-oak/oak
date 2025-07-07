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

use oak_time::instant::{Instant, UNIX_EPOCH};

/// Converts a SystemTime to an Instant.
pub fn from_system_time(instant: SystemTime) -> Instant {
    match instant.duration_since(SystemTime::UNIX_EPOCH) {
        Ok(duration) => UNIX_EPOCH + duration,
        Err(err) => UNIX_EPOCH - err.duration(),
    }
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, SystemTime};

    use googletest::prelude::*;
    use oak_time::UNIX_EPOCH;

    use super::*;

    #[googletest::test]
    fn test_from_system_time_after_epoch() {
        let duration = Duration::from_secs(12345);
        let system_time = SystemTime::UNIX_EPOCH + duration;
        let expected_instant = UNIX_EPOCH + duration;
        assert_that!(from_system_time(system_time), eq(expected_instant));
    }

    #[googletest::test]
    fn test_from_system_time_before_epoch() {
        let duration = Duration::from_secs(54321);
        let system_time = SystemTime::UNIX_EPOCH - duration;
        let expected_instant = UNIX_EPOCH - duration;
        assert_that!(from_system_time(system_time), eq(expected_instant));
    }

    #[googletest::test]
    fn test_from_system_time_at_epoch() {
        let system_time = SystemTime::UNIX_EPOCH;
        let expected_instant = UNIX_EPOCH;
        assert_that!(from_system_time(system_time), eq(expected_instant));
    }
}
