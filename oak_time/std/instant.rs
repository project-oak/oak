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

use oak_time::{duration::Duration, instant::Instant};

/// Returns the current time from the system.
pub fn now() -> Instant {
    from_system_time(SystemTime::now())
}

/// Converts a SystemTime to an Instant.
pub fn from_system_time(instant: SystemTime) -> Instant {
    let duration_from_epoch = match instant.duration_since(SystemTime::UNIX_EPOCH) {
        Ok(duration) => Duration::from_nanos(
            i128::try_from(duration.as_nanos()).expect("failed to convert u128 to i128"),
        ),
        Err(err) => Duration::from_nanos(
            -i128::try_from(err.duration().as_nanos()).expect("failed to convert u128 to i128"),
        ),
    };
    Instant::UNIX_EPOCH + duration_from_epoch
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, SystemTime};

    use googletest::prelude::*;

    use super::*;

    #[googletest::test]
    fn test_from_system_time_after_epoch() {
        let system_time = SystemTime::UNIX_EPOCH + Duration::from_secs(12345);
        let expected_instant = Instant::from_unix_seconds(12345);
        assert_that!(from_system_time(system_time), eq(expected_instant));
    }

    #[googletest::test]
    fn test_from_system_time_before_epoch() {
        let system_time = SystemTime::UNIX_EPOCH - Duration::from_secs(54321);
        let expected_instant = Instant::from_unix_seconds(-54321);
        assert_that!(from_system_time(system_time), eq(expected_instant));
    }

    #[googletest::test]
    fn test_from_system_time_at_epoch() {
        assert_that!(from_system_time(SystemTime::UNIX_EPOCH), eq(Instant::UNIX_EPOCH));
    }
}
