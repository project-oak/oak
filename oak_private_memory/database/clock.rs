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

pub const SECONDS_PER_DAY: i64 = 86400;
pub const SECONDS_PER_YEAR: i64 = 365 * SECONDS_PER_DAY;
pub const MAX_MEMORY_TTL_SECONDS: i64 = 2 * SECONDS_PER_YEAR;
pub const METADATA_BLANKET_TTL_SECONDS: i64 = MAX_MEMORY_TTL_SECONDS + SECONDS_PER_DAY;
pub const CLOCK_DRIFT_BUFFER_SECONDS: i64 = 300; // 5 minutes

/// A trait for providing the current time.
pub trait Clock: Send + Sync {
    fn now(&self) -> SystemTime;
}

/// Converts SystemTime to prost_types::Timestamp.
pub fn system_time_to_timestamp(system_time: SystemTime) -> prost_types::Timestamp {
    let (seconds, nanos) = match system_time.duration_since(SystemTime::UNIX_EPOCH) {
        Ok(duration) => {
            let seconds = duration.as_secs() as i64;
            let nanos = duration.subsec_nanos() as i32;
            (seconds, nanos)
        }
        Err(e) => {
            let duration = e.duration();
            let seconds = -(duration.as_secs() as i64);
            let nanos = -(duration.subsec_nanos() as i32);
            (seconds, nanos)
        }
    };

    prost_types::Timestamp { seconds, nanos }
}

/// A clock that uses the system time.
pub struct SystemClock;

impl Clock for SystemClock {
    fn now(&self) -> SystemTime {
        SystemTime::now()
    }
}

/// Calculates the coarsened blanket TTL (configured TTL, rounded up
/// to next day).
pub fn calculate_coarsened_blanket_ttl(
    clock: &dyn Clock,
    blanket_ttl_seconds: i64,
) -> prost_types::Timestamp {
    let now = clock.now();
    let now_ts = system_time_to_timestamp(now);

    let expiration_seconds = now_ts.seconds + blanket_ttl_seconds;

    let target_ts = prost_types::Timestamp { seconds: expiration_seconds, nanos: now_ts.nanos };

    round_up_to_daily_boundary(target_ts)
}

/// Rounds up a timestamp to the next daily boundary (UTC midnight).
///
/// Bumping the timestamp to daily boundaries coarsens the granularity of the
/// metadata's lifetime, successfully mitigating timing side-channel leaks
/// that could reveal fine-grained user activity.
///
/// To strictly round up and guarantee that data is never deleted *before* its
/// requested lifetime, any non-zero sub-second nanoseconds are treated as an
/// additional second before daily boundary rounding.
pub fn round_up_to_daily_boundary(ts: prost_types::Timestamp) -> prost_types::Timestamp {
    let mut seconds = ts.seconds;
    if ts.nanos > 0 {
        seconds += 1;
    }
    let coarsened_seconds = ((seconds + SECONDS_PER_DAY - 1) / SECONDS_PER_DAY) * SECONDS_PER_DAY;
    prost_types::Timestamp { seconds: coarsened_seconds, nanos: 0 }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

    struct TestClock(SystemTime);
    impl Clock for TestClock {
        fn now(&self) -> SystemTime {
            self.0
        }
    }

    #[test]
    fn test_round_up_to_daily_boundary_exact_boundary() {
        // Exactly 1 day (86400 seconds), 0 nanos
        let ts = prost_types::Timestamp { seconds: SECONDS_PER_DAY, nanos: 0 };
        let rounded = round_up_to_daily_boundary(ts);
        assert_eq!(rounded.seconds, SECONDS_PER_DAY);
        assert_eq!(rounded.nanos, 0);
    }

    #[test]
    fn test_round_up_to_daily_boundary_one_second_past_boundary() {
        // 1 day + 1 second (86401 seconds), 0 nanos
        let ts = prost_types::Timestamp { seconds: SECONDS_PER_DAY + 1, nanos: 0 };
        let rounded = round_up_to_daily_boundary(ts);
        assert_eq!(rounded.seconds, 2 * SECONDS_PER_DAY);
        assert_eq!(rounded.nanos, 0);
    }

    #[test]
    fn test_round_up_to_daily_boundary_exact_boundary_with_nanos() {
        // Exactly 1 day (86400 seconds), 1 nano
        // This should be treated as strictly after the day boundary and round up!
        let ts = prost_types::Timestamp { seconds: SECONDS_PER_DAY, nanos: 1 };
        let rounded = round_up_to_daily_boundary(ts);
        assert_eq!(rounded.seconds, 2 * SECONDS_PER_DAY);
        assert_eq!(rounded.nanos, 0);
    }

    #[test]
    fn test_round_up_to_daily_boundary_epoch_start() {
        // Unix Epoch start: 0 seconds, 0 nanos
        let ts = prost_types::Timestamp { seconds: 0, nanos: 0 };
        let rounded = round_up_to_daily_boundary(ts);
        assert_eq!(rounded.seconds, 0);
        assert_eq!(rounded.nanos, 0);
    }

    #[test]
    fn test_round_up_to_daily_boundary_epoch_start_with_nanos() {
        // 0 seconds, 500 nanos (fraction of first second)
        // Bumps to 1 second, rounds up to 1 day!
        let ts = prost_types::Timestamp { seconds: 0, nanos: 500 };
        let rounded = round_up_to_daily_boundary(ts);
        assert_eq!(rounded.seconds, SECONDS_PER_DAY);
        assert_eq!(rounded.nanos, 0);
    }

    #[test]
    fn test_calculate_coarsened_blanket_ttl() {
        // Set clock to 1 day + 500 nanos (requires strict nanosecond round up)
        let base_time = SystemTime::UNIX_EPOCH
            + Duration::from_secs(SECONDS_PER_DAY as u64)
            + Duration::from_nanos(500);
        let clock = TestClock(base_time);

        let blanket_ttl = calculate_coarsened_blanket_ttl(&clock, METADATA_BLANKET_TTL_SECONDS);

        // Blanket TTL is 2 years + 24 hours (grace period)
        // Expected uncoarsened expiration: now (1 day + 500ns) + blanket_ttl
        // Which is 1 day + METADATA_BLANKET_TTL_SECONDS + 500ns
        // Since nanos > 0, it treats it as +1 second, and then rounds up to the next
        // day boundary.
        let expected_seconds = SECONDS_PER_DAY + METADATA_BLANKET_TTL_SECONDS;
        // Because nanos > 0, it should round up to the next day boundary!
        let expected_coarsened =
            ((expected_seconds + 1 + SECONDS_PER_DAY - 1) / SECONDS_PER_DAY) * SECONDS_PER_DAY;

        assert_eq!(blanket_ttl.seconds, expected_coarsened);
        assert_eq!(blanket_ttl.nanos, 0);
    }
}
