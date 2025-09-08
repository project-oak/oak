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
//

//! Represents a time duration, perhaps negative.

use core::ops::{Add, Div, Sub};

const MILLIS_TO_NANOS: i128 = 1_000_000;
const SECONDS_TO_NANOS: i128 = 1_000 * MILLIS_TO_NANOS;
const MINUTES_TO_NANOS: i128 = 60 * SECONDS_TO_NANOS;
const HOURS_TO_NANOS: i128 = 60 * MINUTES_TO_NANOS;

/// Represents a signed time duration which is the result of e.g. the
/// subtraction of two Instants.
///
/// The technically supported range is plus or minus 5.39 * 10^21 years
/// which is plenty.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct Duration {
    /// Theoretically supported minimum and maximum values (nanoseconds) are:
    /// i128::MAX is 170_141_183_460_469_231_731_687_303_715_884_105_727,
    /// i128::MIN is -i128::MAX - 1.
    nanoseconds: i128,
}

impl Duration {
    /// Creates a new `Duration` from a signed number of hours.
    ///
    /// # Arguments
    ///
    /// * `hours`: The number of hours.
    pub const fn from_hours(hours: i64) -> Self {
        Duration { nanoseconds: HOURS_TO_NANOS * hours as i128 }
    }

    /// Creates a new `Duration` from a signed number of minutes.
    ///
    /// # Arguments
    ///
    /// * `minutes`: The number of minutes.
    pub const fn from_minutes(minutes: i64) -> Self {
        Duration { nanoseconds: MINUTES_TO_NANOS * minutes as i128 }
    }

    /// Creates a new `Duration` from a signed number of seconds.
    ///
    /// # Arguments
    ///
    /// * `seconds`: The number of seconds.
    pub const fn from_seconds(seconds: i64) -> Self {
        Duration { nanoseconds: SECONDS_TO_NANOS * seconds as i128 }
    }

    /// Creates a new `Duration` from a signed number of milliseconds.
    ///
    /// # Arguments
    ///
    /// * `millis`: The number of milliseconds.
    pub const fn from_millis(millis: i64) -> Self {
        Duration { nanoseconds: MILLIS_TO_NANOS * millis as i128 }
    }

    /// Creates a new `Duration` from a signed number of nanoseconds.
    ///
    /// # Arguments
    ///
    /// * `nanos`: The number of nanoseconds.
    pub const fn from_nanos(nanos: i128) -> Self {
        Duration { nanoseconds: nanos }
    }

    /// Converts this dutation into the number of seconds.
    pub fn into_seconds(self) -> i64 {
        let seconds = self.nanoseconds / SECONDS_TO_NANOS;
        i64::try_from(seconds).expect("failed to convert from i128 to i64")
    }

    /// Converts this duration into number of millisesconds.
    pub fn into_millis(self) -> i64 {
        let millis = self.nanoseconds / MILLIS_TO_NANOS;
        i64::try_from(millis).expect("failed to convert from i128 to i64")
    }

    /// Converts this instant into number of nanoseconds.
    pub fn into_nanos(self) -> i128 {
        self.nanoseconds
    }
}

/// Implements the `Add` trait for `Duration`.
///
/// Allows two add `Duration`s, yieldimg `Duration`.
impl Add<Duration> for Duration {
    type Output = Self;

    /// Adds a `Duration` to this `Duration`.
    ///
    /// # Arguments
    ///
    /// * `other`: The `Duration` to add.
    ///
    /// # Returns
    ///
    /// A new `Duration` representing the original instant advanced by `other`.
    fn add(self, other: Duration) -> Self::Output {
        Self { nanoseconds: self.nanoseconds + other.nanoseconds }
    }
}

impl Sub<Duration> for Duration {
    type Output = Duration;

    /// Subtracts another `Duration` from this `Duration`.
    ///
    /// # Arguments
    ///
    /// * `other`: The `Duration` to subtract.
    ///
    /// # Returns
    ///
    /// A `Duration` representing the signed duration.
    fn sub(self, other: Duration) -> Self::Output {
        Duration::from_nanos(self.nanoseconds - other.nanoseconds)
    }
}

impl Div<i32> for Duration {
    type Output = Duration;

    /// Divides a `Duration` by an int32.
    ///
    /// # Arguments
    ///
    /// * `divisor`: The int32 to divide by.
    ///
    /// # Returns
    ///
    /// A `Duration` representing the fraction of the original duration.
    fn div(self, divisor: i32) -> Self::Output {
        Duration::from_nanos(self.nanoseconds / divisor as i128)
    }
}

/// Conditionally implements `From<prost_types::Duration>` for `Duration`
/// when the `prost` feature is enabled.
///
/// This allows converting a `prost_types::Duration` into a `Duration`.
#[cfg(feature = "prost")]
impl From<&prost_types::Duration> for Duration {
    /// Converts a `prost_types::Duration` to a `Duration`.
    ///
    /// # Arguments
    ///
    /// * `duration`: The `prost_types::Duration` to convert.
    fn from(duration: &prost_types::Duration) -> Self {
        Duration {
            nanoseconds: SECONDS_TO_NANOS * duration.seconds as i128 + duration.nanos as i128,
        }
    }
}

/// Conditionally implements `From<prost_types::Duration>` for `Duration`
/// when the `prost` feature is enabled.
///
/// This allows converting a `prost_types::Duration` into an `Duration`.
#[cfg(feature = "prost")]
impl From<prost_types::Duration> for Duration {
    /// Converts a `prost_types::Duration` to a `Duration`.
    ///
    /// # Arguments
    ///
    /// * `duration`: The `prost_types::Duration` to convert.
    fn from(duration: prost_types::Duration) -> Self {
        Duration {
            nanoseconds: SECONDS_TO_NANOS * duration.seconds as i128 + duration.nanos as i128,
        }
    }
}

/// Converts this duration into a `prost_types::Duration`.
///
/// # Panics
///
/// When a value does not fit into `prost_types::Duration`:
/// The range of `Duration`` is far larger than the range of
/// `prost_types::Duration`. Such values do not occur in practice.
#[cfg(feature = "prost")]
impl From<Duration> for prost_types::Duration {
    fn from(duration: Duration) -> Self {
        let seconds = i64::try_from(duration.nanoseconds / SECONDS_TO_NANOS)
            .expect("failed to convert i128 to i64");
        let nanos = i32::try_from(duration.nanoseconds % SECONDS_TO_NANOS)
            .expect("failed to convert i128 to i32");
        // Contrasting prost_types::Timestamp, the nanoseconds in Duration are
        // signed, so no corrective action is needed.
        prost_types::Duration { seconds, nanos }
    }
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;

    use super::Duration;
    use crate::Instant;

    // Minimum and maximum values specified for `prost_types::Duration`.
    // Note: these bounds are computed from: 60 sec/min 60 min/hr 24 hr/day
    // 365.25 days/year. The maximum valid specified duration is therefore
    // plus or minus 10000 years.
    const MIN_VALUE_SECONDS: i64 = -315_576_000_000;
    const MIN_VALUE_NANOS: i32 = -999_999_999;
    const MAX_VALUE_SECONDS: i64 = 315_576_000_000;
    const MAX_VALUE_NANOS: i32 = 999_999_999;

    #[googletest::test]
    fn test_hours_example() {
        const EXPECTED_HOURS: i64 = -987_654;
        let d = Duration::from_hours(EXPECTED_HOURS);
        assert_eq!(EXPECTED_HOURS * 60 * 60, d.into_seconds());
    }

    #[googletest::test]
    fn test_minutes_example() {
        const EXPECTED_MINUTES: i64 = 3_456_789;
        let d = Duration::from_minutes(EXPECTED_MINUTES);
        assert_eq!(EXPECTED_MINUTES * 60, d.into_seconds());
    }

    #[googletest::test]
    fn test_seconds_example() {
        const EXPECTED_SECONDS: i64 = 1_234_567_890;
        let d = Duration::from_seconds(EXPECTED_SECONDS);
        assert_eq!(EXPECTED_SECONDS, d.into_seconds());
    }

    #[googletest::test]
    fn test_millis_example() {
        const EXPECTED_MILLIS: i64 = -9_876_543_210_987;
        let d = Duration::from_millis(EXPECTED_MILLIS);
        assert_eq!(EXPECTED_MILLIS, d.into_millis());
    }

    #[googletest::test]
    fn test_nanos_example() {
        const EXPECTED_NANOS: i128 = 111_222_333_444_555_666_777;
        let d = Duration::from_nanos(EXPECTED_NANOS);
        assert_eq!(d.into_nanos(), EXPECTED_NANOS);
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_duration_conversion_left_min() {
        let expected = Duration::from_millis(1000 * MIN_VALUE_SECONDS);
        let duration_proto: prost_types::Duration = expected.into();
        let actual = Duration::from(duration_proto);
        assert_that!(actual, eq(expected));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_duration_conversion_left_max() {
        let expected = Duration::from_millis(1000 * MAX_VALUE_SECONDS);
        let duration_proto: prost_types::Duration = expected.into();
        let actual = Duration::from(duration_proto);
        assert_that!(actual, eq(expected));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_duration_conversion_right_min() {
        let expected = prost_types::Duration { seconds: MIN_VALUE_SECONDS, nanos: MIN_VALUE_NANOS };
        let actual: prost_types::Duration = Duration::from(expected).into();
        assert_that!(actual, eq(expected));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_duration_conversion_right_max() {
        let expected = prost_types::Duration { seconds: MAX_VALUE_SECONDS, nanos: MAX_VALUE_NANOS };
        let actual: prost_types::Duration = Duration::from(expected).into();
        assert_that!(actual, eq(expected));
    }

    #[googletest::test]
    fn test_middle_example() {
        let before = Instant::from_unix_millis(1_000_000_000);
        let after = Instant::from_unix_millis(9_000_000_000);
        let middle = before + (after - before) / 2;
        assert_eq!(middle.into_unix_millis(), 5_000_000_000);
    }
}
