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

//! Represents a specific moment in time, measured with respect to Unix epoch.
//!
//! It offers ways to create `Instant`s from various representations (like
//! milliseconds since epoch) and perform arithmetic operations (addition and
//! subtraction with `Duration`). It also includes conversions from
//! and to other time-related types like `std::time::SystemTime`
//! and `prost_types::Timestamp` when the respective features are enabled.
//!
//! Unlike `std::time::SystemTime`, this module does not have a concept of a
//! "system time" or system time source. It also does not rely (by default) on
//! the std library.

use core::{
    ops::{Add, AddAssign, Sub, SubAssign},
    time::Duration,
};

// An anchor in time which can be used to create new Instant instances or learn
// about where in time an Instant lies. This is similar to the
// SystemTime::UNIX_EPOCH.
pub const UNIX_EPOCH: Instant = Instant { nanoseconds: 0 };

const MILLIS_TO_NANOS: i128 = 1_000_000;
const SECONDS_TO_NANOS: i128 = 1_000_000_000;

/// Represents a specific moment in time.
///
/// Internally, it stores signed nanonseconds anchored at Unix epoch
/// (January 1, 1970, 00:00:00 UTC).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Instant {
    nanoseconds: i128,
}

impl Instant {
    // An anchor in time which can be used to create new Instant instances or learn
    // about where in time an Instant lies. This is similar to the
    // SystemTime::UNIX_EPOCH.
    pub const UNIX_EPOCH: Instant = UNIX_EPOCH;

    /// Creates a new `Instant` from the number of seconds since the Unix
    /// epoch.
    ///
    /// # Arguments
    ///
    /// * `unix_epoch_seconds`: The number of seconds since the Unix epoch.
    pub const fn from_unix_seconds(unix_epoch_seconds: i64) -> Self {
        Instant { nanoseconds: SECONDS_TO_NANOS * unix_epoch_seconds as i128 }
    }

    /// Creates a new `Instant` from the number of milliseconds since the Unix
    /// epoch.
    ///
    /// # Arguments
    ///
    /// * `unix_epoch_millis`: The number of milliseconds since the Unix epoch.
    pub const fn from_unix_millis(unix_epoch_millis: i64) -> Self {
        Instant { nanoseconds: MILLIS_TO_NANOS * unix_epoch_millis as i128 }
    }

    /// Creates a new `Instant` from the number of nanoseconds since the Unix
    /// epoch.
    ///
    /// # Arguments
    ///
    /// * `unix_epoch_nanos`: The number of nanoseconds since the Unix epoch.
    pub const fn from_unix_nanos(unix_epoch_nanos: i128) -> Self {
        Instant { nanoseconds: unix_epoch_nanos }
    }

    /// Converts this instant into the number of seconds since the Unix epoch.
    pub fn into_unix_seconds(self) -> i64 {
        let seconds = self.nanoseconds / SECONDS_TO_NANOS;
        i64::try_from(seconds).expect("failed to convert from i128 to i64")
    }

    /// Converts this instant into the number of milliseconds since the Unix
    /// epoch.
    pub fn into_unix_millis(self) -> i64 {
        let millis = self.nanoseconds / MILLIS_TO_NANOS;
        i64::try_from(millis).expect("failed to convert from i128 to i64")
    }

    /// Converts this instant into the number of nanoseconds since the Unix
    /// epoch.
    pub fn into_unix_nanos(self) -> i128 {
        self.nanoseconds
    }

    /// Converts this instant into a `prost_types::Timestamp`.
    ///
    /// # Panics
    ///
    /// Panics if seconds or nanos derived from the `Instant` cannot be
    /// converted to their respective types in the `prost_types::Timestamp`
    /// (`i64` and `i32`).
    #[cfg(feature = "prost")]
    pub fn into_timestamp(self) -> prost_types::Timestamp {
        let mut seconds = i64::try_from(self.nanoseconds / SECONDS_TO_NANOS)
            .expect("failed to convert i128 to i64");
        let mut nanos = i32::try_from(self.nanoseconds % SECONDS_TO_NANOS)
            .expect("failed to convert i128 to i32");
        // The `nanos` field in Timestamp is always positive, so we need to
        // adjust accordingly.
        if nanos < 0 {
            nanos += 1_000_000_000;
            seconds -= 1;
        }
        prost_types::Timestamp { seconds, nanos }
    }
}

/// Implements the `Add` trait for `Instant` and `Duration`.
///
/// Allows adding a `Duration` to an `Instant`, resulting in a new
/// `Instant`.
impl Add<Duration> for Instant {
    type Output = Self;

    /// Adds a `Duration` to this `Instant`.
    ///
    /// # Arguments
    ///
    /// * `other`: The `Duration` to add.
    ///
    /// # Returns
    ///
    /// A new `Instant` representing the original instant advanced by `other`.
    fn add(self, other: Duration) -> Self::Output {
        let nanos = self.nanoseconds + other.as_nanos() as i128;
        Self { nanoseconds: nanos }
    }
}

impl Sub<Instant> for Instant {
    type Output = Duration;

    /// Subtracts another `Instant` from this `Instant`.
    ///
    /// # Arguments
    ///
    /// * `other`: The `Instant` to subtract.
    ///
    /// # Returns
    ///
    /// A `Duration` representing the duration between `self` and
    /// `other`. Panics if `other` is later than `self`.
    fn sub(self, other: Instant) -> Self::Output {
        let diff = self.nanoseconds - other.nanoseconds;
        let nanos = u64::try_from(diff).expect("failed to convert i128 to u64");
        Duration::from_nanos(nanos)
    }
}

/// Implements the `AddAssign` trait for `Instant` and `Duration`.
///
/// Allows adding a `Duration` to an `Instant` in-place.
impl AddAssign<Duration> for Instant {
    /// Adds a `Duration` to this `Instant` in-place.
    ///
    /// # Arguments
    ///
    /// * `other`: The `Duration` to add.
    fn add_assign(&mut self, other: Duration) {
        self.nanoseconds += other.as_nanos() as i128;
    }
}

/// Implements the `Sub` trait for `Instant` and `Duration`.
///
/// Allows subtracting a `Duration` from an `Instant`, resulting in
/// a new `Instant`.
impl Sub<Duration> for Instant {
    type Output = Self;

    /// Subtracts a `Duration` from this `Instant`.
    ///
    /// # Arguments
    ///
    /// * `other`: The `Duration` to subtract.
    ///
    /// # Returns
    ///
    /// A new `Instant` representing the original instant moved back by `other`.
    fn sub(self, other: Duration) -> Self {
        Self { nanoseconds: self.nanoseconds - other.as_nanos() as i128 }
    }
}

/// Implements the `SubAssign` trait for `Instant` and `Duration`.
///
/// Allows subtracting a `Duration` from an `Instant` in-place.
impl SubAssign<Duration> for Instant {
    fn sub_assign(&mut self, other: Duration) {
        self.nanoseconds -= other.as_nanos() as i128;
    }
}

#[cfg(feature = "std")]
impl TryFrom<std::time::SystemTime> for Instant {
    type Error = std::time::SystemTimeError;
    /// Tries to convert a `std::time::SystemTime` to an `Instant`.
    ///
    /// # Arguments
    ///
    /// * `instant`: The `std::time::SystemTime` to convert.
    ///
    /// # Returns
    ///
    /// A `Result` containing the `Instant` on success, or a
    /// `std::time::SystemTimeError` if the `SystemTime` is before the Unix
    /// epoch.
    fn try_from(instant: std::time::SystemTime) -> std::result::Result<Self, Self::Error> {
        Ok(UNIX_EPOCH + instant.duration_since(std::time::UNIX_EPOCH).expect("failed"))
    }
}

/// Conditionally implements `From<prost_types::Timestamp>` for `Instant`
/// when the `prost` feature is enabled.
///
/// This allows converting a `prost_types::Timestamp` into an `Instant`.
#[cfg(feature = "prost")]
impl From<&prost_types::Timestamp> for Instant {
    /// Converts a `prost_types::Timestamp` to an `Instant`.
    ///
    /// # Arguments
    ///
    /// * `timestamp`: The `prost_types::Timestamp` to convert.
    fn from(timestamp: &prost_types::Timestamp) -> Self {
        Instant {
            nanoseconds: SECONDS_TO_NANOS * timestamp.seconds as i128 + timestamp.nanos as i128,
        }
    }
}

/// Conditionally implements `From<prost_types::Timestamp>` for `Instant`
/// when the `prost` feature is enabled.
///
/// This allows converting a `prost_types::Timestamp` into an `Instant`.
#[cfg(feature = "prost")]
impl From<prost_types::Timestamp> for Instant {
    /// Converts a `prost_types::Timestamp` to an `Instant`.
    ///
    /// # Arguments
    ///
    /// * `timestamp`: The `prost_types::Timestamp` to convert.
    fn from(timestamp: prost_types::Timestamp) -> Self {
        Instant {
            nanoseconds: SECONDS_TO_NANOS * timestamp.seconds as i128 + timestamp.nanos as i128,
        }
    }
}

impl From<time::UtcDateTime> for Instant {
    fn from(value: time::UtcDateTime) -> Self {
        Instant::from_unix_nanos(value.unix_timestamp_nanos())
    }
}

impl From<time::OffsetDateTime> for Instant {
    fn from(value: time::OffsetDateTime) -> Self {
        Instant::from_unix_nanos(value.unix_timestamp_nanos())
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use googletest::prelude::*;
    use time::macros::{datetime, utc_datetime};

    use super::*;

    // Minimum supported value for Timestamp: 0001-01-01 00:00:00.0 +00:00:00.
    const MIN_VALUE_MILLIS: i64 = -62_135_596_800_000;
    const MIN_VALUE_SECONDS: i64 = -62_135_596_800;

    // Maximum supported value for Timestamp: 9999-12-31T23:59:59.999999999Z.
    const MAX_VALUE_MILLIS: i64 = 253_402_300_799_000;
    const MAX_VALUE_SECONDS: i64 = 253_402_300_799;

    #[googletest::test]
    fn test_unix_seconds_conversion_example() {
        const EXPECTED_SECONDS: i64 = 1234567890;
        let instant = Instant::from_unix_seconds(EXPECTED_SECONDS);
        assert_eq!(EXPECTED_SECONDS, instant.into_unix_seconds());
    }

    #[googletest::test]
    fn test_unix_millis_conversion_example() {
        const EXPECTED_MILLIS: i64 = 1234567890;
        let instant = Instant::from_unix_millis(EXPECTED_MILLIS);
        assert_eq!(EXPECTED_MILLIS, instant.into_unix_millis());
    }

    #[googletest::test]
    fn test_unix_nanos_conversion_example() {
        const EXPECTED_NANOS: i128 = 1234567890123456;
        let instant = Instant::from_unix_nanos(EXPECTED_NANOS);
        assert_eq!(EXPECTED_NANOS, instant.into_unix_nanos());
    }

    #[googletest::test]
    fn test_instant_add() {
        let instant = Instant::from_unix_millis(1000000000);
        let new_instant = instant + Duration::from_millis(1000);
        assert_that!(new_instant, eq(Instant::from_unix_millis(1000001000)));
    }

    #[googletest::test]
    fn test_instant_sub_instant() {
        let instant = Instant::from_unix_millis(1000000000);
        let other = Instant::from_unix_millis(3000000000);
        let diff = other - instant;
        assert_that!(diff, eq(Duration::from_millis(2000000000)));
    }

    #[googletest::test]
    fn test_instant_sub_duration() {
        let instant = Instant::from_unix_millis(1000000000);
        let new_instant = instant - Duration::from_millis(1000);
        assert_that!(new_instant, eq(Instant::from_unix_millis(999999000)));
    }

    #[googletest::test]
    fn test_instant_add_assign() {
        let mut instant = Instant::from_unix_millis(1000000000);
        instant += Duration::from_millis(1000);
        assert_that!(instant, eq(Instant::from_unix_millis(1000001000)));
    }

    #[googletest::test]
    fn test_instant_sub_assign() {
        let mut instant = Instant::from_unix_millis(1000000000);
        instant -= Duration::from_millis(1000);
        assert_that!(instant, eq(Instant::from_unix_millis(999999000)));
    }

    #[cfg(feature = "std")]
    #[googletest::test]
    fn test_instant_from_std_time() -> std::result::Result<(), std::time::SystemTimeError> {
        let instant: Instant = std::time::SystemTime::UNIX_EPOCH.try_into()?;
        assert_that!(instant, eq(Instant::from_unix_millis(0)));

        Ok(())
    }

    #[googletest::test]
    fn test_instant_from_utc_datetime() {
        let source: time::UtcDateTime = utc_datetime!(2014-08-16 11:16);
        let instant: Instant = source.into();
        assert_that!(instant, eq(Instant::from_unix_millis(1408187760000)));
    }

    #[googletest::test]
    fn test_instant_from_offset_datetime() {
        let source: time::OffsetDateTime = datetime!(2014-08-16 11:16+02:00);
        let instant: Instant = source.into();
        assert_that!(instant, eq(Instant::from_unix_millis(1408180560000)));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_timestamp_to_instant_example() {
        let timestamp = prost_types::Timestamp { seconds: 12345, nanos: 67890 };
        let instant = Instant::from(timestamp);
        assert_that!(instant, eq(Instant::UNIX_EPOCH + Duration::new(12345, 67890)));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_instant_to_timestamp_positive() {
        let instant = Instant::from_unix_millis(12345);
        let timestamp = instant.into_timestamp();
        let expected_timestamp = prost_types::Timestamp { seconds: 12, nanos: 345_000_000 };
        assert_that!(&timestamp, eq(&expected_timestamp));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_timestamp_to_instant_negative() {
        let expected = prost_types::Timestamp { seconds: -12345, nanos: 67890 };
        let instant = Instant::from(expected);
        let actual = instant.into_timestamp();
        assert_that!(expected, eq(actual));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_instant_to_timestamp_example() {
        let expected_instant = Instant::from_unix_millis(-12345);
        let actual_timestamp = expected_instant.into_timestamp();
        assert_that!(
            &actual_timestamp,
            eq(&prost_types::Timestamp { seconds: -13, nanos: 655_000_000 })
        );
        let actual_instant = Instant::from(actual_timestamp);
        assert_that!(expected_instant, eq(actual_instant));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_instant_to_timestamp_min() {
        let expected_instant = Instant::from_unix_millis(MIN_VALUE_MILLIS);
        let actual_timestamp = expected_instant.into_timestamp();
        assert_that!(
            &actual_timestamp,
            eq(&prost_types::Timestamp { seconds: MIN_VALUE_SECONDS, nanos: 0 })
        );
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_instant_to_timestamp_max() {
        let expected_instant = Instant::from_unix_millis(MAX_VALUE_MILLIS);
        let actual_timestamp = expected_instant.into_timestamp();
        assert_that!(
            &actual_timestamp,
            eq(&prost_types::Timestamp { seconds: MAX_VALUE_SECONDS, nanos: 0 })
        );
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_timetamp_conversion_left_min() {
        let expected_instant = Instant::from_unix_millis(MIN_VALUE_MILLIS);
        let actual_timestamp = expected_instant.into_timestamp();
        let actual_instant = Instant::from(actual_timestamp);
        assert_that!(expected_instant, eq(actual_instant));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_timetamp_conversion_left_max() {
        let expected_instant = Instant::from_unix_millis(MAX_VALUE_MILLIS);
        let actual_timestamp = expected_instant.into_timestamp();
        let actual_instant = Instant::from(actual_timestamp);
        assert_that!(expected_instant, eq(actual_instant));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_timetamp_conversion_right_min() {
        let expected_timestamp = prost_types::Timestamp { seconds: MIN_VALUE_SECONDS, nanos: 0 };
        let actual_instant = Instant::from(expected_timestamp);
        let actual_timestamp = actual_instant.into_timestamp();
        assert_that!(expected_timestamp, eq(actual_timestamp));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_timetamp_conversion_right_max() {
        let expected_timestamp =
            prost_types::Timestamp { seconds: MAX_VALUE_SECONDS, nanos: 999_999_999 };
        let actual_instant = Instant::from(expected_timestamp);
        let actual_timestamp = actual_instant.into_timestamp();
        assert_that!(expected_timestamp, eq(actual_timestamp));
    }

    #[googletest::test]
    fn test_instant_macro_parsing() {
        // A valid RFC3339 string in UTC.
        assert_that!(
            Instant::from(datetime!(2025-01-01 00:00:00 UTC)),
            eq(Instant::from_unix_millis(1735689600000))
        );

        // A valid RFC3339 string with milliseconds.
        assert_that!(
            Instant::from(datetime!(2025-01-01 00:00:00.123 UTC)),
            eq(Instant::from_unix_millis(1735689600123))
        );

        // A valid RFC3339 string with a positive timezone offset.
        assert_that!(
            Instant::from(datetime!(2025-01-01 02:00:00 +02:00)),
            eq(Instant::from_unix_millis(1735689600000))
        );

        // A valid RFC3339 string with a negative timezone offset.
        assert_that!(
            Instant::from(datetime!(2024-12-31 22:00:00 -02:00)),
            eq(Instant::from_unix_millis(1735689600000))
        );
    }
}
