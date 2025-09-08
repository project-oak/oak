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
//! Doesn't offer support for time zones: any I/O or operations are done in
//! terms of UTC.
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

use alloc::{format, string::String};
use core::ops::{Add, AddAssign, Sub, SubAssign};

use chrono::{DateTime, Utc};

use crate::Duration;

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
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
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
        let (seconds, nanos) = self.into_second_nanos();
        prost_types::Timestamp { seconds, nanos }
    }

    fn from_seconds_nanos(seconds: i64, nanos: i32) -> Self {
        Instant { nanoseconds: SECONDS_TO_NANOS * seconds as i128 + nanos as i128 }
    }

    fn into_second_nanos(self) -> (i64, i32) {
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
        (seconds, nanos)
    }
}

/// Convert an instant into a DateTime in UTC
impl From<Instant> for DateTime<Utc> {
    fn from(value: Instant) -> Self {
        let (seconds, nanos) = value.into_second_nanos();
        // It's OK to convert nanos to u32 because nanos will always be >= 0.
        DateTime::from_timestamp(seconds, nanos as u32).expect("out of range instant")
    }
}

/// Convert a DateTime in UTC into an Instant
impl From<DateTime<Utc>> for Instant {
    fn from(value: DateTime<Utc>) -> Self {
        let seconds = value.timestamp();
        let nanos = value.timestamp_subsec_nanos();
        Self::from_seconds_nanos(seconds, nanos as i32)
    }
}

/// Parses a timestamp given as RFC3339-encoded string into an Instant.
impl TryFrom<&str> for Instant {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let utc: DateTime<Utc> = DateTime::parse_from_rfc3339(value)
            .map_err(|err| format!("failed to parse RFC3339 timestamp: {:?}", err))?
            .into();
        Ok(Self::from(utc))
    }
}

/// Generates instances from human-readable RFC3339 strings. Useful in tests.
#[macro_export]
macro_rules! make_instant {
    ($date:literal) => {
        Instant::try_from($date).expect("bad RFC3339 date")
    };
}

impl core::fmt::Display for Instant {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let datetime: DateTime<Utc> = (*self).into();
        write!(f, "{}", datetime.to_rfc3339())
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
        let nanos = self.nanoseconds + other.into_nanos();
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
    /// A `Duration` representing the signed duration between `self` and
    /// `other`.
    fn sub(self, other: Instant) -> Self::Output {
        Duration::from_nanos(self.nanoseconds - other.nanoseconds)
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
        self.nanoseconds += other.into_nanos();
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
        Self { nanoseconds: self.nanoseconds - other.into_nanos() }
    }
}

/// Implements the `SubAssign` trait for `Instant` and `Duration`.
///
/// Allows subtracting a `Duration` from an `Instant` in-place.
impl SubAssign<Duration> for Instant {
    fn sub_assign(&mut self, other: Duration) {
        self.nanoseconds -= other.into_nanos();
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

/// Support [RFC3339 format] on serializing and deserializing an [`Instant`].
/// Use this module in combination with serde's [`#[with]`][with] attribute.
///
/// On deserialization the time zone is lost, so serialized timestamps will
/// always be in UTC. Even though this has some partial support for time zones,
/// they should be avoided altogether.
///
/// [RFC3339 format]: https://tools.ietf.org/html/rfc3339#section-5.6
/// [with]: https://serde.rs/field-attrs.html#with
pub mod rfc3339 {
    use core::fmt;

    use chrono::{DateTime, Utc};
    use serde::{
        de::{self, Visitor},
        Deserializer, Serializer,
    };

    use super::Instant;

    /// Serializes an [`Instant`] to RFC3339 format.
    pub fn serialize<S: Serializer>(instant: &Instant, serializer: S) -> Result<S::Ok, S::Error> {
        let utc: DateTime<Utc> = (*instant).into();
        serializer.serialize_str(&utc.to_rfc3339())
    }

    /// Deserializes an [`Instant`] from its RFC3339 representation.
    pub fn deserialize<'a, D: Deserializer<'a>>(deserializer: D) -> Result<Instant, D::Error> {
        struct DateVisitor;

        impl Visitor<'_> for DateVisitor {
            type Value = Instant;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("RFC3339 timestamp encoded as string")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Instant::try_from(value).map_err(E::custom)
            }
        }

        deserializer.deserialize_str(DateVisitor)
    }
}

/// Support deserializing an [`Instant`] from a unix timestamp.
/// Use this module in combination with serde's [`#[with]`][with] attribute.
///
/// [with]: https://serde.rs/field-attrs.html#with
pub mod unix_timestamp {
    use serde::{Deserialize, Deserializer, Serializer};

    use super::Instant;

    /// Deserializes an [`Instant`] from a unix timestamp.
    pub fn deserialize<'de, D>(deserializer: D) -> Result<Instant, D::Error>
    where
        D: Deserializer<'de>,
    {
        let seconds = i64::deserialize(deserializer)?;
        Ok(Instant::from_unix_seconds(seconds))
    }

    pub fn serialize<S>(instant: &Instant, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let seconds = instant.into_unix_seconds();
        serializer.serialize_i64(seconds)
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use chrono::{DateTime, Utc};
    use googletest::prelude::*;

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

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_timestamp_to_instant_example() {
        let timestamp = prost_types::Timestamp { seconds: 12345, nanos: 67890 };
        let instant = Instant::from(timestamp);
        assert_that!(
            instant,
            eq(Instant::UNIX_EPOCH + Duration::from_nanos(12345 * SECONDS_TO_NANOS + 67890))
        );
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
            make_instant!("2025-01-01T00:00:00Z"),
            eq(Instant::from_unix_millis(1735689600000))
        );

        // A valid RFC3339 string with milliseconds.
        assert_that!(
            make_instant!("2025-01-01T00:00:00.123Z"),
            eq(Instant::from_unix_millis(1735689600123))
        );

        // A valid RFC3339 string with a positive timezone offset.
        assert_that!(
            make_instant!("2025-01-01T02:00:00+02:00"),
            eq(Instant::from_unix_millis(1735689600000))
        );

        // A valid RFC3339 string with a negative timezone offset.
        assert_that!(
            make_instant!("2024-12-31T22:00:00-02:00"),
            eq(Instant::from_unix_millis(1735689600000))
        );
    }

    #[googletest::test]
    fn test_instant_into_chrono_datetime() {
        let instant = Instant::from_unix_millis(1735689600123);
        let datetime: DateTime<Utc> = instant.into();
        assert_that!(datetime.to_rfc3339(), eq("2025-01-01T00:00:00.123+00:00"));
    }

    #[googletest::test]
    fn test_instant_from_chrono_datetime() {
        let datetime = DateTime::parse_from_rfc3339("2025-01-01T00:00:00.123+00:00")
            .unwrap()
            .with_timezone(&Utc);
        let instant: Instant = datetime.into();
        assert_that!(instant, eq(Instant::from_unix_millis(1735689600123)));
    }

    #[googletest::test]
    fn test_instant_display() {
        let instant = Instant::from_unix_millis(1735689600123);
        assert_that!(std::format!("{}", instant), eq("2025-01-01T00:00:00.123+00:00"));
    }
}
