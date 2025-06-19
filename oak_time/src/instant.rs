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

//! Represents a specific moment in time, measured as the duration since the
//! Unix epoch. The reason for this module is that `core::time::Duration` does
//! not represent a duration since the Unix epoch, but rather a duration between
//! two arbitrary points in time. Using Duration for this purpose is not a good
//! idea, as it can lead to unexpected results.
//!
//! It offers ways to create `Instant`s from various representations (like
//! milliseconds since epoch) and perform arithmetic operations (addition and
//! subtraction with `core::time::Duration`). It also includes conversions from
//! and to other time-related types like `std::time::SystemTime`
//! and `prost_types::Timestamp` when the respective features are enabled.
//!
//! Unlike `std::time::SystemTime`, this module does not have a concept of a
//! "system time" or system time source. It also does not rely (by default) on
//! the std library.

use core::{
    convert::{From, TryInto},
    ops::{Add, AddAssign, Sub, SubAssign},
};

// An anchor in time which can be used to create new Instant instances or learn
// about where in time an Instant lies. This is similar to the
// SystemTime::UNIX_EPOCH.
pub const UNIX_EPOCH: Instant = Instant { unix_epoch_duration: core::time::Duration::new(0, 0) };

/// Represents a specific moment in time.
///
/// Internally, it stores the duration since the Unix epoch (January 1, 1970,
/// 00:00:00 UTC).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Instant {
    unix_epoch_duration: core::time::Duration,
}

impl Instant {
    // An anchor in time which can be used to create new Instant instances or learn
    // about where in time an Instant lies. This is similar to the
    // SystemTime::UNIX_EPOCH.
    pub const UNIX_EPOCH: Instant = UNIX_EPOCH;

    /// Creates a new `Instant` from the number of milliseconds since the Unix
    /// epoch.
    ///
    /// # Arguments
    ///
    /// * `unix_epoch_millis`: The number of milliseconds since the Unix epoch.
    pub fn from_unix_millis(unix_epoch_millis: u64) -> Self {
        UNIX_EPOCH + core::time::Duration::from_millis(unix_epoch_millis)
    }

    /// Creates a new `Instant` from the number of milliseconds since the Unix
    /// epoch.
    ///
    /// # Arguments
    ///
    /// * `unix_epoch_millis`: The number of milliseconds since the Unix epoch.
    ///
    /// # Panics
    ///
    /// Panics if the `unix_epoch_millis` cannot be converted to `u64`.
    pub fn from_unix_millis_i64(unix_epoch_millis: i64) -> Self {
        let unix_epoch_millis: u64 = unix_epoch_millis
            .try_into()
            .expect("Failed to convert milliseconds (value: {unix_epoch_millis})");
        UNIX_EPOCH + core::time::Duration::from_millis(unix_epoch_millis)
    }

    /// Converts this instant into a duration since the Unix epoch.
    pub fn into_unix_epoch_duration(self) -> core::time::Duration {
        self.unix_epoch_duration
    }

    /// Converts this instant into the number of milliseconds since the Unix
    /// epoch.
    pub fn into_unix_millis(self) -> u128 {
        self.unix_epoch_duration.as_millis()
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
        prost_types::Timestamp {
            seconds: self
                .unix_epoch_duration
                .as_secs()
                .try_into()
                .expect("Failed to convert seconds (value: {self.unix_epoch_duration.as_secs()})"),
            nanos: self.unix_epoch_duration.subsec_nanos().try_into().expect(
                "Failed to convert nanoseconds (value: {self.unix_epoch_duration.as_secs()})",
            ),
        }
    }
}

/// Implements the `Add` trait for `Instant` and `core::time::Duration`.
///
/// Allows adding a `core::time::Duration` to an `Instant`, resulting in a new
/// `Instant`.
impl Add<core::time::Duration> for Instant {
    type Output = Self;

    /// Adds a `core::time::Duration` to this `Instant`.
    ///
    /// # Arguments
    ///
    /// * `other`: The `core::time::Duration` to add.
    ///
    /// # Returns
    ///
    /// A new `Instant` representing the original instant advanced by `other`.
    fn add(self, other: core::time::Duration) -> Self::Output {
        Self { unix_epoch_duration: self.unix_epoch_duration + other }
    }
}

impl Sub<Instant> for Instant {
    type Output = core::time::Duration;

    /// Subtracts another `Instant` from this `Instant`.
    ///
    /// # Arguments
    ///
    /// * `other`: The `Instant` to subtract.
    ///
    /// # Returns
    ///
    /// A `core::time::Duration` representing the duration between `self` and
    /// `other`. If `other` is later than `self`, the duration will be
    /// negative (panics if `core::time::Duration` subtraction panics).
    fn sub(self, other: Instant) -> Self::Output {
        self.unix_epoch_duration - other.unix_epoch_duration
    }
}

/// Implements the `AddAssign` trait for `Instant` and `core::time::Duration`.
///
/// Allows adding a `core::time::Duration` to an `Instant` in-place.
impl AddAssign<core::time::Duration> for Instant {
    /// Adds a `core::time::Duration` to this `Instant` in-place.
    ///
    /// # Arguments
    ///
    /// * `other`: The `core::time::Duration` to add.
    fn add_assign(&mut self, other: core::time::Duration) {
        self.unix_epoch_duration += other;
    }
}

/// Implements the `Sub` trait for `Instant` and `core::time::Duration`.
///
/// Allows subtracting a `core::time::Duration` from an `Instant`, resulting in
/// a new `Instant`.
impl Sub<core::time::Duration> for Instant {
    type Output = Self;

    /// Subtracts a `core::time::Duration` from this `Instant`.
    ///
    /// # Arguments
    ///
    /// * `other`: The `core::time::Duration` to subtract.
    ///
    /// # Returns
    ///
    /// A new `Instant` representing the original instant moved back by `other`.
    fn sub(self, other: core::time::Duration) -> Self {
        Self { unix_epoch_duration: self.unix_epoch_duration - other }
    }
}

/// Implements the `SubAssign` trait for `Instant` and `core::time::Duration`.
///
/// Allows subtracting a `core::time::Duration` from an `Instant` in-place.
impl SubAssign<core::time::Duration> for Instant {
    fn sub_assign(&mut self, other: core::time::Duration) {
        self.unix_epoch_duration -= other;
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
        Ok(UNIX_EPOCH + instant.duration_since(std::time::UNIX_EPOCH)?)
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
    ///
    /// # Panics
    ///
    /// Panics if the `seconds` or `nanos` fields of the `timestamp` cannot be
    /// converted to their respective types (`u64` and `u32`).
    fn from(timestamp: &prost_types::Timestamp) -> Self {
        let unix_epoch_duration = core::time::Duration::new(
            timestamp
                .seconds
                .try_into()
                .expect("Failed to convert seconds (value: {timestamp.seconds})"),
            timestamp.nanos.try_into().expect("Failed to convert nanos (value: {timestamp.nanos})"),
        );
        UNIX_EPOCH + unix_epoch_duration
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
    ///
    /// # Panics
    ///
    /// Panics if the `seconds` or `nanos` fields of the `timestamp` cannot be
    /// converted to their respective types (`u64` and `u32`).
    fn from(timestamp: prost_types::Timestamp) -> Self {
        Instant::from(&timestamp)
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use googletest::prelude::*;

    use crate::instant::Instant;

    #[googletest::test]
    fn test_instant() {
        let instant = Instant::from_unix_millis(1234567890);
        assert_that!(
            instant.into_unix_epoch_duration(),
            eq(core::time::Duration::from_millis(1234567890))
        );
    }

    #[googletest::test]
    fn test_instant_from_unix_millis_i64() {
        let instant = Instant::from_unix_millis_i64(1234567890_i64);
        assert_that!(
            instant.into_unix_epoch_duration(),
            eq(core::time::Duration::from_millis(1234567890))
        );
    }

    #[googletest::test]
    fn test_instant_add() {
        let instant = Instant::from_unix_millis(1000000000);
        let new_instant = instant + core::time::Duration::from_millis(1000);
        assert_that!(new_instant, eq(Instant::from_unix_millis(1000001000)));
    }

    #[googletest::test]
    fn test_instant_sub_instant() {
        let instant = Instant::from_unix_millis(1000000000);
        let other = Instant::from_unix_millis(3000000000);
        let diff = other - instant;
        assert_that!(diff, eq(core::time::Duration::from_millis(2000000000)));
    }

    #[googletest::test]
    fn test_instant_sub_duration() {
        let instant = Instant::from_unix_millis(1000000000);
        let new_instant = instant - core::time::Duration::from_millis(1000);
        assert_that!(new_instant, eq(Instant::from_unix_millis(999999000)));
    }

    #[googletest::test]
    fn test_instant_add_assign() {
        let mut instant = Instant::from_unix_millis(1000000000);
        instant += core::time::Duration::from_millis(1000);
        assert_that!(instant, eq(Instant::from_unix_millis(1000001000)));
    }

    #[googletest::test]
    fn test_instant_sub_assign() {
        let mut instant = Instant::from_unix_millis(1000000000);
        instant -= core::time::Duration::from_millis(1000);
        assert_that!(instant, eq(Instant::from_unix_millis(999999000)));
    }

    #[cfg(feature = "std")]
    #[googletest::test]
    fn test_instant_from_std_time() -> std::result::Result<(), std::time::SystemTimeError> {
        let instant: Instant = std::time::SystemTime::UNIX_EPOCH.try_into()?;
        assert_that!(instant, eq(Instant::from_unix_millis(0)));

        Ok(())
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_instant_from_prost_types() {
        let timestamp = prost_types::Timestamp { seconds: 12345, nanos: 67890 };
        let instant = Instant::from(timestamp);
        assert_that!(instant, eq(Instant::UNIX_EPOCH + core::time::Duration::new(12345, 67890)));
    }

    #[cfg(feature = "prost")]
    #[googletest::test]
    fn test_instant_into_prost_types() {
        let instant = Instant::from_unix_millis(12345);
        let timestamp = instant.into_timestamp();
        let expected_timestamp = prost_types::Timestamp { seconds: 12, nanos: 345_000_000 };
        assert_that!(&timestamp, eq(&expected_timestamp));
    }
}
