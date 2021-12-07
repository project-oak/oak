use std::fmt;
use std::ops;

use chrono::TimeZone;

use super::Date;

/// The time zone with fixed offset, from UTC-23:59:59 to UTC+23:59:59.
pub type FixedOffset = chrono::FixedOffset;

/// Liquid's native date + time type.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
#[serde(transparent)]
#[repr(transparent)]
pub struct DateTime {
    #[serde(with = "friendly_date_time")]
    inner: DateTimeImpl,
}

type DateTimeImpl = chrono::DateTime<chrono::FixedOffset>;

impl DateTime {
    /// Create a `DateTime` from the current moment.
    pub fn now() -> Self {
        let d = chrono::Utc::now().with_timezone(&chrono::FixedOffset::east(0));
        Self::with_chrono(d)
    }

    /// Convert a `str` to `Self`
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(other: &str) -> Option<Self> {
        parse_date_time(other).map(|d| Self { inner: d })
    }

    /// Replace fields with `other`.
    pub fn with_date(self, other: Date) -> Self {
        use chrono::{NaiveDateTime, NaiveTime};
        let other = DateTimeImpl::from_utc(
            NaiveDateTime::new(other.inner, NaiveTime::from_hms(0, 0, 0)),
            *self.inner.offset(),
        );
        Self::with_chrono(other)
    }

    /// Changes the associated time zone. This does not change the actual DateTime (but will change the string representation).
    pub fn with_timezone(&self, tz: &chrono::FixedOffset) -> Self {
        Self::with_chrono(self.inner.with_timezone(tz))
    }

    /// Retrieves a date component.
    pub fn date(&self) -> Date {
        Date::with_chrono(self.inner.naive_utc().date())
    }

    /// Formats the combined date and time with the specified format string. See the
    /// chrono::format::strftime module on the supported escape sequences.
    pub fn format<'a>(&self, fmt: &'a str) -> impl fmt::Display + 'a {
        self.inner.format(fmt)
    }

    fn with_chrono(inner: DateTimeImpl) -> Self {
        Self { inner }
    }
}

impl Default for DateTime {
    fn default() -> Self {
        let d = chrono::Utc
            .timestamp(0, 0)
            .with_timezone(&chrono::FixedOffset::east(0));
        DateTime::with_chrono(d)
    }
}

impl fmt::Display for DateTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.format(DATE_TIME_FORMAT).fmt(f)
    }
}

impl ops::Deref for DateTime {
    type Target = chrono::DateTime<chrono::FixedOffset>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl ops::DerefMut for DateTime {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl chrono::Datelike for DateTime {
    #[inline]
    fn year(&self) -> i32 {
        self.inner.year()
    }
    #[inline]
    fn month(&self) -> u32 {
        self.inner.month()
    }
    #[inline]
    fn month0(&self) -> u32 {
        self.inner.month0()
    }
    #[inline]
    fn day(&self) -> u32 {
        self.inner.day()
    }
    #[inline]
    fn day0(&self) -> u32 {
        self.inner.day0()
    }
    #[inline]
    fn ordinal(&self) -> u32 {
        self.inner.ordinal()
    }
    #[inline]
    fn ordinal0(&self) -> u32 {
        self.inner.ordinal0()
    }
    #[inline]
    fn weekday(&self) -> chrono::Weekday {
        self.inner.weekday()
    }
    #[inline]
    fn iso_week(&self) -> chrono::IsoWeek {
        self.inner.iso_week()
    }

    #[inline]
    fn with_year(&self, year: i32) -> Option<Self> {
        self.inner.with_year(year).map(Self::with_chrono)
    }

    #[inline]
    fn with_month(&self, month: u32) -> Option<Self> {
        self.inner.with_month(month).map(Self::with_chrono)
    }

    #[inline]
    fn with_month0(&self, month0: u32) -> Option<Self> {
        self.inner.with_month0(month0).map(Self::with_chrono)
    }

    #[inline]
    fn with_day(&self, day: u32) -> Option<Self> {
        self.inner.with_day(day).map(Self::with_chrono)
    }

    #[inline]
    fn with_day0(&self, day0: u32) -> Option<Self> {
        self.inner.with_day(day0).map(Self::with_chrono)
    }

    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<Self> {
        self.inner.with_ordinal(ordinal).map(Self::with_chrono)
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<Self> {
        self.inner.with_ordinal0(ordinal0).map(Self::with_chrono)
    }
}

impl chrono::Timelike for DateTime {
    #[inline]
    fn hour(&self) -> u32 {
        self.inner.hour()
    }
    #[inline]
    fn minute(&self) -> u32 {
        self.inner.minute()
    }
    #[inline]
    fn second(&self) -> u32 {
        self.inner.second()
    }
    #[inline]
    fn nanosecond(&self) -> u32 {
        self.inner.nanosecond()
    }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<Self> {
        self.inner.with_hour(hour).map(Self::with_chrono)
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<Self> {
        self.inner.with_minute(min).map(Self::with_chrono)
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<Self> {
        self.inner.with_second(sec).map(Self::with_chrono)
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<Self> {
        self.inner.with_nanosecond(nano).map(Self::with_chrono)
    }
}

const DATE_TIME_FORMAT: &str = "%Y-%m-%d %H:%M:%S %z";

mod friendly_date_time {
    use super::*;
    use serde::{self, Deserialize, Deserializer, Serializer};

    pub(crate) fn serialize<S>(date: &DateTimeImpl, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let s = date.format(DATE_TIME_FORMAT).to_string();
        serializer.serialize_str(&s)
    }

    pub(crate) fn deserialize<'de, D>(deserializer: D) -> Result<DateTimeImpl, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        DateTimeImpl::parse_from_str(&s, DATE_TIME_FORMAT).map_err(serde::de::Error::custom)
    }
}

fn parse_date_time(s: &str) -> Option<DateTimeImpl> {
    match s {
        "now" => {
            use chrono::offset;
            let now = offset::Utc::now();
            let now = now.naive_utc();
            let now = DateTimeImpl::from_utc(now, offset::FixedOffset::east(0));
            Some(now)
        }
        _ => {
            let formats = ["%d %B %Y %H:%M:%S %z", "%Y-%m-%d %H:%M:%S %z"];
            formats
                .iter()
                .filter_map(|f| DateTimeImpl::parse_from_str(s, f).ok())
                .next()
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_date_time_empty_is_bad() {
        let input = "";
        let actual = parse_date_time(input);
        assert!(actual.is_none());
    }

    #[test]
    fn parse_date_time_bad() {
        let input = "aaaaa";
        let actual = parse_date_time(input);
        assert!(actual.is_none());
    }

    #[test]
    fn parse_date_time_now() {
        let input = "now";
        let actual = parse_date_time(input);
        assert!(actual.is_some());
    }

    #[test]
    fn parse_date_time_serialized_format() {
        let input = "2016-02-16 10:00:00 +0100";
        let actual = parse_date_time(input);
        assert!(actual.is_some());
    }

    #[test]
    fn parse_date_time_to_string() {
        let date = DateTime::now();
        let input = date.to_string();
        let actual = parse_date_time(&input);
        assert!(actual.is_some());
    }
}
