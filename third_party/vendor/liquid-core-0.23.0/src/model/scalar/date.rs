use std::fmt;
use std::ops;

/// Liquid's native date only type.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
#[serde(transparent)]
pub struct Date {
    #[serde(with = "friendly_date")]
    pub(crate) inner: DateImpl,
}

type DateImpl = chrono::NaiveDate;

impl Date {
    /// Makes a new NaiveDate from the calendar date (year, month and day).
    ///
    /// Panics on the out-of-range date, invalid month and/or day.
    pub fn from_ymd(year: i32, month: u32, day: u32) -> Self {
        Self::with_chrono(DateImpl::from_ymd(year, month, day))
    }

    /// Convert a `str` to `Self`
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(other: &str) -> Option<Self> {
        parse_date(other).map(|d| Self { inner: d })
    }

    pub(crate) fn with_chrono(inner: DateImpl) -> Self {
        Self { inner }
    }
}

impl fmt::Display for Date {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.format(DATE_FORMAT).fmt(f)
    }
}

impl ops::Deref for Date {
    type Target = chrono::NaiveDate;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl ops::DerefMut for Date {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl chrono::Datelike for Date {
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

const DATE_FORMAT: &str = "%Y-%m-%d";

mod friendly_date {
    use super::*;
    use serde::{self, Deserialize, Deserializer, Serializer};

    pub(crate) fn serialize<S>(date: &DateImpl, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let s = date.format(DATE_FORMAT).to_string();
        serializer.serialize_str(&s)
    }

    pub(crate) fn deserialize<'de, D>(deserializer: D) -> Result<DateImpl, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        DateImpl::parse_from_str(&s, DATE_FORMAT).map_err(serde::de::Error::custom)
    }
}

fn parse_date(s: &str) -> Option<DateImpl> {
    match s {
        "today" => {
            use chrono::offset::Utc;
            Some(Utc::today().naive_utc())
        }
        _ => {
            let formats = ["%d %B %Y", "%Y-%m-%d"];
            formats
                .iter()
                .filter_map(|f| DateImpl::parse_from_str(s, f).ok())
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
        let actual = parse_date(input);
        assert!(actual.is_none());
    }

    #[test]
    fn parse_date_time_bad() {
        let input = "aaaaa";
        let actual = parse_date(input);
        assert!(actual.is_none());
    }

    #[test]
    fn parse_date_today() {
        let input = "today";
        let actual = parse_date(input);
        assert!(actual.is_some());
    }
}
