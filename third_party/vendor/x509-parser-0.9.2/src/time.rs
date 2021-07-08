use std::ops::{Add, Sub};
use std::time::Duration;
use std::time::SystemTime;

use chrono::offset::{TimeZone, Utc};
use chrono::{DateTime, Datelike};
use der_parser::ber::{ber_read_element_header, BerObjectContent, BerTag, MAX_OBJECT_SIZE};
use der_parser::der::{parse_der_generalizedtime, parse_der_utctime, DerObject};
use der_parser::error::{BerError, DerResult};
use nom::branch::alt;
use nom::bytes::complete::take;
use nom::combinator::{complete, map_res, opt};

use crate::error::{X509Error, X509Result};

/// An ASN.1 timestamp.
#[derive(Copy, Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct ASN1Time(DateTime<Utc>);

impl ASN1Time {
    pub(crate) fn from_der(i: &[u8]) -> X509Result<Self> {
        map_res(parse_choice_of_time, der_to_utctime)(i).map_err(|_| X509Error::InvalidDate.into())
    }

    pub(crate) fn from_der_opt(i: &[u8]) -> X509Result<Option<Self>> {
        opt(map_res(parse_choice_of_time, der_to_utctime))(i)
            .map_err(|_| X509Error::InvalidDate.into())
    }

    #[inline]
    pub(crate) fn from_datetime_utc(dt: DateTime<Utc>) -> Self {
        ASN1Time(dt)
    }

    /// Makes a new `ASN1Time` from the number of non-leap seconds since Epoch
    pub fn from_timestamp(secs: i64) -> Self {
        ASN1Time(Utc.timestamp(secs, 0))
    }

    /// Returns the number of non-leap seconds since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    #[inline]
    pub fn timestamp(&self) -> i64 {
        self.0.timestamp()
    }

    /// Returns a `ASN1Time` which corresponds to the current date.
    #[inline]
    pub fn now() -> Self {
        ASN1Time(SystemTime::now().into())
    }

    /// Returns an RFC 2822 date and time string such as `Tue, 1 Jul 2003 10:52:37 +0200`.
    #[inline]
    pub fn to_rfc2822(&self) -> String {
        self.0.to_rfc2822()
    }
}

fn parse_choice_of_time(i: &[u8]) -> DerResult {
    alt((
        complete(parse_der_utctime),
        complete(parse_der_generalizedtime),
        complete(parse_malformed_date),
    ))(i)
}

// allow relaxed parsing of UTCTime (ex: 370116130016+0000)
fn parse_malformed_date(i: &[u8]) -> DerResult {
    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn check_char(b: &u8) -> bool {
        (0x20 <= *b && *b <= 0x7f) || (*b == b'+')
    }
    let (rem, hdr) = ber_read_element_header(i)?;
    let len = hdr.len.primitive()?;
    if len > MAX_OBJECT_SIZE {
        return Err(nom::Err::Error(BerError::InvalidLength));
    }
    match hdr.tag {
        BerTag::UtcTime => {
            // if we are in this function, the PrintableString could not be validated.
            // Accept it without validating charset, because some tools do not respect the charset
            // restrictions (for ex. they use '*' while explicingly disallowed)
            let (rem, data) = take(len as usize)(rem)?;
            if !data.iter().all(check_char) {
                return Err(nom::Err::Error(BerError::BerValueError));
            }
            let s = std::str::from_utf8(data).map_err(|_| BerError::BerValueError)?;
            let content = BerObjectContent::UTCTime(s);
            let obj = DerObject::from_header_and_content(hdr, content);
            Ok((rem, obj))
        }
        _ => Err(nom::Err::Error(BerError::InvalidTag)),
    }
}

pub(crate) fn der_to_utctime(obj: DerObject) -> Result<ASN1Time, X509Error> {
    if let BerObjectContent::UTCTime(s) = obj.content {
        let dt = if s.ends_with('Z') {
            // UTC
            if s.len() == 11 {
                // some implementations do not encode the number of seconds
                // accept certificate even if date is not correct
                Utc.datetime_from_str(s, "%y%m%d%H%MZ")
            } else {
                Utc.datetime_from_str(s, "%y%m%d%H%M%SZ")
            }
        } else {
            DateTime::parse_from_str(s, "%y%m%d%H%M%S%z").map(|dt| dt.with_timezone(&Utc))
        };
        match dt {
            Ok(mut tm) => {
                if tm.year() < 50 {
                    tm = tm
                        .with_year(tm.year() + 100)
                        .ok_or(X509Error::InvalidDate)?;
                }
                // tm = tm.with_year(tm.year() + 1900).ok_or(X509Error::InvalidDate)?;
                // eprintln!("date: {}", tm.rfc822());
                Ok(ASN1Time::from_datetime_utc(tm))
            }
            Err(_e) => Err(X509Error::InvalidDate),
        }
    } else if let BerObjectContent::GeneralizedTime(s) = obj.content {
        let dt = if s.ends_with('Z') {
            // UTC
            if s.len() == 11 {
                // some implementations do not encode the number of seconds
                // accept certificate even if date is not correct
                Utc.datetime_from_str(s, "%Y%m%d%H%MZ")
            } else {
                Utc.datetime_from_str(s, "%Y%m%d%H%M%SZ")
            }
        } else {
            DateTime::parse_from_str(s, "%Y%m%d%H%M%S%z").map(|dt| dt.with_timezone(&Utc))
        };
        dt.map(ASN1Time::from_datetime_utc)
            .or(Err(X509Error::InvalidDate))
    } else {
        Err(X509Error::InvalidDate)
    }
}

impl Add<Duration> for ASN1Time {
    type Output = Option<ASN1Time>;

    #[inline]
    fn add(self, rhs: Duration) -> Option<ASN1Time> {
        let secs = rhs.as_secs();
        // u32::MAX is not supported in rust 1.34
        const MAX_U32: u64 = 4_294_967_295;
        if secs > MAX_U32 {
            return None;
        }
        let duration = chrono::Duration::seconds(secs as i64);
        let dt = self.0.checked_add_signed(duration)?;
        Some(ASN1Time(dt))
    }
}

impl Sub<ASN1Time> for ASN1Time {
    type Output = Option<Duration>;

    #[inline]
    fn sub(self, rhs: ASN1Time) -> Option<Duration> {
        self.0.signed_duration_since(rhs.0).to_std().ok()
    }
}
