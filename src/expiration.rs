//! This module contains the [`Expiration`] type and its [`DateTime`] helper type.

pub use crate::max_age::Duration;
#[cfg(all(feature = "chrono", not(feature = "time")))]
use crate::ChronoDateTimeExt as _;


/// A cookie's expiration: either session or a date-time.
///
/// An `Expiration` is constructible via `Expiration::from()` with an
/// `Option<DateTime>` or an `DateTime`:
///
///   * `None` -> `Expiration::Session`
///   * `Some(DateTime)` -> `Expiration::DateTime`
///   * `DateTime` -> `Expiration::DateTime`
///
/// ```rust
/// use cookie::{Expiration, expiration::DateTime};
///
/// let expires = Expiration::from(None);
/// assert_eq!(expires, Expiration::Session);
///
/// let now = DateTime::now();
/// let expires = Expiration::from(now);
/// assert_eq!(expires, Expiration::DateTime(now));
///
/// let expires = Expiration::from(Some(now));
/// assert_eq!(expires, Expiration::DateTime(now));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Expiration {
    /// Expiration for a "permanent" cookie at a specific date-time.
    DateTime(DateTime),
    /// Expiration for a "session" cookie. Browsers define the notion of a
    /// "session" and will automatically expire session cookies when they deem
    /// the "session" to be over. This is typically, but need not be, when the
    /// browser is closed.
    Session,
}

impl Expiration {
    /// Returns `true` if `self` is an `Expiration::DateTime`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use cookie::{Expiration, expiration::DateTime};
    ///
    /// let expires = Expiration::from(None);
    /// assert!(!expires.is_datetime());
    ///
    /// let expires = Expiration::from(DateTime::now());
    /// assert!(expires.is_datetime());
    /// ```
    pub fn is_datetime(&self) -> bool {
        match self {
            Expiration::DateTime(_) => true,
            Expiration::Session => false
        }
    }

    /// Returns `true` if `self` is an `Expiration::Session`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use cookie::{Expiration, expiration::DateTime};
    ///
    /// let expires = Expiration::from(None);
    /// assert!(expires.is_session());
    ///
    /// let expires = Expiration::from(DateTime::now());
    /// assert!(!expires.is_session());
    /// ```
    pub fn is_session(&self) -> bool {
        match self {
            Expiration::DateTime(_) => false,
            Expiration::Session => true
        }
    }

    /// Returns the inner `DateTime` if `self` is a `DateTime`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use cookie::{Expiration, expiration::DateTime};
    ///
    /// let expires = Expiration::from(None);
    /// assert!(expires.datetime().is_none());
    ///
    /// let now = DateTime::now();
    /// let expires = Expiration::from(now);
    /// assert_eq!(expires.datetime(), Some(now));
    /// ```
    pub fn datetime(self) -> Option<DateTime> {
        match self {
            Expiration::Session => None,
            Expiration::DateTime(v) => Some(v)
        }
    }

    /// Applied `f` to the inner `DateTime` if `self` is a `DateTime` and
    /// returns the mapped `Expiration`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use cookie::{Expiration, expiration::{DateTime, Duration}};
    ///
    /// let now = DateTime::now();
    /// let one_week = Duration::from_naive_days(7);
    ///
    /// let expires = Expiration::from(now);
    /// assert_eq!(expires.map(|t| t + one_week).datetime(), Some(now + one_week));
    ///
    /// let expires = Expiration::from(None);
    /// assert_eq!(expires.map(|t| t + one_week).datetime(), None);
    /// ```
    pub fn map<F>(self, f: F) -> Self
        where F: FnOnce(DateTime) -> DateTime
    {
        match self {
            Expiration::Session => Expiration::Session,
            Expiration::DateTime(v) => Expiration::DateTime(f(v)),
        }
    }
}

impl<T: Into<Option<DateTime>>> From<T> for Expiration {
    fn from(option: T) -> Self {
        match option.into() {
            Some(value) => Expiration::DateTime(value),
            None => Expiration::Session
        }
    }
}

/// A cookie’s combined expiration date & time, kept within the range of
/// 4-digit years (the year range 1,000…9,999, inclusive).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DateTime(
    #[cfg(all(feature = "chrono", not(feature = "time")))]
    chrono::DateTime<chrono::FixedOffset>,
    #[cfg(feature = "time")]
    time::OffsetDateTime,
);

impl DateTime {

    /// The lower bound of the valid `DateTime` range (the first instant of the
    /// UTC year 1,000).
    #[cfg(feature = "time")]
    #[cfg_attr(all(nightly, doc), doc(cfg(feature = "time")))]
    pub const MIN: Self = Self(time::macros::datetime!(1000-01-01 00:00:00.000_000 UTC));

    /// The upper bound of the valid `DateTime` range (one microsecond before
    /// the UTC year 10,000).
    #[cfg(feature = "time")]
    #[cfg_attr(all(nightly, doc), doc(cfg(feature = "time")))]
    pub const MAX: Self = Self(time::macros::datetime!(9999-12-31 23:59:59.999_999 UTC));

    /// Creates a new `DateTime` with the current date & time in UTC.
    pub fn now() -> Self {
        #[cfg(feature = "time")]
        { Self(time::OffsetDateTime::now_utc()) }
        #[cfg(all(feature = "chrono", not(feature = "time")))]
        { Self(chrono::Utc::now().ext_fixed_offset()) }
    }

    /// Returns the lower bound of the valid `DateTime` range (the first
    /// instant of the UTC year 1,000).
    pub fn min() -> Self {
        #[cfg(feature = "time")]
        { Self::MIN }
        #[cfg(all(feature = "chrono", not(feature = "time")))]
        {
            use crate::ChronoNaiveDateTimeExt as _;
            Self(chrono::NaiveDate::from_ymd_opt(1000, 1, 1)
                .and_then(|d| d.and_hms_opt(0, 0, 0))
                .unwrap()
                .ext_and_utc()
                .ext_fixed_offset())
        }
    }

    /// Returns the upper bound of the valid `DateTime` range (one microsecond
    /// before the UTC year 10,000).
    pub fn max() -> Self {
        #[cfg(feature = "time")]
        { Self::MAX }
        #[cfg(all(feature = "chrono", not(feature = "time")))]
        {
            use crate::ChronoNaiveDateTimeExt as _;
            Self(chrono::NaiveDate::from_ymd_opt(9999, 12, 31)
                .and_then(|d| d.and_hms_micro_opt(23, 59, 59, 999_999))
                .unwrap()
                .ext_and_utc()
                .ext_fixed_offset())
        }
    }

    /// Returns the number of seconds to this `DateTime` since Unix epoch.
    pub fn unix_timestamp(&self) -> i64 {
        #[cfg(feature = "time")]
        { self.0.unix_timestamp() }
        #[cfg(all(feature = "chrono", not(feature = "time")))]
        { self.0.timestamp() }
    }

    /// Formats the `DateTime` with a UTC offset.
    #[cfg(feature = "time")]
    pub(crate) fn format(&self, fmt: &[time::format_description::FormatItem<'_>])
    -> Result<String, time::error::Format> {
        self.0.to_offset(time::UtcOffset::UTC).format(fmt)
    }

    /// Formats the `DateTime` with a UTC offset.
    #[cfg(all(feature = "chrono", not(feature = "time")))]
    pub(crate) fn format(&self, fmt: &'static str) -> Result<String, ()> {
        Ok(chrono::DateTime::<chrono::Utc>::from(self.0).format(fmt).to_string())
    }

    /// Creates a new `DateTime` with the same date & time and timezone offset
    /// as the [`OffsetDateTime`][todt], clamped to the range [`MIN`]…[`MAX`]
    /// (inclusive).
    ///
    /// The timezone offset will be preserved (unless clamped), and will be
    /// included in any [`OffsetDateTime`][todt] returned from calling
    /// [`into_time`] on a `DateTime` created through `from_time`, but is
    /// otherwise opaque.
    ///
    /// [todt]: time::OffsetDateTime
    #[cfg(feature = "time")]
    #[cfg_attr(all(nightly, doc), doc(cfg(feature = "time")))]
    pub fn from_time(datetime: time::OffsetDateTime) -> Self {
        Self(datetime).min(Self::MAX).max(Self::MIN)
    }

    /// Returns the [`OffsetDateTime`][todt] with the same date & time and
    /// timezone offset as this `DateTime`.
    ///
    /// If this `DateTime` was created from an [`OffsetDateTime`][todt] the
    /// timezone offset will be preserved (unless it was clamped), otherwise
    /// it will be UTC.
    ///
    /// [todt]: time::OffsetDateTime
    #[cfg(feature = "time")]
    #[cfg_attr(all(nightly, doc), doc(cfg(feature = "time")))]
    pub fn into_time(self) -> time::OffsetDateTime {
        self.0
    }

    /// Creates a new `DateTime` with the same date & time and fixed timezone
    /// offset as the [`chrono::DateTime`][cdt], clamped to the range
    /// [`min()`]…[`max()`] (inclusive).
    ///
    /// Any timezoe offset of the [`chrono::DateTime`][cdt] will be fixed, but
    /// otherwise preserved (unless clamped). It will be included in any
    /// [`chrono::DateTime<chrono::FixedOffset>`][cdt] returned from calling
    /// [`into_chrono`] on a `DateTime` created through `from_chrono`, but is
    /// otherwise opaque.
    ///
    /// [cdt]: chrono::DateTime
    #[cfg(feature = "chrono")]
    #[cfg_attr(all(nightly, doc), doc(cfg(feature = "chrono")))]
    pub fn from_chrono<Tz: chrono::TimeZone>(datetime: chrono::DateTime<Tz>) -> Self {
        #[cfg(feature = "time")]
        {
            use chrono::Offset as _;
            let offset = time::UtcOffset::from_whole_seconds(datetime.offset().fix().local_minus_utc())
                .expect("`DateTime` only supports ±1-day offsets");
            Self::from_time(time::OffsetDateTime::from_unix_timestamp_nanos(datetime.timestamp_nanos() as i128)
                .expect("`DateTime` only supports typical cookie dates with 4-digit years")
                .to_offset(offset))
        }
        #[cfg(not(feature = "time"))]
        { Self(datetime.ext_fixed_offset()).min(Self::max()).max(Self::min()) }
    }

    /// Returns the [`chrono::DateTime<chrono::FixedOffset>`][cdt] with the
    /// same date & time and timezone offset as this `DateTime`.
    ///
    /// If this `DateTime` was created from a [`chrono::DateTime`][cdt] the
    /// timezone offset will be preserved (unless it was clamped), otherwise
    /// it will be UTC.
    ///
    /// [cdt]: chrono::DateTime
    #[cfg(feature = "chrono")]
    #[cfg_attr(all(nightly, doc), doc(cfg(feature = "chrono")))]
    pub fn into_chrono(self) -> chrono::DateTime<chrono::FixedOffset> {
        #[cfg(feature = "time")]
        { self.into() }
        #[cfg(not(feature = "time"))]
        { self.0 }
    }
}

#[cfg(any(feature = "time"))]
#[cfg_attr(all(nightly, doc), doc(cfg(feature = "time")))]
impl From<time::OffsetDateTime> for DateTime {
    /// See [`DateTime::from_time`].
    fn from(value: time::OffsetDateTime) -> Self {
        Self::from_time(value)
    }
}

#[cfg(any(feature = "time"))]
#[cfg_attr(all(nightly, doc), doc(cfg(feature = "time")))]
impl From<DateTime> for time::OffsetDateTime {
    /// See [`DateTime::into_time`].
    fn from(value: DateTime) -> Self {
        value.into_time()
    }
}

#[cfg(any(feature = "chrono"))]
#[cfg_attr(all(nightly, doc), doc(cfg(feature = "chrono")))]
impl<Tz: chrono::TimeZone> From<chrono::DateTime<Tz>> for DateTime {
    /// See [`DateTime::from_chrono`].
    fn from(value: chrono::DateTime<Tz>) -> Self {
        Self::from_chrono(value)
    }
}

#[cfg(any(feature = "chrono"))]
#[cfg_attr(all(nightly, doc), doc(cfg(feature = "chrono")))]
impl From<DateTime> for chrono::DateTime<chrono::FixedOffset> {
    /// See [`DateTime::into_chrono`].
    ///
    #[cfg_attr(feature = "time", doc = "The resulting `DateTime` may lose some sub-milisecond precision.")]
    fn from(value: DateTime) -> Self {
        #[cfg(feature = "time")]
        {
            let fixed_offset = match value.0.offset().whole_seconds() {
                secs_east @ 0.. => chrono::FixedOffset::east_opt(secs_east),
                secs_west => chrono::FixedOffset::west_opt(secs_west),
            }.expect("`DateTime` only supports ±1-day offsets");
            use std::convert::TryFrom as _;
            let millis = i64::try_from(value.0.unix_timestamp_nanos() / 1_000_000)
                .expect("`DateTime` only supports typical cookie dates with 4-digit years");
            let naive_datetime = chrono::NaiveDateTime::from_timestamp_millis(millis).unwrap();
            chrono::DateTime::from_utc(naive_datetime, fixed_offset)
        }
        #[cfg(all(feature = "chrono", not(feature = "time")))]
        { value.0 }
    }
}

macro_rules! use_chrono_or_time_duration {
    ( $name:ident ) => {
        #[cfg(feature = "time")]
        use time::Duration as $name;
        #[cfg(all(feature = "chrono", not(feature = "time")))]
        use chrono::Duration as $name;
    };
}

impl std::ops::Add<Duration> for DateTime {
    type Output = DateTime;
    /// Clamped to [`DateTime::MAX`].
    fn add(self, rhs: Duration) -> Self::Output {
        use_chrono_or_time_duration!(ChronoOrTimeDuration);
        Self(self.0 + ChronoOrTimeDuration::seconds(rhs.as_secs() as i64))
            .min(Self::max())
    }
}

impl std::ops::Sub<Duration> for DateTime {
    type Output = DateTime;
    /// Clamped to [`DateTime::MIN`].
    fn sub(self, rhs: Duration) -> Self::Output {
        use_chrono_or_time_duration!(ChronoOrTimeDuration);
        Self(self.0 - ChronoOrTimeDuration::seconds(rhs.as_secs() as i64))
            .max(Self::min())
    }
}

impl std::ops::AddAssign<Duration> for DateTime {
    /// Clamped to [`DateTime::MAX`].
    fn add_assign(&mut self, rhs: Duration) {
        use_chrono_or_time_duration!(ChronoOrTimeDuration);
        self.0 += ChronoOrTimeDuration::seconds(rhs.as_secs() as i64);
        if *self > Self::max() { *self = Self::max() }
    }
}

impl std::ops::SubAssign<Duration> for DateTime {
    /// Clamped to [`DateTime::MIN`].
    fn sub_assign(&mut self, rhs: Duration) {
        use_chrono_or_time_duration!(ChronoOrTimeDuration);
        self.0 -= ChronoOrTimeDuration::seconds(rhs.as_secs() as i64);
        if *self < Self::min() { *self = Self::min() }
    }
}

#[cfg(all(test, feature = "time", feature = "chrono"))]
mod tests {
    use super::DateTime;

    #[test]
    fn from_chrono() {
        let chrono_naive = chrono::NaiveDate::from_ymd_opt(2023, 9, 25)
            .and_then(|d| d.and_hms_milli_opt(22, 35, 28, 123))
            .unwrap();
        let chrono_offset = chrono::FixedOffset::east_opt(3600).unwrap();
        let chrono_dt = chrono::DateTime::<chrono::FixedOffset>::from_local(chrono_naive, chrono_offset);

        let dt = DateTime::from_chrono(chrono_dt);
        assert_eq!(dt.unix_timestamp(), 1695677728);

        let time_dt = dt.into_time();
        assert_eq!(time_dt.offset().whole_seconds(), 3600);
        assert_eq!(time_dt, time::macros::datetime!(2023-09-25 22:35:28.123 +01));

        assert_eq!(dt, DateTime::from_time(time_dt));
    }

    #[test]
    fn into_chrono() {
        let time_dt = time::macros::datetime!(2023-09-25 22:35:28.123 +01);
        let dt = DateTime::from_time(time_dt);

        let chrono_dt = dt.into_chrono();

        let chrono_naive = chrono::NaiveDate::from_ymd_opt(2023, 9, 25)
            .and_then(|d| d.and_hms_milli_opt(22, 35, 28, 123))
            .unwrap();
        let chrono_offset = chrono::FixedOffset::east_opt(3600).unwrap();
        assert_eq!(chrono_dt, chrono::DateTime::<chrono::FixedOffset>::from_local(chrono_naive, chrono_offset));

        assert_eq!(dt, DateTime::from_chrono(chrono_dt));
    }
}
