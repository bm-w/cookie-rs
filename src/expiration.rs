//! This module contains the [`Expiration`] type and its [`DateTime`] helper type.

pub use crate::max_age::Duration;

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

/// TODO: Docs. (UTC).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DateTime(pub(crate) time::OffsetDateTime);

impl DateTime {

    /// TODO: Docs. (UTC).
    pub const MAX: Self = Self(time::macros::datetime!(9999-12-31 23:59:59.999_999 UTC));

    /// TODO: Docs. (UTC).
    pub fn now() -> Self {
        Self(time::OffsetDateTime::now_utc())
    }

    /// TODO: Docs. (UTC).
    pub fn unix_timestamp(&self) -> i64 {
        self.0.unix_timestamp()
    }

    /// Formats the `DateTime` with the UTC offset.
    pub(crate) fn format(&self, fmt: &[time::format_description::FormatItem<'_>])
    -> Result<String, time::error::Format> {
        self.0.format(fmt)
    }

    pub(crate) fn _from_time(datetime: time::OffsetDateTime) -> Self {
        Self(datetime.to_offset(time::UtcOffset::UTC))
    }

    /// TODO: Docs.
    #[cfg(feature = "time")]
    pub fn from_time(datetime: time::OffsetDateTime) -> Self {
        Self::_from_time(datetime)
    }

    /// TODO: Docs.
    #[cfg(feature = "time")]
    pub fn into_time(self) -> time::OffsetDateTime {
        self.into()
    }
}

#[cfg(any(test, feature = "time"))]
impl From<time::OffsetDateTime> for DateTime {
    fn from(value: time::OffsetDateTime) -> Self {
        Self::_from_time(value)
    }
}

#[cfg(any(test, feature = "time"))]
impl From<DateTime> for time::OffsetDateTime {
    fn from(value: DateTime) -> Self {
        value.0
    }
}

impl std::ops::Add<Duration> for DateTime {
    type Output = DateTime;
    fn add(self, rhs: Duration) -> Self::Output {
        Self(self.0 + time::Duration::seconds(rhs.as_secs() as i64))
    }
}

impl std::ops::Sub<Duration> for DateTime {
    type Output = DateTime;
    fn sub(self, rhs: Duration) -> Self::Output {
        Self(self.0 - time::Duration::seconds(rhs.as_secs() as i64))
    }
}

impl std::ops::AddAssign<Duration> for DateTime {
    fn add_assign(&mut self, rhs: Duration) {
        self.0.add_assign(time::Duration::seconds(rhs.as_secs() as i64))
    }
}

impl std::ops::SubAssign<Duration> for DateTime {
    fn sub_assign(&mut self, rhs: Duration) {
        self.0.sub_assign(time::Duration::seconds(rhs.as_secs() as i64))
    }
}
