//! [`QName`].
//!
//! [`QName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-QName

use core::convert::TryFrom;
use core::num::NonZeroUsize;

use crate::names::error::{NameError, TargetNameType};
use crate::names::{NameStr, NcnameStr, NmtokenStr};

/// String slice for [`QName`].
///
/// [`QName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-QName
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct QnameStr(str);

impl QnameStr {
    /// Creates a new `&QnameStr`.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`QName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::QnameStr;
    /// let noprefix = QnameStr::from_str("hello")?;
    /// assert_eq!(noprefix, "hello");
    ///
    /// let prefixed = QnameStr::from_str("foo:bar")?;
    /// assert_eq!(prefixed, "foo:bar");
    ///
    /// assert!(QnameStr::from_str("").is_err(), "Empty string is not a QName");
    /// assert!(QnameStr::from_str("foo bar").is_err(), "Whitespace is not allowed");
    /// assert!(QnameStr::from_str("foo:bar:baz").is_err(), "Two or more colons are not allowed");
    /// assert!(QnameStr::from_str("0foo").is_err(), "ASCII digit at the beginning is not allowed");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`QName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-QName
    // `FromStr` can be implemented only for types with static lifetime.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, NameError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&QnameStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be a valid [`QName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::QnameStr;
    /// let name = unsafe {
    ///     QnameStr::new_unchecked("foo:bar")
    /// };
    /// assert_eq!(name, "foo:bar");
    /// ```
    ///
    /// [`QName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-QName
    #[inline]
    #[must_use]
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Validates the given string.
    fn validate(s: &str) -> Result<(), NameError> {
        match Self::parse_as_possible(s) {
            Ok(_) => Ok(()),
            Err((_colon_pos, valid_up_to)) => {
                Err(NameError::new(TargetNameType::Qname, valid_up_to))
            }
        }
    }

    /// Parses the given string from the beginning as possible.
    ///
    /// Retruns `Ok(colon_position)` if the string is valid QName.
    /// Returns `Err((colon_position, valid_up_to))` if the string is invalid.
    fn parse_as_possible(s: &str) -> Result<Option<NonZeroUsize>, (Option<NonZeroUsize>, usize)> {
        // Parse the first component (prefix or full QName without prefix).
        let prefix_len = match NcnameStr::from_str(s) {
            Ok(_) => return Ok(None),
            Err(e) => e.valid_up_to(),
        };
        if prefix_len == 0 {
            // No valid prefix found.
            return Err((None, 0));
        }
        assert!(
            prefix_len < s.len(),
            "`prefix_len` cannot be `s.len()`, because `s` is invalid as `NcnameStr`"
        );
        if s.as_bytes()[prefix_len] != b':' {
            // Prefix does not followed by a colon.
            return Err((None, prefix_len));
        }
        let local_part = &s[(prefix_len + 1)..];

        match NcnameStr::from_str(local_part) {
            Ok(_) => Ok(NonZeroUsize::new(prefix_len)),
            Err(e) if e.valid_up_to() == 0 => Err((None, prefix_len)),
            Err(e) => Err((
                NonZeroUsize::new(prefix_len),
                prefix_len + 1 + e.valid_up_to(),
            )),
        }
    }

    /// Returns the string as `&str`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::QnameStr;
    /// let name = QnameStr::from_str("foo:bar")?;
    /// assert_eq!(name, "foo:bar");
    ///
    /// let s: &str = name.as_str();
    /// assert_eq!(s, "foo:bar");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Returns the length of the prefix, if available.
    ///
    /// Note that this is O(length) operation.
    #[must_use]
    fn prefix_len(&self) -> Option<NonZeroUsize> {
        self.as_str().find(':').and_then(NonZeroUsize::new)
    }

    /// Returns whether the QName has a prefix.
    ///
    /// Note that this is O(length) operation.
    /// Consider using [`QnameRef::has_prefix`] method if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::QnameStr;
    /// let local_only = QnameStr::from_str("hello")?;
    /// assert!(!local_only.has_prefix());
    ///
    /// let prefixed = QnameStr::from_str("foo:bar")?;
    /// assert!(prefixed.has_prefix());
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`QnameRef::has_prefix`]: struct.QnameRef.html#method.has_prefix
    #[inline]
    #[must_use]
    pub fn has_prefix(&self) -> bool {
        self.as_str().find(':').is_some()
    }

    /// Returns the prefix if available.
    ///
    /// Note that this is O(length) operation.
    /// Consider using [`QnameRef::prefix`] method if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::QnameStr;
    /// let prefixed = QnameStr::from_str("foo:bar")?;
    /// assert_eq!(prefixed.prefix().map(|s| s.as_str()), Some("foo"));
    ///
    /// let noprefix = QnameStr::from_str("foo")?;
    /// assert_eq!(noprefix.prefix().map(|s| s.as_str()), None);
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`QnameRef::prefix`]: struct.QnameRef.html#method.prefix
    #[inline]
    #[must_use]
    pub fn prefix(&self) -> Option<&NcnameStr> {
        QnameRef::new(self, self.prefix_len()).prefix()
    }

    /// Returns the local part.
    ///
    /// Note that this is O(length) operation.
    /// Consider using [`QnameRef::local_part`] method if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::QnameStr;
    /// let prefixed = QnameStr::from_str("foo:bar")?;
    /// assert_eq!(prefixed.local_part(), "bar");
    ///
    /// let noprefix = QnameStr::from_str("foo")?;
    /// assert_eq!(noprefix.local_part(), "foo");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`QnameRef::local_part`]: struct.QnameRef.html#method.local_part
    #[inline]
    #[must_use]
    pub fn local_part(&self) -> &NcnameStr {
        QnameRef::new(self, self.prefix_len()).local_part()
    }

    /// Returns a pair of the prefix (if available) and the local part.
    ///
    /// Note that this is O(length) operation.
    /// Consider using [`QnameRef::prefix_and_local`] method if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::QnameStr;
    /// use std::convert::TryFrom;
    ///
    /// let noprefix = QnameStr::from_str("hello")?;
    /// assert_eq!(noprefix.prefix_and_local(), (noprefix.prefix(), noprefix.local_part()));
    ///
    /// let prefixed = QnameStr::from_str("foo:bar")?;
    /// assert_eq!(prefixed.prefix_and_local(), (prefixed.prefix(), prefixed.local_part()));
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`QnameRef::prefix_and_local`]: struct.QnameRef.html#method.prefix_and_local
    #[inline]
    #[must_use]
    pub fn prefix_and_local(&self) -> (Option<&NcnameStr>, &NcnameStr) {
        QnameRef::new(self, self.prefix_len()).prefix_and_local()
    }
}

impl_traits_for_custom_string_slice!(QnameStr);

impl AsRef<NameStr> for QnameStr {
    #[inline]
    fn as_ref(&self) -> &NameStr {
        unsafe {
            debug_assert!(
                NameStr::from_str(self.as_str()).is_ok(),
                "QName {:?} must be a valid Name",
                self.as_str()
            );
            // This is safe because a QName is also a valid NCName.
            NameStr::new_unchecked(self.as_str())
        }
    }
}

impl AsRef<NmtokenStr> for QnameStr {
    #[inline]
    fn as_ref(&self) -> &NmtokenStr {
        unsafe {
            debug_assert!(
                NmtokenStr::from_str(self.as_str()).is_ok(),
                "QName {:?} must be a valid Nmtoken",
                self.as_str()
            );
            // This is safe because a QName is also a valid Nmtoken.
            NmtokenStr::new_unchecked(self.as_str())
        }
    }
}

impl<'a> From<&'a NcnameStr> for &'a QnameStr {
    #[inline]
    fn from(s: &'a NcnameStr) -> Self {
        s.as_ref()
    }
}

impl<'a> From<QnameRef<'a>> for &'a QnameStr {
    #[inline]
    fn from(s: QnameRef<'a>) -> Self {
        s.content
    }
}

impl<'a> TryFrom<&'a str> for &'a QnameStr {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        QnameStr::validate(s)?;
        Ok(unsafe {
            // This is safe because the string is validated.
            QnameStr::new_unchecked(s)
        })
    }
}

impl<'a> TryFrom<&'a QnameStr> for &'a NcnameStr {
    type Error = NameError;

    fn try_from(s: &'a QnameStr) -> Result<Self, Self::Error> {
        if let Some(p_len) = s.prefix_len() {
            return Err(NameError::new(TargetNameType::Ncname, p_len.get()));
        }

        unsafe {
            debug_assert!(
                NcnameStr::from_str(s.as_str()).is_ok(),
                "QName {:?} without prefix must be a valid NCName",
                s.as_str()
            );
            // This is safe because a QName without prefix is also a valid NCName.
            Ok(NcnameStr::new_unchecked(s.as_str()))
        }
    }
}

/// Parsed [`QName`] reference.
///
/// [`QName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-QName
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QnameRef<'a> {
    /// Content string.
    content: &'a QnameStr,
    /// Length of the prefix, if available.
    ///
    /// If this is `Some(p_len)`, `self.content.as_str().as_bytes()[p_len] == b':'` is guaranteed.
    prefix_len: Option<NonZeroUsize>,
}

impl<'a> QnameRef<'a> {
    /// Creates a new `QnameRef`.
    ///
    /// # Panics
    ///
    /// Panics if the `prefix_len` does not point to the colon in the `content`.
    #[must_use]
    fn new(content: &'a QnameStr, prefix_len: Option<NonZeroUsize>) -> Self {
        if let Some(p_len) = prefix_len {
            if content.as_str().as_bytes()[p_len.get()] != b':' {
                panic!(
                    "`prefix_len` (={:?}) should point to the colon \
                    (if available) of the qname {:?}",
                    p_len.get(),
                    content
                );
            }
        }
        Self {
            content,
            prefix_len,
        }
    }

    /// Creates a new `QnameRef<'_>` from the given string slice.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`QName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::QnameRef;
    /// let noprefix = QnameRef::from_str("hello")?;
    /// assert_eq!(noprefix, "hello");
    ///
    /// let prefixed = QnameRef::from_str("foo:bar")?;
    /// assert_eq!(prefixed, "foo:bar");
    ///
    /// assert!(QnameRef::from_str("").is_err(), "Empty string is not a QName");
    /// assert!(QnameRef::from_str("foo bar").is_err(), "Whitespace is not allowed");
    /// assert!(QnameRef::from_str("foo:bar:baz").is_err(), "Two or more colons are not allowed");
    /// assert!(QnameRef::from_str("0foo").is_err(), "ASCII digit at the beginning is not allowed");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`QName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-QName
    // `FromStr` can be implemented only for types with static lifetime.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn from_str(s: &'a str) -> Result<Self, NameError> {
        Self::try_from(s)
    }

    /// Returns the string as `&QnameStr`.
    #[inline]
    #[must_use]
    pub fn as_qname_str(&self) -> &'a QnameStr {
        self.content
    }

    /// Returns the string as `&str`.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &'a str {
        self.content.as_str()
    }

    /// Returns whether the QName has a prefix.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::QnameRef;
    /// let local_only = QnameRef::from_str("hello")?;
    /// assert!(!local_only.has_prefix());
    ///
    /// let prefixed = QnameRef::from_str("foo:bar")?;
    /// assert!(prefixed.has_prefix());
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn has_prefix(&self) -> bool {
        self.prefix_len.is_some()
    }

    /// Returns the prefix, if available.
    #[must_use]
    pub fn prefix(&self) -> Option<&'a NcnameStr> {
        self.prefix_len.as_ref().map(|p_len| {
            let prefix = &self.as_str()[..p_len.get()];
            unsafe {
                debug_assert!(
                    NcnameStr::from_str(prefix).is_ok(),
                    "The prefix {:?} must be a valid NCName",
                    prefix
                );
                // This is safe because the prefix is a valid NCName.
                NcnameStr::new_unchecked(prefix)
            }
        })
    }

    /// Returns the local part.
    #[must_use]
    pub fn local_part(&self) -> &'a NcnameStr {
        let start = self.prefix_len.as_ref().map_or(0, |p_len| p_len.get() + 1);
        let local_part = &self.as_str()[start..];
        unsafe {
            debug_assert!(
                NcnameStr::from_str(local_part).is_ok(),
                "The local part {:?} must be a valid NCName",
                local_part
            );
            // This is safe because the local part is a valid NCName.
            NcnameStr::new_unchecked(local_part)
        }
    }

    /// Returns a pair of the prefix (if available) and the local part.
    ///
    /// This is efficient version of `(self.prefix(), self.local_part())`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::QnameRef;
    /// use std::convert::TryFrom;
    ///
    /// let noprefix = QnameRef::try_from("hello")?;
    /// assert_eq!(noprefix.prefix_and_local(), (noprefix.prefix(), noprefix.local_part()));
    ///
    /// let prefixed = QnameRef::try_from("hello")?;
    /// assert_eq!(prefixed.prefix_and_local(), (prefixed.prefix(), prefixed.local_part()));
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[must_use]
    pub fn prefix_and_local(&self) -> (Option<&'a NcnameStr>, &'a NcnameStr) {
        match self.prefix_len {
            Some(p_len) => {
                let prefix = {
                    let prefix = &self.as_str()[..p_len.get()];
                    unsafe {
                        debug_assert!(
                            NcnameStr::from_str(prefix).is_ok(),
                            "The prefix {:?} must be a valid NCName",
                            prefix
                        );
                        // This is safe because the prefix is a valid NCName.
                        NcnameStr::new_unchecked(prefix)
                    }
                };
                let local_part = {
                    let local_part = &self.as_str()[(p_len.get() + 1)..];
                    unsafe {
                        debug_assert!(
                            NcnameStr::from_str(local_part).is_ok(),
                            "The local part {:?} must be a valid NCName",
                            local_part
                        );
                        // This is safe because the local part is a valid NCName.
                        NcnameStr::new_unchecked(local_part)
                    }
                };
                (Some(prefix), local_part)
            }
            None => {
                let ncname = unsafe {
                    debug_assert!(
                        NcnameStr::from_str(self.as_str()).is_ok(),
                        "QName without prefix must be a valid NCName"
                    );
                    NcnameStr::new_unchecked(self.as_str())
                };
                (None, ncname)
            }
        }
    }
}

impl PartialEq<str> for QnameRef<'_> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}
impl_cmp!(str, QnameRef<'_>);

impl PartialEq<&'_ str> for QnameRef<'_> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}
impl_cmp!(&str, QnameRef<'_>);

impl PartialEq<str> for &'_ QnameRef<'_> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}
impl_cmp!(str, &QnameRef<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<alloc::string::String> for QnameRef<'_> {
    #[inline]
    fn eq(&self, other: &alloc::string::String) -> bool {
        self.as_str() == *other
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(alloc::string::String, QnameRef<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<&alloc::string::String> for QnameRef<'_> {
    #[inline]
    fn eq(&self, other: &&alloc::string::String) -> bool {
        self.as_str() == **other
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(&alloc::string::String, QnameRef<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<alloc::boxed::Box<str>> for QnameRef<'_> {
    #[inline]
    fn eq(&self, other: &alloc::boxed::Box<str>) -> bool {
        self.as_str() == other.as_ref()
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(alloc::boxed::Box<str>, QnameRef<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<alloc::borrow::Cow<'_, str>> for QnameRef<'_> {
    #[inline]
    fn eq(&self, other: &alloc::borrow::Cow<'_, str>) -> bool {
        self.as_str() == *other
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(alloc::borrow::Cow<'_, str>, QnameRef<'_>);

impl AsRef<str> for QnameRef<'_> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<QnameStr> for QnameRef<'_> {
    #[inline]
    fn as_ref(&self) -> &QnameStr {
        self.content
    }
}

impl<'a> From<&'a QnameStr> for QnameRef<'a> {
    fn from(s: &'a QnameStr) -> Self {
        let prefix_len = s.as_str().find(':').and_then(NonZeroUsize::new);
        Self {
            content: s,
            prefix_len,
        }
    }
}

impl<'a> TryFrom<&'a str> for QnameRef<'a> {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        match QnameStr::parse_as_possible(s) {
            Ok(prefix_len) => {
                let content = unsafe {
                    // This is safe because the string is validated by
                    // `QnameStr::parse_as_possible()`.
                    QnameStr::new_unchecked(s)
                };
                Ok(Self {
                    content,
                    prefix_len,
                })
            }
            Err((_colon_pos, valid_up_to)) => {
                Err(NameError::new(TargetNameType::Qname, valid_up_to))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ncname(s: &str) -> &NcnameStr {
        NcnameStr::from_str(s)
            .unwrap_or_else(|e| panic!("Failed to cerate NcnameStr from {:?}: {}", s, e))
    }

    fn qname(s: &str) -> &QnameStr {
        QnameStr::from_str(s)
            .unwrap_or_else(|e| panic!("Failed to cerate QnameStr from {:?}: {}", s, e))
    }

    fn qname_ref(s: &str) -> QnameRef<'_> {
        QnameRef::from_str(s)
            .unwrap_or_else(|e| panic!("Failed to cerate QnameRef from {:?}: {}", s, e))
    }

    fn ensure_eq(s: &str) {
        assert_eq!(
            QnameStr::from_str(s).expect("Should not fail"),
            s,
            "String: {:?}",
            s
        );
    }

    fn ensure_error_at(s: &str, valid_up_to: usize) {
        let err = QnameStr::from_str(s).expect_err("Should fail");
        assert_eq!(err.valid_up_to(), valid_up_to, "String: {:?}", s);
    }

    #[test]
    fn qname_str_valid() {
        ensure_eq("hello");
        ensure_eq("abc123");
        ensure_eq("foo:bar");
    }

    #[test]
    fn qname_str_invalid() {
        ensure_error_at("", 0);
        ensure_error_at("-foo", 0);
        ensure_error_at("0foo", 0);
        ensure_error_at("foo bar", 3);
        ensure_error_at("foo/bar", 3);

        ensure_error_at("foo:bar:baz", 7);
        ensure_error_at(":foo", 0);
        ensure_error_at("foo:", 3);
        ensure_error_at("foo::bar", 3);
        ensure_error_at("foo:-bar", 3);
    }

    #[test]
    fn parse_as_possible() {
        assert_eq!(QnameStr::parse_as_possible("foo"), Ok(None));
        assert_eq!(
            QnameStr::parse_as_possible("foo:bar"),
            Ok(NonZeroUsize::new(3))
        );

        assert_eq!(QnameStr::parse_as_possible(""), Err((None, 0)));
        assert_eq!(QnameStr::parse_as_possible("foo:"), Err((None, 3)));
        assert_eq!(QnameStr::parse_as_possible(":foo"), Err((None, 0)));
        assert_eq!(
            QnameStr::parse_as_possible("foo:bar:baz"),
            Err((NonZeroUsize::new(3), 7))
        );
        assert_eq!(QnameStr::parse_as_possible("foo::bar"), Err((None, 3)));
    }

    #[test]
    fn qname_ref_from_str() {
        assert_eq!(
            QnameRef::from_str("hello").map(|v| v.as_qname_str()),
            Ok(qname("hello"))
        );
        assert_eq!(
            QnameRef::from_str("foo:bar").map(|v| v.as_qname_str()),
            Ok(qname("foo:bar"))
        );

        assert_eq!(
            QnameRef::from_str("foo:-bar"),
            Err(NameError::new(TargetNameType::Qname, 3))
        );
    }

    #[test]
    fn qname_ref_prefix() {
        assert_eq!(qname_ref("hello").prefix(), None);
        assert_eq!(qname_ref("foo:bar").prefix(), Some(ncname("foo")));
    }

    #[test]
    fn qname_ref_local_part() {
        assert_eq!(qname_ref("hello").local_part(), ncname("hello"));
        assert_eq!(qname_ref("foo:bar").local_part(), ncname("bar"));
    }

    #[test]
    fn qname_ref_prefix_and_local() {
        assert_eq!(
            qname_ref("hello").prefix_and_local(),
            (None, ncname("hello"))
        );
        assert_eq!(
            qname_ref("foo:bar").prefix_and_local(),
            (Some(ncname("foo")), ncname("bar"))
        );
    }
}
