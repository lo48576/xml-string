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
        // Parse the first component (prefix or full QName without prefix).
        let prefix_len = match NcnameStr::from_str(s) {
            Ok(_) => return Ok(()),
            Err(e) => e.valid_up_to(),
        };
        if prefix_len == 0 {
            // No valid prefix found.
            return Err(NameError::new(TargetNameType::Qname, 0));
        }
        assert!(
            prefix_len < s.len(),
            "`prefix_len` cannot be `s.len()`, because `s` is invalid as `NcnameStr`"
        );
        if s.as_bytes()[prefix_len] != b':' {
            // Prefix does not followed by a colon.
            return Err(NameError::new(TargetNameType::Qname, prefix_len));
        }
        let local_part = &s[(prefix_len + 1)..];

        match NcnameStr::from_str(local_part) {
            Ok(_) => Ok(()),
            Err(e) if e.valid_up_to() == 0 => {
                Err(NameError::new(TargetNameType::Qname, prefix_len))
            }
            Err(e) => Err(NameError::new(
                TargetNameType::Qname,
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

    /// Returns the prefix if available.
    ///
    /// Note that this is O(length) operation.
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
    #[inline]
    #[must_use]
    pub fn prefix(&self) -> Option<&NcnameStr> {
        self.prefix_len().map(|p_len| {
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
    ///
    /// Note that this is O(length) operation.
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
    #[inline]
    #[must_use]
    pub fn local_part(&self) -> &NcnameStr {
        let start = self.prefix_len().map_or(0, |p_len| p_len.get() + 1);
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
    #[inline]
    #[must_use]
    pub fn prefix_and_local(&self) -> (Option<&NcnameStr>, &NcnameStr) {
        match self.prefix_len() {
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
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
