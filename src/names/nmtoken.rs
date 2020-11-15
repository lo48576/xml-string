//! [`Nmtoken`].
//!
//! [`Nmtoken`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Nmtoken

use core::convert::TryFrom;

use crate::names::chars;
use crate::names::error::{NameError, TargetNameType};
use crate::names::{NameStr, NcnameStr, QnameStr};

/// String slice for [`Nmtoken`].
///
/// [`Nmtoken`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Nmtoken
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct NmtokenStr(str);

impl NmtokenStr {
    /// Creates a new `&NmtokenStr`.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`Nmtoken`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::NmtokenStr;
    /// assert_eq!(NmtokenStr::from_str("hello")?, "hello");
    /// assert_eq!(NmtokenStr::from_str("012")?, "012");
    ///
    /// assert!(NmtokenStr::from_str("").is_err(), "Empty string is not an Nmtoken");
    /// assert!(NmtokenStr::from_str("foo bar").is_err(), "Whitespace is not allowed");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`Nmtoken`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Nmtoken
    // `FromStr` can be implemented only for types with static lifetime.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn from_str(s: &str) -> Result<&Self, NameError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&NmtokenStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be a valid [`Nmtoken`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::NmtokenStr;
    /// let tok = unsafe {
    ///     NmtokenStr::new_unchecked("hello")
    /// };
    /// assert_eq!(tok, "hello");
    /// ```
    ///
    /// [`Nmtoken`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Nmtoken
    #[inline]
    #[must_use]
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Validates the given string.
    fn validate(s: &str) -> Result<(), NameError> {
        if s.is_empty() {
            return Err(NameError::new(TargetNameType::Nmtoken, 0));
        }

        // Check whether all characters are `NameChar`.
        match s.char_indices().find(|(_, c)| !chars::is_name_continue(*c)) {
            Some((i, _)) => Err(NameError::new(TargetNameType::Nmtoken, i)),
            None => Ok(()),
        }
    }

    /// Returns the string as `&str`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::NmtokenStr;
    /// let tok = NmtokenStr::from_str("hello")?;
    /// assert_eq!(tok, "hello");
    ///
    /// let s: &str = tok.as_str();
    /// assert_eq!(s, "hello");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl_traits_for_custom_string_slice!(NmtokenStr);

impl<'a> TryFrom<&'a str> for &'a NmtokenStr {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        NmtokenStr::validate(s)?;
        Ok(unsafe {
            // This is safe because the string is validated.
            NmtokenStr::new_unchecked(s)
        })
    }
}

impl<'a> From<&'a NameStr> for &'a NmtokenStr {
    #[inline]
    fn from(s: &'a NameStr) -> Self {
        s.as_ref()
    }
}

impl<'a> From<&'a QnameStr> for &'a NmtokenStr {
    #[inline]
    fn from(s: &'a QnameStr) -> Self {
        s.as_ref()
    }
}

impl<'a> From<&'a NcnameStr> for &'a NmtokenStr {
    #[inline]
    fn from(s: &'a NcnameStr) -> Self {
        s.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ensure_eq(s: &str) {
        assert_eq!(
            NmtokenStr::from_str(s).expect("Should not fail"),
            s,
            "String: {:?}",
            s
        );
    }

    fn ensure_error_at(s: &str, valid_up_to: usize) {
        let err = NmtokenStr::from_str(s).expect_err("Should fail");
        assert_eq!(err.valid_up_to(), valid_up_to, "String: {:?}", s);
    }

    #[test]
    fn nmtoken_str_valid() {
        ensure_eq("hello");
        ensure_eq("abc123");
        ensure_eq("foo:bar");
        ensure_eq(":foo");
        ensure_eq("foo:");
        ensure_eq("-foo");
        ensure_eq("0foo");
        ensure_eq("foo.bar");
        ensure_eq(".foo");
    }

    #[test]
    fn nmtoken_str_invalid() {
        ensure_error_at("", 0);
        ensure_error_at("foo bar", 3);
        ensure_error_at("foo/bar", 3);
    }
}
