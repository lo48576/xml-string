//! [`NCName`].
//!
//! [`NCName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-NCName

use core::convert::TryFrom;

use crate::names::chars;
use crate::names::error::{NameError, TargetNameType};
use crate::names::{NameStr, NmtokenStr, QnameStr};

/// String slice for [`NCName`].
///
/// [`NCName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-NCName
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct NcnameStr(str);

impl NcnameStr {
    /// Creates a new `&NcnameStr`.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`NCName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::NcnameStr;
    /// let name = NcnameStr::from_str("hello")?;
    /// assert_eq!(name, "hello");
    ///
    /// assert!(NcnameStr::from_str("").is_err(), "Empty string is not an NCName");
    /// assert!(NcnameStr::from_str("foo bar").is_err(), "Whitespace is not allowed");
    /// assert!(NcnameStr::from_str("foo:bar").is_err(), "Colon is not allowed");
    /// assert!(NcnameStr::from_str("0foo").is_err(), "ASCII digit at the beginning is not allowed");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`NCName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-NCName
    // `FromStr` can be implemented only for types with static lifetime.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn from_str(s: &str) -> Result<&Self, NameError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&NcnameStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be a valid [`NCName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::NcnameStr;
    /// let name = unsafe {
    ///     NcnameStr::new_unchecked("hello")
    /// };
    /// assert_eq!(name, "hello");
    /// ```
    ///
    /// [`NCName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-NCName
    #[inline]
    #[must_use]
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Validates the given string.
    fn validate(s: &str) -> Result<(), NameError> {
        let mut chars = s.char_indices();

        // Check the first character.
        if !chars
            .next()
            .map_or(false, |(_, c)| chars::is_ncname_start(c))
        {
            return Err(NameError::new(TargetNameType::Ncname, 0));
        }

        // Check the following characters.
        if let Some((i, _)) = chars.find(|(_, c)| !chars::is_ncname_continue(*c)) {
            return Err(NameError::new(TargetNameType::Ncname, i));
        }

        Ok(())
    }

    /// Returns the string as `&str`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::NcnameStr;
    /// let name = NcnameStr::from_str("hello")?;
    /// assert_eq!(name, "hello");
    ///
    /// let s: &str = name.as_str();
    /// assert_eq!(s, "hello");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Parses the leading `NcnameStr` and returns the value and the rest input.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::NcnameStr;
    /// let input = "hello:world";
    /// let expected = NcnameStr::from_str("hello").expect("valid NCName");
    /// assert_eq!(
    ///     NcnameStr::parse_next(input),
    ///     Ok((expected, ":world"))
    /// );
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// ```
    /// # use xml_string::names::NcnameStr;
    /// let input = "012";
    /// assert!(NcnameStr::parse_next(input).is_err());
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    pub fn parse_next(s: &str) -> Result<(&Self, &str), NameError> {
        match Self::from_str(s) {
            Ok(v) => Ok((v, &s[s.len()..])),
            Err(e) if e.valid_up_to() == 0 => Err(e),
            Err(e) => {
                let valid_up_to = e.valid_up_to();
                let v = unsafe {
                    let valid = &s[..valid_up_to];
                    debug_assert!(Self::validate(valid).is_ok());
                    // This is safe because the substring is valid.
                    Self::new_unchecked(valid)
                };
                Ok((v, &s[valid_up_to..]))
            }
        }
    }
}

impl_traits_for_custom_string_slice!(NcnameStr);

impl AsRef<NmtokenStr> for NcnameStr {
    #[inline]
    fn as_ref(&self) -> &NmtokenStr {
        unsafe {
            debug_assert!(
                NmtokenStr::from_str(self.as_str()).is_ok(),
                "NCName {:?} must be a valid Nmtoken",
                self.as_str()
            );
            // This is safe because an NCName is also a valid Nmtoken.
            NmtokenStr::new_unchecked(self.as_str())
        }
    }
}

impl AsRef<NameStr> for NcnameStr {
    #[inline]
    fn as_ref(&self) -> &NameStr {
        unsafe {
            debug_assert!(
                NameStr::from_str(self.as_str()).is_ok(),
                "An NCName is also a Name"
            );
            NameStr::new_unchecked(self.as_str())
        }
    }
}

impl AsRef<QnameStr> for NcnameStr {
    #[inline]
    fn as_ref(&self) -> &QnameStr {
        unsafe {
            debug_assert!(
                QnameStr::from_str(self.as_str()).is_ok(),
                "An NCName is also a Qname"
            );
            QnameStr::new_unchecked(self.as_str())
        }
    }
}

impl<'a> TryFrom<&'a str> for &'a NcnameStr {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        NcnameStr::validate(s)?;
        Ok(unsafe {
            // This is safe because the string is validated.
            NcnameStr::new_unchecked(s)
        })
    }
}

impl<'a> TryFrom<&'a NameStr> for &'a NcnameStr {
    type Error = NameError;

    fn try_from(s: &'a NameStr) -> Result<Self, Self::Error> {
        if let Some(colon_pos) = s.as_str().find(':') {
            return Err(NameError::new(TargetNameType::Ncname, colon_pos));
        }

        unsafe {
            debug_assert!(
                NcnameStr::validate(s.as_str()).is_ok(),
                "Name {:?} without colons is also a valid NCName",
                s.as_str()
            );
            Ok(NcnameStr::new_unchecked(s.as_str()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ensure_eq(s: &str) {
        assert_eq!(
            NcnameStr::from_str(s).expect("Should not fail"),
            s,
            "String: {:?}",
            s
        );
    }

    fn ensure_error_at(s: &str, valid_up_to: usize) {
        let err = NcnameStr::from_str(s).expect_err("Should fail");
        assert_eq!(err.valid_up_to(), valid_up_to, "String: {:?}", s);
    }

    #[test]
    fn ncname_str_valid() {
        ensure_eq("hello");
        ensure_eq("abc123");
    }

    #[test]
    fn ncname_str_invalid() {
        ensure_error_at("", 0);
        ensure_error_at("-foo", 0);
        ensure_error_at("0foo", 0);
        ensure_error_at("foo bar", 3);
        ensure_error_at("foo/bar", 3);

        ensure_error_at("foo:bar", 3);
        ensure_error_at(":foo", 0);
        ensure_error_at("foo:", 3);
    }
}
