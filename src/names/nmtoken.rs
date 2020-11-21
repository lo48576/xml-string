//! [`Nmtoken`].
//!
//! [`Nmtoken`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Nmtoken

use core::convert::TryFrom;

use crate::names::chars;
use crate::names::error::{NameError, TargetNameType};
use crate::names::{Name, Ncname, Qname};

/// String slice for [`Nmtoken`].
///
/// [`Nmtoken`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Nmtoken
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Nmtoken(str);

impl Nmtoken {
    /// Creates a new `&Nmtoken`.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`Nmtoken`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Nmtoken;
    /// assert_eq!(Nmtoken::from_str("hello")?, "hello");
    /// assert_eq!(Nmtoken::from_str("012")?, "012");
    ///
    /// assert!(Nmtoken::from_str("").is_err(), "Empty string is not an Nmtoken");
    /// assert!(Nmtoken::from_str("foo bar").is_err(), "Whitespace is not allowed");
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

    /// Creates a new `&Nmtoken` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be a valid [`Nmtoken`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Nmtoken;
    /// let tok = unsafe {
    ///     Nmtoken::new_unchecked("hello")
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
    /// # use xml_string::names::Nmtoken;
    /// let tok = Nmtoken::from_str("hello")?;
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

    /// Parses the leading `Nmtoken` and returns the value and the rest input.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::Nmtoken;
    /// let input = "hello, world";
    /// let expected = Nmtoken::from_str("hello").expect("valid Nmtoken");
    /// assert_eq!(
    ///     Nmtoken::parse_next(input),
    ///     Ok((expected, ", world"))
    /// );
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// ```
    /// # use xml_string::names::Nmtoken;
    /// let input = " ";
    /// assert!(Nmtoken::parse_next(input).is_err());
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

impl_traits_for_custom_string_slice!(Nmtoken);

impl<'a> TryFrom<&'a str> for &'a Nmtoken {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        Nmtoken::validate(s)?;
        Ok(unsafe {
            // This is safe because the string is validated.
            Nmtoken::new_unchecked(s)
        })
    }
}

impl<'a> From<&'a Name> for &'a Nmtoken {
    #[inline]
    fn from(s: &'a Name) -> Self {
        s.as_ref()
    }
}

impl<'a> From<&'a Qname> for &'a Nmtoken {
    #[inline]
    fn from(s: &'a Qname) -> Self {
        s.as_ref()
    }
}

impl<'a> From<&'a Ncname> for &'a Nmtoken {
    #[inline]
    fn from(s: &'a Ncname) -> Self {
        s.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ensure_eq(s: &str) {
        assert_eq!(
            Nmtoken::from_str(s).expect("Should not fail"),
            s,
            "String: {:?}",
            s
        );
    }

    fn ensure_error_at(s: &str, valid_up_to: usize) {
        let err = Nmtoken::from_str(s).expect_err("Should fail");
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
