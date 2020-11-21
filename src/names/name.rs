//! [`Name`].
//!
//! [`Name`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Name

use core::convert::TryFrom;

use crate::names::chars;
use crate::names::error::{NameError, TargetNameType};
use crate::names::{Ncname, Nmtoken, Qname};

/// String slice for [`Name`].
///
/// [`Name`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Name
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Name(str);

impl Name {
    /// Creates a new `&Name`.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`Name`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Name;
    /// let name = Name::from_str("hello")?;
    /// assert_eq!(name, "hello");
    ///
    /// assert!(Name::from_str("").is_err(), "Empty string is not a Name");
    /// assert!(Name::from_str("foo bar").is_err(), "Whitespace is not allowed");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`Name`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Name
    // `FromStr` can be implemented only for types with static lifetime.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn from_str(s: &str) -> Result<&Self, NameError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&Name` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be a valid [`Name`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Name;
    /// let name = unsafe {
    ///     Name::new_unchecked("hello")
    /// };
    /// assert_eq!(name, "hello");
    /// ```
    ///
    /// [`Name`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Name
    #[inline]
    #[must_use]
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Validates the given string.
    fn validate(s: &str) -> Result<(), NameError> {
        let mut chars = s.char_indices();

        // Check the first character.
        if !chars.next().map_or(false, |(_, c)| chars::is_name_start(c)) {
            return Err(NameError::new(TargetNameType::Name, 0));
        }

        // Check the following characters.
        if let Some((i, _)) = chars.find(|(_, c)| !chars::is_name_continue(*c)) {
            return Err(NameError::new(TargetNameType::Name, i));
        }

        Ok(())
    }

    /// Returns the string as `&str`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Name;
    /// let name = Name::from_str("hello")?;
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

    /// Parses the leading `Name` and returns the value and the rest input.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::Name;
    /// let input = "hello, world";
    /// let expected = Name::from_str("hello").expect("valid Name");
    /// assert_eq!(
    ///     Name::parse_next(input),
    ///     Ok((expected, ", world"))
    /// );
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// ```
    /// # use xml_string::names::Name;
    /// let input = "012";
    /// assert!(Name::parse_next(input).is_err());
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

impl_traits_for_custom_string_slice!(Name);

impl AsRef<Nmtoken> for Name {
    #[inline]
    fn as_ref(&self) -> &Nmtoken {
        unsafe {
            debug_assert!(
                Nmtoken::from_str(self.as_str()).is_ok(),
                "Name {:?} must be a valid Nmtoken",
                self.as_str()
            );
            // This is safe because a Name is also a valid Nmtoken.
            Nmtoken::new_unchecked(self.as_str())
        }
    }
}

impl<'a> From<&'a Ncname> for &'a Name {
    #[inline]
    fn from(s: &'a Ncname) -> Self {
        s.as_ref()
    }
}

impl<'a> From<&'a Qname> for &'a Name {
    #[inline]
    fn from(s: &'a Qname) -> Self {
        s.as_ref()
    }
}

impl<'a> TryFrom<&'a str> for &'a Name {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        Name::validate(s)?;
        Ok(unsafe {
            // This is safe because the string is validated.
            Name::new_unchecked(s)
        })
    }
}

impl<'a> TryFrom<&'a Nmtoken> for &'a Name {
    type Error = NameError;

    fn try_from(s: &'a Nmtoken) -> Result<Self, Self::Error> {
        let first = s
            .as_str()
            .chars()
            .next()
            .expect("Should never fail: Nmtoken is not empty");
        if !chars::is_name_start(first) {
            return Err(NameError::new(TargetNameType::Name, 0));
        }

        Ok(unsafe {
            // This is safe because a Nmtoken starting with NameStartChar is also a valid Name.
            debug_assert!(Name::validate(s.as_str()).is_ok());
            Name::new_unchecked(s.as_str())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ensure_eq(s: &str) {
        assert_eq!(
            Name::from_str(s).expect("Should not fail"),
            s,
            "String: {:?}",
            s
        );
    }

    fn ensure_error_at(s: &str, valid_up_to: usize) {
        let err = Name::from_str(s).expect_err("Should fail");
        assert_eq!(err.valid_up_to(), valid_up_to, "String: {:?}", s);
    }

    #[test]
    fn name_str_valid() {
        ensure_eq("hello");
        ensure_eq("abc123");
        ensure_eq("foo:bar");
        ensure_eq(":foo");
        ensure_eq("foo:");
    }

    #[test]
    fn name_str_invalid() {
        ensure_error_at("", 0);
        ensure_error_at("-foo", 0);
        ensure_error_at("0foo", 0);
        ensure_error_at("foo bar", 3);
        ensure_error_at("foo/bar", 3);
    }
}
