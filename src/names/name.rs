//! [`Name`].
//!
//! [`Name`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Name

use core::convert::TryFrom;

use crate::names::chars;
use crate::names::error::{NameError, TargetNameType};
use crate::names::{NcnameStr, QnameStr};

/// String slice for [`Name`].
///
/// [`Name`]: https://www.w3.org/TR/2008/REC-xml-20081126/#NT-Name
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct NameStr(str);

impl NameStr {
    /// Creates a new `&NameStr`.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`Name`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::NameStr;
    /// let name = NameStr::from_str("hello")?;
    /// assert_eq!(name, "hello");
    ///
    /// assert!(NameStr::from_str("").is_err(), "Empty string is not a Name");
    /// assert!(NameStr::from_str("foo bar").is_err(), "Whitespace is not allowed");
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

    /// Creates a new `&NameStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be a valid [`Name`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::NameStr;
    /// let name = unsafe {
    ///     NameStr::new_unchecked("hello")
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
    /// # use xml_string::names::NameStr;
    /// let name = NameStr::from_str("hello")?;
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
}

impl_traits_for_custom_string_slice!(NameStr);

impl<'a> From<&'a NcnameStr> for &'a NameStr {
    #[inline]
    fn from(s: &'a NcnameStr) -> Self {
        s.as_ref()
    }
}

impl<'a> From<&'a QnameStr> for &'a NameStr {
    #[inline]
    fn from(s: &'a QnameStr) -> Self {
        s.as_ref()
    }
}

impl<'a> TryFrom<&'a str> for &'a NameStr {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        NameStr::validate(s)?;
        Ok(unsafe {
            // This is safe because the string is validated.
            NameStr::new_unchecked(s)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ensure_eq(s: &str) {
        assert_eq!(
            NameStr::from_str(s).expect("Should not fail"),
            s,
            "String: {:?}",
            s
        );
    }

    fn ensure_error_at(s: &str, valid_up_to: usize) {
        let err = NameStr::from_str(s).expect_err("Should fail");
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
