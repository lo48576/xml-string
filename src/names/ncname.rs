//! [`NCName`].
//!
//! [`NCName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-NCName

use core::convert::TryFrom;

use crate::names::chars;
use crate::names::error::{NameError, TargetNameType};
use crate::names::{Eqname, Name, Nmtoken, Qname};

/// String slice for [`NCName`].
///
/// [`NCName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-NCName
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Ncname(str);

#[allow(clippy::len_without_is_empty)]
impl Ncname {
    /// Creates a new `&Ncname`.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`NCName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Ncname;
    /// let name = Ncname::from_str("hello")?;
    /// assert_eq!(name, "hello");
    ///
    /// assert!(Ncname::from_str("").is_err(), "Empty string is not an NCName");
    /// assert!(Ncname::from_str("foo bar").is_err(), "Whitespace is not allowed");
    /// assert!(Ncname::from_str("foo:bar").is_err(), "Colon is not allowed");
    /// assert!(Ncname::from_str("0foo").is_err(), "ASCII digit at the beginning is not allowed");
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

    /// Creates a new `&Ncname` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be a valid [`NCName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Ncname;
    /// let name = unsafe {
    ///     Ncname::new_unchecked("hello")
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
    /// # use xml_string::names::Ncname;
    /// let name = Ncname::from_str("hello")?;
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

    /// Returns the length of the string in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Ncname;
    /// let name = Ncname::from_str("foo")?;
    /// assert_eq!(name.len(), 3);
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Parses the leading `Ncname` and returns the value and the rest input.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::Ncname;
    /// let input = "hello:world";
    /// let expected = Ncname::from_str("hello").expect("valid NCName");
    /// assert_eq!(
    ///     Ncname::parse_next(input),
    ///     Ok((expected, ":world"))
    /// );
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// ```
    /// # use xml_string::names::Ncname;
    /// let input = "012";
    /// assert!(Ncname::parse_next(input).is_err());
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

    /// Converts a `Box<Ncname>` into a `Box<str>` without copying or allocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Ncname;
    /// let name = Ncname::from_str("ncname")?;
    /// let boxed_name: Box<Ncname> = name.into();
    /// assert_eq!(&*boxed_name, name);
    /// let boxed_str: Box<str> = boxed_name.into_boxed_str();
    /// assert_eq!(&*boxed_str, name.as_str());
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[cfg(feature = "alloc")]
    pub fn into_boxed_str(self: alloc::boxed::Box<Self>) -> Box<str> {
        unsafe {
            // This is safe because `Ncname` has the same memory layout as `str`
            // (thanks to `#[repr(transparent)]`).
            alloc::boxed::Box::<str>::from_raw(alloc::boxed::Box::<Self>::into_raw(self) as *mut str)
        }
    }
}

impl_traits_for_custom_string_slice!(Ncname);

impl AsRef<Nmtoken> for Ncname {
    #[inline]
    fn as_ref(&self) -> &Nmtoken {
        unsafe {
            debug_assert!(
                Nmtoken::from_str(self.as_str()).is_ok(),
                "NCName {:?} must be a valid Nmtoken",
                self.as_str()
            );
            // This is safe because an NCName is also a valid Nmtoken.
            Nmtoken::new_unchecked(self.as_str())
        }
    }
}

impl AsRef<Name> for Ncname {
    #[inline]
    fn as_ref(&self) -> &Name {
        unsafe {
            debug_assert!(
                Name::from_str(self.as_str()).is_ok(),
                "An NCName is also a Name"
            );
            Name::new_unchecked(self.as_str())
        }
    }
}

impl AsRef<Qname> for Ncname {
    #[inline]
    fn as_ref(&self) -> &Qname {
        unsafe {
            debug_assert!(
                Qname::from_str(self.as_str()).is_ok(),
                "An NCName is also a Qname"
            );
            Qname::new_unchecked(self.as_str())
        }
    }
}

impl AsRef<Eqname> for Ncname {
    #[inline]
    fn as_ref(&self) -> &Eqname {
        unsafe {
            debug_assert!(
                Eqname::from_str(self.as_str()).is_ok(),
                "An NCName is also a Eqname"
            );
            Eqname::new_unchecked(self.as_str())
        }
    }
}

impl<'a> TryFrom<&'a str> for &'a Ncname {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        Ncname::validate(s)?;
        Ok(unsafe {
            // This is safe because the string is validated.
            Ncname::new_unchecked(s)
        })
    }
}

impl<'a> TryFrom<&'a Name> for &'a Ncname {
    type Error = NameError;

    fn try_from(s: &'a Name) -> Result<Self, Self::Error> {
        if let Some(colon_pos) = s.as_str().find(':') {
            return Err(NameError::new(TargetNameType::Ncname, colon_pos));
        }

        unsafe {
            debug_assert!(
                Ncname::validate(s.as_str()).is_ok(),
                "Name {:?} without colons is also a valid NCName",
                s.as_str()
            );
            Ok(Ncname::new_unchecked(s.as_str()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ensure_eq(s: &str) {
        assert_eq!(
            Ncname::from_str(s).expect("Should not fail"),
            s,
            "String: {:?}",
            s
        );
    }

    fn ensure_error_at(s: &str, valid_up_to: usize) {
        let err = Ncname::from_str(s).expect_err("Should fail");
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
