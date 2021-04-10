//! [`URIQualifiedName`].
//!
//! [`URIQualifiedName`]:
//!     https://www.w3.org/TR/2017/REC-xpath-31-20170321/#prod-xpath31-URIQualifiedName
use core::convert::TryFrom;
use core::fmt;
use core::num::NonZeroUsize;

use crate::names::error::{NameError, TargetNameType};
use crate::names::{Eqname, Ncname};

/// String slice for [`URIQualifiedName`].
///
/// [`URIQualifiedName`]:
///     https://www.w3.org/TR/2017/REC-xpath-31-20170321/#prod-xpath31-URIQualifiedName
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct UriQualifiedName(str);

#[allow(clippy::len_without_is_empty)]
impl UriQualifiedName {
    /// Creates a new `&UriQualifiedName`.
    ///
    /// [`URIQualifiedName`] has `Q{uri}ncname` format.
    /// `UriQualifiedName` type validates NCName part, but does not validate URI part.
    ///
    /// > In most contexts, processors are not required to raise errors if a URI
    /// > is not lexically valid according to [RFC3986] and [RFC3987].
    /// > See [2.4.5 URI Literals][XPATH31-2.4.5] for details.
    /// >
    /// > --- [XML Path Language (XPath) 3.1, 2 Basics][XPATH31-2]
    ///
    /// > XPath 3.1 requires a statically known, valid URI in a BracedURILiteral.
    /// > An implementation may raise a static error err:XQST0046 if the value
    /// > of a Braced URI Literal is of nonzero length and is neither an
    /// > absolute URI nor a relative URI.
    /// >
    /// > --- [XML Path Language (XPath) 3.1, 2.4.5 URI Literals][XPATH31-2.4.5]
    ///
    /// It is user's responsibility to validate URI part if necessary.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`URIQualifiedName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::UriQualifiedName;
    /// let name = UriQualifiedName::from_str("Q{http://example.com/}name")?;
    /// assert_eq!(name, "Q{http://example.com/}name");
    ///
    /// assert_eq!(
    ///     UriQualifiedName::from_str("Q{}name")?,
    ///     "Q{}name",
    ///     "Empty URI is OK"
    /// );
    /// assert_eq!(
    ///     UriQualifiedName::from_str("Q{foo}bar")?,
    ///     "Q{foo}bar",
    ///     "URI is not validated"
    /// );
    ///
    /// assert!(
    ///     UriQualifiedName::from_str("foo").is_err(),
    ///     "URIQualifiedName has `Q{{uri}}ncname` format"
    /// );
    /// assert!(
    ///     UriQualifiedName::from_str("Q{http://example.com}foo:bar").is_err(),
    ///     "Colon is not allowed"
    /// );
    /// assert!(
    ///     UriQualifiedName::from_str("Q{foo{bar}qux").is_err(),
    ///     "URI part cannot have `{{` and `}}`"
    /// );
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`URIQualifiedName`]:
    ///     https://www.w3.org/TR/2017/REC-xpath-31-20170321/#prod-xpath31-URIQualifiedName
    /// [RFC3986]: https://tools.ietf.org/html/rfc3986
    /// [RFC3987]: https://tools.ietf.org/html/rfc3987
    /// [XPATH31-2]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#id-basics
    /// [XPATH31-2.4.5]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#id-uri-literals
    // `FromStr` can be implemented only for types with static lifetime.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, NameError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&UriQualifiedName` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be a valid [`URIQualifiedName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::UriQualifiedName;
    /// let name = unsafe {
    ///     UriQualifiedName::new_unchecked("Q{foo}bar")
    /// };
    /// assert_eq!(name, "Q{foo}bar");
    /// ```
    ///
    /// [`URIQualifiedName`]:
    ///     https://www.w3.org/TR/2017/REC-xpath-31-20170321/#prod-xpath31-URIQualifiedName
    #[inline]
    #[must_use]
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Validates the given string.
    fn validate(s: &str) -> Result<(), NameError> {
        match Self::parse_as_possible(s) {
            Ok(_) => Ok(()),
            Err(e) => Err(NameError::new(
                TargetNameType::UriQualifiedName,
                e.map_or(0, |(_local_name_start, valid_up_to)| valid_up_to.get()),
            )),
        }
    }

    /// Parses the given string from the beginning as possible.
    ///
    /// Retruns `Ok(local_name_start)` if the string is valid QName.
    /// Returns `Err(None)` if the string is completely invalid.
    /// Returns `Err(Some((local_name_start, valid_up_to)))` if the string is invalid
    /// but has valid substring as the prefix.
    pub(super) fn parse_as_possible(
        s: &str,
    ) -> Result<NonZeroUsize, Option<(NonZeroUsize, NonZeroUsize)>> {
        let uri_and_rest = s.strip_prefix("Q{").ok_or(None)?;
        let uri_len = match uri_and_rest.find(|c| c == '{' || c == '}') {
            Some(pos) if uri_and_rest.as_bytes()[pos] == b'}' => pos,
            _ => return Err(None),
        };

        let local_name_start = NonZeroUsize::new(uri_len + 3).expect("Should never be zero");
        let local_name = &s[local_name_start.get()..];
        match Ncname::from_str(local_name) {
            Ok(_) => Ok(local_name_start),
            Err(e) if e.valid_up_to() == 0 => Err(None),
            Err(e) => Err(Some((
                local_name_start,
                NonZeroUsize::new(local_name_start.get() + e.valid_up_to())
                    .expect("Should never be zero"),
            ))),
        }
    }

    /// Returns the string as `&str`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::UriQualifiedName;
    /// let name = UriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name, "Q{foo}bar");
    ///
    /// let s: &str = name.as_str();
    /// assert_eq!(s, "Q{foo}bar");
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
    /// # use xml_string::names::UriQualifiedName;
    /// let name = UriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name.len(), "Q{foo}bar".len());
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Parses the leading `UriQualifiedName` and returns the value and the rest input.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::UriQualifiedName;
    /// let input = "Q{foo}bar:012";
    /// let expected = UriQualifiedName::from_str("Q{foo}bar")
    ///     .expect("valid UriQualifiedName");
    /// assert_eq!(
    ///     UriQualifiedName::parse_next(input),
    ///     Ok((expected, ":012"))
    /// );
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// ```
    /// # use xml_string::names::UriQualifiedName;
    /// let input = "012";
    /// assert!(UriQualifiedName::parse_next(input).is_err());
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

    /// Returns the position where the local name starts.
    ///
    /// Note that this is O(length) operation.
    #[must_use]
    fn local_name_start(&self) -> NonZeroUsize {
        // Find `[2..]` since the first two characters are `Q{`.
        let pos = self.as_str()[2..]
            .find('}')
            .expect("Should never fail: Valid URIQualifiedName has `}` character")
            + 3;
        NonZeroUsize::new(pos)
            .expect("Should never fail: URIQualifiedName cannot start with the local name")
    }

    /// Returns the URI.
    ///
    /// Note that this is O(length) operation.
    /// Consider using [`ParsedUriQualifiedName::uri`] method if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::UriQualifiedName;
    /// let name = UriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name.uri(), "foo");
    ///
    /// let empty_uri = UriQualifiedName::from_str("Q{}foo")?;
    /// assert_eq!(empty_uri.uri(), "");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn uri(&self) -> &str {
        ParsedUriQualifiedName::new(self, self.local_name_start()).uri()
    }

    /// Returns the local name.
    ///
    /// Note that this is O(length) operation.
    /// Consider using [`ParsedUriQualifiedName::local_name`] method if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::UriQualifiedName;
    /// let name = UriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name.local_name(), "bar");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn local_name(&self) -> &Ncname {
        ParsedUriQualifiedName::new(self, self.local_name_start()).local_name()
    }

    /// Returns a pair of the uri and the local name.
    ///
    /// Note that this is O(length) operation.
    /// Consider using [`ParsedUriQualifiedName::uri_and_local`] method if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::UriQualifiedName;
    /// use std::convert::TryFrom;
    ///
    /// let name = UriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name.uri_and_local(), (name.uri(), name.local_name()));
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn uri_and_local(&self) -> (&str, &Ncname) {
        ParsedUriQualifiedName::new(self, self.local_name_start()).uri_and_local()
    }

    /// Converts a `Box<UriQualifiedName>` into a `Box<str>` without copying or allocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::UriQualifiedName;
    /// let name = UriQualifiedName::from_str("Q{foo}bar")?;
    /// let boxed_name: Box<UriQualifiedName> = name.into();
    /// assert_eq!(&*boxed_name, name);
    /// let boxed_str: Box<str> = boxed_name.into_boxed_str();
    /// assert_eq!(&*boxed_str, name.as_str());
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[cfg(feature = "alloc")]
    pub fn into_boxed_str(self: alloc::boxed::Box<Self>) -> Box<str> {
        unsafe {
            // This is safe because `UriQualifiedName` has the same memory layout as `str`
            // (thanks to `#[repr(transparent)]`).
            alloc::boxed::Box::<str>::from_raw(alloc::boxed::Box::<Self>::into_raw(self) as *mut str)
        }
    }
}

impl_traits_for_custom_string_slice!(UriQualifiedName);

impl AsRef<Eqname> for UriQualifiedName {
    #[inline]
    fn as_ref(&self) -> &Eqname {
        unsafe {
            debug_assert!(
                Eqname::from_str(self.as_str()).is_ok(),
                "URIQualifiedName {:?} must be a valid Eqname",
                self.as_str()
            );
            // This is safe because a URIQualifiedName is also a valid Eqname.
            Eqname::new_unchecked(self.as_str())
        }
    }
}

impl<'a> From<ParsedUriQualifiedName<'a>> for &'a UriQualifiedName {
    #[inline]
    fn from(s: ParsedUriQualifiedName<'a>) -> Self {
        s.content
    }
}

impl<'a> TryFrom<&'a str> for &'a UriQualifiedName {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        UriQualifiedName::validate(s)?;
        Ok(unsafe {
            // This is safe because the string is validated.
            UriQualifiedName::new_unchecked(s)
        })
    }
}

/// Parsed [`URIQualifiedName`] reference.
///
/// [`URIQualifiedName`]:
///     https://www.w3.org/TR/2017/REC-xpath-31-20170321/#prod-xpath31-URIQualifiedName
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ParsedUriQualifiedName<'a> {
    /// Content string.
    content: &'a UriQualifiedName,
    /// Start position of the local name.
    local_name_start: NonZeroUsize,
}

#[allow(clippy::len_without_is_empty)]
impl<'a> ParsedUriQualifiedName<'a> {
    /// Creates a new `ParsedUriQualifiedName`.
    ///
    /// # Panics
    ///
    /// Panics if the `local_name_start` does not point to the start position of
    /// the local name.
    #[must_use]
    pub(super) fn new(content: &'a UriQualifiedName, local_name_start: NonZeroUsize) -> Self {
        if content.as_str().as_bytes()[local_name_start.get() - 1] != b'}' {
            panic!(
                "`local_name_pos` (={:?}) should point to the next position
                 of the `}}` character in the URIQualifiedName {:?}",
                local_name_start.get(),
                content
            );
        }
        Self {
            content,
            local_name_start,
        }
    }

    /// Creates a new `ParsedUriQualifiedName<'_>` from the given string slice.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`URIQualifiedName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::ParsedUriQualifiedName;
    /// let name = ParsedUriQualifiedName::from_str("Q{http://example.com/}name")?;
    /// assert_eq!(name, "Q{http://example.com/}name");
    ///
    /// assert_eq!(
    ///     ParsedUriQualifiedName::from_str("Q{}name")?,
    ///     "Q{}name",
    ///     "Empty URI is OK"
    /// );
    /// assert_eq!(
    ///     ParsedUriQualifiedName::from_str("Q{foo}bar")?,
    ///     "Q{foo}bar",
    ///     "URI is not validated"
    /// );
    ///
    /// assert!(
    ///     ParsedUriQualifiedName::from_str("foo").is_err(),
    ///     "URIQualifiedName has `Q{{uri}}ncname` format"
    /// );
    /// assert!(
    ///     ParsedUriQualifiedName::from_str("Q{http://example.com}foo:bar").is_err(),
    ///     "Colon is not allowed"
    /// );
    /// assert!(
    ///     ParsedUriQualifiedName::from_str("Q{foo{bar}qux").is_err(),
    ///     "URI part cannot have `{{` and `}}`"
    /// );
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`URIQualifiedName`]:
    ///     https://www.w3.org/TR/2017/REC-xpath-31-20170321/#prod-xpath31-URIQualifiedName
    // `FromStr` can be implemented only for types with static lifetime.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn from_str(s: &'a str) -> Result<Self, NameError> {
        Self::try_from(s)
    }

    /// Returns the string as `&UriQualifiedName`.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::ParsedUriQualifiedName;
    /// use xml_string::names::UriQualifiedName;
    ///
    /// let name = ParsedUriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name, "Q{foo}bar");
    ///
    /// let s: &UriQualifiedName = name.as_uri_qualified_name();
    /// assert_eq!(s, "Q{foo}bar");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_uri_qualified_name(&self) -> &'a UriQualifiedName {
        self.content
    }

    /// Returns the string as `&str`.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::ParsedUriQualifiedName;
    /// let name = ParsedUriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name, "Q{foo}bar");
    ///
    /// let s: &str = name.as_str();
    /// assert_eq!(s, "Q{foo}bar");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &'a str {
        self.content.as_str()
    }

    /// Returns the length of the string in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::ParsedUriQualifiedName;
    /// let name = ParsedUriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name.len(), "Q{foo}bar".len());
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.content.len()
    }

    /// Returns the URI.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::ParsedUriQualifiedName;
    /// let name = ParsedUriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name.uri(), "foo");
    ///
    /// let empty_uri = ParsedUriQualifiedName::from_str("Q{}foo")?;
    /// assert_eq!(empty_uri.uri(), "");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[must_use]
    pub fn uri(&self) -> &'a str {
        &self.as_str()[2..(self.local_name_start.get() - 1)]
    }

    /// Returns the local name.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::ParsedUriQualifiedName;
    /// let name = ParsedUriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name.local_name(), "bar");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[must_use]
    pub fn local_name(&self) -> &'a Ncname {
        let local_name = &self.as_str()[self.local_name_start.get()..];
        unsafe {
            debug_assert!(
                Ncname::from_str(local_name).is_ok(),
                "The local name {:?} must be a valid NCName",
                local_name
            );
            // This is safe because the local name is a valid NCName.
            Ncname::new_unchecked(local_name)
        }
    }

    /// Returns a pair of the URI and the local name.
    ///
    /// This is efficient version of `(self.uri(), self.local_name())`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::ParsedUriQualifiedName;
    /// use std::convert::TryFrom;
    ///
    /// let name = ParsedUriQualifiedName::from_str("Q{foo}bar")?;
    /// assert_eq!(name.uri_and_local(), (name.uri(), name.local_name()));
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[must_use]
    pub fn uri_and_local(&self) -> (&'a str, &'a Ncname) {
        let local_name_start = self.local_name_start.get();
        let uri = &self.as_str()[2..(local_name_start - 1)];
        let local_name = &self.as_str()[local_name_start..];
        let local_name = unsafe {
            debug_assert!(
                Ncname::from_str(local_name).is_ok(),
                "The local name {:?} must be a valid NCName",
                local_name
            );
            // This is safe because the local name is a valid NCName.
            Ncname::new_unchecked(local_name)
        };
        (uri, local_name)
    }
}

impl PartialEq<str> for ParsedUriQualifiedName<'_> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}
impl_cmp!(str, ParsedUriQualifiedName<'_>);

impl PartialEq<&'_ str> for ParsedUriQualifiedName<'_> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}
impl_cmp!(&str, ParsedUriQualifiedName<'_>);

impl PartialEq<str> for &'_ ParsedUriQualifiedName<'_> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}
impl_cmp!(str, &ParsedUriQualifiedName<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<alloc::string::String> for ParsedUriQualifiedName<'_> {
    #[inline]
    fn eq(&self, other: &alloc::string::String) -> bool {
        self.as_str() == *other
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(alloc::string::String, ParsedUriQualifiedName<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<&alloc::string::String> for ParsedUriQualifiedName<'_> {
    #[inline]
    fn eq(&self, other: &&alloc::string::String) -> bool {
        self.as_str() == **other
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(&alloc::string::String, ParsedUriQualifiedName<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<alloc::boxed::Box<str>> for ParsedUriQualifiedName<'_> {
    #[inline]
    fn eq(&self, other: &alloc::boxed::Box<str>) -> bool {
        self.as_str() == other.as_ref()
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(alloc::boxed::Box<str>, ParsedUriQualifiedName<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<alloc::borrow::Cow<'_, str>> for ParsedUriQualifiedName<'_> {
    #[inline]
    fn eq(&self, other: &alloc::borrow::Cow<'_, str>) -> bool {
        self.as_str() == *other
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(alloc::borrow::Cow<'_, str>, ParsedUriQualifiedName<'_>);

impl AsRef<str> for ParsedUriQualifiedName<'_> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<UriQualifiedName> for ParsedUriQualifiedName<'_> {
    #[inline]
    fn as_ref(&self) -> &UriQualifiedName {
        self.content
    }
}

impl AsRef<Eqname> for ParsedUriQualifiedName<'_> {
    #[inline]
    fn as_ref(&self) -> &Eqname {
        self.content.as_ref()
    }
}

impl<'a> From<&'a UriQualifiedName> for ParsedUriQualifiedName<'a> {
    fn from(s: &'a UriQualifiedName) -> Self {
        let local_name_start = s.local_name_start();
        Self {
            content: s,
            local_name_start,
        }
    }
}

impl<'a> TryFrom<&'a str> for ParsedUriQualifiedName<'a> {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        match UriQualifiedName::parse_as_possible(s) {
            Ok(local_name_start) => {
                let content = unsafe {
                    // This is safe because the string is validated by
                    // `UriQualifiedName::parse_as_possible()`.
                    UriQualifiedName::new_unchecked(s)
                };
                Ok(Self {
                    content,
                    local_name_start,
                })
            }
            Err(e) => Err(NameError::new(
                TargetNameType::UriQualifiedName,
                e.map_or(0, |(_local_name_start, valid_up_to)| valid_up_to.get()),
            )),
        }
    }
}

impl fmt::Debug for ParsedUriQualifiedName<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Display for ParsedUriQualifiedName<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ncname(s: &str) -> &Ncname {
        Ncname::from_str(s)
            .unwrap_or_else(|e| panic!("Failed to cerate Ncname from {:?}: {}", s, e))
    }

    fn uqn(s: &str) -> &UriQualifiedName {
        UriQualifiedName::from_str(s)
            .unwrap_or_else(|e| panic!("Failed to create UriQualifiedName from {:?}: {}", s, e))
    }

    fn parsed_uqn(s: &str) -> ParsedUriQualifiedName<'_> {
        ParsedUriQualifiedName::from_str(s).unwrap_or_else(|e| {
            panic!(
                "Failed to create ParsedUriQualifiedName from {:?}: {}",
                s, e
            )
        })
    }

    fn ensure_eq(s: &str) {
        assert_eq!(
            UriQualifiedName::from_str(s).expect("Should not fail"),
            s,
            "String: {:?}",
            s
        );
    }

    fn ensure_error_at(s: &str, valid_up_to: usize) {
        let err = UriQualifiedName::from_str(s).expect_err("Should fail");
        assert_eq!(err.valid_up_to(), valid_up_to, "String: {:?}", s);
    }

    #[test]
    fn uqname_str_valid() {
        ensure_eq("Q{}local");
        ensure_eq("Q{foo}bar");
        ensure_eq("Q{http://example.com/}local");
    }

    #[test]
    fn uqname_str_invalid() {
        ensure_error_at("", 0);
        ensure_error_at("Q", 0);
        ensure_error_at("Q{", 0);
        ensure_error_at("Q{}", 0);
        ensure_error_at("Q{}:", 0);
        ensure_error_at("Q{}foo:", 6);
        ensure_error_at("Q{}foo:bar", 6);
        ensure_error_at("Q{foo}bar:baz", 9);
        ensure_error_at("Q{foo}bar}baz", 9);
        ensure_error_at("Q{foo{bar}baz", 0);
    }

    #[test]
    fn parse_as_possible() {
        assert_eq!(
            UriQualifiedName::parse_as_possible("Q{}bar"),
            Ok(NonZeroUsize::new(3).expect("Should never fail: not zero"))
        );
        assert_eq!(
            UriQualifiedName::parse_as_possible("Q{foo}bar"),
            Ok(NonZeroUsize::new(6).expect("Should never fail: not zero"))
        );

        assert_eq!(UriQualifiedName::parse_as_possible(""), Err(None));
        assert_eq!(
            UriQualifiedName::parse_as_possible("Q{}foo:bar"),
            Err(NonZeroUsize::new(3).zip(NonZeroUsize::new(6)))
        );
        assert_eq!(
            UriQualifiedName::parse_as_possible("Q{foo}bar:baz"),
            Err(NonZeroUsize::new(6).zip(NonZeroUsize::new(9)))
        );
    }

    #[test]
    fn parsed_uri_qualified_name_from_str() {
        assert_eq!(
            ParsedUriQualifiedName::from_str("Q{foo}bar").map(|v| v.as_uri_qualified_name()),
            Ok(uqn("Q{foo}bar"))
        );

        assert_eq!(
            ParsedUriQualifiedName::from_str("Q{foo}:bar"),
            Err(NameError::new(TargetNameType::UriQualifiedName, 0))
        );

        assert_eq!(
            ParsedUriQualifiedName::from_str("Q{foo}bar:baz"),
            Err(NameError::new(TargetNameType::UriQualifiedName, 9))
        );
    }

    #[test]
    fn parsed_uri_qualified_name_uri() {
        assert_eq!(parsed_uqn("Q{}foo").uri(), "");
        assert_eq!(parsed_uqn("Q{foo}bar").uri(), "foo");
    }

    #[test]
    fn parsed_uri_qualified_name_local_name() {
        assert_eq!(parsed_uqn("Q{}foo").local_name(), ncname("foo"));
        assert_eq!(parsed_uqn("Q{foo}bar").local_name(), ncname("bar"));
    }

    #[test]
    fn parsed_uri_qualified_name_uri_and_local() {
        assert_eq!(parsed_uqn("Q{}foo").uri_and_local(), ("", ncname("foo")));
        assert_eq!(
            parsed_uqn("Q{foo}bar").uri_and_local(),
            ("foo", ncname("bar"))
        );
    }
}
