//! [`EQName`]: `QName` OR `URIQualifiedName`.
//!
//! [`EQName`]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#prod-xpath31-EQName

use core::cmp;
use core::convert::TryFrom;
use core::fmt;
use core::hash;
use core::num::NonZeroUsize;

use crate::names::error::{NameError, TargetNameType};
use crate::names::{Ncname, ParsedQname, ParsedUriQualifiedName, Qname, UriQualifiedName};

/// A type for data which is specific to each variant of [`EQName`][spec-eqname]:
/// [`QName`][spec-qname] or [`URIQualifiedName`][spec-uqn].
///
/// [spec-eqname]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-EQName
/// [spec-qname]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-QName
/// [spec-uqn]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-URIQualifiedName
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EqnameVariantData<Q, U> {
    /// Data specific to `QName`.
    Q(Q),
    /// Data specific to `URIQualifiedName`.
    UriQualified(U),
}

impl<Q, U> EqnameVariantData<Q, U> {
    /// Returns the variant data with reference types.
    fn as_ref(&self) -> EqnameVariantData<&Q, &U> {
        match self {
            Self::Q(v) => EqnameVariantData::Q(v),
            Self::UriQualified(v) => EqnameVariantData::UriQualified(v),
        }
    }
}

/// A type to represent namespace of an [`EQName`][spec-eqname].
///
/// If the `EQName` is a [`QName`][spec-qname], then returns `None` or `Prefix(prefix)`.
/// If the name is a [`URIQualifiedName`][spec-uqn], then returns `Uri(uri)`.
///
/// [spec-eqname]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-EQName
/// [spec-qname]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-QName
/// [spec-uqn]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-URIQualifiedName
// Practically, this can be represented by `Option<EqnameVariantData<&Ncname, &str>>`,
// but more specific type is preferred. Putting namespace URI in `&str` and
// prefix in `&Ncname` to the same type without "URI" and "prefix" annotation
// would be very confusing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EqnameNamespace<'a> {
    /// No prefix or namespace.
    None,
    /// Namespace prefix.
    Prefix(&'a Ncname),
    /// Namespace URI.
    Uri(&'a str),
}

/// String slice for [`EQName`][spec-eqname].
///
/// [`EQName`][spec-eqname] is union of [`QName`][spec-qname] and
/// [`URIQualifiedName`][spec-uqn].
/// See the documentation for [`Qname`] type and [`UriQualifiedName`] type.
///
/// [spec-eqname]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-EQName
/// [spec-qname]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-QName
/// [spec-uqn]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-URIQualifiedName
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Eqname(str);

#[allow(clippy::len_without_is_empty)]
impl Eqname {
    /// Creates a new `&UriQualifiedName`.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`EQName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// let prefixed_q = Eqname::from_str("foo:bar")?;
    /// assert_eq!(prefixed_q, "foo:bar");
    ///
    /// let nc = Eqname::from_str("ncname")?;
    /// assert_eq!(nc, "ncname");
    ///
    /// let uri_qualified = Eqname::from_str("Q{http://example.com/}name")?;
    /// assert_eq!(uri_qualified, "Q{http://example.com/}name");
    ///
    /// assert_eq!(
    ///     Eqname::from_str("Q{}name")?,
    ///     "Q{}name",
    ///     "Empty URI is OK"
    /// );
    /// assert_eq!(
    ///     Eqname::from_str("Q{foo}bar")?,
    ///     "Q{foo}bar",
    ///     "URI is not validated"
    /// );
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`EQName`]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-EQName
    // `FromStr` can be implemented only for types with static lifetime.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, NameError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&Eqname` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be a valid [`EQName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// let q = unsafe {
    ///     Eqname::new_unchecked("foo:bar")
    /// };
    /// assert_eq!(q, "foo:bar");
    ///
    /// let uri_qualified = unsafe {
    ///     Eqname::new_unchecked("Q{foo}bar")
    /// };
    /// assert_eq!(uri_qualified, "Q{foo}bar");
    /// ```
    ///
    /// [`EQName`]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-EQName
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
                TargetNameType::Eqname,
                e.map_or(0, |(_local_name_start, valid_up_to)| valid_up_to.get()),
            )),
        }
    }

    /// Returns whether the string should be parsed as URIQualifiedName.
    ///
    /// Note that this should be called only for a valid EQName.
    /// Never use this for non-validated strings.
    #[inline]
    fn should_be_parsed_as_uri_qualified(s: &str) -> bool {
        s.as_bytes()[1] == b'{'
    }

    /// Parses the given string from the beginning as possible.
    ///
    /// Retruns `Ok(EqnameVariantData::Q(local_name_start))` if the string is valid QName.
    /// Retruns `Ok(EqnameVariantData::UriQualified(local_name_start))` if the string is valid
    /// URIQualifiedName.
    /// Returns `Err(None)` if the string is completely invalid.
    /// Returns `Err(Some((local_name_start, valid_up_to)))` if the string is invalid
    /// but has valid substring as the prefix.
    fn parse_as_possible(
        s: &str,
    ) -> Result<EqnameVariantData<usize, NonZeroUsize>, Option<(usize, NonZeroUsize)>> {
        // This check should not be `Self::should_be_parsed_as_uri_qualified`,
        // because the string is not yet validated.
        if s.starts_with("Q{") {
            UriQualifiedName::parse_as_possible(s)
                .map(EqnameVariantData::UriQualified)
                .map_err(|e| {
                    Some(match e {
                        None => (0, NonZeroUsize::new(1).expect("1 is not zero")),
                        Some((local_name_start, valid_up_to)) => {
                            (local_name_start.get(), valid_up_to)
                        }
                    })
                })
        } else {
            match Qname::parse_as_possible(s) {
                Ok(colon_pos) => {
                    let local_name_start = colon_pos.map_or(0, |v| v.get() + 1);
                    Ok(EqnameVariantData::Q(local_name_start))
                }
                Err((colon_pos, valid_up_to)) => Err(NonZeroUsize::new(valid_up_to)
                    .map(|valid_up_to| (colon_pos.map_or(0, |v| v.get() + 1), valid_up_to))),
            }
        }
    }

    /// Returns the string as `&str`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// let q = Eqname::from_str("foo:bar")?;
    /// assert_eq!(q, "foo:bar");
    /// assert_eq!(q.as_str(), "foo:bar");
    ///
    /// let uri_qualified = Eqname::from_str("Q{foo}bar")?;
    /// assert_eq!(uri_qualified, "Q{foo}bar");
    /// assert_eq!(uri_qualified.as_str(), "Q{foo}bar");
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
    /// # use xml_string::names::Eqname;
    /// let q = Eqname::from_str("foo:bar")?;
    /// assert_eq!(q.len(), "foo:bar".len());
    ///
    /// let uri_qualified = Eqname::from_str("Q{foo}bar")?;
    /// assert_eq!(uri_qualified.len(), "Q{foo}bar".len());
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns the name in the type specific to the variant
    /// (i.e. [`Qname`] or [`UriQualifiedName`]).
    pub fn to_variant(&self) -> EqnameVariantData<&Qname, &UriQualifiedName> {
        if Self::should_be_parsed_as_uri_qualified(self.as_str()) {
            unsafe {
                debug_assert!(
                    UriQualifiedName::from_str(self.as_str()).is_ok(),
                    "The string should be URIQualifiedName"
                );
                // This is safe because the string must be valid URIQualifiedName,
                // if `Self::should_be_parsed_as_uri_qualified` returns `true`.
                EqnameVariantData::UriQualified(UriQualifiedName::new_unchecked(self.as_str()))
            }
        } else {
            unsafe {
                debug_assert!(
                    Qname::from_str(self.as_str()).is_ok(),
                    "The string should be QName"
                );
                // This is safe because the string must be valid QName,
                // if `Self::should_be_parsed_as_uri_qualified` returns `false`.
                EqnameVariantData::Q(Qname::new_unchecked(self.as_str()))
            }
        }
    }

    /// Returns the string as `QName`, if valid.
    pub fn as_qname(&self) -> Option<&Qname> {
        if Self::should_be_parsed_as_uri_qualified(self.as_str()) {
            return None;
        }
        unsafe {
            debug_assert!(
                Qname::from_str(self.as_str()).is_ok(),
                "The string should be QName"
            );
            // This is safe because the string must be valid QName,
            // if `Self::should_be_parsed_as_uri_qualified` returns `false`.
            Some(Qname::new_unchecked(self.as_str()))
        }
    }

    /// Returns the string as `URIQualifiedName`, if valid.
    pub fn as_uri_qualified_name(&self) -> Option<&UriQualifiedName> {
        if !Self::should_be_parsed_as_uri_qualified(self.as_str()) {
            return None;
        }
        unsafe {
            debug_assert!(
                UriQualifiedName::from_str(self.as_str()).is_ok(),
                "The string should be URIQualifiedName"
            );
            // This is safe because the string must be valid URIQualifiedName,
            // if `Self::should_be_parsed_as_uri_qualified` returns `true`.
            Some(UriQualifiedName::new_unchecked(self.as_str()))
        }
    }

    /// Parses the leading `Eqname` and returns the value and the rest input.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// let input = "foo:bar:012";
    /// let expected = Eqname::from_str("foo:bar")
    ///     .expect("valid QName");
    /// assert_eq!(
    ///     Eqname::parse_next(input),
    ///     Ok((expected, ":012"))
    /// );
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// let input = "Q{foo}bar:012";
    /// let expected = Eqname::from_str("Q{foo}bar")
    ///     .expect("valid UriQualifiedName");
    /// assert_eq!(
    ///     Eqname::parse_next(input),
    ///     Ok((expected, ":012"))
    /// );
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// let input = "012";
    /// assert!(Eqname::parse_next(input).is_err());
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
    fn local_name_start(&self) -> usize {
        let s = self.as_str();
        if Self::should_be_parsed_as_uri_qualified(s) {
            s.find('}')
                .expect("Should never fail: Valid URIQualifiedName contains '}' character")
                + 1
        } else {
            s.find(':').map_or(0, |colon_pos| colon_pos + 1)
        }
    }

    /// Returns the namespace part if available: prefix for [`Qname`], URI for [`UriQualifiedName`].
    ///
    /// Note that this is O(length) operation.
    /// Consider using [`ParsedEqname::local_name`] method if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// use xml_string::names::{EqnameNamespace, Ncname, Qname};
    ///
    /// let nc = Eqname::from_str("local")?;
    /// assert_eq!(nc.namespace(), EqnameNamespace::None);
    ///
    /// let q = Eqname::from_str("foo:bar")?;
    /// let q_prefix = Ncname::from_str("foo")
    ///     .expect("Should never fail: Valid NCName");
    /// assert_eq!(q.namespace(), EqnameNamespace::Prefix(q_prefix));
    ///
    /// let uri_qualified = Eqname::from_str("Q{foo}bar")?;
    /// assert_eq!(uri_qualified.namespace(), EqnameNamespace::Uri("foo"));
    ///
    /// let uri_qualified_empty = Eqname::from_str("Q{}bar")?;
    /// assert_eq!(uri_qualified_empty.namespace(), EqnameNamespace::Uri(""));
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    pub fn namespace(&self) -> EqnameNamespace<'_> {
        match self.to_variant() {
            EqnameVariantData::Q(q) => q
                .prefix()
                .map_or(EqnameNamespace::None, EqnameNamespace::Prefix),
            EqnameVariantData::UriQualified(uri_qualified) => {
                EqnameNamespace::Uri(uri_qualified.uri())
            }
        }
    }

    /// Returns the local name.
    ///
    /// Note that this is O(length) operation.
    /// Consider using [`ParsedEqname::local_name`] method if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// let q = Eqname::from_str("foo:bar")?;
    /// assert_eq!(q.local_name(), "bar");
    ///
    /// let nc = Eqname::from_str("bar")?;
    /// assert_eq!(nc.local_name(), "bar");
    ///
    /// let uri_qualified = Eqname::from_str("Q{foo}bar")?;
    /// assert_eq!(uri_qualified.local_name(), "bar");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn local_name(&self) -> &Ncname {
        match self.to_variant() {
            EqnameVariantData::Q(qname) => qname.local_part(),
            EqnameVariantData::UriQualified(uri_qualified) => uri_qualified.local_name(),
        }
    }

    /// Returns a pair of the namespace and the local name.
    ///
    /// This returns the same result as `(self.namespace(), self.local_name())`,
    /// but more efficiently than calling [`Eqname::namespace`] and
    /// [`Eqname::local_name`] individually.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// use xml_string::names::{EqnameNamespace, Ncname};
    ///
    /// let ncname_bar = Ncname::from_str("bar")
    ///     .expect("Should never fail: Valid NCName");
    ///
    /// let nc = Eqname::from_str("bar")?;
    /// assert_eq!(nc.namespace_and_local(), (EqnameNamespace::None, ncname_bar));
    ///
    /// let q = Eqname::from_str("foo:bar")?;
    /// let expected_prefix = Ncname::from_str("foo")
    ///     .expect("Should never fail: Valid NCName");
    /// assert_eq!(
    ///     q.namespace_and_local(),
    ///     (EqnameNamespace::Prefix(expected_prefix), ncname_bar)
    /// );
    ///
    /// let uri_qualified = Eqname::from_str("Q{foo}bar")?;
    /// assert_eq!(uri_qualified.namespace_and_local(), (EqnameNamespace::Uri("foo"), ncname_bar));
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[must_use]
    pub fn namespace_and_local(&self) -> (EqnameNamespace<'_>, &'_ Ncname) {
        match self.to_variant() {
            EqnameVariantData::Q(q) => {
                let (prefix, local) = q.prefix_and_local();
                (
                    prefix.map_or(EqnameNamespace::None, EqnameNamespace::Prefix),
                    local,
                )
            }
            EqnameVariantData::UriQualified(uri_qualified) => {
                let (uri, local) = uri_qualified.uri_and_local();
                (EqnameNamespace::Uri(uri), local)
            }
        }
    }

    /// Converts a `Box<Eqname>` into a `Box<str>` without copying or allocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// let name = Eqname::from_str("q:name")?;
    /// let boxed_name: Box<Eqname> = name.into();
    /// assert_eq!(&*boxed_name, name);
    /// let boxed_str: Box<str> = boxed_name.into_boxed_str();
    /// assert_eq!(&*boxed_str, name.as_str());
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[cfg(feature = "alloc")]
    pub fn into_boxed_str(self: alloc::boxed::Box<Self>) -> Box<str> {
        unsafe {
            // This is safe because `Eqname` has the same memory layout as `str`
            // (thanks to `#[repr(transparent)]`).
            alloc::boxed::Box::<str>::from_raw(alloc::boxed::Box::<Self>::into_raw(self) as *mut str)
        }
    }
}

impl_traits_for_custom_string_slice!(Eqname);

impl<'a> From<&'a Ncname> for &'a Eqname {
    #[inline]
    fn from(s: &'a Ncname) -> Self {
        s.as_ref()
    }
}

impl<'a> From<&'a Qname> for &'a Eqname {
    #[inline]
    fn from(s: &'a Qname) -> Self {
        s.as_ref()
    }
}

impl<'a> From<&'a UriQualifiedName> for &'a Eqname {
    #[inline]
    fn from(s: &'a UriQualifiedName) -> Self {
        s.as_ref()
    }
}

impl<'a> From<ParsedEqname<'a>> for &'a Eqname {
    #[inline]
    fn from(s: ParsedEqname<'a>) -> Self {
        s.as_eqname()
    }
}

impl<'a> TryFrom<&'a str> for &'a Eqname {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        Eqname::validate(s)?;
        Ok(unsafe {
            // This is safe because the string is validated.
            Eqname::new_unchecked(s)
        })
    }
}

impl<'a> TryFrom<&'a Eqname> for &'a Ncname {
    type Error = NameError;

    fn try_from(s: &'a Eqname) -> Result<Self, Self::Error> {
        if let EqnameVariantData::Q(qname) = s.to_variant() {
            Self::try_from(qname)
        } else {
            debug_assert!(s.as_str().starts_with("Q{"));
            // `valid_up_to` is 1, because the string starts with "Q{".
            Err(NameError::new(TargetNameType::Ncname, 1))
        }
    }
}

/// Parsed [`EQName`] reference.
///
/// [`EQName`]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#prod-xpath31-EQName
#[derive(Clone, Copy, Eq)]
pub struct ParsedEqname<'a> {
    /// Content string.
    content: EqnameVariantData<ParsedQname<'a>, ParsedUriQualifiedName<'a>>,
}

impl<'a> ParsedEqname<'a> {
    /// Creates a new `ParsedEqname`.
    ///
    /// # Panics
    ///
    /// Panics if `local_name_start` points is invalid.
    #[must_use]
    fn new(content: &'a Eqname, local_name_start: usize) -> Self {
        let content = match content.to_variant() {
            EqnameVariantData::Q(qname) => {
                let prefix_len = NonZeroUsize::new(local_name_start.saturating_sub(1));
                EqnameVariantData::Q(ParsedQname::new(qname, prefix_len))
            }
            EqnameVariantData::UriQualified(uri_qualified_name) => {
                let local_name_start = NonZeroUsize::new(local_name_start)
                    .expect("`local_name_start` should be nonzero");
                EqnameVariantData::UriQualified(ParsedUriQualifiedName::new(
                    uri_qualified_name,
                    local_name_start,
                ))
            }
        };
        Self { content }
    }

    /// Creates a new `ParsedEqname<'_>` from the given string slice.
    ///
    /// # Failures
    ///
    /// Fails if the given string is not a valid [`EQName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::ParsedEqname;
    /// let nc = ParsedEqname::from_str("hello")?;
    /// assert_eq!(nc, "hello");
    ///
    /// let q = ParsedEqname::from_str("foo:bar")?;
    /// assert_eq!(q, "foo:bar");
    ///
    /// let uri_qualified = ParsedEqname::from_str("Q{foo}bar")?;
    /// assert_eq!(uri_qualified, "Q{foo}bar");
    ///
    /// assert!(ParsedEqname::from_str("").is_err(), "Empty string is not an EQName");
    /// assert!(ParsedEqname::from_str("foo bar").is_err(), "Whitespace is not allowed");
    /// assert!(ParsedEqname::from_str("foo:bar:baz").is_err(), "Two or more colons are not allowed");
    /// assert!(ParsedEqname::from_str("0foo").is_err(), "ASCII digit at the beginning is not allowed");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    ///
    /// [`EQName`]: https://www.w3.org/TR/2017/REC-xpath-31-20170321/#prod-xpath31-EQName
    // `FromStr` can be implemented only for types with static lifetime.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn from_str(s: &'a str) -> Result<Self, NameError> {
        Self::try_from(s)
    }

    /// Returns the string as `&Eqname`.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::ParsedEqname;
    /// use xml_string::names::Eqname;
    ///
    /// let name = ParsedEqname::from_str("foo:bar")?;
    /// assert_eq!(name, "foo:bar");
    ///
    /// let s: &Eqname = name.as_eqname();
    /// assert_eq!(s, "foo:bar");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_eqname(&self) -> &'a Eqname {
        unsafe {
            // Paranoia test.
            debug_assert!(Eqname::from_str(self.as_str()).is_ok());
            // This is safe because both of QName and URIQualifiedName is valid EQName.
            Eqname::new_unchecked(self.as_str())
        }
    }

    /// Returns the string as `&Qname` if it is QName.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::ParsedEqname;
    /// use xml_string::names::Qname;
    ///
    /// let name = ParsedEqname::from_str("foo:bar")?;
    /// assert_eq!(name, "foo:bar");
    ///
    /// let s: &Qname = name.as_qname()
    ///     .expect("The string is QName");
    /// assert_eq!(s, "foo:bar");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_qname(&self) -> Option<&'a Qname> {
        match &self.content {
            EqnameVariantData::Q(v) => Some(v.as_qname()),
            EqnameVariantData::UriQualified(_) => None,
        }
    }

    /// Returns the string as `&UriQualifiedName` if it is URIQualifiedName.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::ParsedEqname;
    /// use xml_string::names::UriQualifiedName;
    ///
    /// let name = ParsedEqname::from_str("Q{foo}bar")?;
    /// assert_eq!(name, "Q{foo}bar");
    ///
    /// let s: &UriQualifiedName = name.as_uri_qualified_name()
    ///     .expect("The string is URIQualifiedName");
    /// assert_eq!(s, "Q{foo}bar");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_uri_qualified_name(&self) -> Option<&'a UriQualifiedName> {
        match &self.content {
            EqnameVariantData::Q(_) => None,
            EqnameVariantData::UriQualified(v) => Some(v.as_uri_qualified_name()),
        }
    }

    /// Returns the string as `&str`.
    ///
    /// # Exmaples
    ///
    /// ```
    /// # use xml_string::names::ParsedEqname;
    /// let name = ParsedEqname::from_str("hello")?;
    /// assert_eq!(name, "hello");
    ///
    /// let s: &str = name.as_str();
    /// assert_eq!(s, "hello");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &'a str {
        match self.content {
            EqnameVariantData::Q(v) => v.as_str(),
            EqnameVariantData::UriQualified(v) => v.as_str(),
        }
    }

    /// Returns the name in the type specific to the variant
    /// (i.e. [`Qname`] or [`UriQualifiedName`]).
    pub fn to_variant(&self) -> EqnameVariantData<&Qname, &UriQualifiedName> {
        match self.content {
            EqnameVariantData::Q(v) => EqnameVariantData::Q(v.as_qname()),
            EqnameVariantData::UriQualified(v) => {
                EqnameVariantData::UriQualified(v.as_uri_qualified_name())
            }
        }
    }

    /// Returns the name in the type specific to the variant
    /// (i.e. [`ParsedQname`] or [`ParsedUriQualifiedName`]).
    pub fn to_parsed_variant(
        &self,
    ) -> EqnameVariantData<&ParsedQname<'a>, &ParsedUriQualifiedName<'a>> {
        self.content.as_ref()
    }

    /// Returns the namespace part if available: prefix for [`Qname`], URI for [`UriQualifiedName`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::Eqname;
    /// use xml_string::names::{EqnameNamespace, Ncname, Qname};
    ///
    /// let nc = Eqname::from_str("local")?;
    /// assert_eq!(nc.namespace(), EqnameNamespace::None);
    ///
    /// let q = Eqname::from_str("foo:bar")?;
    /// let q_prefix = Ncname::from_str("foo")
    ///     .expect("Should never fail: Valid NCName");
    /// assert_eq!(q.namespace(), EqnameNamespace::Prefix(q_prefix));
    ///
    /// let uri_qualified = Eqname::from_str("Q{foo}bar")?;
    /// assert_eq!(uri_qualified.namespace(), EqnameNamespace::Uri("foo"));
    ///
    /// let uri_qualified_empty = Eqname::from_str("Q{}bar")?;
    /// assert_eq!(uri_qualified_empty.namespace(), EqnameNamespace::Uri(""));
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    pub fn namespace(&self) -> EqnameNamespace<'a> {
        match self.content {
            EqnameVariantData::Q(q) => q
                .prefix()
                .map_or(EqnameNamespace::None, EqnameNamespace::Prefix),
            EqnameVariantData::UriQualified(uri_qualified) => {
                EqnameNamespace::Uri(uri_qualified.uri())
            }
        }
    }

    /// Returns the local part.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::ParsedEqname;
    ///
    /// let nc = ParsedEqname::from_str("foo")?;
    /// assert_eq!(nc.local_name(), "foo");
    /// let q = ParsedEqname::from_str("foo:bar")?;
    /// assert_eq!(q.local_name(), "bar");
    ///
    /// let uri_qualified = ParsedEqname::from_str("Q{foo}bar")?;
    /// assert_eq!(uri_qualified.local_name(), "bar");
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[must_use]
    pub fn local_name(&self) -> &'a Ncname {
        match self.content {
            EqnameVariantData::Q(v) => v.local_part(),
            EqnameVariantData::UriQualified(v) => v.local_name(),
        }
    }

    /// Returns a pair of the namespace and the local name.
    ///
    /// This returns the same result as `(self.namespace(), self.local_name())`,
    /// but more efficiently than calling [`ParsedEqname::namespace`] and
    /// [`ParsedEqname::local_name`] individually.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::ParsedEqname;
    /// use xml_string::names::{EqnameNamespace, Ncname};
    ///
    /// let ncname_bar = Ncname::from_str("bar")
    ///     .expect("Should never fail: Valid NCName");
    ///
    /// let nc = ParsedEqname::from_str("bar")?;
    /// assert_eq!(nc.namespace_and_local(), (EqnameNamespace::None, ncname_bar));
    ///
    /// let q = ParsedEqname::from_str("foo:bar")?;
    /// let expected_prefix = Ncname::from_str("foo")
    ///     .expect("Should never fail: Valid NCName");
    /// assert_eq!(
    ///     q.namespace_and_local(),
    ///     (EqnameNamespace::Prefix(expected_prefix), ncname_bar)
    /// );
    ///
    /// let uri_qualified = ParsedEqname::from_str("Q{foo}bar")?;
    /// assert_eq!(uri_qualified.namespace_and_local(), (EqnameNamespace::Uri("foo"), ncname_bar));
    /// # Ok::<_, xml_string::names::NameError>(())
    /// ```
    #[must_use]
    pub fn namespace_and_local(&self) -> (EqnameNamespace<'a>, &'a Ncname) {
        match self.content {
            EqnameVariantData::Q(q) => {
                let (prefix, local) = q.prefix_and_local();
                (
                    prefix.map_or(EqnameNamespace::None, EqnameNamespace::Prefix),
                    local,
                )
            }
            EqnameVariantData::UriQualified(uri_qualified) => {
                let (uri, local) = uri_qualified.uri_and_local();
                (EqnameNamespace::Uri(uri), local)
            }
        }
    }
}

impl PartialEq for ParsedEqname<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl PartialOrd for ParsedEqname<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl Ord for ParsedEqname<'_> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_str().cmp(&other.as_str())
    }
}

impl hash::Hash for ParsedEqname<'_> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl PartialEq<str> for ParsedEqname<'_> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}
impl_cmp!(str, ParsedEqname<'_>);

impl PartialEq<&'_ str> for ParsedEqname<'_> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}
impl_cmp!(&str, ParsedEqname<'_>);

impl PartialEq<str> for &'_ ParsedEqname<'_> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}
impl_cmp!(str, &ParsedEqname<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<alloc::string::String> for ParsedEqname<'_> {
    #[inline]
    fn eq(&self, other: &alloc::string::String) -> bool {
        self.as_str() == *other
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(alloc::string::String, ParsedEqname<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<&alloc::string::String> for ParsedEqname<'_> {
    #[inline]
    fn eq(&self, other: &&alloc::string::String) -> bool {
        self.as_str() == **other
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(&alloc::string::String, ParsedEqname<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<alloc::boxed::Box<str>> for ParsedEqname<'_> {
    #[inline]
    fn eq(&self, other: &alloc::boxed::Box<str>) -> bool {
        self.as_str() == other.as_ref()
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(alloc::boxed::Box<str>, ParsedEqname<'_>);

#[cfg(feature = "alloc")]
impl PartialEq<alloc::borrow::Cow<'_, str>> for ParsedEqname<'_> {
    #[inline]
    fn eq(&self, other: &alloc::borrow::Cow<'_, str>) -> bool {
        self.as_str() == *other
    }
}
#[cfg(feature = "alloc")]
impl_cmp!(alloc::borrow::Cow<'_, str>, ParsedEqname<'_>);

impl AsRef<str> for ParsedEqname<'_> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<Eqname> for ParsedEqname<'_> {
    fn as_ref(&self) -> &Eqname {
        match &self.content {
            EqnameVariantData::Q(qname) => qname.as_ref(),
            EqnameVariantData::UriQualified(uri_qualified) => uri_qualified.as_ref(),
        }
    }
}

impl<'a> From<&'a Eqname> for ParsedEqname<'a> {
    fn from(s: &'a Eqname) -> Self {
        Self::new(s, s.local_name_start())
    }
}

impl<'a> TryFrom<&'a str> for ParsedEqname<'a> {
    type Error = NameError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        let local_name_start = match Eqname::parse_as_possible(s) {
            Ok(EqnameVariantData::Q(start)) => start,
            Ok(EqnameVariantData::UriQualified(start)) => start.get(),
            Err(e) => {
                return Err(NameError::new(
                    TargetNameType::Eqname,
                    e.map_or(0, |(_colon_pos, valid_up_to)| valid_up_to.get()),
                ))
            }
        };
        let content = unsafe {
            // This is safe because the string is validated by
            // `Eqname::parse_as_possible()`.
            Eqname::new_unchecked(s)
        };
        Ok(Self::new(content, local_name_start))
    }
}

impl fmt::Debug for ParsedEqname<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Display for ParsedEqname<'_> {
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

    fn eqname(s: &str) -> &Eqname {
        Eqname::from_str(s)
            .unwrap_or_else(|e| panic!("Failed to create Eqname from {:?}: {}", s, e))
    }

    fn parsed_eqname(s: &str) -> ParsedEqname<'_> {
        ParsedEqname::from_str(s)
            .unwrap_or_else(|e| panic!("Failed to create ParsedEqname from {:?}: {}", s, e))
    }

    fn ensure_eq(s: &str) {
        assert_eq!(
            Eqname::from_str(s).expect("Should not fail"),
            s,
            "String: {:?}",
            s
        );
    }

    fn ensure_error_at(s: &str, valid_up_to: usize) {
        let err = Eqname::from_str(s).expect_err("Should fail");
        assert_eq!(err.valid_up_to(), valid_up_to, "String: {:?}", s);
    }

    #[test]
    fn qname_str_valid() {
        ensure_eq("local");
        ensure_eq("foo:bar");
        ensure_eq("Q");
    }

    #[test]
    fn qname_str_invalid() {
        ensure_error_at("", 0);
        ensure_error_at(":", 0);
        ensure_error_at("foo:", 3);
        ensure_error_at(":bar", 0);
        ensure_error_at("foo::bar", 3);
        ensure_error_at("foo:bar:", 7);
        ensure_error_at(":foo:bar", 0);
        ensure_error_at("foo:bar:baz", 7);
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
        ensure_error_at("Q{", 1);
        ensure_error_at("Q{}", 1);
        ensure_error_at("Q{}:", 1);
        ensure_error_at("Q{}foo:", 6);
        ensure_error_at("Q{}foo:bar", 6);
        ensure_error_at("Q{foo}bar:baz", 9);
        ensure_error_at("Q{foo}bar}baz", 9);
        ensure_error_at("Q{foo{bar}baz", 1);
    }

    #[test]
    fn parse_as_possible() {
        assert_eq!(
            Eqname::parse_as_possible("local"),
            Ok(EqnameVariantData::Q(0))
        );
        assert_eq!(
            Eqname::parse_as_possible("foo:bar"),
            Ok(EqnameVariantData::Q(4))
        );

        assert_eq!(Eqname::parse_as_possible(""), Err(None));

        assert_eq!(
            Eqname::parse_as_possible("foo:"),
            Err(Some(0).zip(NonZeroUsize::new(3)))
        );
        assert_eq!(
            Eqname::parse_as_possible("foo:bar:"),
            Err(Some(4).zip(NonZeroUsize::new(7)))
        );
        assert_eq!(
            Eqname::parse_as_possible("foo::bar"),
            Err(Some(0).zip(NonZeroUsize::new(3)))
        );
        assert_eq!(Eqname::parse_as_possible(":foo"), Err(None));

        assert_eq!(
            Eqname::parse_as_possible("Q{}bar"),
            Ok(EqnameVariantData::UriQualified(
                NonZeroUsize::new(3).expect("Should never fail: not zero")
            ))
        );
        assert_eq!(
            Eqname::parse_as_possible("Q{foo}bar"),
            Ok(EqnameVariantData::UriQualified(
                NonZeroUsize::new(6).expect("Should never fail: not zero")
            ))
        );

        assert_eq!(
            Eqname::parse_as_possible("Q{}foo:bar"),
            Err(Some(3).zip(NonZeroUsize::new(6)))
        );
        assert_eq!(
            Eqname::parse_as_possible("Q{foo}bar:baz"),
            Err(Some(6).zip(NonZeroUsize::new(9)))
        );
    }

    #[test]
    fn parsed_eqname_from_str() {
        assert_eq!(
            ParsedEqname::from_str("foo").map(|v| v.as_eqname()),
            Ok(eqname("foo"))
        );
        assert_eq!(
            ParsedEqname::from_str("foo:bar").map(|v| v.as_eqname()),
            Ok(eqname("foo:bar"))
        );
        assert_eq!(
            ParsedEqname::from_str("Q{foo}bar").map(|v| v.as_eqname()),
            Ok(eqname("Q{foo}bar"))
        );

        assert_eq!(
            ParsedEqname::from_str(""),
            Err(NameError::new(TargetNameType::Eqname, 0))
        );
        assert_eq!(
            ParsedEqname::from_str("foo::bar"),
            Err(NameError::new(TargetNameType::Eqname, 3))
        );
        assert_eq!(
            ParsedEqname::from_str("Q{foo}:bar"),
            Err(NameError::new(TargetNameType::Eqname, 1))
        );
        assert_eq!(
            ParsedEqname::from_str("Q{foo}bar:baz"),
            Err(NameError::new(TargetNameType::Eqname, 9))
        );
    }

    #[test]
    fn parsed_eqname_namespace() {
        assert_eq!(parsed_eqname("local").namespace(), EqnameNamespace::None);

        assert_eq!(
            parsed_eqname("foo:bar").namespace(),
            EqnameNamespace::Prefix(ncname("foo"))
        );

        assert_eq!(
            parsed_eqname("Q{}foo").namespace(),
            EqnameNamespace::Uri("")
        );
        assert_eq!(
            parsed_eqname("Q{foo}bar").namespace(),
            EqnameNamespace::Uri("foo")
        );
    }

    #[test]
    fn parsed_uri_qualified_name_local_name() {
        assert_eq!(parsed_eqname("local").local_name(), ncname("local"));
        assert_eq!(parsed_eqname("foo:bar").local_name(), ncname("bar"));
        assert_eq!(parsed_eqname("Q{}foo").local_name(), ncname("foo"));
        assert_eq!(parsed_eqname("Q{foo}bar").local_name(), ncname("bar"));
    }

    #[test]
    fn parsed_eqname_namespace_and_local() {
        assert_eq!(
            parsed_eqname("local").namespace_and_local(),
            (EqnameNamespace::None, ncname("local"))
        );
        assert_eq!(
            parsed_eqname("foo:bar").namespace_and_local(),
            (EqnameNamespace::Prefix(ncname("foo")), ncname("bar"))
        );
        assert_eq!(
            parsed_eqname("Q{}foo").namespace_and_local(),
            (EqnameNamespace::Uri(""), ncname("foo"))
        );
        assert_eq!(
            parsed_eqname("Q{foo}bar").namespace_and_local(),
            (EqnameNamespace::Uri("foo"), ncname("bar"))
        );
    }
}
