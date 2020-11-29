//! Name error.

use core::fmt;

/// Name error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NameError {
    /// Target type.
    target: TargetNameType,
    /// The position of the first byte an error part starts.
    valid_up_to: usize,
}

impl NameError {
    /// Creates a new `NameError`.
    #[inline]
    #[must_use]
    pub(super) fn new(target: TargetNameType, valid_up_to: usize) -> Self {
        Self {
            target,
            valid_up_to,
        }
    }

    /// Returns the index in the given string up to which valid name was verified.
    ///
    /// Note that `&source_str[..err.valid_up_to()]` might be invalid when `valid_up_to` is zero.
    /// In other words, it depends on target type whether the empty string is valid or not.
    /// This error type does not assume anything about it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xml_string::names::NameError;
    /// use xml_string::names::Ncname;
    ///
    /// let err_nonempty = Ncname::from_str("foo:bar").expect_err("NCName cannot have a colon");
    /// assert_eq!(err_nonempty.valid_up_to(), 3);
    /// assert!(Ncname::from_str("foo").is_ok());
    ///
    /// let err_empty = Ncname::from_str("").expect_err("NCName cannot be empty");
    /// assert_eq!(err_empty.valid_up_to(), 0);
    /// assert!(
    ///     Ncname::from_str("").is_err(),
    ///     "Note that `&s[..err.valid_up_to()]` is not always valid for the empty source string"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn valid_up_to(&self) -> usize {
        self.valid_up_to
    }
}

impl fmt::Display for NameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Failed to parse the string as {}: invalid from {} bytes",
            self.target.name(),
            self.valid_up_to
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for NameError {}

/// Target name type of a conversion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(super) enum TargetNameType {
    /// [`Name`].
    ///
    /// [`Name`]: https://www.w3.org/TR/REC-xml/#NT-Name
    Name,
    /// [`NCName`].
    ///
    /// [`NCName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-NCName
    Ncname,
    /// [`Nmtoken`].
    ///
    /// [`Nmtoken`]: https://www.w3.org/TR/REC-xml/#NT-Nmtoken
    Nmtoken,
    /// [`QName`].
    ///
    /// [`QName`]: https://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-QName
    Qname,
    /// [`URIQualifiedName`].
    ///
    /// [`URIQualifiedName`]:
    ///     https://www.w3.org/TR/2017/REC-xpath-31-20170321/#prod-xpath31-URIQualifiedName
    UriQualifiedName,
}

impl TargetNameType {
    /// Returns the target name type name.
    fn name(self) -> &'static str {
        match self {
            Self::Name => "Name",
            Self::Ncname => "NCName",
            Self::Nmtoken => "Nmtoken",
            Self::Qname => "QName",
            Self::UriQualifiedName => "URIQualifiedName",
        }
    }
}
