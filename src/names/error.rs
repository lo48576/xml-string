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
}

impl TargetNameType {
    /// Returns the target name type name.
    fn name(self) -> &'static str {
        match self {
            Self::Name => "Name",
            Self::Ncname => "NCName",
        }
    }
}
