//! Macros.

/// Implement `PartialEq` and `Eq` for the given types.
macro_rules! impl_cmp {
    ($ty_lhs:ty, $ty_rhs:ty) => {
        impl PartialEq<$ty_rhs> for $ty_lhs {
            #[inline]
            fn eq(&self, o: &$ty_rhs) -> bool {
                <str as PartialEq<str>>::eq(AsRef::as_ref(self), AsRef::as_ref(o))
            }
        }
        impl PartialOrd<$ty_rhs> for $ty_lhs {
            #[inline]
            fn partial_cmp(&self, o: &$ty_rhs) -> Option<core::cmp::Ordering> {
                <str as PartialOrd<str>>::partial_cmp(AsRef::as_ref(self), AsRef::as_ref(o))
            }
        }
    };
}

/// Implement `PartialEq` and `Eq` symmetrically for the given types.
macro_rules! impl_cmp_symmetric {
    ($ty_lhs:ty, $ty_rhs:ty) => {
        impl_cmp!($ty_lhs, $ty_rhs);
        impl_cmp!($ty_rhs, $ty_lhs);
    };
}

/// Implements std traits for a custom string slice type.
///
/// # Safety
///
/// `$custom_str` type should have the same memory layout as `str`.
/// For example, this is safe when `$custom_str` is defined as
/// `#[repr(transparent)] struct $custom_str(str);`.
/// The caller of this macro is responsible to satisfy this condition.
macro_rules! impl_traits_for_custom_string_slice {
    ($custom_str:ty) => {
        #[cfg(feature = "alloc")]
        impl alloc::borrow::ToOwned for $custom_str {
            type Owned = alloc::boxed::Box<$custom_str>;

            fn to_owned(&self) -> Self::Owned {
                From::from(self)
            }
        }

        impl_cmp_symmetric!($custom_str, str);
        impl_cmp_symmetric!($custom_str, &'_ str);
        impl_cmp_symmetric!(&'_ $custom_str, str);

        #[cfg(feature = "alloc")]
        impl_cmp_symmetric!($custom_str, alloc::string::String);
        #[cfg(feature = "alloc")]
        impl_cmp_symmetric!($custom_str, &alloc::string::String);
        #[cfg(feature = "alloc")]
        impl_cmp_symmetric!($custom_str, alloc::boxed::Box<str>);
        #[cfg(feature = "alloc")]
        impl_cmp_symmetric!(alloc::boxed::Box<$custom_str>, str);
        #[cfg(feature = "alloc")]
        impl_cmp_symmetric!($custom_str, alloc::borrow::Cow<'_, str>);

        impl AsRef<str> for $custom_str {
            #[inline]
            fn as_ref(&self) -> &str {
                &self.0
            }
        }

        #[cfg(feature = "alloc")]
        impl AsRef<str> for alloc::boxed::Box<$custom_str> {
            #[inline]
            fn as_ref(&self) -> &str {
                &(**self).0
            }
        }

        impl AsRef<$custom_str> for $custom_str {
            #[inline]
            fn as_ref(&self) -> &$custom_str {
                self
            }
        }

        impl core::fmt::Debug for &$custom_str {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(self.as_ref())
            }
        }

        impl core::fmt::Display for &$custom_str {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(self.as_ref())
            }
        }

        #[cfg(feature = "alloc")]
        impl From<&$custom_str> for alloc::boxed::Box<$custom_str> {
            fn from(s: &$custom_str) -> Self {
                use alloc::boxed::Box;

                let inner = s.as_str();
                let inner_boxed = Box::<str>::from(inner);
                unsafe {
                    // This is safe when `$custom_str` has the same memory layout as `str`.
                    // For example, this is safe when `$custom_str` is defined as
                    // `#[repr(transparent)] struct $custom_str(str);`.
                    // The caller of this macro is responsible to satisfy this condition.
                    Box::<$custom_str>::from_raw(
                        Box::<str>::into_raw(inner_boxed) as *mut $custom_str
                    )
                }
            }
        }

        #[cfg(feature = "alloc")]
        impl From<&$custom_str> for alloc::rc::Rc<$custom_str> {
            fn from(s: &$custom_str) -> Self {
                use alloc::rc::Rc;

                let inner = s.as_str();
                let inner_boxed = Rc::<str>::from(inner);
                unsafe {
                    // This is safe when `$custom_str` has the same memory layout as `str`.
                    // For example, this is safe when `$custom_str` is defined as
                    // `#[repr(transparent)] struct $custom_str(str);`.
                    // The caller of this macro is responsible to satisfy this condition.
                    Rc::<$custom_str>::from_raw(
                        Rc::<str>::into_raw(inner_boxed) as *const $custom_str
                    )
                }
            }
        }

        #[cfg(feature = "alloc")]
        impl From<&$custom_str> for alloc::sync::Arc<$custom_str> {
            fn from(s: &$custom_str) -> Self {
                use alloc::sync::Arc;

                let inner = s.as_str();
                let inner_boxed = Arc::<str>::from(inner);
                unsafe {
                    // This is safe when `$custom_str` has the same memory layout as `str`.
                    // For example, this is safe when `$custom_str` is defined as
                    // `#[repr(transparent)] struct $custom_str(str);`.
                    // The caller of this macro is responsible to satisfy this condition.
                    Arc::<$custom_str>::from_raw(
                        Arc::<str>::into_raw(inner_boxed) as *const $custom_str
                    )
                }
            }
        }
    };
}
