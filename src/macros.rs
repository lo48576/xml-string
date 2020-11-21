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

macro_rules! impl_traits_for_custom_string_slice {
    ($custom_str:ty) => {
        impl_cmp_symmetric!($custom_str, str);
        impl_cmp_symmetric!($custom_str, &'_ str);
        impl_cmp_symmetric!(&'_ $custom_str, str);

        #[cfg(feature = "alloc")]
        impl_cmp_symmetric!($custom_str, $crate::alloc::string::String);
        #[cfg(feature = "alloc")]
        impl_cmp_symmetric!($custom_str, &$crate::alloc::string::String);
        #[cfg(feature = "alloc")]
        impl_cmp_symmetric!($custom_str, $crate::alloc::boxed::Box<str>);
        #[cfg(feature = "alloc")]
        impl_cmp_symmetric!($crate::alloc::boxed::Box<$custom_str>, str);
        #[cfg(feature = "alloc")]
        impl_cmp_symmetric!($custom_str, $crate::alloc::borrow::Cow<'_, str>);

        impl AsRef<str> for $custom_str {
            #[inline]
            fn as_ref(&self) -> &str {
                &self.0
            }
        }

        #[cfg(feature = "alloc")]
        impl AsRef<str> for $crate::alloc::boxed::Box<$custom_str> {
            #[inline]
            fn as_ref(&self) -> &str {
                &(**self).0
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
    };
}
