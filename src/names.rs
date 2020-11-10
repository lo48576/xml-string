//! Name types.

mod chars;
mod error;
mod name;
mod ncname;

pub use self::error::NameError;
pub use self::name::NameStr;
pub use self::ncname::NcnameStr;
