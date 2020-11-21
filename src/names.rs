//! Name types.

mod chars;
mod error;
mod name;
mod ncname;
mod nmtoken;
mod qname;

pub use self::error::NameError;
pub use self::name::Name;
pub use self::ncname::Ncname;
pub use self::nmtoken::Nmtoken;
pub use self::qname::{ParsedQname, Qname};
