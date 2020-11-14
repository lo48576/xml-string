//! Name types.

mod chars;
mod error;
mod name;
mod ncname;
mod nmtoken;
mod qname;

pub use self::error::NameError;
pub use self::name::NameStr;
pub use self::ncname::NcnameStr;
pub use self::nmtoken::NmtokenStr;
pub use self::qname::QnameStr;
