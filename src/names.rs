//! Name types.

mod chars;
mod eqname;
mod error;
mod name;
mod ncname;
mod nmtoken;
mod qname;
mod uri_qualified_name;

pub use self::eqname::{Eqname, EqnameNamespace, EqnameVariantData, ParsedEqname};
pub use self::error::NameError;
pub use self::name::Name;
pub use self::ncname::Ncname;
pub use self::nmtoken::Nmtoken;
pub use self::qname::{ParsedQname, Qname};
pub use self::uri_qualified_name::{ParsedUriQualifiedName, UriQualifiedName};
