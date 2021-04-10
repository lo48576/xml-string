# Change Log

## [Unreleased]

* [`EQName`](https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-EQName)
  support is added.
* `len` methods are added to string types.

### Added
* [`EQName`](https://www.w3.org/TR/2017/REC-xpath-31-20170321/#doc-xpath31-EQName)
  support is added.
    + This would be useful for XPath processors.
* `len` methods are added to string types.
    * `is_empty()` is not added since they are obviously non-empty string.
      Users should be aware they will never be empty, before checking if they are empty.

## [0.0.1]

Initial release.

Supported string types are:

* `names::Name`,
* `names::Ncname`,
* `names::Qname`, `names::ParsedQname`,
* `names::UriQualifiedName`, `names::ParsedUriQualifiedName`, and
* `names::Nmtoken`.

[Unreleased]: <https://gitlab.com/lo48576/xml-string/-/compare/v0.0.1...develop>
[0.0.1]: <https://gitlab.com/lo48576/xml-string/-/releases/v0.0.1>
