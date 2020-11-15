//! Utilities for characters.

/// A type for name char validity flags.
type ValidityFlags = u8;
/// Mask for `Name` start char.
const FLAG_NAME_START: ValidityFlags = 1 << 0;
/// Mask for `Name` continue char.
const FLAG_NAME_CONTINUE: ValidityFlags = 1 << 1;
/// Mask for `NCName` start char.
const FLAG_NCNAME_START: ValidityFlags = 1 << 2;
/// Mask for `NCName` continue char.
const FLAG_NCNAME_CONTINUE: ValidityFlags = 1 << 3;
/// Validity flags for ASCII chars.
const NAME_CHAR_VALIDITY: [ValidityFlags; 128] = [
    0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, //< 0x00
    0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, //< 0x08
    0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, //< 0x10
    0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, //< 0x18
    0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, //< 0x20
    0b0000, 0b0000, 0b0000, 0b0000, 0b0000, 0b1010, 0b1010, 0b0000, //< 0x28
    0b1010, 0b1010, 0b1010, 0b1010, 0b1010, 0b1010, 0b1010, 0b1010, //< 0x30
    0b1010, 0b1010, 0b0011, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, //< 0x38
    0b0000, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, //< 0x40
    0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, //< 0x48
    0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, //< 0x50
    0b1111, 0b1111, 0b1111, 0b0000, 0b0000, 0b0000, 0b0000, 0b1111, //< 0x58
    0b0000, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, //< 0x60
    0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, //< 0x68
    0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, 0b1111, //< 0x70
    0b1111, 0b1111, 0b1111, 0b0000, 0b0000, 0b0000, 0b0000, 0b0000, //< 0x78
];
/// A mask to get an index of `NAME_CHAR_VALIDITY` from an ASCII character.
const ASCII_INDEX_MASK: usize = 0x7f;

/// Checks whether the given ASCII character is [`NameStartChar`].
///
/// [`NameStartChar`]: https://www.w3.org/TR/REC-xml/#NT-NameStartChar
#[must_use]
fn is_name_start_ascii(c: char) -> bool {
    NAME_CHAR_VALIDITY[(c as usize) & ASCII_INDEX_MASK] & FLAG_NAME_START != 0
}

/// Checks whether the given ASCII character is [`NameChar`].
///
/// [`NameChar`]: https://www.w3.org/TR/REC-xml/#NT-NameChar
#[must_use]
fn is_name_continue_ascii(c: char) -> bool {
    NAME_CHAR_VALIDITY[(c as usize) & ASCII_INDEX_MASK] & FLAG_NAME_CONTINUE != 0
}

/// Checks whether the given ASCII character is the start character of [`NCName`].
///
/// [`NCName`]: https://www.w3.org/TR/REC-xml-names/#NT-NCName
#[must_use]
fn is_ncname_start_ascii(c: char) -> bool {
    NAME_CHAR_VALIDITY[(c as usize) & ASCII_INDEX_MASK] & FLAG_NCNAME_START != 0
}

/// Checks whether the given ASCII character is the continuing character of [`NCName`].
///
/// [`NCName`]: https://www.w3.org/TR/REC-xml-names/#NT-NCName
#[must_use]
fn is_ncname_continue_ascii(c: char) -> bool {
    NAME_CHAR_VALIDITY[(c as usize) & ASCII_INDEX_MASK] & FLAG_NCNAME_CONTINUE != 0
}

/// Checks whether the given non-ASCII character is [`NameStartChar`].
///
/// [`NameStartChar`]: https://www.w3.org/TR/REC-xml/#NT-NameStartChar
fn is_name_start_nonascii(c: char) -> bool {
    matches!(c,
        '\u{C0}'..='\u{D6}'
        | '\u{D8}'..='\u{F6}'
        | '\u{F8}'..='\u{2FF}'
        | '\u{370}'..='\u{37D}'
        | '\u{37F}'..='\u{1FFF}'
        | '\u{200C}'..='\u{200D}'
        | '\u{2070}'..='\u{218F}'
        | '\u{2C00}'..='\u{2FEF}'
        | '\u{3001}'..='\u{D7FF}'
        | '\u{F900}'..='\u{FDCF}'
        | '\u{FDF0}'..='\u{FFFD}'
        | '\u{10000}'..='\u{EFFFF}')
}

/// Checks whether the given non-ASCII character is [`NameChar`].
///
/// [`NameChar`]: https://www.w3.org/TR/REC-xml/#NT-NameChar
fn is_name_continue_nonascii(c: char) -> bool {
    matches!(c,
        '\u{B7}'
        | '\u{C0}'..='\u{D6}'
        | '\u{D8}'..='\u{F6}'
        | '\u{F8}'..='\u{37D}'
        | '\u{37F}'..='\u{1FFF}'
        | '\u{200C}'..='\u{200D}'
        | '\u{203F}'..='\u{2040}'
        | '\u{2070}'..='\u{218F}'
        | '\u{2C00}'..='\u{2FEF}'
        | '\u{3001}'..='\u{D7FF}'
        | '\u{F900}'..='\u{FDCF}'
        | '\u{FDF0}'..='\u{FFFD}'
        | '\u{10000}'..='\u{EFFFF}')
}

/// Checks whether the given character is [`NameStartChar`].
///
/// [`NameStartChar`]: https://www.w3.org/TR/REC-xml/#NT-NameStartChar
pub(super) fn is_name_start(c: char) -> bool {
    if c.is_ascii() {
        is_name_start_ascii(c)
    } else {
        is_name_start_nonascii(c)
    }
}

/// Checks whether the given character is [`NameChar`].
///
/// [`NameChar`]: https://www.w3.org/TR/REC-xml/#NT-NameChar
#[must_use]
pub(super) fn is_name_continue(c: char) -> bool {
    if c.is_ascii() {
        is_name_continue_ascii(c)
    } else {
        is_name_continue_nonascii(c)
    }
}

/// Checks whether the given character is the start character of [`NCName`].
///
/// [`NCName`]: https://www.w3.org/TR/REC-xml-names/#NT-NCName
#[must_use]
pub(super) fn is_ncname_start(c: char) -> bool {
    if c.is_ascii() {
        is_ncname_start_ascii(c)
    } else {
        is_name_start_nonascii(c)
    }
}

/// Checks whether the given character is the continuing character of [`NCName`].
///
/// [`NCName`]: https://www.w3.org/TR/REC-xml-names/#NT-NCName
#[must_use]
pub(super) fn is_ncname_continue(c: char) -> bool {
    if c.is_ascii() {
        is_ncname_continue_ascii(c)
    } else {
        is_name_continue_nonascii(c)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_name_start_ascii_spec(c: char) -> bool {
        matches!(c, ':' | 'A'..='Z' | '_' | 'a'..='z')
    }

    fn is_name_continue_ascii_spec(c: char) -> bool {
        matches!(c, ':' | 'A'..='Z' | '_' | 'a'..='z' | '-' | '.' | '0'..='9')
    }

    #[test]
    fn name_start_ascii() {
        for i in 0_u8..127 {
            let c = i as char;
            assert_eq!(
                is_name_start_ascii(c),
                is_name_start_ascii_spec(c),
                "test failed for {:?}",
                c
            );
        }
    }

    #[test]
    fn name_continue_ascii() {
        for i in 0_u8..127 {
            let c = i as char;
            assert_eq!(
                is_name_continue_ascii(c),
                is_name_continue_ascii_spec(c),
                "test failed for {:?}",
                c
            );
        }
    }

    #[test]
    fn ncname_start_ascii() {
        for i in 0_u8..127 {
            let c = i as char;
            assert_eq!(
                is_ncname_start_ascii(c),
                is_name_start_ascii_spec(c) && (c != ':'),
                "test failed for {:?}",
                c
            );
        }
    }

    #[test]
    fn ncname_continue_ascii() {
        for i in 0_u8..127 {
            let c = i as char;
            assert_eq!(
                is_ncname_continue_ascii(c),
                is_name_continue_ascii_spec(c) && (c != ':'),
                "test failed for {:?}",
                c
            );
        }
    }
}
