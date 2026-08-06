//! Column values, and the three ways this shell renders them.

use std::fmt::Write as _;

use covalence_lib_sqlite::types::ValueRef;

/// One column of one row, owned so that aligned modes can measure a whole
/// result before printing any of it.
#[derive(Clone, Debug, PartialEq)]
pub enum Cell {
    /// `SQL` `NULL`.
    Null,
    /// A 64-bit signed integer.
    Integer(i64),
    /// An IEEE-754 double.
    Real(f64),
    /// Text. Invalid UTF-8 is replaced, which upstream does not do.
    Text(String),
    /// A blob.
    Blob(Vec<u8>),
}

impl Cell {
    /// Captures a borrowed `SQLite` value.
    #[must_use]
    pub fn capture(value: ValueRef<'_>) -> Self {
        match value {
            ValueRef::Null => Self::Null,
            ValueRef::Integer(number) => Self::Integer(number),
            ValueRef::Real(number) => Self::Real(number),
            ValueRef::Text(bytes) => Self::Text(String::from_utf8_lossy(bytes).into_owned()),
            ValueRef::Blob(bytes) => Self::Blob(bytes.to_vec()),
        }
    }

    /// Whether this value should be right-aligned in an aligned mode.
    #[must_use]
    pub const fn is_numeric(&self) -> bool {
        matches!(self, Self::Integer(_) | Self::Real(_))
    }

    /// The plain rendering used by `list`, `column` and `box`.
    ///
    /// `null_text` is `.nullvalue`. Blobs render as an `SQL` blob literal
    /// rather than as raw bytes: upstream writes the bytes themselves, which
    /// is unreadable, ambiguous with text, and lets blob content inject
    /// terminal escapes.
    #[must_use]
    pub fn plain(&self, null_text: &str) -> String {
        match self {
            Self::Null => null_text.to_owned(),
            Self::Integer(number) => number.to_string(),
            Self::Real(number) => real(*number),
            Self::Text(text) => text.clone(),
            Self::Blob(bytes) => blob_literal(bytes),
        }
    }

    /// The `SQL` literal used by `quote` and by `.dump`.
    #[must_use]
    pub fn sql_literal(&self) -> String {
        match self {
            Self::Null => "NULL".to_owned(),
            Self::Integer(number) => number.to_string(),
            Self::Real(number) => real(*number),
            Self::Text(text) => quote_text(text),
            Self::Blob(bytes) => blob_literal(bytes),
        }
    }

    /// The JSON rendering used by `json`.
    #[must_use]
    pub fn json(&self) -> String {
        match self {
            Self::Null => "null".to_owned(),
            Self::Integer(number) => number.to_string(),
            Self::Real(number) => real(*number),
            Self::Text(text) => json_string(text),
            // Upstream renders a blob as a JSON string of `\u00XX` escapes,
            // one per byte. It is lossy in the same way there.
            Self::Blob(bytes) => {
                let mut out = String::with_capacity(bytes.len() * 6 + 2);
                out.push('"');
                for byte in bytes {
                    let _ = write!(out, "\\u{:04x}", u32::from(*byte));
                }
                out.push('"');
                out
            }
        }
    }
}

/// Renders a double the way `SQLite` does for the cases that matter.
///
/// `SQLite` prints a float that happens to be integral with a trailing `.0`,
/// and prints non-finite values as `Inf`, `-Inf` and `NaN` (the last of which
/// `SQLite` stores as `NULL`, so it should never arrive here).
fn real(number: f64) -> String {
    if number.is_nan() {
        return "NaN".to_owned();
    }
    if number.is_infinite() {
        return if number > 0.0 { "Inf" } else { "-Inf" }.to_owned();
    }
    let rendered = format!("{number}");
    if rendered
        .bytes()
        .all(|byte| byte.is_ascii_digit() || byte == b'-')
    {
        format!("{rendered}.0")
    } else {
        rendered
    }
}

/// `'text'`, with interior quotes doubled.
fn quote_text(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('\'');
    for character in text.chars() {
        if character == '\'' {
            out.push('\'');
        }
        out.push(character);
    }
    out.push('\'');
    out
}

/// `x'0011ff'`.
fn blob_literal(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2 + 3);
    out.push_str("x'");
    for byte in bytes {
        let _ = write!(out, "{byte:02x}");
    }
    out.push('\'');
    out
}

/// A JSON string literal.
fn json_string(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for character in text.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            control if control < ' ' => {
                let _ = write!(out, "\\u{:04x}", u32::from(control));
            }
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

/// Quotes an identifier for `.dump` and `.schema`, bare when it is safe.
pub(crate) fn quote_identifier(name: &str) -> String {
    let plain = !name.is_empty()
        && name
            .chars()
            .next()
            .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        && name
            .chars()
            .all(|character| character.is_ascii_alphanumeric() || character == '_');
    if plain {
        name.to_owned()
    } else {
        let mut out = String::with_capacity(name.len() + 2);
        out.push('"');
        for character in name.chars() {
            if character == '"' {
                out.push('"');
            }
            out.push(character);
        }
        out.push('"');
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The JSON form upstream uses for bytes: one `\\u00XX` per byte.
    fn hex_escapes(bytes: &[u8]) -> String {
        let mut out = String::from('"');
        for byte in bytes {
            let _ = write!(out, "\\u{:04x}", u32::from(*byte));
        }
        out.push('"');
        out
    }

    #[test]
    fn null_uses_the_configured_placeholder() {
        assert_eq!(Cell::Null.plain(""), "");
        assert_eq!(Cell::Null.plain("NIL"), "NIL");
        assert_eq!(Cell::Null.sql_literal(), "NULL");
        assert_eq!(Cell::Null.json(), "null");
    }

    #[test]
    fn integral_doubles_keep_a_decimal_point() {
        assert_eq!(Cell::Real(2.0).plain(""), "2.0");
        assert_eq!(Cell::Real(3.5).plain(""), "3.5");
        assert_eq!(Cell::Real(-4.0).plain(""), "-4.0");
        assert_eq!(Cell::Integer(2).plain(""), "2");
    }

    #[test]
    fn text_is_quoted_by_doubling() {
        assert_eq!(Cell::Text("it's".to_owned()).sql_literal(), "'it''s'");
        assert_eq!(Cell::Text("it's".to_owned()).plain(""), "it's");
    }

    #[test]
    fn blobs_render_as_literals_everywhere_but_json() {
        let blob = Cell::Blob(vec![0x00, 0xff, 0x41]);
        assert_eq!(blob.plain(""), "x'00ff41'");
        assert_eq!(blob.sql_literal(), "x'00ff41'");
        assert_eq!(blob.json(), hex_escapes(&[0x00, 0xff, 0x41]));
        assert_eq!(Cell::Blob(Vec::new()).sql_literal(), "x''");
    }

    #[test]
    fn json_escapes_control_characters() {
        assert_eq!(
            Cell::Text("a\"b\\c\nd".to_owned()).json(),
            r#""a\"b\\c\nd""#
        );
        assert_eq!(Cell::Text("\u{1}".to_owned()).json(), hex_escapes(&[0x01]));
        // Non-ASCII passes through as UTF-8, as upstream does.
        assert_eq!(Cell::Text("é".to_owned()).json(), "\"é\"");
    }

    #[test]
    fn identifiers_are_quoted_only_when_they_must_be() {
        assert_eq!(quote_identifier("value"), "value");
        assert_eq!(quote_identifier("_x1"), "_x1");
        assert_eq!(quote_identifier("two words"), "\"two words\"");
        assert_eq!(quote_identifier("1st"), "\"1st\"");
        assert_eq!(quote_identifier("a\"b"), "\"a\"\"b\"");
    }

    #[test]
    fn numeric_cells_are_the_ones_that_right_align() {
        assert!(Cell::Integer(1).is_numeric());
        assert!(Cell::Real(1.0).is_numeric());
        assert!(!Cell::Null.is_numeric());
        assert!(!Cell::Text(String::new()).is_numeric());
        assert!(!Cell::Blob(Vec::new()).is_numeric());
    }
}
