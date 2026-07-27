//! The WebAssembly text format dialect.

use std::borrow::Cow;

use crate::sax::{BytesLit, Token};
use crate::text::{Dialect, Error, ErrorKind, Parser, parse};

/// The lexical layer of the WebAssembly text format.
///
/// This dialect covers WAT's *tokens*, which is what a SAX boundary needs: it
/// does not know that `module` introduces a module or that `(func …)` folds.
/// Three differences from [`Pose`](super::Pose) drive the whole design of this
/// crate:
///
/// - trivia includes `;;` line comments and nested `(; … ;)` block comments;
/// - a token is a run of WAT id-characters, so `$name`, `i32.add`, and `0x1p3`
///   are all single atoms;
/// - a string literal denotes *bytes*, not text, because `\hh` can encode any
///   byte. Strings therefore arrive as [`Token::Bytes`], which a destination
///   type opts into by overriding [`FromToken::from_bytes`].
///
/// `inf`, `nan`, and `nan:0x…` are reported as numbers. WAT resolves those
/// spellings by context, and no WAT keyword shares them.
///
/// [`FromToken::from_bytes`]: crate::sax::FromToken::from_bytes
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Wat;

/// Parses `input` as WAT text into a lazy SAX event stream.
#[must_use]
pub fn parse_wat(input: &str) -> Parser<'_, Wat> {
    parse(input, Wat)
}

impl Dialect for Wat {
    fn skip_trivia(&self, input: &str, from: usize) -> Result<usize, Error> {
        let bytes = input.as_bytes();
        let mut offset = from;
        loop {
            while matches!(bytes.get(offset), Some(byte) if is_whitespace(*byte)) {
                offset += 1;
            }
            if input[offset..].starts_with(";;") {
                offset += input[offset..].find('\n').unwrap_or(input.len() - offset);
            } else if input[offset..].starts_with("(;") {
                offset = skip_block_comment(input, offset)?;
            } else {
                return Ok(offset);
            }
        }
    }

    fn scan_atom<'a>(&self, input: &'a str, from: usize) -> Result<(Token<'a>, usize), Error> {
        if input.as_bytes()[from] == b'"' {
            return scan_string(input, from);
        }

        let end = input[from..]
            .bytes()
            .position(|byte| !is_id_char(byte))
            .map_or(input.len(), |offset| from + offset);
        if end == from {
            // A byte that starts no token at all, such as a lone `;`.
            return Err(Error::new(from, ErrorKind::InvalidSymbol));
        }

        let text = &input[from..end];
        let token = if is_number(text) {
            Token::Number(text)
        } else {
            Token::Symbol(text)
        };
        Ok((token, end))
    }
}

const fn is_whitespace(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\r')
}

/// The WAT `idchar` set, which covers keywords, `$`-identifiers, and reserved
/// tokens alike.
const fn is_id_char(byte: u8) -> bool {
    byte.is_ascii_alphanumeric()
        || matches!(
            byte,
            b'!' | b'#'
                | b'$'
                | b'%'
                | b'&'
                | b'\''
                | b'*'
                | b'+'
                | b'-'
                | b'.'
                | b'/'
                | b':'
                | b'<'
                | b'='
                | b'>'
                | b'?'
                | b'@'
                | b'\\'
                | b'^'
                | b'_'
                | b'`'
                | b'|'
                | b'~'
        )
}

/// Skips a `(; … ;)` comment, which nests.
///
/// Scanning byte-wise is safe because every delimiter byte is ASCII and no
/// UTF-8 continuation byte can equal one.
fn skip_block_comment(input: &str, from: usize) -> Result<usize, Error> {
    let bytes = input.as_bytes();
    // The caller has already matched the opening `(;`, so the depth cannot
    // reach zero before the loop decrements it.
    let mut depth = 1usize;
    let mut index = from + 2;

    while index < bytes.len() {
        if bytes[index] == b'(' && bytes.get(index + 1) == Some(&b';') {
            depth += 1;
            index += 2;
        } else if bytes[index] == b';' && bytes.get(index + 1) == Some(&b')') {
            depth -= 1;
            index += 2;
            if depth == 0 {
                return Ok(index);
            }
        } else {
            index += 1;
        }
    }

    Err(Error::new(from, ErrorKind::UnterminatedComment))
}

/// Scans a WAT string literal, which denotes a byte sequence.
fn scan_string(input: &str, from: usize) -> Result<(Token<'_>, usize), Error> {
    let bytes = input.as_bytes();
    let start = from + 1;
    let mut index = start;
    let mut decoded: Option<Vec<u8>> = None;

    while index < bytes.len() {
        match bytes[index] {
            b'"' => {
                let raw = &input[start..index];
                let value = decoded.map_or(Cow::Borrowed(raw.as_bytes()), Cow::Owned);
                return Ok((Token::Bytes(BytesLit::new(raw, value)), index + 1));
            }
            b'\\' => {
                let output = decoded.get_or_insert_with(|| input.as_bytes()[start..index].to_vec());
                index = scan_escape(input, index, output)?;
            }
            // `stringchar` excludes the control characters and DEL, which must
            // be written as escapes. A continuation byte is always >= 0x80, so
            // testing bytes cannot misjudge a multibyte character.
            byte if byte < 0x20 || byte == 0x7f => {
                return Err(Error::new(index, ErrorKind::InvalidCharacter));
            }
            byte => {
                if let Some(output) = &mut decoded {
                    output.push(byte);
                }
                index += 1;
            }
        }
    }

    Err(Error::new(from, ErrorKind::UnterminatedLiteral))
}

/// Decodes the escape starting at the backslash `index`, returning the offset
/// just past it.
fn scan_escape(input: &str, index: usize, output: &mut Vec<u8>) -> Result<usize, Error> {
    let bytes = input.as_bytes();
    let invalid = || Error::new(index, ErrorKind::InvalidEscape);

    let byte = match bytes.get(index + 1) {
        Some(byte) => *byte,
        // Let the caller's loop end and report the unterminated literal.
        None => return Ok(input.len()),
    };

    let simple = match byte {
        b't' => Some(b'\t'),
        b'n' => Some(b'\n'),
        b'r' => Some(b'\r'),
        b'"' => Some(b'"'),
        b'\'' => Some(b'\''),
        b'\\' => Some(b'\\'),
        _ => None,
    };
    if let Some(byte) = simple {
        output.push(byte);
        return Ok(index + 2);
    }

    if byte == b'u' {
        return scan_unicode_escape(input, index, output);
    }

    // `\hh`: two hex digits denoting one raw byte.
    let Some(low) = bytes.get(index + 2) else {
        // Truncated by end of input rather than misspelled; let the caller's
        // loop end and report the unterminated literal.
        return Ok(input.len());
    };
    let (Some(high), Some(low)) = ((byte as char).to_digit(16), (*low as char).to_digit(16)) else {
        return Err(invalid());
    };
    let value = u8::try_from(high * 16 + low).expect("two hex digits fit in a byte");
    output.push(value);
    Ok(index + 3)
}

/// Decodes `\u{…}` into the UTF-8 encoding of one scalar value.
///
/// The braced body is a `hexnum`, so it admits `_` between digits. Digits are
/// consumed one at a time rather than by searching for the closing brace, so
/// the scan cannot run past the end of the literal.
fn scan_unicode_escape(input: &str, index: usize, output: &mut Vec<u8>) -> Result<usize, Error> {
    let invalid = || Error::new(index, ErrorKind::InvalidEscape);
    let Some(rest) = input.get(index + 2..).filter(|rest| !rest.is_empty()) else {
        // Truncated by end of input; the caller reports the open literal.
        return Ok(input.len());
    };
    let body = rest.strip_prefix('{').ok_or_else(invalid)?;

    let mut value: u32 = 0;
    let mut digits = 0usize;
    let mut consumed = 0usize;
    let mut after_separator = false;

    for byte in body.bytes() {
        consumed += 1;
        match byte {
            b'}' if digits > 0 && !after_separator => {
                let character = char::from_u32(value).ok_or_else(invalid)?;
                let mut buffer = [0u8; 4];
                output.extend_from_slice(character.encode_utf8(&mut buffer).as_bytes());
                // `\u{` precedes the body, whose last byte is the `}`.
                return Ok(index + 3 + consumed);
            }
            b'_' if digits > 0 && !after_separator => after_separator = true,
            _ => {
                let digit = (byte as char).to_digit(16).ok_or_else(invalid)?;
                value = value
                    .checked_mul(16)
                    .and_then(|value| value.checked_add(digit))
                    .ok_or_else(invalid)?;
                digits += 1;
                after_separator = false;
            }
        }
    }

    // `body` runs to the end of the input, so exhausting it without a closing
    // brace means truncation rather than a misspelling.
    Ok(input.len())
}

/// Recognises the WAT numeric literals `uN`, `sN`, and `fN`.
fn is_number(text: &str) -> bool {
    let body = text.strip_prefix(['+', '-']).unwrap_or(text);
    if body == "inf" || body == "nan" {
        return true;
    }
    if let Some(hex) = body.strip_prefix("nan:0x") {
        return take_digits(hex.as_bytes(), 0, true) == Some(hex.len());
    }

    let (digits, hex) = body
        .strip_prefix("0x")
        .map_or((body, false), |rest| (rest, true));
    let bytes = digits.as_bytes();
    let Some(mut index) = take_digits(bytes, 0, hex) else {
        return false;
    };

    // WAT permits a trailing point with no fractional digits.
    if bytes.get(index) == Some(&b'.') {
        index += 1;
        if let Some(end) = take_digits(bytes, index, hex) {
            index = end;
        }
    }

    let (lower, upper) = if hex { (b'p', b'P') } else { (b'e', b'E') };
    if matches!(bytes.get(index), Some(byte) if *byte == lower || *byte == upper) {
        index += 1;
        if matches!(bytes.get(index), Some(b'+' | b'-')) {
            index += 1;
        }
        // An exponent is always decimal, even for a hexadecimal significand.
        let Some(end) = take_digits(bytes, index, false) else {
            return false;
        };
        index = end;
    }

    index == bytes.len()
}

/// Consumes one or more digits, allowing `_` only between two of them.
fn take_digits(bytes: &[u8], from: usize, hex: bool) -> Option<usize> {
    let is_digit = |byte: u8| {
        if hex {
            byte.is_ascii_hexdigit()
        } else {
            byte.is_ascii_digit()
        }
    };
    if !matches!(bytes.get(from), Some(byte) if is_digit(*byte)) {
        return None;
    }

    let mut index = from + 1;
    loop {
        match bytes.get(index) {
            Some(byte) if is_digit(*byte) => index += 1,
            Some(b'_') if matches!(bytes.get(index + 1), Some(byte) if is_digit(*byte)) => {
                index += 2;
            }
            _ => return Some(index),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Wat, is_number, parse_wat};
    use crate::sax::{Atom, Event, Production, Token};
    use crate::text::{ErrorKind, ReadError, read};
    use crate::{SExpr, Symbol};

    fn productions(input: &str) -> Vec<Production> {
        parse_wat(input)
            .filter_map(|event| match event.expect("valid input") {
                Event::Atom(token) => Some(token.production()),
                _ => None,
            })
            .collect()
    }

    fn error(input: &str) -> ErrorKind {
        parse_wat(input)
            .find_map(Result::err)
            .expect("an error")
            .kind()
    }

    fn bytes(input: &str) -> Vec<u8> {
        parse_wat(input)
            .find_map(|event| match event.expect("valid input") {
                Event::Atom(Token::Bytes(literal)) => Some(literal.into_value().into_owned()),
                _ => None,
            })
            .expect("a byte literal")
    }

    #[test]
    fn identifiers_keywords_and_numbers_are_separate_productions() {
        assert_eq!(
            productions("(func $add (param i32) (i32.add 1 0x2p3))"),
            [
                Production::Symbol, // func
                Production::Symbol, // $add
                Production::Symbol, // param
                Production::Symbol, // i32
                Production::Symbol, // i32.add
                Production::Number, // 1
                Production::Number, // 0x2p3
            ]
        );
    }

    #[test]
    fn numeric_literals_follow_the_wat_grammar() {
        for valid in [
            "0",
            "1_000",
            "-42",
            "+7",
            "0x1f",
            "0xdead_beef",
            "1.",
            "1.5",
            "1e10",
            "1E-3",
            "0x1p3",
            "0x1.8p-2",
            "inf",
            "-inf",
            "nan",
            "nan:0x400000",
        ] {
            assert!(is_number(valid), "{valid} should be a number");
        }
        for invalid in ["", "_1", "1_", "0x", "1e", "$1", "i32", "nan:0x", "0b1"] {
            assert!(!is_number(invalid), "{invalid} should not be a number");
        }
    }

    #[test]
    fn line_and_nested_block_comments_are_trivia() {
        assert_eq!(
            productions(";; leading\n(a (; inner (; nested ;) still ;) b)"),
            [Production::Symbol, Production::Symbol]
        );
        assert_eq!(error("(; unterminated"), ErrorKind::UnterminatedComment);
    }

    #[test]
    fn a_lone_semicolon_starts_no_token() {
        assert_eq!(error("(a ; b)"), ErrorKind::InvalidSymbol);
    }

    #[test]
    fn strings_denote_bytes_and_decode_every_escape_form() {
        assert_eq!(bytes(r#""plain""#), b"plain");
        assert_eq!(bytes(r#""tab\tquote\"slash\\""#), b"tab\tquote\"slash\\");
        // `\hh` can produce bytes that are not valid UTF-8 on their own.
        assert_eq!(bytes(r#""\00\ff""#), [0x00, 0xff]);
        assert_eq!(bytes(r#""\u{41}\u{1f600}""#), "A\u{1f600}".as_bytes());
    }

    #[test]
    fn string_errors_name_their_cause() {
        assert_eq!(error(r#""unterminated"#), ErrorKind::UnterminatedLiteral);
        assert_eq!(error(r#""\q""#), ErrorKind::InvalidEscape);
        assert_eq!(error(r#""\u{}""#), ErrorKind::InvalidEscape);
        assert_eq!(error(r#""\u{d800}""#), ErrorKind::InvalidEscape);
        assert_eq!(error(r#""\f""#), ErrorKind::InvalidEscape);
    }

    #[test]
    fn byte_strings_reach_a_type_that_opts_into_them() {
        let tree: SExpr<Atom> = read(r#"(data "\00")"#, Wat).expect("valid input");
        assert_eq!(
            tree,
            SExpr::list(vec![
                SExpr::atom(Atom::Symbol(Symbol::new("data"))),
                SExpr::atom(Atom::Bytes(vec![0x00])),
            ])
        );
    }

    #[test]
    fn a_type_without_byte_support_rejects_the_production() {
        // `Symbol` never overrides `from_bytes`, so the provided method runs.
        let error = read::<Symbol, _>(r#"(data "x")"#, Wat).expect_err("bytes are unsupported");
        match &error {
            ReadError::Token { offset, error } => {
                assert_eq!(*offset, 6);
                assert_eq!(error.production(), Production::Bytes);
            }
            other => panic!("expected a token error, got {other:?}"),
        }
        assert_eq!(error.to_string(), "unsupported bytes atom at byte 6");
    }

    #[test]
    fn unicode_escapes_respect_scalar_value_bounds() {
        assert_eq!(bytes(r#""\u{10ffff}""#), "\u{10ffff}".as_bytes());
        // Above the scalar range, and inside the surrogate range.
        assert_eq!(error(r#""\u{110000}""#), ErrorKind::InvalidEscape);
        assert_eq!(error(r#""\u{dfff}""#), ErrorKind::InvalidEscape);
        // A brace that never closes cannot silently span the literal.
        assert_eq!(error(r#""\u{1""#), ErrorKind::InvalidEscape);
    }

    #[test]
    fn control_characters_must_be_written_as_escapes() {
        // `stringchar` excludes everything below U+20, plus DEL.
        assert_eq!(error("\"a\nb\""), ErrorKind::InvalidCharacter);
        assert_eq!(error("\"a\tb\""), ErrorKind::InvalidCharacter);
        assert_eq!(error("\"a\u{7f}b\""), ErrorKind::InvalidCharacter);
        // The escaped spellings of the same bytes stay legal.
        assert_eq!(bytes(r#""a\nb""#), b"a\nb");
        // Multibyte text is unaffected: continuation bytes are all >= 0x80.
        assert_eq!(bytes("\"caf\u{e9}\""), "caf\u{e9}".as_bytes());
    }

    #[test]
    fn unicode_escapes_accept_hexnum_separators() {
        // The braced body is a `hexnum`, which allows `_` between digits.
        assert_eq!(bytes(r#""\u{1_f600}""#), "\u{1f600}".as_bytes());
        // ...but only between them.
        assert_eq!(error(r#""\u{_1}""#), ErrorKind::InvalidEscape);
        assert_eq!(error(r#""\u{1_}""#), ErrorKind::InvalidEscape);
        assert_eq!(error(r#""\u{1__2}""#), ErrorKind::InvalidEscape);
        // An overlong body overflows rather than wrapping.
        assert_eq!(error(r#""\u{ffffffffff}""#), ErrorKind::InvalidEscape);
    }

    #[test]
    fn an_escape_truncated_by_end_of_input_is_an_unterminated_literal() {
        for truncated in ["\"a\\", "\"a\\1", "\"a\\u", "\"a\\u{4"] {
            assert_eq!(
                error(truncated),
                ErrorKind::UnterminatedLiteral,
                "{truncated:?}"
            );
        }
    }
}
