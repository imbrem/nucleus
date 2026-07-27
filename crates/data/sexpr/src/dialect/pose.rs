//! The POSE portable S-expression dialect.

use std::borrow::Cow;

use crate::sax::{StrLit, Token};
use crate::text::{Dialect, Error, ErrorKind, Parser, parse};

/// Portable S-expressions, as specified by the POSE project.
///
/// POSE is deliberately a least common denominator: lists, strings, numbers,
/// and symbols, with `;` line comments. It is the crate's reference dialect
/// because its grammar is small enough to implement exactly.
///
/// Three consequences of following that grammar are worth stating, because
/// each rejects input other Lisp readers accept:
///
/// - a symbol's letters are lowercase ASCII only, so `Foo` is not a symbol;
/// - numbers may not have a leading zero, so `01` is not a number;
/// - a string recognises only the escapes `\\` and `\"`.
///
/// Atoms end at whitespace, `(`, `)`, `;`, `"`, or end of input, so `a"b"`
/// holds two expressions.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pose;

/// Parses `input` as POSE text into a lazy SAX event stream.
#[must_use]
pub fn parse_pose(input: &str) -> Parser<'_, Pose> {
    parse(input, Pose)
}

impl Dialect for Pose {
    fn skip_trivia(&self, input: &str, from: usize) -> Result<usize, Error> {
        let bytes = input.as_bytes();
        let mut offset = from;
        loop {
            while matches!(bytes.get(offset), Some(byte) if is_whitespace(*byte)) {
                offset += 1;
            }
            if bytes.get(offset) == Some(&b';') {
                // `newline = CR | LF`, so either ends a comment. The newline
                // itself stays; the next pass skips it as whitespace.
                offset += input[offset..]
                    .find(['\r', '\n'])
                    .unwrap_or(input.len() - offset);
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
            .position(is_delimiter)
            .map_or(input.len(), |offset| from + offset);
        let text = &input[from..end];

        if is_number(text) {
            Ok((Token::Number(text), end))
        } else if is_symbol(text) {
            Ok((Token::Symbol(text), end))
        } else if looks_numeric(text) {
            Err(Error::new(from, ErrorKind::InvalidNumber))
        } else {
            Err(Error::new(from, ErrorKind::InvalidSymbol))
        }
    }
}

/// `whitespace = HT | VT | FF | space | CR | LF`.
///
/// This is narrower than [`u8::is_ascii_whitespace`], which omits VT, and much
/// narrower than Unicode whitespace.
const fn is_whitespace(byte: u8) -> bool {
    matches!(byte, b'\t' | 0x0B | 0x0C | b' ' | b'\r' | b'\n')
}

const fn is_delimiter(byte: u8) -> bool {
    is_whitespace(byte) || matches!(byte, b'(' | b')' | b';' | b'"')
}

const fn is_punct_first(byte: u8) -> bool {
    matches!(
        byte,
        b'!' | b'$' | b'&' | b'*' | b'+' | b'-' | b'/' | b'<' | b'=' | b'>' | b'_'
    )
}

const fn is_punct_cont(byte: u8) -> bool {
    is_punct_first(byte) || matches!(byte, b'.' | b'?' | b'@')
}

/// `number = integer fraction exponent`, with `integer = minus? digit |
/// minus? onenine digits`.
fn is_number(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut index = usize::from(bytes.first() == Some(&b'-'));

    // A leading zero terminates the integer part, which is what forbids the
    // octal-looking spellings POSE excludes.
    match bytes.get(index) {
        Some(b'0') => index += 1,
        Some(byte) if byte.is_ascii_digit() => index = take_digits(bytes, index),
        _ => return false,
    }

    if bytes.get(index) == Some(&b'.') {
        let digits = take_digits(bytes, index + 1);
        if digits == index + 1 {
            return false;
        }
        index = digits;
    }

    if matches!(bytes.get(index), Some(b'e' | b'E')) {
        index += 1;
        if matches!(bytes.get(index), Some(b'+' | b'-')) {
            index += 1;
        }
        let digits = take_digits(bytes, index);
        if digits == index {
            return false;
        }
        index = digits;
    }

    index == bytes.len()
}

fn take_digits(bytes: &[u8], mut index: usize) -> usize {
    while matches!(bytes.get(index), Some(byte) if byte.is_ascii_digit()) {
        index += 1;
    }
    index
}

/// `symbol = wordsym | signsym | colonsym`.
///
/// Every `signsym` is also a `wordsym`: both signs are in `punct-1st`, and
/// `wordsym-cont` is a superset of `signsym-2nd` and `signsym-cont`. Only the
/// union is checked here.
fn is_symbol(text: &str) -> bool {
    text.strip_prefix(':')
        .map_or_else(|| is_word_symbol(text), is_word_symbol)
}

fn is_word_symbol(text: &str) -> bool {
    let mut bytes = text.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    let first_ok = first.is_ascii_lowercase() || is_punct_first(first);
    first_ok
        && bytes
            .all(|byte| byte.is_ascii_lowercase() || is_punct_cont(byte) || byte.is_ascii_digit())
}

/// Whether a rejected atom was closer to a number than to a symbol, so the
/// error names the production the author was likely reaching for.
fn looks_numeric(text: &str) -> bool {
    let bytes = text.as_bytes();
    match bytes.first() {
        Some(byte) if byte.is_ascii_digit() => true,
        Some(b'-') => matches!(bytes.get(1), Some(byte) if byte.is_ascii_digit()),
        _ => false,
    }
}

/// `string = '"' string-char* '"'`, where the only escapes are `\\` and `\"`.
fn scan_string(input: &str, from: usize) -> Result<(Token<'_>, usize), Error> {
    let bytes = input.as_bytes();
    let start = from + 1;
    let mut index = start;
    let mut decoded: Option<String> = None;

    while index < bytes.len() {
        match bytes[index] {
            b'"' => {
                let raw = &input[start..index];
                let value = decoded.map_or(Cow::Borrowed(raw), Cow::Owned);
                return Ok((Token::String(StrLit::new(raw, value)), index + 1));
            }
            b'\\' => {
                let output = decoded.get_or_insert_with(|| input[start..index].to_owned());
                match bytes.get(index + 1) {
                    Some(b'\\') => output.push('\\'),
                    Some(b'"') => output.push('"'),
                    Some(_) => return Err(Error::new(index, ErrorKind::InvalidEscape)),
                    None => break,
                }
                index += 2;
            }
            _ => {
                let character = input[index..].chars().next().expect("UTF-8 boundary");
                if let Some(output) = &mut decoded {
                    output.push(character);
                }
                index += character.len_utf8();
            }
        }
    }

    Err(Error::new(from, ErrorKind::UnterminatedLiteral))
}

#[cfg(test)]
mod tests {
    use super::{Pose, is_number, is_symbol, parse_pose};
    use crate::sax::{Atom, Event, Production, Token};
    use crate::text::{ErrorKind, ReadError, read, read_all};
    use crate::{SExpr, Symbol};

    fn tokens(input: &str) -> Result<Vec<Event<Token<'_>>>, ErrorKind> {
        parse_pose(input)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| error.kind())
    }

    fn productions(input: &str) -> Vec<Production> {
        parse_pose(input)
            .filter_map(|event| match event.expect("valid input") {
                Event::Atom(token) => Some(token.production()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn each_atom_reports_its_own_production() {
        assert_eq!(
            productions(r#"(sym :key 42 -1.5e3 "text")"#),
            [
                Production::Symbol,
                Production::Symbol,
                Production::Number,
                Production::Number,
                Production::String,
            ]
        );
    }

    #[test]
    fn numbers_follow_the_json_like_integer_rule() {
        for valid in [
            "0", "-0", "5", "50", "-42", "1.5", "0.5", "1e3", "1E+3", "-1.5e-3",
        ] {
            assert!(is_number(valid), "{valid} should be a number");
        }
        // Leading zeros, bare fractions, and empty exponents are all excluded.
        for invalid in [
            "01", "00", "-01", "1.", ".5", "1e", "1e+", "+5", "1_000", "",
        ] {
            assert!(!is_number(invalid), "{invalid} should not be a number");
        }
    }

    #[test]
    fn symbols_are_lowercase_ascii_with_a_fixed_punctuation_set() {
        for valid in [
            "foo", "-", "+", "->", "a1", "a.b", "a?", "a@", ":key", "_x", "+5",
        ] {
            assert!(is_symbol(valid), "{valid} should be a symbol");
        }
        // Uppercase is not a POSE letter, and `.`/`?`/`@` cannot lead.
        for invalid in ["Foo", "aB", ".a", "?a", "@a", ":", "::a", "1a", "", "é"] {
            assert!(!is_symbol(invalid), "{invalid} should not be a symbol");
        }
    }

    #[test]
    fn an_atom_that_is_neither_reports_the_nearer_production() {
        assert_eq!(tokens("01"), Err(ErrorKind::InvalidNumber));
        assert_eq!(tokens("1."), Err(ErrorKind::InvalidNumber));
        assert_eq!(tokens("Foo"), Err(ErrorKind::InvalidSymbol));
        assert_eq!(tokens(":"), Err(ErrorKind::InvalidSymbol));
    }

    #[test]
    fn a_minus_atom_falls_back_from_number_to_symbol() {
        // `-5x` fails the number grammar but is a legal wordsym.
        assert_eq!(productions("-5x"), [Production::Symbol]);
        assert_eq!(productions("-5"), [Production::Number]);
        assert_eq!(productions("-"), [Production::Symbol]);
    }

    #[test]
    fn comments_and_the_full_whitespace_set_are_trivia() {
        assert_eq!(
            productions("; leading\n(a\u{b}b\u{c}c) ; trailing"),
            [Production::Symbol, Production::Symbol, Production::Symbol]
        );
        assert!(tokens("; only a comment").expect("valid").is_empty());
    }

    #[test]
    fn strings_borrow_until_an_escape_forces_a_copy() {
        let events = parse_pose(r#"("plain" "with \" quote")"#)
            .collect::<Result<Vec<_>, _>>()
            .expect("valid input");
        let literals: Vec<_> = events
            .iter()
            .filter_map(|event| match event {
                Event::Atom(Token::String(literal)) => Some(literal),
                _ => None,
            })
            .collect();

        assert_eq!(literals[0].value(), "plain");
        assert_eq!(literals[0].raw(), "plain");
        // The raw spelling keeps the escape; the value resolves it.
        assert_eq!(literals[1].raw(), r#"with \" quote"#);
        assert_eq!(literals[1].value(), r#"with " quote"#);
    }

    #[test]
    fn string_errors_name_their_cause() {
        assert_eq!(
            tokens(r#""unterminated"#),
            Err(ErrorKind::UnterminatedLiteral)
        );
        assert_eq!(tokens(r#""trailing\"#), Err(ErrorKind::UnterminatedLiteral));
        assert_eq!(tokens(r#""bad \n escape""#), Err(ErrorKind::InvalidEscape));
    }

    #[test]
    fn structural_errors_carry_offsets() {
        let error = parse_pose("(a))").find_map(Result::err).expect("an error");
        assert_eq!(error.kind(), ErrorKind::UnexpectedListEnd);
        assert_eq!(error.offset(), 3);

        let error = parse_pose("(a").find_map(Result::err).expect("an error");
        assert_eq!(error.kind(), ErrorKind::UnclosedList);
        assert_eq!(error.offset(), 2);
    }

    #[test]
    fn reading_produces_a_tree_of_tagged_atoms() {
        let tree: SExpr<Atom> = read(r#"(add 1 "two")"#, Pose).expect("valid input");
        assert_eq!(
            tree,
            SExpr::list(vec![
                SExpr::atom(Atom::Symbol(Symbol::new("add"))),
                SExpr::atom(Atom::Number(Symbol::new("1"))),
                SExpr::atom(Atom::String(Symbol::new("two"))),
            ])
        );
    }

    #[test]
    fn reading_separates_root_count_from_syntax() {
        assert_eq!(read_all::<Atom, _>("a b c", Pose).expect("valid").len(), 3);
        assert!(matches!(
            read::<Atom, _>("a b", Pose),
            Err(ReadError::Structure(_))
        ));
        assert!(matches!(
            read::<Atom, _>("", Pose),
            Err(ReadError::Structure(_))
        ));
        assert!(matches!(
            read::<Atom, _>("(a", Pose),
            Err(ReadError::Syntax(_))
        ));
    }

    #[test]
    fn adjacent_atoms_need_no_separator() {
        assert_eq!(
            read_all::<Atom, _>(r#"a"b""#, Pose).expect("valid").len(),
            2
        );
    }

    #[test]
    fn strings_carry_multibyte_text_through_the_decoding_path() {
        // The leading escape forces the copying path, so the multibyte text
        // after it is pushed by the branch that must copy whole characters
        // rather than bytes.
        let tree: SExpr<Atom> = read("\"\\\" caf\u{e9}\"", Pose).expect("valid input");
        assert_eq!(tree, SExpr::atom(Atom::String(Symbol::new("\" caf\u{e9}"))));
        // Without an escape the literal borrows, multibyte or not.
        let tree: SExpr<Atom> = read("\"caf\u{e9}\"", Pose).expect("valid input");
        assert_eq!(tree, SExpr::atom(Atom::String(Symbol::new("caf\u{e9}"))));
    }

    #[test]
    fn empty_and_nested_lists_are_structural() {
        let tree: SExpr<Atom> = read("(() (a))", Pose).expect("valid input");
        assert_eq!(
            tree,
            SExpr::list(vec![
                SExpr::list(vec![]),
                SExpr::list(vec![SExpr::atom(Atom::Symbol(Symbol::new("a")))]),
            ])
        );
    }

    #[test]
    fn a_string_may_span_lines() {
        let tree: SExpr<Atom> = read("\"one\ntwo\"", Pose).expect("valid input");
        assert_eq!(tree, SExpr::atom(Atom::String(Symbol::new("one\ntwo"))));
    }

    #[test]
    fn a_comment_ends_at_either_newline_character() {
        // `newline = CR | LF`, so a lone CR must terminate a comment. Missing
        // that silently swallows the rest of the input.
        assert_eq!(productions("; c\ra"), [Production::Symbol]);
        assert_eq!(productions("; c\r\na"), [Production::Symbol]);
        assert_eq!(productions("; c\na"), [Production::Symbol]);
        // A CR-terminated comment must not eat the closing parenthesis.
        assert_eq!(
            read_all::<Atom, _>("(a ; c\r)", Pose).expect("valid").len(),
            1
        );
    }
}
