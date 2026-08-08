//! S-expressions: what the REPL reads, and what it hands back.
//!
//! The REPL takes s-expressions rather than dot-commands for one reason that
//! matters and one that follows from it.
//!
//! The one that matters: results are *data*. `(objects)` does not print a
//! blob of text that a caller must parse back; it evaluates to a list of
//! addresses, and printing is what the terminal does to a value at the end. A
//! command surface which returns text has to grow a second, machine-readable
//! surface the first time anything wants to consume it. This one does not.
//!
//! The one that follows: quoting is uniform. `(sqlite ADDRESS "SELECT * FROM
//! t")` needs no special argument splitter, because a string literal is
//! already a token. The dot-command surface needed a hand-rolled shell-style
//! splitter for exactly this case.
//!
//! # Where this is going
//!
//! This is the reader for a Scheme, arrived at early rather than retrofitted.
//! It is deliberately not one yet: there are no lambdas, no environments, and
//! no tail calls. What it has is the shape those need — a value type closed
//! under lists, a reader that produces it, and an evaluator that walks it.

use std::fmt;
use std::str::FromStr;

use covalence_lib_hash::O256;

/// A value: what the reader produces and what evaluation returns.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    /// The empty list, `()`. Also what a command returns when it has nothing
    /// to say.
    Nil,
    /// `#t` or `#f`.
    Bool(bool),
    /// A signed 64-bit integer.
    Integer(i64),
    /// A string literal.
    Text(String),
    /// An identifier.
    Symbol(String),
    /// A content address.
    ///
    /// Addresses are their own kind rather than strings because they are the
    /// one value this REPL is *about*. A 64-character hex token reads as an
    /// address, so pasting one is all it takes.
    Address(O256),
    /// A proper list.
    List(Vec<Value>),
}

impl Value {
    /// Builds a list, collapsing the empty one to [`Nil`](Value::Nil).
    #[must_use]
    pub fn list(items: Vec<Self>) -> Self {
        if items.is_empty() {
            Self::Nil
        } else {
            Self::List(items)
        }
    }

    /// Returns the text of a string or symbol.
    ///
    /// Both are accepted wherever a name is wanted: `(connect "http://…")`
    /// and `(put "db.sqlite")` read better quoted, and requiring quotes on a
    /// bare word would be pedantry.
    #[must_use]
    pub fn as_text(&self) -> Option<&str> {
        match self {
            Self::Text(text) | Self::Symbol(text) => Some(text),
            _ => None,
        }
    }

    /// Returns the address this value denotes.
    #[must_use]
    pub fn as_address(&self) -> Option<O256> {
        match self {
            Self::Address(address) => Some(*address),
            // A quoted address is still an address; refusing it would be a
            // distinction with no meaning behind it.
            Self::Text(text) => O256::from_str(text).ok(),
            _ => None,
        }
    }

    /// Renders for a person rather than for the reader.
    ///
    /// This is Scheme's `display`, and [`Display`](fmt::Display) is its
    /// `write`: the difference is that a string prints as its characters
    /// rather than as the literal which would read back to it. A REPL wants
    /// `write` for data -- so a printed address can be pasted back -- and
    /// `display` for a string that *is* the message, like the help text.
    #[must_use]
    pub fn display(&self) -> String {
        match self {
            Self::Text(text) => text.clone(),
            other => other.to_string(),
        }
    }

    /// Returns the integer this value denotes.
    #[must_use]
    pub const fn as_integer(&self) -> Option<i64> {
        match self {
            Self::Integer(value) => Some(*value),
            _ => None,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Nil => formatter.write_str("()"),
            Self::Bool(true) => formatter.write_str("#t"),
            Self::Bool(false) => formatter.write_str("#f"),
            Self::Integer(value) => write!(formatter, "{value}"),
            Self::Text(text) => write!(formatter, "{text:?}"),
            Self::Symbol(name) => formatter.write_str(name),
            Self::Address(address) => write!(formatter, "{}", address.hex()),
            Self::List(items) => {
                formatter.write_str("(")?;
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(" ")?;
                    }
                    write!(formatter, "{item}")?;
                }
                formatter.write_str(")")
            }
        }
    }
}

/// Input which is not an s-expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReadError {
    /// A `)` with no `(`.
    UnexpectedClose,
    /// End of input inside a list, string, or escape.
    Unterminated,
}

impl fmt::Display for ReadError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedClose => formatter.write_str("unexpected )"),
            Self::Unterminated => formatter.write_str("unterminated expression"),
        }
    }
}

impl std::error::Error for ReadError {}

/// Reads every form in `input`.
///
/// A line may hold more than one form; each is evaluated in turn. `;` begins
/// a comment which runs to the end of the line.
///
/// # Errors
///
/// Returns an error for unbalanced parentheses or an unterminated string.
pub fn read(input: &str) -> Result<Vec<Value>, ReadError> {
    let mut reader = Reader {
        rest: input.chars().peekable(),
    };
    let mut forms = Vec::new();
    while let Some(form) = reader.form()? {
        forms.push(form);
    }
    Ok(forms)
}

struct Reader<'a> {
    rest: std::iter::Peekable<std::str::Chars<'a>>,
}

impl Reader<'_> {
    /// Reads one form, or `None` at end of input.
    ///
    /// Returns [`ReadError::UnexpectedClose`] on a `)`, which the list reader
    /// catches and treats as the end of its list. Depth is bounded by the
    /// input, and input is one line typed by a person.
    fn form(&mut self) -> Result<Option<Value>, ReadError> {
        self.skip_blanks();
        let Some(&character) = self.rest.peek() else {
            return Ok(None);
        };
        match character {
            ')' => {
                self.rest.next();
                Err(ReadError::UnexpectedClose)
            }
            '(' => {
                self.rest.next();
                let mut items = Vec::new();
                loop {
                    match self.form() {
                        Ok(Some(item)) => items.push(item),
                        // The `)` that ends this list.
                        Err(ReadError::UnexpectedClose) => break,
                        Ok(None) => return Err(ReadError::Unterminated),
                        Err(error) => return Err(error),
                    }
                }
                Ok(Some(Value::list(items)))
            }
            '\'' => {
                self.rest.next();
                let quoted = self.form()?.ok_or(ReadError::Unterminated)?;
                Ok(Some(Value::List(vec![
                    Value::Symbol("quote".to_owned()),
                    quoted,
                ])))
            }
            '"' => {
                self.rest.next();
                self.string().map(Some)
            }
            _ => Ok(Some(atom(&self.token()))),
        }
    }

    fn skip_blanks(&mut self) {
        while let Some(&character) = self.rest.peek() {
            if character == ';' {
                while self.rest.next().is_some_and(|c| c != '\n') {}
            } else if character.is_whitespace() {
                self.rest.next();
            } else {
                return;
            }
        }
    }

    fn string(&mut self) -> Result<Value, ReadError> {
        let mut text = String::new();
        loop {
            match self.rest.next().ok_or(ReadError::Unterminated)? {
                '"' => return Ok(Value::Text(text)),
                '\\' => match self.rest.next().ok_or(ReadError::Unterminated)? {
                    'n' => text.push('\n'),
                    't' => text.push('\t'),
                    escaped => text.push(escaped),
                },
                character => text.push(character),
            }
        }
    }

    fn token(&mut self) -> String {
        let mut text = String::new();
        while let Some(&character) = self.rest.peek() {
            if character.is_whitespace() || matches!(character, '(' | ')' | '"' | ';') {
                break;
            }
            text.push(character);
            self.rest.next();
        }
        text
    }
}

/// Classifies a bare token.
///
/// Addresses are checked before integers, which matters: an address of 64
/// hex digits that all happen to be decimal parses perfectly well as an
/// `i64`, and the all-zero address is exactly that. Nothing is lost by the
/// order, because `O256::from_str` accepts only 64 characters and no integer
/// anyone types is that long.
fn atom(token: &str) -> Value {
    match token {
        "#t" | "#true" => return Value::Bool(true),
        "#f" | "#false" => return Value::Bool(false),
        _ => {}
    }
    if let Ok(address) = O256::from_str(token) {
        return Value::Address(address);
    }
    if let Ok(value) = token.parse::<i64>() {
        return Value::Integer(value);
    }
    Value::Symbol(token.to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn one(input: &str) -> Value {
        let mut forms = read(input).expect("read");
        assert_eq!(forms.len(), 1, "expected one form in {input:?}");
        forms.remove(0)
    }

    #[test]
    fn atoms_classify_by_shape() {
        assert_eq!(one("42"), Value::Integer(42));
        assert_eq!(one("-7"), Value::Integer(-7));
        assert_eq!(one("#t"), Value::Bool(true));
        assert_eq!(one("#f"), Value::Bool(false));
        assert_eq!(one("objects"), Value::Symbol("objects".to_owned()));
        assert_eq!(one(r#""a b""#), Value::Text("a b".to_owned()));
    }

    #[test]
    fn a_hex_address_reads_as_an_address() {
        let hex = "0".repeat(64);
        // All-decimal digits, so this also parses as an integer; the address
        // must win, or the one address you can type by hand is not one.
        assert!(matches!(one(&hex), Value::Address(_)), "{:?}", one(&hex));
        assert!(matches!(one(&"ab".repeat(32)), Value::Address(_)));
        // One character short is a symbol, not a silently truncated address.
        assert!(matches!(one(&"0".repeat(63)), Value::Integer(0)));
        assert!(matches!(one(&"ab".repeat(31)), Value::Symbol(_)));
    }

    #[test]
    fn lists_nest_and_empty_lists_are_nil() {
        assert_eq!(one("()"), Value::Nil);
        assert_eq!(
            one("(a (b c))"),
            Value::List(vec![
                Value::Symbol("a".to_owned()),
                Value::List(vec![
                    Value::Symbol("b".to_owned()),
                    Value::Symbol("c".to_owned()),
                ]),
            ])
        );
    }

    #[test]
    fn a_line_may_hold_several_forms() {
        assert_eq!(read("(a) (b)").expect("read").len(), 2);
    }

    #[test]
    fn strings_carry_spaces_so_no_argument_splitter_is_needed() {
        assert_eq!(
            one(r#"(sqlite "SELECT * FROM t")"#),
            Value::List(vec![
                Value::Symbol("sqlite".to_owned()),
                Value::Text("SELECT * FROM t".to_owned()),
            ])
        );
        assert_eq!(
            one(r#""say \"hi\"""#),
            Value::Text(r#"say "hi""#.to_owned())
        );
    }

    #[test]
    fn quote_is_sugar_for_a_quote_form() {
        assert_eq!(
            one("'a"),
            Value::List(vec![
                Value::Symbol("quote".to_owned()),
                Value::Symbol("a".to_owned()),
            ])
        );
    }

    #[test]
    fn comments_run_to_end_of_line() {
        assert_eq!(read("; nothing here").expect("read"), Vec::new());
        assert_eq!(
            one("(a) ; trailing"),
            Value::List(vec![Value::Symbol("a".to_owned())])
        );
    }

    #[test]
    fn unbalanced_input_is_an_error() {
        assert_eq!(read("(a"), Err(ReadError::Unterminated));
        assert_eq!(read(")"), Err(ReadError::UnexpectedClose));
        assert_eq!(read(r#""open"#), Err(ReadError::Unterminated));
    }

    #[test]
    fn display_shows_a_string_and_write_shows_its_literal() {
        assert_eq!(one(r#""a b""#).to_string(), r#""a b""#);
        assert_eq!(one(r#""a b""#).display(), "a b");
        // Anything else renders the same either way.
        assert_eq!(one("(a 1)").display(), "(a 1)");
    }

    #[test]
    fn values_print_as_the_syntax_that_reads_them() {
        for input in ["()", "42", "#t", "#f", "(a b)", "(a (b c))", r#""a b""#] {
            assert_eq!(one(input).to_string(), input, "round trip {input}");
        }
    }
}
