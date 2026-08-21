//! Parsing conventions for Nucleus.
//!
//! [`winnow`] is the parser library for this repository. Parsers for external
//! input formats are built from its combinators rather than from a hand-rolled
//! scanner, so that error positions, backtracking, and stream handling behave
//! the same way in every format.
//!
//! Parsers are written against winnow's stream abstraction rather than a
//! concrete input type, so the same combinators run over `&str`, `&[u8]`, and
//! token slices. Several of the formats here — Metamath, S-expressions, LRAT —
//! are token-oriented rather than byte-oriented, and their grammars are written
//! above a tokenizer instead of over bytes.
//!
//! Parsers borrow from their input rather than allocating per token. Owning the
//! result is the caller's choice, not the parser's.
//!
//! Parsing is untrusted-input handling and sits outside the trusted computing
//! base. A parser suggests structure; authority comes from a kernel that
//! re-derives it. Recursion is therefore bounded: deeply nested input from an
//! untrusted source has to produce an error, not a stack overflow.
//!
//! Parser errors are converted into the owning crate's own domain error type at
//! its boundary. Winnow's error types are an implementation detail and do not
//! appear in a public API.

/// Winnow's parser, combinator, and stream APIs.
pub use winnow;

#[cfg(test)]
mod tests {
    use super::winnow::{
        ModalResult, Parser,
        combinator::{repeat, terminated},
        token::any,
    };

    /// `$c <symbol>... $.` read from a token stream, borrowing every symbol.
    fn constants<'a>(input: &mut &'a [&'a str]) -> ModalResult<Vec<&'a str>> {
        let keyword = any.verify(|token: &&str| *token == "$c");
        let symbol = any.verify(|token: &&str| !token.starts_with('$'));
        let terminator = any.verify(|token: &&str| *token == "$.");

        (keyword, terminated(repeat(1.., symbol), terminator))
            .map(|(_, symbols)| symbols)
            .parse_next(input)
    }

    #[test]
    fn reexport_parses_a_token_stream() {
        let statement = ["$c", "wff", "|-", "$."];
        assert_eq!(
            constants.parse(&statement[..]).expect("parsed statement"),
            vec!["wff", "|-"]
        );

        let unterminated = ["$c", "wff"];
        assert!(constants.parse(&unterminated[..]).is_err());
    }
}
