//! The default owned symbol used by Nucleus data APIs.
//!
//! [`Symbol`] identifies an exact UTF-8 string. It performs no normalization,
//! case folding, validation of language syntax, or interning. In particular,
//! the empty string is a valid symbol. Parsers remain responsible for spelling,
//! escaping, namespaces, and any restrictions imposed by their language.
//!
//! A symbol's canonical boundary representation is the unmodified UTF-8 byte
//! sequence returned by [`Symbol::as_bytes`]. Native and Wasm callers should
//! exchange those bytes as UTF-8; WIT callers use `string`; `SQLite` callers use
//! `TEXT`; and S-expression encodings apply their own escaping to
//! [`Symbol::as_str`]. Decoding bytes is explicit and rejects invalid UTF-8.

use std::{
    borrow::Borrow,
    fmt,
    str::{self, Utf8Error},
};

/// An immutable, owned symbol with exact UTF-8 identity.
///
/// The representation is private so it can change without affecting users.
#[derive(Clone, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Symbol(String);

impl Symbol {
    /// Creates a symbol by copying `text`.
    #[must_use]
    pub fn new(text: &str) -> Self {
        Self(text.to_owned())
    }

    /// Creates a symbol from text with static lifetime.
    ///
    /// This constructor records the caller's intent without promising a
    /// particular storage strategy.
    #[must_use]
    pub fn from_static(text: &'static str) -> Self {
        Self::new(text)
    }

    /// Returns the exact text that identifies this symbol.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Returns the canonical UTF-8 boundary encoding of this symbol.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Consumes this symbol and returns its text.
    #[must_use]
    pub fn into_string(self) -> String {
        self.0
    }

    /// Decodes a symbol from its canonical UTF-8 boundary encoding.
    ///
    /// # Errors
    ///
    /// Returns an error when `bytes` is not valid UTF-8.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Utf8Error> {
        str::from_utf8(bytes).map(Self::new)
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Borrow<str> for Symbol {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(formatter)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

impl From<&str> for Symbol {
    fn from(text: &str) -> Self {
        Self::new(text)
    }
}

impl From<String> for Symbol {
    fn from(text: String) -> Self {
        Self(text)
    }
}

impl From<Symbol> for String {
    fn from(symbol: Symbol) -> Self {
        symbol.into_string()
    }
}

impl TryFrom<&[u8]> for Symbol {
    type Error = Utf8Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        Self::from_bytes(bytes)
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{BTreeSet, HashSet},
        hash::{DefaultHasher, Hash, Hasher},
    };

    use super::Symbol;

    fn hash(symbol: &Symbol) -> u64 {
        let mut hasher = DefaultHasher::new();
        symbol.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn constructors_preserve_inline_heap_and_static_text() {
        let inline = Symbol::new("atom");
        let heap = Symbol::from("a deliberately long symbol that exceeds small-string storage");
        let static_text = Symbol::from_static("static");

        assert_eq!(inline.as_str(), "atom");
        assert_eq!(
            heap.as_str(),
            "a deliberately long symbol that exceeds small-string storage"
        );
        assert_eq!(static_text.as_str(), "static");
    }

    #[test]
    fn empty_and_arbitrary_unicode_are_valid() {
        assert_eq!(Symbol::default().as_str(), "");
        assert_eq!(Symbol::new("λ/雪/🦀").as_str(), "λ/雪/🦀");
    }

    #[test]
    fn identity_is_exact_without_normalization_or_case_folding() {
        assert_ne!(Symbol::new("Name"), Symbol::new("name"));
        assert_ne!(Symbol::new("\u{e9}"), Symbol::new("e\u{301}"));
    }

    #[test]
    fn ordering_and_hashing_follow_exact_text() {
        let symbols = [
            Symbol::new("beta"),
            Symbol::new("alpha"),
            Symbol::new("alpha"),
        ];

        assert_eq!(symbols[1], symbols[2]);
        assert_eq!(hash(&symbols[1]), hash(&symbols[2]));
        assert_eq!(
            symbols.iter().cloned().collect::<BTreeSet<_>>(),
            [Symbol::new("alpha"), Symbol::new("beta")]
                .into_iter()
                .collect()
        );
        assert_eq!(symbols.into_iter().collect::<HashSet<_>>().len(), 2);
    }

    #[test]
    fn utf8_boundary_round_trip_is_exact() {
        let original = Symbol::new("λ/雪/🦀");
        let decoded = Symbol::from_bytes(original.as_bytes()).unwrap();

        assert_eq!(decoded, original);
        assert!(Symbol::from_bytes(&[0xff]).is_err());
    }

    #[test]
    fn conversions_do_not_expose_storage() {
        let symbol = Symbol::from(String::from("owned"));
        let borrowed: &str = symbol.as_ref();
        assert_eq!(borrowed, "owned");

        let text: String = symbol.into();
        assert_eq!(text, "owned");
    }
}
