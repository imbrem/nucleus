//! Byte strings inside arithmetic expressions.
//!
//! A byte is a natural below 256, and a byte string is a sequence of them.
//! Neither is a type in the logic: `tm.bytes` rows are syntax with no lowering,
//! so the kernel rejects one, and the init slice defines no byte type. A byte
//! string therefore lives only in the expression tree.
//!
//! What that buys, and what it costs:
//!
//! - `len` and `index` return naturals, so they become ordinary literals and
//!   the arithmetic around them is proved like any other.
//! - `slice` and `cat` return byte strings, so they are folded before any term
//!   is built.
//! - The byte operations themselves are therefore **computed, not proved**. A
//!   theorem about `len(b) + 1` says nothing about `len`; it says the literal it
//!   folded to, plus one, is what the normalizer claims.
//!
//! For a symbolic byte string, pass a natural standing for the projection you
//! care about and let the normalizer treat it as an atom:
//! `Expr::atom(length_term) + 1` needs nothing from this module.

use std::rc::Rc;

use crate::{Expr, NaturalError};

/// The largest value a byte can take, exclusive.
pub const BYTE_BOUND: u64 = 256;

/// A byte string built from literals, slices, and concatenations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Bytes(Rc<Node>);

#[derive(Debug, Eq, PartialEq)]
enum Node {
    Literal(Vec<u8>),
    Slice(Bytes, u64, u64),
    Cat(Bytes, Bytes),
}

impl Bytes {
    /// A literal byte string.
    #[must_use]
    pub fn literal(bytes: impl Into<Vec<u8>>) -> Self {
        Self(Rc::new(Node::Literal(bytes.into())))
    }

    /// The bytes from `start` up to `end`.
    ///
    /// Bounds are checked when the string is folded, not here.
    #[must_use]
    pub fn slice(&self, start: u64, end: u64) -> Self {
        Self(Rc::new(Node::Slice(self.clone(), start, end)))
    }

    /// This string followed by `other`.
    #[must_use]
    pub fn cat(&self, other: &Self) -> Self {
        Self(Rc::new(Node::Cat(self.clone(), other.clone())))
    }

    /// Folds the string down to its bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if a slice runs past the end of what it slices, or
    /// starts after it ends.
    pub fn value(&self) -> Result<Vec<u8>, NaturalError> {
        match &*self.0 {
            Node::Literal(bytes) => Ok(bytes.clone()),
            Node::Slice(inner, start, end) => {
                let bytes = inner.value()?;
                let length = as_index(bytes.len())?;
                if start > end || *end > length {
                    return Err(NaturalError::WrongForm {
                        expected: "a slice within the string",
                    });
                }
                let start = usize::try_from(*start).map_err(|_| index_error())?;
                let end = usize::try_from(*end).map_err(|_| index_error())?;
                Ok(bytes[start..end].to_vec())
            }
            Node::Cat(left, right) => {
                let mut bytes = left.value()?;
                bytes.extend_from_slice(&right.value()?);
                Ok(bytes)
            }
        }
    }

    /// The length, as an arithmetic expression.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`value`](Self::value).
    pub fn len(&self) -> Result<Expr, NaturalError> {
        let length = as_index(self.value()?.len())?;
        Ok(Expr::literal(length))
    }

    /// The byte at `at`, as an arithmetic expression.
    ///
    /// # Errors
    ///
    /// Returns an error if `at` is past the end, or under the same conditions
    /// as [`value`](Self::value).
    pub fn index(&self, at: u64) -> Result<Expr, NaturalError> {
        let bytes = self.value()?;
        let position = usize::try_from(at).map_err(|_| index_error())?;
        let byte = bytes.get(position).ok_or(NaturalError::WrongForm {
            expected: "an index within the string",
        })?;
        Ok(Expr::literal(u64::from(*byte)))
    }
}

impl From<&[u8]> for Bytes {
    fn from(bytes: &[u8]) -> Self {
        Self::literal(bytes.to_vec())
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(bytes: Vec<u8>) -> Self {
        Self::literal(bytes)
    }
}

fn as_index(length: usize) -> Result<u64, NaturalError> {
    u64::try_from(length).map_err(|_| index_error())
}

fn index_error() -> NaturalError {
    NaturalError::WrongForm {
        expected: "a byte-string index within range",
    }
}
