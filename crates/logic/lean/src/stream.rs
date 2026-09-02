//! Logic-independent streaming NDJSON and dense indexed tables.

use std::io::BufRead;

use covalence_lib_error::snafu::Snafu;
use covalence_lib_json::Value;

/// A framing or JSON failure while consuming an NDJSON stream.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// Reading the underlying byte stream failed.
    #[snafu(display("could not read NDJSON line {line}: {source}"))]
    Read {
        /// One-based line number being read.
        line: usize,
        /// Underlying I/O failure.
        source: std::io::Error,
    },
    /// A line was not one complete JSON value.
    #[snafu(display("invalid JSON on NDJSON line {line}: {source}"))]
    Json {
        /// One-based line number.
        line: usize,
        /// JSON parser failure.
        source: covalence_lib_json::Error,
    },
    /// The stream contained an empty physical record.
    #[snafu(display("empty NDJSON record on line {line}"))]
    Empty {
        /// One-based line number.
        line: usize,
    },
}

/// Parse one complete JSON value per physical line and call `visit` immediately.
///
/// This function holds no whole-stream buffer. CRLF is accepted by removing a
/// single trailing `\r`; empty records are rejected instead of silently changing
/// dense line/record positions.
///
/// # Errors
///
/// Returns [`Error`] for I/O failure, an empty record, or malformed JSON. A
/// visitor error is returned unchanged.
pub fn for_each<R, E>(
    mut reader: R,
    mut visit: impl FnMut(usize, Value) -> Result<(), E>,
) -> Result<(), ForEachError<E>>
where
    R: BufRead,
{
    let mut line = String::new();
    let mut number = 0;
    loop {
        line.clear();
        number += 1;
        let count = reader.read_line(&mut line).map_err(|source| {
            ForEachError::Framing(Error::Read {
                line: number,
                source,
            })
        })?;
        if count == 0 {
            return Ok(());
        }
        if line.ends_with('\n') {
            line.pop();
            if line.ends_with('\r') {
                line.pop();
            }
        }
        if line.is_empty() {
            return Err(ForEachError::Framing(Error::Empty { line: number }));
        }
        let value = covalence_lib_json::from_str(&line).map_err(|source| {
            ForEachError::Framing(Error::Json {
                line: number,
                source,
            })
        })?;
        visit(number, value).map_err(ForEachError::Visitor)?;
    }
}

/// Either generic NDJSON framing failed or the format-specific visitor declined.
#[derive(Debug)]
pub enum ForEachError<E> {
    /// Generic framing or JSON syntax failure.
    Framing(Error),
    /// Format-specific record failure.
    Visitor(E),
}

/// A vector-backed table whose explicit indices must be dense and append-only.
#[derive(Clone, Debug)]
pub struct DenseTable<T> {
    rows: Vec<T>,
}

impl<T> DenseTable<T> {
    /// Start with implicit prefix rows, such as Lean name/level index zero.
    #[must_use]
    pub fn with_prefix(rows: Vec<T>) -> Self {
        Self { rows }
    }

    /// The next valid explicit index.
    #[must_use]
    pub fn next_index(&self) -> usize {
        self.rows.len()
    }

    /// Append `value` at `index` if it is exactly the next dense position.
    ///
    /// # Errors
    ///
    /// Returns the next expected index when `index` is a duplicate, gap, or
    /// out-of-order insertion.
    pub fn insert(&mut self, index: usize, value: T) -> Result<(), usize> {
        if index != self.rows.len() {
            return Err(self.rows.len());
        }
        self.rows.push(value);
        Ok(())
    }

    /// Resolve only a row already established in this table.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.rows.get(index)
    }
}
