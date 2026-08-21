/// Errors from parsing or verifying a Metamath database.
#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum MmError {
    // --- structural / parse ---
    #[error("parse error: {0}")]
    Parse(String),

    #[error("duplicate label `{0}`")]
    DuplicateLabel(String),

    #[error("`{label}`: unknown symbol `{symbol}`")]
    UnknownSymbol { label: String, symbol: String },

    #[error("malformed expression in `{label}`: {message}")]
    MalformedExpr { label: String, message: String },

    #[error("file inclusion error for `{path}`: {message}")]
    FileError { path: String, message: String },

    // --- proof checking ---
    #[error("proof of `{theorem}` references unknown label `{label}`")]
    UnknownLabel { theorem: String, label: String },

    #[error("stack underflow while applying `{step}` in proof of `{theorem}`")]
    StackUnderflow { theorem: String, step: String },

    #[error(
        "typecode mismatch in proof of `{theorem}` applying `{step}`: \
         floating hypothesis for `{var}` expects typecode `{expected}`, got `{found}`"
    )]
    TypecodeMismatch {
        theorem: String,
        step: String,
        var: String,
        expected: String,
        found: String,
    },

    #[error(
        "essential-hypothesis mismatch in proof of `{theorem}` applying `{step}`: \
         expected `{expected}`, got `{found}`"
    )]
    HypothesisMismatch {
        theorem: String,
        step: String,
        expected: String,
        found: String,
    },

    #[error(
        "distinct-variable violation in proof of `{theorem}` applying `{step}`: \
         `{a}` and `{b}` must be distinct, but their substitutions share variable `{shared}` \
         (or are not provably distinct)"
    )]
    DisjointViolation {
        theorem: String,
        step: String,
        a: String,
        b: String,
        shared: String,
    },

    #[error("proof of `{theorem}` left {count} expressions on the stack (expected exactly 1)")]
    StackResidue { theorem: String, count: usize },

    #[error("proof of `{theorem}` produced `{found}` but the claimed statement is `{expected}`")]
    ResultMismatch {
        theorem: String,
        expected: String,
        found: String,
    },

    #[error("compressed-proof error in `{theorem}`: {message}")]
    CompressedProofError { theorem: String, message: String },

    /// A [`DatabaseSink`](crate::DatabaseSink) backend failed while building a
    /// statement (e.g. a HOL-backed sink whose `⊢ Derivable_…` construction
    /// failed). Generic — the message carries the backend's own error text.
    #[error("backend error building `{label}`: {message}")]
    Backend { label: String, message: String },
}
