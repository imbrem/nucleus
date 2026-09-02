//! The failures parsing or verifying a Metamath database can produce.
//!
//! Every variant names one cause. There is deliberately **no** stringly-typed
//! catch-all: a `Parse(String)` variant carrying a `format!`ed sentence is
//! something no caller can branch on, and the tests that grew around it had to
//! assert on substrings of prose. The taxonomy below is what those assertions
//! were reaching for.
//!
//! Only [`MmError::FileError`] and [`MmError::Backend`] carry a `source`; both
//! sit at a boundary where the concrete failure belongs to somebody else (the
//! host filesystem, and an out-of-crate [`DatabaseSink`](crate::DatabaseSink)
//! implementation respectively). Everything else *is* the failure, so there is
//! nothing beneath it to chain.

use std::error::Error;
use std::fmt;

use covalence_lib_error::snafu::Snafu;

use crate::database::SymbolKind;

/// The position a label was read in, so a malformed one can say where it came
/// from — the three are lexically identical but arrive by different routes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelPosition {
    /// The label introducing a `$f`, `$e`, `$a` or `$p` statement.
    Statement,
    /// One step of a normal (uncompressed) proof.
    ProofStep,
    /// One entry of a compressed proof's `( ... )` label block.
    CompressedProofBlock,
}

impl fmt::Display for LabelPosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Statement => "label",
            Self::ProofStep => "proof step label",
            Self::CompressedProofBlock => "compressed-proof label",
        })
    }
}

/// Errors from parsing or verifying a Metamath database.
///
/// Not [`Clone`], [`PartialEq`] or [`Eq`]: [`MmError::FileError`] carries a
/// [`std::io::Error`] and [`MmError::Backend`] a boxed foreign error, neither of
/// which is any of those. Match on the variant, or render it.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(visibility(pub(crate)))]
pub enum MmError {
    // --- token character classes -------------------------------------------
    /// A label used a character outside the spec's label class.
    #[snafu(display("invalid {position} {token:?}, labels may use only A-Z a-z 0-9 . - _"))]
    InvalidLabel {
        /// Where the label was read.
        position: LabelPosition,
        /// The offending token.
        token: String,
    },

    /// A math symbol used a character outside the spec's math-symbol class.
    #[snafu(display(
        "invalid math symbol {token:?} in {context}, \
         math symbols are printable ASCII other than $"
    ))]
    InvalidMathSymbol {
        /// The statement the symbol appeared in: a keyword such as `$c`, or an
        /// assertion's label.
        context: String,
        /// The offending token.
        token: String,
    },

    // --- delimiters --------------------------------------------------------
    /// A `$(` comment was never closed.
    #[snafu(display("unterminated comment, $( has no matching $)"))]
    UnterminatedComment,

    /// A `$)` appeared with no `$(` open.
    #[snafu(display("unmatched $)"))]
    UnmatchedCommentClose,

    /// A scope block was still open at end of input.
    #[snafu(display("unclosed ${{"))]
    UnclosedScope,

    /// A scope block was closed with none open.
    #[snafu(display("unmatched $}}"))]
    UnmatchedScopeClose,

    /// A statement held a token the grammar cannot use there.
    #[snafu(display("unexpected {token} in {context}, expected {expected}"))]
    UnexpectedToken {
        /// The construct being read.
        context: String,
        /// The token that stopped it.
        token: String,
        /// What the grammar would have accepted.
        expected: String,
    },

    /// Input ran out part-way through a statement.
    #[snafu(display("unterminated {context}, expected {expected}"))]
    UnexpectedEnd {
        /// The construct left unfinished.
        context: String,
        /// What would have finished it.
        expected: String,
    },

    // --- statement placement -----------------------------------------------
    /// A `$c` appeared inside a scope block.
    #[snafu(display("$c is only allowed in the outermost scope"))]
    MisplacedConstant,

    /// A `$[` inclusion appeared inside a statement, or inside a scope block.
    #[snafu(display("$[ is only allowed between statements at the outermost scope"))]
    MisplacedInclude,

    // --- statement shape ---------------------------------------------------
    /// A `$d` named fewer than the two variables distinctness relates.
    #[snafu(display("$d needs two or more variables, found {count}"))]
    DisjointArity {
        /// How many were named.
        count: usize,
    },

    /// A `$d` named the same variable twice.
    #[snafu(display("$d names {var} twice, and a variable is never distinct from itself"))]
    DisjointRepeatsVariable {
        /// The repeated variable.
        var: String,
    },

    /// A `$f` was not the `typecode var` pair the spec requires.
    #[snafu(display(
        "floating hypothesis {label} must be a typecode and a variable, found {symbols:?}"
    ))]
    MalformedFloat {
        /// The `$f` label.
        label: String,
        /// The symbols actually given.
        symbols: Vec<String>,
    },

    /// A `$p` ended without the `$=` introducing its proof.
    #[snafu(display("theorem {label} states no proof, expected $="))]
    MissingProof {
        /// The `$p` label.
        label: String,
    },

    /// A `$a` axiom carried a `$=` proof.
    #[snafu(display("axiom {label} is a $a and cannot carry a proof"))]
    AxiomWithProof {
        /// The `$a` label.
        label: String,
    },

    /// A proof contained the `?` placeholder for a step nobody supplied.
    #[snafu(display("proof of {label} contains the incomplete-proof placeholder ?"))]
    IncompleteProof {
        /// The theorem whose proof is incomplete.
        label: String,
    },

    // --- declarations ------------------------------------------------------
    /// Two statements claimed the same label.
    #[snafu(display("label {label} is already declared"))]
    DuplicateLabel {
        /// The label claimed twice.
        label: String,
    },

    /// A `$c` re-declared an existing symbol.
    #[snafu(display("symbol {symbol} is already declared"))]
    Redeclared {
        /// The symbol declared twice.
        symbol: String,
    },

    /// A symbol was declared both a `$c` constant and a `$v` variable.
    #[snafu(display("symbol {symbol} is declared as both a constant and a variable"))]
    KindConflict {
        /// The symbol with two kinds.
        symbol: String,
    },

    /// A position that admits only variables named something else.
    #[snafu(display("{symbol} in {context} is not a declared variable"))]
    UndeclaredVariable {
        /// The statement the symbol appeared in.
        context: String,
        /// The symbol that is not a variable.
        symbol: String,
    },

    /// A statement used a symbol no `$c` or `$v` declares.
    #[snafu(display("undeclared symbol {symbol} in {label}"))]
    UnknownSymbol {
        /// The statement using it.
        label: String,
        /// The undeclared symbol.
        symbol: String,
    },

    /// A `$e`, `$a` or `$p` stated an empty expression.
    #[snafu(display("expression of {label} is empty, expected at least a typecode"))]
    EmptyExpression {
        /// The statement with no expression.
        label: String,
    },

    /// A mandatory variable had no active floating hypothesis to type it.
    #[snafu(display("variable {var} in {label} has no active floating hypothesis"))]
    UntypedVariable {
        /// The assertion whose frame could not be built.
        label: String,
        /// The untyped variable.
        var: String,
    },

    /// A [`Database::map_symbols`](crate::Database::map_symbols) renaming mapped
    /// a constant and a variable onto one name.
    #[snafu(display(
        "symbol renaming collides on {renamed}, \
         where {previous} is a {previous_kind} and {symbol} is a {kind}"
    ))]
    RenamingCollision {
        /// The image both symbols claim.
        renamed: String,
        /// The symbol that claimed it first.
        previous: String,
        /// That symbol's kind.
        previous_kind: SymbolKind,
        /// The symbol that collided with it.
        symbol: String,
        /// That symbol's kind.
        kind: SymbolKind,
    },

    /// A [`Database::map_symbols`](crate::Database::map_symbols) renaming mapped
    /// two symbols of the same kind onto one name.
    #[snafu(display(
        "symbol renaming is not injective, {first} and {second} both map to {renamed}"
    ))]
    RenamingNotInjective {
        /// The image both symbols claim.
        renamed: String,
        /// The symbol that claimed it first.
        first: String,
        /// The symbol that collided with it.
        second: String,
    },

    // --- boundaries --------------------------------------------------------
    /// A `$[ ... $]` include could not be read.
    #[snafu(display("could not read included file {path}: {source}"))]
    FileError {
        /// The filename as the directive spelled it.
        path: String,
        /// The resolver's failure.
        source: std::io::Error,
    },

    /// A [`DatabaseSink`](crate::DatabaseSink) backend failed while building a
    /// statement (a HOL-backed sink whose `⊢ Derivable_…` construction failed,
    /// say). Generic: the concrete failure belongs to an implementation this
    /// crate does not know.
    #[snafu(display("backend failed building {label}: {source}"))]
    Backend {
        /// The statement being built.
        label: String,
        /// The backend's own failure.
        source: Box<dyn Error + Send + Sync>,
    },

    // --- proof checking ----------------------------------------------------
    /// A proof cited a label the database does not declare.
    #[snafu(display("proof of {theorem} references undeclared label {label}"))]
    UnknownLabel {
        /// The theorem being proved.
        theorem: String,
        /// The label it cited.
        label: String,
    },

    /// A proof cited a label declared no earlier than the theorem itself — the
    /// reading-order discipline that stops a theorem proving itself.
    #[snafu(display(
        "proof of {theorem} references {label}, \
         which is not declared until later in the database"
    ))]
    ForwardReference {
        /// The theorem being proved.
        theorem: String,
        /// The label it cited.
        label: String,
    },

    /// A proof cited a floating or essential hypothesis outside its scope.
    #[snafu(display(
        "proof of {theorem} references {label}, a hypothesis that is not active \
         where {theorem} is asserted"
    ))]
    InactiveHypothesis {
        /// The theorem being proved.
        theorem: String,
        /// The `$f` or `$e` label it cited.
        label: String,
    },

    /// An assertion was applied with fewer arguments on the stack than its
    /// mandatory frame consumes.
    #[snafu(display("stack underflow applying {step} in proof of {theorem}"))]
    StackUnderflow {
        /// The theorem being proved.
        theorem: String,
        /// The step that underflowed.
        step: String,
    },

    /// An argument's typecode did not match the floating hypothesis it fills.
    #[snafu(display(
        "typecode mismatch in proof of {theorem} applying {step}, \
         the floating hypothesis for {var} expects {expected}, found {found}"
    ))]
    TypecodeMismatch {
        /// The theorem being proved.
        theorem: String,
        /// The step being applied.
        step: String,
        /// The variable being substituted.
        var: String,
        /// The typecode its `$f` declares.
        expected: String,
        /// The typecode the argument has.
        found: String,
    },

    /// A substituted essential hypothesis did not match the argument supplied.
    #[snafu(display(
        "essential-hypothesis mismatch in proof of {theorem} applying {step}, \
         expected {expected}, found {found}"
    ))]
    HypothesisMismatch {
        /// The theorem being proved.
        theorem: String,
        /// The step being applied.
        step: String,
        /// The hypothesis under the derived substitution.
        expected: String,
        /// The expression actually supplied.
        found: String,
    },

    /// Two substitutions a `$d` requires to be disjoint share a variable.
    #[snafu(display(
        "distinct-variable violation in proof of {theorem} applying {step}, \
         the substitutions for {a} and {b} share variable {shared}"
    ))]
    DisjointViolation {
        /// The theorem being proved.
        theorem: String,
        /// The step being applied.
        step: String,
        /// The first variable of the applied `$d`.
        a: String,
        /// The second variable of the applied `$d`.
        b: String,
        /// The variable both substitutions contain.
        shared: String,
    },

    /// A `$d` obligation the application generates is not discharged by the
    /// proving theorem's own in-scope `$d` set.
    ///
    /// Which `$d` of `step` generated the obligation is not carried: it is
    /// recoverable from `step`, and a sixth `String` here would push `MmError`
    /// past the size at which every `Result` in the crate pays for it.
    #[snafu(display(
        "distinct-variable violation in proof of {theorem} applying {step}, \
         which requires $d {x} {y} that {theorem} does not declare"
    ))]
    DisjointNotDeclared {
        /// The theorem being proved.
        theorem: String,
        /// The step being applied.
        step: String,
        /// The variable the first substitution contributed.
        x: String,
        /// The variable the second substitution contributed.
        y: String,
    },

    /// A proof ended with other than exactly one expression on the stack.
    #[snafu(display(
        "proof of {theorem} left {count} expressions on the stack, expected exactly 1"
    ))]
    StackResidue {
        /// The theorem being proved.
        theorem: String,
        /// How many were left.
        count: usize,
    },

    /// A proof ended with an expression other than the one claimed.
    #[snafu(display("proof of {theorem} produced {found}, but it claims {expected}"))]
    ResultMismatch {
        /// The theorem being proved.
        theorem: String,
        /// The claimed statement.
        expected: String,
        /// What the proof actually derived.
        found: String,
    },

    // --- compressed proofs -------------------------------------------------
    /// A `Z` save marker ran with nothing on the stack to save.
    #[snafu(display("Z save marker with an empty stack in proof of {theorem}"))]
    EmptySaveStack {
        /// The theorem being proved.
        theorem: String,
    },

    /// A heap backreference addressed an entry that has not been saved.
    #[snafu(display(
        "heap backreference {index} in proof of {theorem} is out of range, \
         the heap has {len} entries"
    ))]
    HeapOutOfRange {
        /// The theorem being proved.
        theorem: String,
        /// The index addressed.
        index: usize,
        /// How many entries the heap holds.
        len: usize,
    },

    /// A proof integer decoded to zero, which addresses nothing (they are
    /// 1-based).
    #[snafu(display("proof integer 0 in proof of {theorem} addresses no proof step"))]
    ZeroProofInteger {
        /// The theorem being proved.
        theorem: String,
    },

    /// A run of continuation digits overflowed `usize`. Untrusted input, so the
    /// accumulation is checked: a wrapped value would land on a small — and
    /// therefore valid — proof step.
    #[snafu(display("proof integer in proof of {theorem} is too large to address any proof step"))]
    ProofIntegerOverflow {
        /// The theorem being proved.
        theorem: String,
    },

    /// A `Z` or `?` appeared part-way through a proof integer.
    #[snafu(display("unexpected {letter:?} mid-integer in the letter block of {theorem}"))]
    UnexpectedLetter {
        /// The theorem being proved.
        theorem: String,
        /// The offending letter.
        letter: char,
    },

    /// A letter block held a character outside the `A`–`Z` / `?` alphabet.
    #[snafu(display("invalid character {letter:?} in the letter block of {theorem}"))]
    InvalidLetter {
        /// The theorem being proved.
        theorem: String,
        /// The offending character.
        letter: char,
    },

    /// A letter block ended with a proof integer still accumulating.
    #[snafu(display("letter block of {theorem} ends mid-integer"))]
    TruncatedProofInteger {
        /// The theorem being proved.
        theorem: String,
    },
}
