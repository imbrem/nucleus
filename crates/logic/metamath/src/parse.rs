//! A parser for the `.mm` format.
//!
//! Supports the keyword set `$c $v $f $e $d $a $p $.`, scoping `${ ... $}`,
//! comments `$( ... $)`, **`$[ include $]` file inclusion** (via the
//! [`SourceResolver`] trait), and **both** proof encodings — normal
//! (uncompressed) label sequences and the [`Proof::Compressed`] `( labels )
//! LETTERS` form.
//!
//! Metamath is whitespace-delimited and has no nested delimiters at the token
//! level — no string literals, no bracketing below a statement — so there is
//! nothing for a grammar to do underneath a token. The reader is therefore a
//! whitespace split feeding a [`winnow`](covalence_lib_parse::winnow) grammar
//! **over a token slice**, the shape [`covalence_lib_parse`] prescribes for
//! token-oriented formats, rather than a byte-level grammar.
//!
//! Tokens are `&str` borrowed from the source buffer. A database is tens of
//! megabytes of two- and three-character tokens, and owning each one costs more
//! than reading the file: the sink decides what to keep.
//!
//! The reader drives a [`DatabaseSink`]: [`parse`] / [`parse_with_resolver`]
//! build the in-memory [`crate::Database`] (the canonical sink), but the same
//! reader can feed a future HOL-backed Nucleus sink.
//!
//! ## Hostile input
//!
//! Ingesting third-party `.mm` files is the whole point of the crate, so the
//! reader treats everything it reads as hostile rather than as a well-formed
//! database with the odd typo:
//!
//! * **`${ ... $}` nesting is a loop, not recursion.** One stack frame per open
//!   block let a few hundred thousand `${` abort the whole process with a stack
//!   overflow — not a failure mode a validator may inflict on its host. So the
//!   grammar covers a *single* statement and a loop drives it; the nesting
//!   depth is an integer, and the same counter answers "is this `$c` in the
//!   outermost scope?", which the spec requires it to be.
//! * **Tokens are checked against the spec's character classes** — see
//!   [`is_label_char`] and [`is_math_symbol_char`]. Without this a label such as
//!   `tz(e` is read happily and resurfaces much later as a confusing
//!   unknown-label failure, or as nothing at all. Comment *text* is exempt; see
//!   the README.
//! * **`$[ ... $]` is honoured only between statements at the outermost scope**,
//!   as the spec requires, rather than at any point in the token stream.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use covalence_lib_parse::winnow::{
    ModalResult, Parser,
    combinator::{opt, repeat, terminated},
    error::{ErrMode, ParserError},
    stream::{Stream, StreamIsPartial},
    token::any,
};

use crate::database::{Database, DatabaseSink, Proof, SymbolKind};
use crate::error::MmError;
use crate::expr::{Expr, from_symbols};

// ---------------------------------------------------------------------------
// Source resolver trait and implementations
// ---------------------------------------------------------------------------

/// Resolve and read Metamath source files for `$[ filename $]` inclusion.
pub trait SourceResolver {
    /// Resolve and read a source file.
    ///
    /// `filename` — the token between `$[` and `$]`.
    /// `referrer` — canonical key of the file containing the directive (`None`
    /// for the root file).
    ///
    /// Returns `(canonical_key, contents)`. The key is used for deduplication
    /// (a file included twice is read once).
    fn resolve(
        &self,
        filename: &str,
        referrer: Option<&str>,
    ) -> Result<(String, String), std::io::Error>;
}

/// Resolves files from the filesystem, relative to the referrer's directory.
pub struct FileResolver {
    base_dir: PathBuf,
}

impl FileResolver {
    pub fn new(base_dir: impl Into<PathBuf>) -> Self {
        Self {
            base_dir: base_dir.into(),
        }
    }
}

impl SourceResolver for FileResolver {
    fn resolve(
        &self,
        filename: &str,
        referrer: Option<&str>,
    ) -> Result<(String, String), std::io::Error> {
        let dir = match referrer {
            Some(r) => Path::new(r)
                .parent()
                .unwrap_or(self.base_dir.as_path())
                .to_path_buf(),
            None => self.base_dir.clone(),
        };
        let path = dir.join(filename);
        let canonical = path
            .canonicalize()
            .map_err(|e| std::io::Error::new(e.kind(), format!("{}: {e}", path.display())))?;
        let key = canonical.to_string_lossy().into_owned();
        let contents = std::fs::read_to_string(&canonical)?;
        Ok((key, contents))
    }
}

/// In-memory resolver for testing. Looks up filenames in a map.
pub struct MemoryResolver {
    files: std::collections::HashMap<String, String>,
}

impl MemoryResolver {
    pub fn new(files: std::collections::HashMap<String, String>) -> Self {
        Self { files }
    }
}

impl SourceResolver for MemoryResolver {
    fn resolve(
        &self,
        filename: &str,
        _referrer: Option<&str>,
    ) -> Result<(String, String), std::io::Error> {
        let contents = self.files.get(filename).ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!("file not found: {filename}"),
            )
        })?;
        Ok((filename.to_owned(), contents.clone()))
    }
}

// ---------------------------------------------------------------------------
// Token character classes
// ---------------------------------------------------------------------------
//
// The three classes the Metamath spec defines over the ASCII repertoire, kept
// as free predicates so any other reader over the same grammar can reuse them
// verbatim.

/// Whether `c` may appear in a **label**.
///
/// Metamath spec §4.1.1: a label consists of the characters `A`–`Z`, `a`–`z`,
/// `0`–`9`, and `.`, `-`, `_` — nothing else.
pub(crate) fn is_label_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_')
}

/// Whether `c` may appear in a **math symbol**.
///
/// Metamath spec §4.1.1: a math symbol is any sequence of printable ASCII
/// characters other than `$`, which is reserved to start a keyword.
pub(crate) fn is_math_symbol_char(c: char) -> bool {
    c.is_ascii_graphic() && c != '$'
}

/// Check that `token` is a well-formed label. `what` names the position the
/// token was read in (`label`, `proof step label`, ...), so the diagnostic can
/// say where a bad one came from.
pub(crate) fn validate_label(token: &str, what: &str) -> Result<(), MmError> {
    if token.is_empty() || !token.chars().all(is_label_char) {
        return Err(MmError::Parse(format!(
            "invalid {what} `{token}` (labels may use only `A-Z a-z 0-9 . - _`)"
        )));
    }
    Ok(())
}

/// Check that `token` is a well-formed math symbol. `ctx` names the statement
/// it appeared in (a keyword such as `$c`, or an assertion's label).
pub(crate) fn validate_math_symbol(token: &str, ctx: &str) -> Result<(), MmError> {
    if token.is_empty() || !token.chars().all(is_math_symbol_char) {
        return Err(MmError::Parse(format!(
            "invalid math symbol `{token}` in `{ctx}` \
             (math symbols are printable ASCII other than `$`)"
        )));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Public parse API
// ---------------------------------------------------------------------------

/// Parse a `.mm` source string into a [`Database`] (no file inclusion).
pub fn parse(input: &str) -> Result<Database, MmError> {
    let mut db = Database::new();
    parse_into(input, &mut db)?;
    db.finish()
}

/// Parse a `.mm` source string, driving a caller-supplied [`DatabaseSink`] (no
/// file inclusion). Unlike [`parse`] — which builds the in-memory [`Database`] —
/// this lets an *alternative backend* consume the statement stream directly: in
/// particular a HOL-backed sink that constructs kernel theorems as it reads.
/// The reader drives the high-level
/// `DatabaseSink` API; the backend decides what to build.
pub fn parse_into(input: &str, sink: &mut impl DatabaseSink) -> Result<(), MmError> {
    parse_tokens(&tokenize(input)?, sink)
}

/// Like [`parse_into`] but resolving `$[ ... $]` includes via `resolver`.
pub fn parse_into_with_resolver(
    filename: &str,
    resolver: &dyn SourceResolver,
    sink: &mut impl DatabaseSink,
) -> Result<(), MmError> {
    let (key, contents) = resolver
        .resolve(filename, None)
        .map_err(|e| MmError::FileError {
            path: filename.to_owned(),
            message: e.to_string(),
        })?;
    // A database that includes nothing is one buffer, and its tokens borrow it.
    // Whether it does is a question about *tokens*: a `$[` inside a comment is
    // prose, not a directive.
    let tokens = tokenize(&contents)?;
    if !tokens.contains(&"$[") {
        return parse_tokens(&tokens, sink);
    }
    let mut seen = HashSet::new();
    seen.insert(key.clone());
    let mut spliced = String::new();
    let mut scan = IncludeScan::new();
    expand_includes(
        &contents,
        resolver,
        Some(&key),
        &mut seen,
        &mut scan,
        &mut spliced,
    )?;
    parse_tokens(&tokenize(&spliced)?, sink)
}

/// Parse a Metamath database starting from `filename`, resolving `$[ ... $]`
/// includes via `resolver`.
pub fn parse_with_resolver(
    filename: &str,
    resolver: &dyn SourceResolver,
) -> Result<Database, MmError> {
    let mut db = Database::new();
    parse_into_with_resolver(filename, resolver, &mut db)?;
    db.finish()
}

// ---------------------------------------------------------------------------
// File inclusion
// ---------------------------------------------------------------------------

/// The structure the inclusion pass has to track to decide whether a `$[` sits
/// where the spec allows one.
///
/// Both facts are properties of the *database*, not of one file, so the state is
/// threaded through the recursion: an included file may not open an inclusion
/// from inside a `${` its referrer left open.
struct IncludeScan {
    /// `${ ... $}` nesting depth reached so far.
    depth: usize,
    /// Whether the pass sits at a statement boundary: the start of the database,
    /// or just past a `$.`, `${`, or `$}`.
    between_statements: bool,
}

impl IncludeScan {
    /// A fresh scan. A database starts at depth 0, between statements.
    fn new() -> Self {
        Self {
            depth: 0,
            between_statements: true,
        }
    }
}

/// Tokenise `input`, recursively splicing the sources named by `$[ file $]`
/// into `out` — one token per line, comments already stripped.
///
/// Inclusion assembles a database from several buffers, so its tokens cannot
/// all borrow the one the caller read; splicing the *sources* and tokenising
/// the result once keeps them borrowed from a single buffer again. The second
/// tokenisation that costs is paid only where inclusion is actually used, and
/// never by [`parse`].
///
/// Metamath spec §4.1.2 permits an inclusion only *between* statements and only
/// at the outermost scope; anywhere else it is rejected rather than spliced,
/// since a file pasted into the middle of a `$p` or inside a `${` block means
/// something quite different from what it looks like.
fn expand_includes(
    input: &str,
    resolver: &dyn SourceResolver,
    referrer: Option<&str>,
    seen: &mut HashSet<String>,
    scan: &mut IncludeScan,
    out: &mut String,
) -> Result<(), MmError> {
    let raw = tokenize(input)?;
    let mut it = raw.into_iter();
    while let Some(tok) = it.next() {
        // Only a `$` keyword can move the scan, and one byte rules out every
        // label and math symbol — nearly every token in a real database.
        if tok.starts_with('$') {
            match tok {
                "$[" => {
                    if scan.depth > 0 || !scan.between_statements {
                        return Err(MmError::Parse(
                            "`$[` is only allowed between statements at the outermost scope".into(),
                        ));
                    }
                    let filename = it
                        .next()
                        .ok_or_else(|| MmError::Parse("expected filename after `$[`".into()))?;
                    let close = it.next().ok_or_else(|| {
                        MmError::Parse("expected `$]` after include filename".into())
                    })?;
                    if close != "$]" {
                        return Err(MmError::Parse(format!(
                            "expected `$]`, got `{close}` in include"
                        )));
                    }
                    let (key, contents) =
                        resolver
                            .resolve(filename, referrer)
                            .map_err(|e| MmError::FileError {
                                path: filename.to_owned(),
                                message: e.to_string(),
                            })?;
                    if seen.insert(key.clone()) {
                        expand_includes(&contents, resolver, Some(&key), seen, scan, out)?;
                    }
                    continue;
                }
                "${" => {
                    scan.depth += 1;
                    scan.between_statements = true;
                }
                "$}" => {
                    // An unmatched `$}` is the parser's error to report, not ours.
                    scan.depth = scan.depth.saturating_sub(1);
                    scan.between_statements = true;
                }
                "$." => scan.between_statements = true,
                _ => scan.between_statements = false,
            }
        } else {
            scan.between_statements = false;
        }
        out.push_str(tok);
        out.push('\n');
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Tokeniser
// ---------------------------------------------------------------------------

/// Whitespace-tokenise, stripping `$( ... $)` comments. Every token borrows
/// from `input`.
///
/// Only the surviving tokens are held to the spec's character classes; a
/// comment may say anything at all. See the README for why that deviation is
/// deliberate.
fn tokenize(input: &str) -> Result<Vec<&str>, MmError> {
    let mut out = Vec::new();
    let mut raw = input.split_ascii_whitespace();
    while let Some(tok) = raw.next() {
        if tok == "$(" {
            // Consume to matching `$)`.
            let mut closed = false;
            for t in raw.by_ref() {
                if t == "$)" {
                    closed = true;
                    break;
                }
            }
            if !closed {
                return Err(MmError::Parse("unterminated comment `$(`".into()));
            }
            continue;
        }
        if tok == "$)" {
            return Err(MmError::Parse("unmatched `$)`".into()));
        }
        out.push(tok);
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Grammar: token stream → DatabaseSink
// ---------------------------------------------------------------------------

/// A stream of borrowed `.mm` tokens.
///
/// The grammar is written against winnow's [`Stream`] rather than against
/// `&[&str]`, so a reader that tokenises differently — lazily, or out of a
/// memory-mapped file — reuses it without touching a combinator.
trait TokenStream<'a>: Stream<Token = &'a str> + StreamIsPartial {}

impl<'a, I: Stream<Token = &'a str> + StreamIsPartial> TokenStream<'a> for I {}

/// The grammar's error.
///
/// Every diagnostic the reader commits to rides in `Fatal`; `NoMatch` is a leaf
/// parser saying only "not mine", which is how a `repeat` ends and therefore
/// the *common* case, not an exceptional one — so it carries no payload and
/// costs no allocation. The diagnostic is boxed for the same reason: a fault is
/// returned by value from every parser in the grammar, and an [`MmError`] is
/// wide enough that carrying one inline would cost the succeeding path too.
#[derive(Debug)]
enum Fault {
    NoMatch,
    Fatal(Box<MmError>),
}

impl<I: Stream> ParserError<I> for Fault {
    type Inner = Self;

    fn from_input(_input: &I) -> Self {
        Fault::NoMatch
    }

    fn into_inner(self) -> Result<Self::Inner, Self> {
        Ok(self)
    }
}

/// Commit to `error`: the reader has read enough to know the input is wrong, so
/// no other branch of the grammar is worth trying.
fn fatal(error: MmError) -> ErrMode<Fault> {
    ErrMode::Cut(Fault::Fatal(Box::new(error)))
}

/// Commit to the parse diagnostic `message`.
fn reject(message: String) -> ErrMode<Fault> {
    fatal(MmError::Parse(message))
}

/// The [`MmError`] a grammar failure carries.
///
/// Winnow's error mode stops here: it is how this module's parsers talk to each
/// other, and the crate's callers see [`MmError`] alone. Only the leaves
/// backtrack, and each of them sits inside a `repeat` or an `opt` that consumes
/// the backtrack, so what arrives is a committed diagnostic.
fn diagnostic(fault: ErrMode<Fault>) -> MmError {
    match fault {
        ErrMode::Cut(Fault::Fatal(error)) | ErrMode::Backtrack(Fault::Fatal(error)) => *error,
        _ => MmError::Parse("unexpected end of input".into()),
    }
}

/// Read every statement in `tokens` into `sink`.
///
/// `${ ... $}` nesting is a loop rather than one recursive parser call per
/// block: `.mm` files are untrusted input, and a stack frame per open block
/// turned a few hundred thousand `${` into a process-killing stack overflow.
/// `depth` doubles as the answer to "may a `$c` appear here?" — the spec
/// confines constant declarations to the outermost scope.
///
/// A `$}` at depth 0 is an unmatched-scope error, and a `${` still open at end
/// of input is an unclosed-scope error.
fn parse_tokens(tokens: &[&str], sink: &mut impl DatabaseSink) -> Result<(), MmError> {
    let mut input = tokens;
    let mut depth: usize = 0;
    while !input.is_empty() {
        statement(&mut input, &mut depth, sink).map_err(diagnostic)?;
    }
    if depth > 0 {
        return Err(MmError::Parse("unclosed `${`".into()));
    }
    Ok(())
}

/// Read the one statement `input` starts with into `sink`.
fn statement<'a, I: TokenStream<'a>>(
    input: &mut I,
    depth: &mut usize,
    sink: &mut impl DatabaseSink,
) -> ModalResult<(), Fault> {
    match any.parse_next(input)? {
        "$}" if *depth == 0 => Err(reject("unmatched `$}`".into())),
        "$}" => {
            *depth -= 1;
            sink.pop_scope().map_err(fatal)
        }
        "${" => {
            *depth += 1;
            sink.push_scope();
            Ok(())
        }
        "$c" if *depth > 0 => Err(reject("`$c` is only allowed in the outermost scope".into())),
        "$c" => {
            let symbols = symbol_list("$c").parse_next(input)?;
            sink.declare(SymbolKind::Constant, &symbols).map_err(fatal)
        }
        "$v" => {
            let symbols = symbol_list("$v").parse_next(input)?;
            sink.declare(SymbolKind::Variable, &symbols).map_err(fatal)
        }
        "$d" => {
            let vars = symbol_list("$d").parse_next(input)?;
            // Distinctness is a relation between two variables: a `$d` naming
            // fewer restricts nothing, so accepting one silently turns a typo
            // into a hypothesis that was never imposed.
            if vars.len() < 2 {
                return Err(reject(format!(
                    "`$d` needs two or more variables, got {}",
                    vars.len()
                )));
            }
            sink.add_disjoint(&vars).map_err(fatal)
        }
        kw if kw.starts_with('$') => Err(reject(format!(
            "unexpected keyword `{kw}` (expected a label or `$c/$v/$d/${{/$}}`)"
        ))),
        // A label introduces a $f/$e/$a/$p statement.
        label => labelled(input, label, sink),
    }
}

/// Read the `$f`, `$e`, `$a` or `$p` statement introduced by `label`.
fn labelled<'a, I: TokenStream<'a>>(
    input: &mut I,
    label: &'a str,
    sink: &mut impl DatabaseSink,
) -> ModalResult<(), Fault> {
    validate_label(label, "label").map_err(fatal)?;
    let Some(kw) = opt(any).parse_next(input)? else {
        return Err(reject(format!("expected keyword after label `{label}`")));
    };
    match kw {
        "$f" => {
            let body = symbol_list("$f").parse_next(input)?;
            if body.len() != 2 {
                return Err(reject(format!(
                    "`{label}` $f must be `typecode var`, got {body:?}"
                )));
            }
            sink.add_float(label, body[0], body[1]).map_err(fatal)
        }
        "$e" => {
            let symbols = symbol_list("$e").parse_next(input)?;
            let expr = expression(label, &symbols).map_err(fatal)?;
            sink.add_essential(label, expr).map_err(fatal)
        }
        "$a" => assertion(input, label, false, sink),
        "$p" => assertion(input, label, true, sink),
        other => Err(reject(format!(
            "unexpected keyword `{other}` after label `{label}`"
        ))),
    }
}

/// Read the conclusion of the assertion `label`, and — for a `$p` — its proof.
fn assertion<'a, I: TokenStream<'a>>(
    input: &mut I,
    label: &'a str,
    provable: bool,
    sink: &mut impl DatabaseSink,
) -> ModalResult<(), Fault> {
    let symbols: Vec<&'a str> = repeat(0.., math_symbol(label)).parse_next(input)?;
    let proof = match opt(any).parse_next(input)? {
        // A `$p` whose conclusion just stops is a theorem nobody proved, which
        // is not the same claim as the `$a` it now looks like.
        Some("$.") if provable => {
            return Err(reject(format!("`{label}` $p has no proof (missing `$=`)")));
        }
        Some("$.") => None,
        Some("$=") if provable => Some(proof(input, label)?),
        Some("$=") => {
            return Err(reject(format!(
                "`{label}` is a `$a` axiom and cannot have a proof (`$=`)"
            )));
        }
        Some(t) => return Err(reject(format!("unexpected `{t}` in `{label}`"))),
        None => return Err(reject(format!("unterminated `{label}`"))),
    };
    let conclusion = expression(label, &symbols).map_err(fatal)?;
    sink.add_assertion(label, conclusion, proof).map_err(fatal)
}

/// Read a proof body (the part after `$=`): either a normal label sequence up
/// to `$.`, or a compressed `( labels ) LETTERS $.` block.
fn proof<'a, I: TokenStream<'a>>(input: &mut I, label: &'a str) -> ModalResult<Proof, Fault> {
    // A compressed proof announces itself with the `(` opening its label block.
    if opt(any.verify(|t: &str| t == "("))
        .parse_next(input)?
        .is_some()
    {
        return compressed_proof(input, label);
    }
    terminated(repeat(0.., proof_step(label)), end_of_proof(label))
        .map(Proof::Normal)
        .parse_next(input)
}

/// Read a compressed proof: `( label1 label2 ... ) LETTERS... $.`, with the `(`
/// already consumed.
fn compressed_proof<'a, I: TokenStream<'a>>(
    input: &mut I,
    label: &'a str,
) -> ModalResult<Proof, Fault> {
    // Label block until `)`. Every entry is a label, so a missing `)` is caught
    // at the first keyword instead of swallowing the rest of the database as
    // proof text.
    let mut labels = Vec::new();
    loop {
        match opt(any).parse_next(input)? {
            Some(")") => break,
            Some(t) => {
                validate_label(t, "compressed-proof label").map_err(fatal)?;
                labels.push(t.to_owned());
            }
            None => {
                return Err(reject(format!(
                    "unterminated compressed-proof label block in `{label}`"
                )));
            }
        }
    }
    // Letter block: concatenate all tokens until `$.`. Its alphabet (`A`–`Z`
    // plus `?`) is the decoder's business, in `verify`.
    let mut letters = Vec::new();
    loop {
        match opt(any).parse_next(input)? {
            Some("$.") => break,
            Some(t) => letters.extend_from_slice(t.as_bytes()),
            None => {
                return Err(reject(format!(
                    "unterminated compressed-proof letter block in `{label}`"
                )));
            }
        }
    }
    Ok(Proof::Compressed { labels, letters })
}

/// `<math symbol>... $.`: the body of a `$c`, `$v`, `$d`, `$f` or `$e`.
///
/// How many symbols each of those admits — two for a `$f`, two or more for a
/// `$d` — is the caller's to say, since only the caller knows which it read.
fn symbol_list<'a, I: TokenStream<'a>>(
    ctx: &'a str,
) -> impl Parser<I, Vec<&'a str>, ErrMode<Fault>> {
    terminated(repeat(0.., math_symbol(ctx)), end_of_statement(ctx))
}

/// One math symbol: any token outside the `$` keyword space.
///
/// Backtracking on a keyword is what ends a symbol list. A token that is no
/// keyword but no legal symbol either cuts instead: `p$h` is a typo inside the
/// statement being read, not the start of the next one.
fn math_symbol<'a, I: TokenStream<'a>>(ctx: &'a str) -> impl Parser<I, &'a str, ErrMode<Fault>> {
    move |input: &mut I| {
        let token = any
            .verify(|token: &str| !token.starts_with('$'))
            .parse_next(input)?;
        validate_math_symbol(token, ctx).map_err(fatal)?;
        Ok(token)
    }
}

/// The `$.` closing a symbol list.
///
/// Whatever stopped [`math_symbol`] is named here rather than reported as a
/// bare "expected `$.`", which leaves the author to guess which token the
/// reader objected to.
fn end_of_statement<'a, I: TokenStream<'a>>(ctx: &'a str) -> impl Parser<I, (), ErrMode<Fault>> {
    move |input: &mut I| match opt(any).parse_next(input)? {
        Some("$.") => Ok(()),
        Some(t) => Err(reject(format!("unexpected `{t}` in {ctx} (expected `$.`)"))),
        None => Err(reject(format!("unterminated {ctx}"))),
    }
}

/// One step of a normal proof: the label of an assertion or hypothesis.
fn proof_step<'a, I: TokenStream<'a>>(label: &'a str) -> impl Parser<I, String, ErrMode<Fault>> {
    move |input: &mut I| {
        let token = any
            .verify(|token: &str| !token.starts_with('$'))
            .parse_next(input)?;
        // `?` is the placeholder for a step nobody has supplied. A database may
        // carry one; a proof this crate accepts may not.
        if token == "?" {
            return Err(reject(format!(
                "`{label}` contains an incomplete-proof placeholder `?`"
            )));
        }
        validate_label(token, "proof step label").map_err(fatal)?;
        Ok(token.to_owned())
    }
}

/// The `$.` closing a normal proof.
fn end_of_proof<'a, I: TokenStream<'a>>(label: &'a str) -> impl Parser<I, (), ErrMode<Fault>> {
    move |input: &mut I| match opt(any).parse_next(input)? {
        Some("$.") => Ok(()),
        Some(t) => Err(reject(format!("unexpected `{t}` in proof of `{label}`"))),
        None => Err(reject(format!("unterminated proof of `{label}`"))),
    }
}

/// Build the [`Expr`] a `$e`, `$a` or `$p` states, whose first symbol is the
/// typecode.
fn expression(label: &str, symbols: &[&str]) -> Result<Expr, MmError> {
    from_symbols(symbols.iter().copied()).ok_or_else(|| MmError::MalformedExpr {
        label: label.to_string(),
        message: "expression is empty (needs at least a typecode)".into(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{render, typecode_of};

    #[test]
    fn parse_constants_and_vars() {
        let db = parse("$c wff |- $. $v ph $.").unwrap();
        assert!(db.is_symbol("wff"));
        assert!(!db.is_variable("wff"));
        assert!(db.is_variable("ph"));
    }

    #[test]
    fn comments_skipped() {
        let db = parse("$( hello $) $c a $.").unwrap();
        assert!(db.is_symbol("a"));
    }

    #[test]
    fn float_parsed() {
        let db = parse("$c wff $. $v ph $. wph $f wff ph $.").unwrap();
        let stmt = db.statement_by_label("wph").unwrap();
        assert!(matches!(stmt, crate::database::Statement::Float(_)));
    }

    #[test]
    fn axiom_conclusion_is_expr() {
        let db = parse("$c term 0 $. tze $a term 0 $.").unwrap();
        let a = db.assertions().next().unwrap();
        assert_eq!(typecode_of(&a.conclusion), Some("term"));
        assert_eq!(render(&a.conclusion), "term 0");
    }

    #[test]
    fn unterminated_comment_errors() {
        assert!(parse("$( oops").is_err());
    }

    #[test]
    fn compressed_proof_parsed() {
        let src = "$c term 0 $. tze $a term 0 $. th $p term 0 $= ( tze ) AB $.";
        let db = parse(src).unwrap();
        let crate::database::Statement::Assert(a) = db.statement_by_label("th").unwrap() else {
            panic!("expected assertion");
        };
        match &a.proof {
            Some(Proof::Compressed { labels, letters }) => {
                assert_eq!(labels, &["tze"]);
                assert_eq!(letters, b"AB");
            }
            other => panic!("expected compressed proof, got {other:?}"),
        }
    }

    #[test]
    fn duplicate_label_rejected() {
        let src = "$c term $. $v t $. tt $f term t $. tt $f term t $.";
        assert!(matches!(parse(src), Err(MmError::DuplicateLabel(_))));
    }

    #[test]
    fn unmatched_scope_close_errors() {
        assert!(parse("$c a $. $}").is_err());
    }

    // --- file inclusion -----------------------------------------------------

    fn mem(files: &[(&str, &str)]) -> MemoryResolver {
        MemoryResolver::new(
            files
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect(),
        )
    }

    #[test]
    fn include_two_files() {
        let resolver = mem(&[
            ("root.mm", "$[ defs.mm $] wph $f wff ph $."),
            ("defs.mm", "$c wff $. $v ph $."),
        ]);
        let db = parse_with_resolver("root.mm", &resolver).unwrap();
        assert!(db.is_symbol("wff"));
        assert!(db.statement_by_label("wph").is_some());
    }

    #[test]
    fn include_duplicate_skipped() {
        let resolver = mem(&[("root.mm", "$[ a.mm $] $[ a.mm $]"), ("a.mm", "$c wff $.")]);
        let db = parse_with_resolver("root.mm", &resolver).unwrap();
        assert!(db.is_symbol("wff"));
    }

    #[test]
    fn include_nested() {
        let resolver = mem(&[
            ("root.mm", "$[ a.mm $] wph $f wff ph $."),
            ("a.mm", "$[ b.mm $] $v ph $."),
            ("b.mm", "$c wff $."),
        ]);
        let db = parse_with_resolver("root.mm", &resolver).unwrap();
        assert!(db.is_symbol("wff"));
        assert!(db.statement_by_label("wph").is_some());
    }

    #[test]
    fn include_unknown_file_error() {
        let resolver = mem(&[("root.mm", "$[ missing.mm $]")]);
        let err = parse_with_resolver("root.mm", &resolver).unwrap_err();
        assert!(
            matches!(err, MmError::FileError { ref path, .. } if path == "missing.mm"),
            "expected FileError for missing.mm, got: {err}"
        );
    }
}
