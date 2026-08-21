//! A parser for the `.mm` format.
//!
//! Supports the keyword set `$c $v $f $e $d $a $p $.`, scoping `${ ... $}`,
//! comments `$( ... $)`, **`$[ include $]` file inclusion** (via the
//! [`SourceResolver`] trait), and **both** proof encodings — normal
//! (uncompressed) label sequences and the [`Proof::Compressed`] `( labels )
//! LETTERS` form.
//!
//! Metamath tokenisation is whitespace-separated tokens (the language has no
//! string literals or nested delimiters at the token level), so the lexer is a
//! hand-rolled scanner.
//!
//! The reader drives a [`DatabaseSink`]: [`parse`] / [`parse_with_resolver`]
//! build the in-memory [`crate::Database`] (the canonical sink), but the same
//! reader can feed a future HOL-backed Nucleus sink.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

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
// Public parse API
// ---------------------------------------------------------------------------

/// Parse a `.mm` source string into a [`Database`] (no file inclusion).
pub fn parse(input: &str) -> Result<Database, MmError> {
    let tokens = tokenize(input)?;
    let mut db = Database::new();
    parse_tokens(&tokens, &mut db)?;
    db.finish()
}

/// Parse a `.mm` source string, driving a caller-supplied [`DatabaseSink`] (no
/// file inclusion). Unlike [`parse`] — which builds the in-memory [`Database`] —
/// this lets an *alternative backend* consume the statement stream directly: in
/// particular a HOL-backed sink that constructs kernel theorems as it reads.
/// The reader drives the high-level
/// `DatabaseSink` API; the backend decides what to build.
pub fn parse_into(input: &str, sink: &mut impl DatabaseSink) -> Result<(), MmError> {
    let tokens = tokenize(input)?;
    parse_tokens(&tokens, sink)
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
    let mut seen = HashSet::new();
    seen.insert(key.clone());
    let mut tokens = Vec::new();
    expand_includes(&contents, resolver, Some(&key), &mut seen, &mut tokens)?;
    parse_tokens(&tokens, sink)
}

/// Parse a Metamath database starting from `filename`, resolving `$[ ... $]`
/// includes via `resolver`.
pub fn parse_with_resolver(
    filename: &str,
    resolver: &dyn SourceResolver,
) -> Result<Database, MmError> {
    let (key, contents) = resolver
        .resolve(filename, None)
        .map_err(|e| MmError::FileError {
            path: filename.to_owned(),
            message: e.to_string(),
        })?;
    let mut seen = HashSet::new();
    seen.insert(key.clone());
    let mut tokens = Vec::new();
    expand_includes(&contents, resolver, Some(&key), &mut seen, &mut tokens)?;
    let mut db = Database::new();
    parse_tokens(&tokens, &mut db)?;
    db.finish()
}

/// Tokenise `input`, recursively expanding `$[ file $]` includes into `out`.
fn expand_includes(
    input: &str,
    resolver: &dyn SourceResolver,
    referrer: Option<&str>,
    seen: &mut HashSet<String>,
    out: &mut Vec<String>,
) -> Result<(), MmError> {
    let raw = tokenize(input)?;
    let mut it = raw.into_iter();
    while let Some(tok) = it.next() {
        if tok == "$[" {
            let filename = it
                .next()
                .ok_or_else(|| MmError::Parse("expected filename after `$[`".into()))?;
            let close = it
                .next()
                .ok_or_else(|| MmError::Parse("expected `$]` after include filename".into()))?;
            if close != "$]" {
                return Err(MmError::Parse(format!(
                    "expected `$]`, got `{close}` in include"
                )));
            }
            let (key, contents) =
                resolver
                    .resolve(&filename, referrer)
                    .map_err(|e| MmError::FileError {
                        path: filename.clone(),
                        message: e.to_string(),
                    })?;
            if seen.insert(key.clone()) {
                expand_includes(&contents, resolver, Some(&key), seen, out)?;
            }
        } else {
            out.push(tok);
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Tokeniser
// ---------------------------------------------------------------------------

/// Whitespace-tokenise, stripping `$( ... $)` comments.
fn tokenize(input: &str) -> Result<Vec<String>, MmError> {
    let mut out = Vec::new();
    let mut raw = input.split_ascii_whitespace().peekable();
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
        out.push(tok.to_string());
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Parser: token stream → DatabaseSink
// ---------------------------------------------------------------------------

/// Parse the whole token stream into `sink`.
fn parse_tokens(tokens: &[String], sink: &mut impl DatabaseSink) -> Result<(), MmError> {
    let mut p = Parser {
        toks: tokens,
        pos: 0,
    };
    p.parse_block(sink, true)
}

struct Parser<'a> {
    toks: &'a [String],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&'a str> {
        self.toks.get(self.pos).map(String::as_str)
    }

    fn next(&mut self) -> Option<&'a str> {
        let t = self.toks.get(self.pos).map(String::as_str);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    /// Parse statements until end of input or a closing `$}`. `top_level` is
    /// true for the outermost block; a `$}` there is an unmatched-scope error.
    fn parse_block(
        &mut self,
        sink: &mut impl DatabaseSink,
        top_level: bool,
    ) -> Result<(), MmError> {
        while let Some(tok) = self.peek() {
            match tok {
                "$}" if top_level => {
                    return Err(MmError::Parse("unmatched `$}`".into()));
                }
                "$}" => return Ok(()),
                "${" => {
                    self.next();
                    sink.push_scope();
                    self.parse_block(sink, false)?;
                    match self.next() {
                        Some("$}") => sink.pop_scope()?,
                        _ => return Err(MmError::Parse("unclosed `${`".into())),
                    }
                }
                "$c" => {
                    self.next();
                    let syms = self.read_until_dot("$c")?;
                    sink.declare(SymbolKind::Constant, &str_refs(&syms))?;
                }
                "$v" => {
                    self.next();
                    let syms = self.read_until_dot("$v")?;
                    sink.declare(SymbolKind::Variable, &str_refs(&syms))?;
                }
                "$d" => {
                    self.next();
                    let syms = self.read_until_dot("$d")?;
                    sink.add_disjoint(&str_refs(&syms))?;
                }
                kw if kw.starts_with('$') => {
                    return Err(MmError::Parse(format!(
                        "unexpected keyword `{kw}` (expected a label or `$c/$v/$d/${{/$}}`)"
                    )));
                }
                _ => {
                    // A label introduces a $f/$e/$a/$p statement.
                    let label = self.next().unwrap().to_string();
                    let kw = self.next().ok_or_else(|| {
                        MmError::Parse(format!("expected keyword after label `{label}`"))
                    })?;
                    match kw {
                        "$f" => self.parse_float(sink, label)?,
                        "$e" => self.parse_essential(sink, label)?,
                        "$a" => self.parse_assert(sink, label, false)?,
                        "$p" => self.parse_assert(sink, label, true)?,
                        other => {
                            return Err(MmError::Parse(format!(
                                "unexpected keyword `{other}` after label `{label}`"
                            )));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Read tokens up to and consuming `$.`.
    fn read_until_dot(&mut self, ctx: &str) -> Result<Vec<String>, MmError> {
        let mut out = Vec::new();
        loop {
            match self.next() {
                Some("$.") => return Ok(out),
                Some(t) if t.starts_with('$') => {
                    return Err(MmError::Parse(format!(
                        "unexpected `{t}` in {ctx} (expected `$.`)"
                    )));
                }
                Some(t) => out.push(t.to_string()),
                None => return Err(MmError::Parse(format!("unterminated {ctx}"))),
            }
        }
    }

    fn parse_float(&mut self, sink: &mut impl DatabaseSink, label: String) -> Result<(), MmError> {
        let body = self.read_until_dot("$f")?;
        if body.len() != 2 {
            return Err(MmError::Parse(format!(
                "`{label}` $f must be `typecode var`, got {body:?}"
            )));
        }
        sink.add_float(&label, &body[0], &body[1])
    }

    fn parse_essential(
        &mut self,
        sink: &mut impl DatabaseSink,
        label: String,
    ) -> Result<(), MmError> {
        let syms = self.read_until_dot("$e")?;
        let expr = self.make_expr(&label, &syms)?;
        sink.add_essential(&label, expr)
    }

    fn parse_assert(
        &mut self,
        sink: &mut impl DatabaseSink,
        label: String,
        provable: bool,
    ) -> Result<(), MmError> {
        // Read the conclusion symbols up to `$.` (axiom) or `$=` (theorem).
        let mut syms = Vec::new();
        let proof: Option<Proof> = loop {
            match self.next() {
                Some("$.") => break None,
                Some("$=") if provable => {
                    break Some(self.read_proof(&label)?);
                }
                Some("$=") => {
                    return Err(MmError::Parse(format!(
                        "`{label}` is a `$a` axiom and cannot have a proof (`$=`)"
                    )));
                }
                Some(t) if t.starts_with('$') => {
                    return Err(MmError::Parse(format!("unexpected `{t}` in `{label}`")));
                }
                Some(t) => syms.push(t.to_string()),
                None => return Err(MmError::Parse(format!("unterminated `{label}`"))),
            }
        };
        if provable && proof.is_none() {
            return Err(MmError::Parse(format!(
                "`{label}` $p has no proof (missing `$=`)"
            )));
        }
        let conclusion = self.make_expr(&label, &syms)?;
        sink.add_assertion(&label, conclusion, proof)
    }

    /// Read a proof body (the part after `$=`): either a normal label sequence
    /// up to `$.`, or a compressed `( labels ) LETTERS $.` block.
    fn read_proof(&mut self, label: &str) -> Result<Proof, MmError> {
        if self.peek() == Some("(") {
            return self.read_compressed_proof(label);
        }
        let mut labels = Vec::new();
        loop {
            match self.next() {
                Some("$.") => return Ok(Proof::Normal(labels)),
                Some("?") => {
                    return Err(MmError::Parse(format!(
                        "`{label}` contains an incomplete-proof placeholder `?`"
                    )));
                }
                Some(t) if t.starts_with('$') => {
                    return Err(MmError::Parse(format!(
                        "unexpected `{t}` in proof of `{label}`"
                    )));
                }
                Some(t) => labels.push(t.to_string()),
                None => return Err(MmError::Parse(format!("unterminated proof of `{label}`"))),
            }
        }
    }

    /// Read a compressed proof: `( label1 label2 ... ) LETTERS... $.` (the `(`
    /// is at the current position).
    fn read_compressed_proof(&mut self, label: &str) -> Result<Proof, MmError> {
        // Consume `(`.
        self.next();
        // Label block until `)`.
        let mut labels = Vec::new();
        loop {
            match self.next() {
                Some(")") => break,
                Some(t) => labels.push(t.to_string()),
                None => {
                    return Err(MmError::Parse(format!(
                        "unterminated compressed-proof label block in `{label}`"
                    )));
                }
            }
        }
        // Letter block: concatenate all tokens until `$.`.
        let mut letters = Vec::new();
        loop {
            match self.next() {
                Some("$.") => break,
                Some(t) => letters.extend_from_slice(t.as_bytes()),
                None => {
                    return Err(MmError::Parse(format!(
                        "unterminated compressed-proof letter block in `{label}`"
                    )));
                }
            }
        }
        Ok(Proof::Compressed { labels, letters })
    }

    /// Build an [`Expr`] from a symbol list (the first being the typecode),
    /// validating it is non-empty.
    fn make_expr(&self, label: &str, syms: &[String]) -> Result<Expr, MmError> {
        from_symbols(syms.iter().map(String::as_str)).ok_or_else(|| MmError::MalformedExpr {
            label: label.to_string(),
            message: "expression is empty (needs at least a typecode)".into(),
        })
    }
}

/// Borrow a `&[String]` as a `Vec<&str>` for the `DatabaseSink` API.
fn str_refs(v: &[String]) -> Vec<&str> {
    v.iter().map(String::as_str).collect()
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
