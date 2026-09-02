//! Reader for the pinned `lean4export` 3.1.0 schema.

use std::collections::HashSet;
use std::io::BufRead;

use covalence_lib_error::snafu::Snafu;
use covalence_lib_json::{Map, Value};

use crate::stream::{self, DenseTable, ForEachError};

/// The only accepted `lean4export` format version.
pub const FORMAT_VERSION: &str = "3.1.0";

/// Version provenance from the required first record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Metadata {
    /// Exporter program name (normally `lean4export`).
    pub exporter_name: String,
    /// Exporter implementation version.
    pub exporter_version: String,
    /// Lean version that produced the stream.
    pub lean_version: String,
    /// Lean source revision reported by the producing toolchain.
    pub lean_githash: String,
    /// NDJSON schema version.
    pub format_version: String,
}

/// Validated format-level contents of one export stream.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Export {
    /// Required stream metadata.
    pub metadata: Metadata,
    /// Number of explicit name rows (excluding implicit anonymous name zero).
    pub names: usize,
    /// Number of explicit universe-level rows (excluding implicit level zero).
    pub levels: usize,
    /// Number of expression rows.
    pub expressions: usize,
    /// Number of declarations, counting members of an inductive group.
    pub declarations: usize,
}

/// A rejected `lean4export` stream.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// NDJSON framing or JSON syntax was invalid.
    #[snafu(display("could not frame Lean export: {source}"))]
    Framing {
        /// Generic NDJSON failure.
        source: stream::Error,
    },
    /// The first record was absent.
    #[snafu(display("Lean export has no metadata record"))]
    MissingMetadata,
    /// A second metadata record appeared.
    #[snafu(display("unexpected Lean export metadata on line {line}"))]
    RepeatedMetadata {
        /// One-based line number.
        line: usize,
    },
    /// The pinned format version did not match.
    #[snafu(display(
        "unsupported Lean export format {found:?} on line {line}, expected {FORMAT_VERSION}"
    ))]
    Version {
        /// One-based line number.
        line: usize,
        /// Version in the input.
        found: String,
    },
    /// A record or required field had an unsupported shape.
    #[snafu(display("invalid Lean export record on line {line}: {reason}"))]
    Invalid {
        /// One-based line number.
        line: usize,
        /// Stable description of the violated schema rule.
        reason: String,
    },
    /// The record kind is not in version 3.1.0.
    #[snafu(display("unsupported Lean export record {kind:?} on line {line}"))]
    Unsupported {
        /// One-based line number.
        line: usize,
        /// Top-level record key.
        kind: String,
    },
    /// An explicit table index was not the next dense position.
    #[snafu(display("non-dense {table} index {found} on line {line}, expected {expected}"))]
    Index {
        /// One-based line number.
        line: usize,
        /// Table namespace (`in`, `il`, or `ie`).
        table: &'static str,
        /// Index from the input.
        found: usize,
        /// Only accepted next index.
        expected: usize,
    },
    /// A table reference did not point to an already established row.
    #[snafu(display("unknown or forward {table} reference {index} in {field} on line {line}"))]
    Reference {
        /// One-based line number.
        line: usize,
        /// Referenced table namespace.
        table: &'static str,
        /// Field carrying the reference.
        field: String,
        /// Referenced index.
        index: usize,
    },
    /// Two declarations introduced the same name index.
    #[snafu(display("duplicate declaration name index {index} on line {line}"))]
    DuplicateDeclaration {
        /// One-based line number.
        line: usize,
        /// Repeated name index.
        index: usize,
    },
}

struct State {
    metadata: Option<Metadata>,
    names: DenseTable<()>,
    levels: DenseTable<()>,
    expressions: DenseTable<()>,
    declared: HashSet<usize>,
    declarations: usize,
}

impl State {
    fn new() -> Self {
        Self {
            metadata: None,
            names: DenseTable::with_prefix(vec![()]),
            levels: DenseTable::with_prefix(vec![()]),
            expressions: DenseTable::with_prefix(Vec::new()),
            declared: HashSet::new(),
            declarations: 0,
        }
    }

    fn visit(&mut self, line: usize, value: &Value) -> Result<(), Error> {
        let object = object(value, line, "record")?;
        if self.metadata.is_none() {
            self.metadata = Some(parse_metadata(object, line)?);
            return Ok(());
        }
        if object.contains_key("meta") {
            return Err(Error::RepeatedMetadata { line });
        }
        if object.len() == 2 && object.contains_key("in") {
            return self.name(line, object);
        }
        if object.len() == 2 && object.contains_key("il") {
            return self.level(line, object);
        }
        if object.len() == 2 && object.contains_key("ie") {
            return self.expression(line, object);
        }
        if object.len() != 1 {
            return invalid(
                line,
                "record must have one declaration key or one kind plus one index",
            );
        }
        let (kind, body) = object.iter().next().expect("one key checked");
        match kind.as_str() {
            "axiom" | "def" | "opaque" | "thm" | "quot" => {
                self.declaration(line, kind, object_value(body, line, kind)?)
            }
            "inductive" => self.inductive(line, object_value(body, line, kind)?),
            _ => Err(Error::Unsupported {
                line,
                kind: kind.clone(),
            }),
        }
    }

    fn name(&mut self, line: usize, record: &Map<String, Value>) -> Result<(), Error> {
        let index = usize_value(field(record, "in", line)?, line, "in")?;
        let (kind, body) = other(record, "in", line)?;
        let data = object_value(body, line, kind)?;
        match kind {
            "str" => {
                self.name_ref(line, data, "pre")?;
                string(field(data, "str", line)?, line, "str")?;
            }
            "num" => {
                self.name_ref(line, data, "pre")?;
                usize_value(field(data, "i", line)?, line, "i")?;
            }
            _ => {
                return Err(Error::Unsupported {
                    line,
                    kind: kind.to_owned(),
                });
            }
        }
        insert(&mut self.names, line, "in", index)
    }

    fn level(&mut self, line: usize, record: &Map<String, Value>) -> Result<(), Error> {
        let index = usize_value(field(record, "il", line)?, line, "il")?;
        let (kind, body) = other(record, "il", line)?;
        match kind {
            "succ" => self.level_ref_value(line, body, "succ")?,
            "max" | "imax" => self.level_refs(line, body, kind)?,
            "param" => self.name_ref_value(line, body, "param")?,
            _ => {
                return Err(Error::Unsupported {
                    line,
                    kind: kind.to_owned(),
                });
            }
        }
        insert(&mut self.levels, line, "il", index)
    }

    fn expression(&mut self, line: usize, record: &Map<String, Value>) -> Result<(), Error> {
        let index = usize_value(field(record, "ie", line)?, line, "ie")?;
        let (kind, body) = other(record, "ie", line)?;
        match kind {
            "bvar" => {
                usize_value(body, line, "bvar")?;
            }
            "sort" => self.level_ref_value(line, body, "sort")?,
            "const" => {
                let data = object_value(body, line, "const")?;
                self.name_ref(line, data, "name")?;
                self.level_ref_array(line, field(data, "us", line)?, "us")?;
            }
            "app" => self.expr_fields(line, body, &["fn", "arg"])?,
            "lam" | "forallE" => {
                let data = object_value(body, line, kind)?;
                self.name_ref(line, data, "name")?;
                self.expr_ref(line, data, "type")?;
                self.expr_ref(line, data, "body")?;
                one_of(
                    field(data, "binderInfo", line)?,
                    line,
                    "binderInfo",
                    &["default", "implicit", "strictImplicit", "instImplicit"],
                )?;
            }
            "letE" => {
                let data = object_value(body, line, kind)?;
                self.name_ref(line, data, "name")?;
                for name in ["type", "value", "body"] {
                    self.expr_ref(line, data, name)?;
                }
                boolean(field(data, "nondep", line)?, line, "nondep")?;
            }
            "proj" => {
                let data = object_value(body, line, kind)?;
                self.name_ref(line, data, "typeName")?;
                usize_value(field(data, "idx", line)?, line, "idx")?;
                self.expr_ref(line, data, "struct")?;
            }
            "natVal" | "strVal" => {
                string(body, line, kind)?;
            }
            "mdata" => {
                let data = object_value(body, line, kind)?;
                self.expr_ref(line, data, "expr")?;
                object(field(data, "data", line)?, line, "data")?;
            }
            _ => {
                return Err(Error::Unsupported {
                    line,
                    kind: kind.to_owned(),
                });
            }
        }
        insert(&mut self.expressions, line, "ie", index)
    }

    fn declaration(
        &mut self,
        line: usize,
        kind: &str,
        data: &Map<String, Value>,
    ) -> Result<(), Error> {
        let name = self.common_decl(line, data)?;
        match kind {
            "axiom" => {
                boolean(field(data, "isUnsafe", line)?, line, "isUnsafe")?;
            }
            "def" => {
                self.expr_ref(line, data, "value")?;
                validate_hints(field(data, "hints", line)?, line)?;
                one_of(
                    field(data, "safety", line)?,
                    line,
                    "safety",
                    &["unsafe", "safe", "partial"],
                )?;
                self.name_ref_array(line, field(data, "all", line)?, "all")?;
            }
            "opaque" => {
                self.expr_ref(line, data, "value")?;
                self.name_ref_array(line, field(data, "all", line)?, "all")?;
                boolean(field(data, "isUnsafe", line)?, line, "isUnsafe")?;
            }
            "thm" => {
                self.expr_ref(line, data, "value")?;
                self.name_ref_array(line, field(data, "all", line)?, "all")?;
            }
            "quot" => {
                one_of(
                    field(data, "kind", line)?,
                    line,
                    "kind",
                    &["type", "ctor", "lift", "ind"],
                )?;
            }
            _ => unreachable!(),
        }
        self.add_declaration(line, name)
    }

    fn inductive(&mut self, line: usize, data: &Map<String, Value>) -> Result<(), Error> {
        for value in array(field(data, "types", line)?, line, "types")? {
            let item = object_value(value, line, "inductive type")?;
            let name = self.common_decl(line, item)?;
            for key in ["numParams", "numIndices", "numNested"] {
                usize_value(field(item, key, line)?, line, key)?;
            }
            self.name_ref_array(line, field(item, "all", line)?, "all")?;
            self.name_ref_array(line, field(item, "ctors", line)?, "ctors")?;
            for key in ["isRec", "isUnsafe", "isReflexive"] {
                boolean(field(item, key, line)?, line, key)?;
            }
            self.add_declaration(line, name)?;
        }
        for value in array(field(data, "ctors", line)?, line, "ctors")? {
            let item = object_value(value, line, "constructor")?;
            let name = self.common_decl(line, item)?;
            self.name_ref(line, item, "induct")?;
            for key in ["cidx", "numParams", "numFields"] {
                usize_value(field(item, key, line)?, line, key)?;
            }
            boolean(field(item, "isUnsafe", line)?, line, "isUnsafe")?;
            self.add_declaration(line, name)?;
        }
        for value in array(field(data, "recs", line)?, line, "recs")? {
            let item = object_value(value, line, "recursor")?;
            let name = self.common_decl(line, item)?;
            self.name_ref_array(line, field(item, "all", line)?, "all")?;
            for key in ["numParams", "numIndices", "numMotives", "numMinors"] {
                usize_value(field(item, key, line)?, line, key)?;
            }
            for rule in array(field(item, "rules", line)?, line, "rules")? {
                let rule = object_value(rule, line, "recursor rule")?;
                self.name_ref(line, rule, "ctor")?;
                usize_value(field(rule, "nfields", line)?, line, "nfields")?;
                self.expr_ref(line, rule, "rhs")?;
            }
            boolean(field(item, "k", line)?, line, "k")?;
            boolean(field(item, "isUnsafe", line)?, line, "isUnsafe")?;
            self.add_declaration(line, name)?;
        }
        Ok(())
    }

    fn common_decl(&self, line: usize, data: &Map<String, Value>) -> Result<usize, Error> {
        let name = self.name_ref(line, data, "name")?;
        self.name_ref_array(line, field(data, "levelParams", line)?, "levelParams")?;
        self.expr_ref(line, data, "type")?;
        Ok(name)
    }

    fn add_declaration(&mut self, line: usize, name: usize) -> Result<(), Error> {
        if !self.declared.insert(name) {
            return Err(Error::DuplicateDeclaration { line, index: name });
        }
        self.declarations += 1;
        Ok(())
    }

    fn name_ref(&self, line: usize, data: &Map<String, Value>, key: &str) -> Result<usize, Error> {
        Self::reference(line, &self.names, "in", field(data, key, line)?, key)
    }
    fn name_ref_value(&self, line: usize, value: &Value, key: &str) -> Result<(), Error> {
        Self::reference(line, &self.names, "in", value, key).map(|_| ())
    }
    fn level_ref_value(&self, line: usize, value: &Value, key: &str) -> Result<(), Error> {
        Self::reference(line, &self.levels, "il", value, key).map(|_| ())
    }
    fn expr_ref(&self, line: usize, data: &Map<String, Value>, key: &str) -> Result<usize, Error> {
        Self::reference(line, &self.expressions, "ie", field(data, key, line)?, key)
    }
    fn reference<T>(
        line: usize,
        table: &DenseTable<T>,
        namespace: &'static str,
        value: &Value,
        field_name: &str,
    ) -> Result<usize, Error> {
        let index = usize_value(value, line, field_name)?;
        table.get(index).ok_or_else(|| Error::Reference {
            line,
            table: namespace,
            field: field_name.to_owned(),
            index,
        })?;
        Ok(index)
    }
    fn name_ref_array(&self, line: usize, value: &Value, key: &str) -> Result<(), Error> {
        for item in array(value, line, key)? {
            Self::reference(line, &self.names, "in", item, key)?;
        }
        Ok(())
    }
    fn level_ref_array(&self, line: usize, value: &Value, key: &str) -> Result<(), Error> {
        for item in array(value, line, key)? {
            Self::reference(line, &self.levels, "il", item, key)?;
        }
        Ok(())
    }
    fn level_refs(&self, line: usize, value: &Value, key: &str) -> Result<(), Error> {
        let items = array(value, line, key)?;
        if items.len() != 2 {
            return invalid(line, &format!("{key} must contain two level references"));
        }
        self.level_ref_array(line, value, key)
    }
    fn expr_fields(&self, line: usize, value: &Value, keys: &[&str]) -> Result<(), Error> {
        let data = object_value(value, line, "expression")?;
        for key in keys {
            self.expr_ref(line, data, key)?;
        }
        Ok(())
    }
}

/// Stream and validate a `lean4export` 3.1.0 file.
///
/// This validates format shape, dense indices, backward references, declaration
/// name uniqueness, and enum vocabularies. It does not reconstruct Lean syntax,
/// typecheck declarations, or create Nucleus facts.
///
/// # Errors
///
/// Returns [`Error`] for malformed NDJSON, absent or skewed metadata, unknown
/// records, malformed fields, non-dense indices, forward references, or
/// duplicate declarations.
pub fn read<R: BufRead>(reader: R) -> Result<Export, Error> {
    let mut state = State::new();
    match stream::for_each(reader, |line, value| state.visit(line, &value)) {
        Ok(()) => {}
        Err(ForEachError::Framing(source)) => return Err(Error::Framing { source }),
        Err(ForEachError::Visitor(error)) => return Err(error),
    }
    let metadata = state.metadata.ok_or(Error::MissingMetadata)?;
    Ok(Export {
        metadata,
        names: state.names.next_index() - 1,
        levels: state.levels.next_index() - 1,
        expressions: state.expressions.next_index(),
        declarations: state.declarations,
    })
}

fn parse_metadata(record: &Map<String, Value>, line: usize) -> Result<Metadata, Error> {
    if record.len() != 1 {
        return invalid(line, "first record must contain only meta");
    }
    let meta = object_value(field(record, "meta", line)?, line, "meta")?;
    let exporter = object_value(field(meta, "exporter", line)?, line, "exporter")?;
    let lean = object_value(field(meta, "lean", line)?, line, "lean")?;
    let format = object_value(field(meta, "format", line)?, line, "format")?;
    let format_version =
        string(field(format, "version", line)?, line, "format.version")?.to_owned();
    if format_version != FORMAT_VERSION {
        return Err(Error::Version {
            line,
            found: format_version,
        });
    }
    Ok(Metadata {
        exporter_name: string(field(exporter, "name", line)?, line, "exporter.name")?.to_owned(),
        exporter_version: string(field(exporter, "version", line)?, line, "exporter.version")?
            .to_owned(),
        lean_version: string(field(lean, "version", line)?, line, "lean.version")?.to_owned(),
        lean_githash: string(field(lean, "githash", line)?, line, "lean.githash")?.to_owned(),
        format_version: FORMAT_VERSION.to_owned(),
    })
}

fn field<'a>(data: &'a Map<String, Value>, key: &str, line: usize) -> Result<&'a Value, Error> {
    data.get(key).ok_or_else(|| Error::Invalid {
        line,
        reason: format!("missing {key}"),
    })
}
fn object<'a>(value: &'a Value, line: usize, name: &str) -> Result<&'a Map<String, Value>, Error> {
    value.as_object().ok_or_else(|| Error::Invalid {
        line,
        reason: format!("{name} must be an object"),
    })
}
fn object_value<'a>(
    value: &'a Value,
    line: usize,
    name: &str,
) -> Result<&'a Map<String, Value>, Error> {
    object(value, line, name)
}
fn array<'a>(value: &'a Value, line: usize, name: &str) -> Result<&'a [Value], Error> {
    value
        .as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| Error::Invalid {
            line,
            reason: format!("{name} must be an array"),
        })
}
fn string<'a>(value: &'a Value, line: usize, name: &str) -> Result<&'a str, Error> {
    value.as_str().ok_or_else(|| Error::Invalid {
        line,
        reason: format!("{name} must be a string"),
    })
}
fn boolean(value: &Value, line: usize, name: &str) -> Result<bool, Error> {
    value.as_bool().ok_or_else(|| Error::Invalid {
        line,
        reason: format!("{name} must be a boolean"),
    })
}
fn usize_value(value: &Value, line: usize, name: &str) -> Result<usize, Error> {
    let n = value.as_u64().ok_or_else(|| Error::Invalid {
        line,
        reason: format!("{name} must be a nonnegative integer"),
    })?;
    usize::try_from(n).map_err(|_| Error::Invalid {
        line,
        reason: format!("{name} exceeds platform index range"),
    })
}
fn other<'a>(
    record: &'a Map<String, Value>,
    index: &str,
    line: usize,
) -> Result<(&'a str, &'a Value), Error> {
    record
        .iter()
        .find(|(key, _)| key.as_str() != index)
        .map(|(key, value)| (key.as_str(), value))
        .ok_or_else(|| Error::Invalid {
            line,
            reason: "indexed record has no kind".to_owned(),
        })
}
fn insert(
    table: &mut DenseTable<()>,
    line: usize,
    namespace: &'static str,
    index: usize,
) -> Result<(), Error> {
    table.insert(index, ()).map_err(|expected| Error::Index {
        line,
        table: namespace,
        found: index,
        expected,
    })
}
fn invalid<T>(line: usize, reason: &str) -> Result<T, Error> {
    Err(Error::Invalid {
        line,
        reason: reason.to_owned(),
    })
}
fn one_of(value: &Value, line: usize, name: &str, choices: &[&str]) -> Result<(), Error> {
    let value = string(value, line, name)?;
    if choices.contains(&value) {
        Ok(())
    } else {
        invalid(line, &format!("unsupported {name} {value:?}"))
    }
}
fn validate_hints(value: &Value, line: usize) -> Result<(), Error> {
    if let Some(text) = value.as_str() {
        return if ["opaque", "abbrev"].contains(&text) {
            Ok(())
        } else {
            invalid(line, "unsupported reduction hints")
        };
    }
    let data = object_value(value, line, "hints")?;
    usize_value(field(data, "regular", line)?, line, "hints.regular")?;
    Ok(())
}
