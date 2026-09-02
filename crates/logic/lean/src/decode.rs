//! Stateful decoding from JSON records into typed Lean export syntax.

use std::collections::HashSet;

use covalence_lib_error::snafu::Snafu;
use covalence_lib_json::{Map, Value};

use crate::lean4export::{FORMAT_VERSION, Metadata};
use crate::syntax::{
    BinderInfo, Constructor, Declaration, DeclarationHeader, DefinitionSafety, Expr, ExprId,
    InductiveType, Level, LevelId, Name, NameId, QuotKind, Record, Recursor, RecursorRule,
    ReducibilityHints, Tables,
};

/// One result from accepting a physical export record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Event {
    Metadata(Metadata),
    Record(Record),
}

/// A schema or reference failure while decoding one export record.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("invalid Lean export record on line {line}: {reason}"))]
pub struct Error {
    /// One-based physical line number.
    pub line: usize,
    /// Violated schema or ordering rule.
    pub reason: String,
}

/// Streaming decoder retaining only the backward-reference tables required by
/// later records.
#[derive(Debug, Default)]
pub struct Decoder {
    metadata: Option<Metadata>,
    tables: Tables,
    declared: HashSet<NameId>,
}

impl Decoder {
    /// Create an empty decoder with Lean's implicit anonymous name and zero level.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Borrow all typed records accepted so far.
    #[must_use]
    pub const fn tables(&self) -> &Tables {
        &self.tables
    }

    /// Decode and append one JSON record.
    ///
    /// # Errors
    ///
    /// Returns [`Error`] for malformed metadata or syntax, unknown record
    /// kinds, non-dense indices, forward references, or duplicate declarations.
    pub fn accept(&mut self, line: usize, value: &Value) -> Result<Event, Error> {
        let record = object(value, line, "record")?;
        if self.metadata.is_none() {
            let metadata = parse_metadata(record, line)?;
            self.metadata = Some(metadata.clone());
            return Ok(Event::Metadata(metadata));
        }
        if record.contains_key("meta") {
            return fail(line, "metadata may appear only on the first line");
        }
        if record.len() == 2 && record.contains_key("in") {
            return self.name(line, record).map(Event::Record);
        }
        if record.len() == 2 && record.contains_key("il") {
            return self.level(line, record).map(Event::Record);
        }
        if record.len() == 2 && record.contains_key("ie") {
            return self.expression(line, record).map(Event::Record);
        }
        if record.len() != 1 {
            return fail(
                line,
                "expected one declaration key or one kind plus one index",
            );
        }
        let (kind, body) = record.iter().next().expect("one key checked");
        let body = object(body, line, kind)?;
        let declaration = self.declaration(line, kind, body)?;
        for name in declaration.names() {
            if !self.declared.insert(name) {
                return fail(
                    line,
                    &format!("duplicate declaration name index {}", name.0),
                );
            }
        }
        let ordinal = self.tables.declarations.len();
        self.tables.declarations.push(declaration);
        Ok(Event::Record(Record::Declaration(ordinal)))
    }

    /// Finish decoding and require that metadata was present.
    ///
    /// # Errors
    ///
    /// Returns [`Error`] when the input ended before its metadata record.
    pub fn finish(self) -> Result<Tables, Error> {
        if self.metadata.is_none() {
            return fail(1, "missing metadata record");
        }
        Ok(self.tables)
    }

    fn name(&mut self, line: usize, record: &Map<String, Value>) -> Result<Record, Error> {
        let index = usize_value(field(record, "in", line)?, line, "in")?;
        if index != self.tables.names.len() {
            return fail(
                line,
                &format!(
                    "non-dense name index {index}, expected {}",
                    self.tables.names.len()
                ),
            );
        }
        let (kind, body) = other(record, "in", line)?;
        let data = object(body, line, kind)?;
        let name = match kind {
            "str" => Name::Str {
                prefix: self.name_id(field(data, "pre", line)?, line, "str.pre")?,
                value: string(field(data, "str", line)?, line, "str.str")?.to_owned(),
            },
            "num" => Name::Num {
                prefix: self.name_id(field(data, "pre", line)?, line, "num.pre")?,
                value: usize_value(field(data, "i", line)?, line, "num.i")?,
            },
            _ => return fail(line, &format!("unsupported name record {kind:?}")),
        };
        let id = NameId(index);
        self.tables.names.push(name);
        Ok(Record::Name(id))
    }

    fn level(&mut self, line: usize, record: &Map<String, Value>) -> Result<Record, Error> {
        let index = usize_value(field(record, "il", line)?, line, "il")?;
        if index != self.tables.levels.len() {
            return fail(
                line,
                &format!(
                    "non-dense level index {index}, expected {}",
                    self.tables.levels.len()
                ),
            );
        }
        let (kind, body) = other(record, "il", line)?;
        let level = match kind {
            "succ" => Level::Succ(self.level_id(body, line, "succ")?),
            "max" | "imax" => {
                let pair = array(body, line, kind)?;
                if pair.len() != 2 {
                    return fail(line, &format!("{kind} must contain two levels"));
                }
                let left = self.level_id(&pair[0], line, kind)?;
                let right = self.level_id(&pair[1], line, kind)?;
                if kind == "max" {
                    Level::Max(left, right)
                } else {
                    Level::IMax(left, right)
                }
            }
            "param" => Level::Param(self.name_id(body, line, "param")?),
            _ => return fail(line, &format!("unsupported level record {kind:?}")),
        };
        let id = LevelId(index);
        self.tables.levels.push(level);
        Ok(Record::Level(id))
    }

    fn expression(&mut self, line: usize, record: &Map<String, Value>) -> Result<Record, Error> {
        let index = usize_value(field(record, "ie", line)?, line, "ie")?;
        if index != self.tables.expressions.len() {
            return fail(
                line,
                &format!(
                    "non-dense expression index {index}, expected {}",
                    self.tables.expressions.len()
                ),
            );
        }
        let (kind, body) = other(record, "ie", line)?;
        let expression = match kind {
            "bvar" => Expr::BVar(usize_value(body, line, "bvar")?),
            "sort" => Expr::Sort(self.level_id(body, line, "sort")?),
            "const" => {
                let data = object(body, line, "const")?;
                Expr::Const {
                    name: self.name_id(field(data, "name", line)?, line, "const.name")?,
                    universes: self.level_ids(field(data, "us", line)?, line, "const.us")?,
                }
            }
            "app" => {
                let data = object(body, line, "app")?;
                Expr::App {
                    function: self.expr_id(field(data, "fn", line)?, line, "app.fn")?,
                    argument: self.expr_id(field(data, "arg", line)?, line, "app.arg")?,
                }
            }
            "lam" | "forallE" => {
                let data = object(body, line, kind)?;
                let name = self.name_id(field(data, "name", line)?, line, "binder.name")?;
                let ty = self.expr_id(field(data, "type", line)?, line, "binder.type")?;
                let body = self.expr_id(field(data, "body", line)?, line, "binder.body")?;
                let binder_info = binder_info(field(data, "binderInfo", line)?, line)?;
                if kind == "lam" {
                    Expr::Lam {
                        name,
                        ty,
                        body,
                        binder_info,
                    }
                } else {
                    Expr::Forall {
                        name,
                        ty,
                        body,
                        binder_info,
                    }
                }
            }
            "letE" => {
                let data = object(body, line, "letE")?;
                Expr::Let {
                    name: self.name_id(field(data, "name", line)?, line, "letE.name")?,
                    ty: self.expr_id(field(data, "type", line)?, line, "letE.type")?,
                    value: self.expr_id(field(data, "value", line)?, line, "letE.value")?,
                    body: self.expr_id(field(data, "body", line)?, line, "letE.body")?,
                    nondependent: boolean(field(data, "nondep", line)?, line, "letE.nondep")?,
                }
            }
            "proj" => {
                let data = object(body, line, "proj")?;
                Expr::Proj {
                    type_name: self.name_id(
                        field(data, "typeName", line)?,
                        line,
                        "proj.typeName",
                    )?,
                    index: usize_value(field(data, "idx", line)?, line, "proj.idx")?,
                    structure: self.expr_id(field(data, "struct", line)?, line, "proj.struct")?,
                }
            }
            "natVal" => Expr::NatLit(string(body, line, "natVal")?.to_owned()),
            "strVal" => Expr::StrLit(string(body, line, "strVal")?.to_owned()),
            "mdata" => {
                let data = object(body, line, "mdata")?;
                let metadata = field(data, "data", line)?;
                object(metadata, line, "mdata.data")?;
                Expr::MData {
                    expression: self.expr_id(field(data, "expr", line)?, line, "mdata.expr")?,
                    data: metadata.clone(),
                }
            }
            _ => return fail(line, &format!("unsupported expression record {kind:?}")),
        };
        let id = ExprId(index);
        self.tables.expressions.push(expression);
        Ok(Record::Expr(id))
    }

    fn declaration(
        &self,
        line: usize,
        kind: &str,
        data: &Map<String, Value>,
    ) -> Result<Declaration, Error> {
        match kind {
            "axiom" => Ok(Declaration::Axiom {
                header: self.header(data, line)?,
                is_unsafe: boolean(field(data, "isUnsafe", line)?, line, "axiom.isUnsafe")?,
            }),
            "def" => Ok(Declaration::Definition {
                header: self.header(data, line)?,
                value: self.expr_id(field(data, "value", line)?, line, "def.value")?,
                hints: hints(field(data, "hints", line)?, line)?,
                safety: safety(field(data, "safety", line)?, line)?,
                all: self.name_ids(field(data, "all", line)?, line, "def.all")?,
            }),
            "opaque" => Ok(Declaration::Opaque {
                header: self.header(data, line)?,
                value: self.expr_id(field(data, "value", line)?, line, "opaque.value")?,
                all: self.name_ids(field(data, "all", line)?, line, "opaque.all")?,
                is_unsafe: boolean(field(data, "isUnsafe", line)?, line, "opaque.isUnsafe")?,
            }),
            "thm" => Ok(Declaration::Theorem {
                header: self.header(data, line)?,
                value: self.expr_id(field(data, "value", line)?, line, "thm.value")?,
                all: self.name_ids(field(data, "all", line)?, line, "thm.all")?,
            }),
            "quot" => Ok(Declaration::Quotient {
                header: self.header(data, line)?,
                kind: quot_kind(field(data, "kind", line)?, line)?,
            }),
            "inductive" => self.inductive(data, line),
            _ => fail(line, &format!("unsupported declaration record {kind:?}")),
        }
    }

    fn inductive(&self, data: &Map<String, Value>, line: usize) -> Result<Declaration, Error> {
        let mut types = Vec::new();
        for value in array(field(data, "types", line)?, line, "inductive.types")? {
            let item = object(value, line, "inductive type")?;
            types.push(InductiveType {
                header: self.header(item, line)?,
                num_params: nat_field(item, "numParams", line)?,
                num_indices: nat_field(item, "numIndices", line)?,
                all: self.name_ids(field(item, "all", line)?, line, "inductive.all")?,
                constructors: self.name_ids(
                    field(item, "ctors", line)?,
                    line,
                    "inductive.ctors",
                )?,
                num_nested: nat_field(item, "numNested", line)?,
                is_recursive: bool_field(item, "isRec", line)?,
                is_unsafe: bool_field(item, "isUnsafe", line)?,
                is_reflexive: bool_field(item, "isReflexive", line)?,
            });
        }
        let mut constructors = Vec::new();
        for value in array(field(data, "ctors", line)?, line, "inductive.ctors")? {
            let item = object(value, line, "constructor")?;
            constructors.push(Constructor {
                header: self.header(item, line)?,
                inductive: self.name_id(
                    field(item, "induct", line)?,
                    line,
                    "constructor.induct",
                )?,
                constructor_index: nat_field(item, "cidx", line)?,
                num_params: nat_field(item, "numParams", line)?,
                num_fields: nat_field(item, "numFields", line)?,
                is_unsafe: bool_field(item, "isUnsafe", line)?,
            });
        }
        let mut recursors = Vec::new();
        for value in array(field(data, "recs", line)?, line, "inductive.recs")? {
            let item = object(value, line, "recursor")?;
            let mut rules = Vec::new();
            for rule in array(field(item, "rules", line)?, line, "recursor.rules")? {
                let rule = object(rule, line, "recursor rule")?;
                rules.push(RecursorRule {
                    constructor: self.name_id(field(rule, "ctor", line)?, line, "rule.ctor")?,
                    num_fields: nat_field(rule, "nfields", line)?,
                    rhs: self.expr_id(field(rule, "rhs", line)?, line, "rule.rhs")?,
                });
            }
            recursors.push(Recursor {
                header: self.header(item, line)?,
                all: self.name_ids(field(item, "all", line)?, line, "recursor.all")?,
                num_params: nat_field(item, "numParams", line)?,
                num_indices: nat_field(item, "numIndices", line)?,
                num_motives: nat_field(item, "numMotives", line)?,
                num_minors: nat_field(item, "numMinors", line)?,
                rules,
                k: bool_field(item, "k", line)?,
                is_unsafe: bool_field(item, "isUnsafe", line)?,
            });
        }
        Ok(Declaration::Inductive {
            types,
            constructors,
            recursors,
        })
    }

    fn header(&self, data: &Map<String, Value>, line: usize) -> Result<DeclarationHeader, Error> {
        Ok(DeclarationHeader {
            name: self.name_id(field(data, "name", line)?, line, "declaration.name")?,
            level_params: self.name_ids(
                field(data, "levelParams", line)?,
                line,
                "declaration.levelParams",
            )?,
            ty: self.expr_id(field(data, "type", line)?, line, "declaration.type")?,
        })
    }

    fn name_id(&self, value: &Value, line: usize, field_name: &str) -> Result<NameId, Error> {
        let index = usize_value(value, line, field_name)?;
        if index >= self.tables.names.len() {
            return fail(
                line,
                &format!("unknown or forward name reference {index} in {field_name}"),
            );
        }
        Ok(NameId(index))
    }
    fn level_id(&self, value: &Value, line: usize, field_name: &str) -> Result<LevelId, Error> {
        let index = usize_value(value, line, field_name)?;
        if index >= self.tables.levels.len() {
            return fail(
                line,
                &format!("unknown or forward level reference {index} in {field_name}"),
            );
        }
        Ok(LevelId(index))
    }
    fn expr_id(&self, value: &Value, line: usize, field_name: &str) -> Result<ExprId, Error> {
        let index = usize_value(value, line, field_name)?;
        if index >= self.tables.expressions.len() {
            return fail(
                line,
                &format!("unknown or forward expression reference {index} in {field_name}"),
            );
        }
        Ok(ExprId(index))
    }
    fn name_ids(&self, value: &Value, line: usize, field_name: &str) -> Result<Vec<NameId>, Error> {
        array(value, line, field_name)?
            .iter()
            .map(|value| self.name_id(value, line, field_name))
            .collect()
    }
    fn level_ids(
        &self,
        value: &Value,
        line: usize,
        field_name: &str,
    ) -> Result<Vec<LevelId>, Error> {
        array(value, line, field_name)?
            .iter()
            .map(|value| self.level_id(value, line, field_name))
            .collect()
    }
}

fn parse_metadata(record: &Map<String, Value>, line: usize) -> Result<Metadata, Error> {
    if record.len() != 1 {
        return fail(line, "first record must contain only meta");
    }
    let meta = object(field(record, "meta", line)?, line, "meta")?;
    let exporter = object(field(meta, "exporter", line)?, line, "meta.exporter")?;
    let lean = object(field(meta, "lean", line)?, line, "meta.lean")?;
    let format = object(field(meta, "format", line)?, line, "meta.format")?;
    let version = string(field(format, "version", line)?, line, "format.version")?;
    if version != FORMAT_VERSION {
        return fail(
            line,
            &format!("unsupported format {version:?}, expected {FORMAT_VERSION}"),
        );
    }
    Ok(Metadata {
        exporter_name: text_field(exporter, "name", line)?.to_owned(),
        exporter_version: text_field(exporter, "version", line)?.to_owned(),
        lean_version: text_field(lean, "version", line)?.to_owned(),
        lean_githash: text_field(lean, "githash", line)?.to_owned(),
        format_version: version.to_owned(),
    })
}

fn binder_info(value: &Value, line: usize) -> Result<BinderInfo, Error> {
    match string(value, line, "binderInfo")? {
        "default" => Ok(BinderInfo::Default),
        "implicit" => Ok(BinderInfo::Implicit),
        "strictImplicit" => Ok(BinderInfo::StrictImplicit),
        "instImplicit" => Ok(BinderInfo::InstImplicit),
        value => fail(line, &format!("unknown binder info {value:?}")),
    }
}
fn safety(value: &Value, line: usize) -> Result<DefinitionSafety, Error> {
    match string(value, line, "safety")? {
        "unsafe" => Ok(DefinitionSafety::Unsafe),
        "safe" => Ok(DefinitionSafety::Safe),
        "partial" => Ok(DefinitionSafety::Partial),
        value => fail(line, &format!("unknown definition safety {value:?}")),
    }
}
fn quot_kind(value: &Value, line: usize) -> Result<QuotKind, Error> {
    match string(value, line, "quot.kind")? {
        "type" => Ok(QuotKind::Type),
        "ctor" => Ok(QuotKind::Ctor),
        "lift" => Ok(QuotKind::Lift),
        "ind" => Ok(QuotKind::Ind),
        value => fail(line, &format!("unknown quotient kind {value:?}")),
    }
}
fn hints(value: &Value, line: usize) -> Result<ReducibilityHints, Error> {
    if let Some(value) = value.as_str() {
        return match value {
            "opaque" => Ok(ReducibilityHints::Opaque),
            "abbrev" => Ok(ReducibilityHints::Abbrev),
            value => fail(line, &format!("unknown reducibility hints {value:?}")),
        };
    }
    let data = object(value, line, "hints")?;
    Ok(ReducibilityHints::Regular(nat_field(
        data, "regular", line,
    )?))
}
fn field<'a>(data: &'a Map<String, Value>, key: &str, line: usize) -> Result<&'a Value, Error> {
    data.get(key).ok_or_else(|| Error {
        line,
        reason: format!("missing {key}"),
    })
}
fn object<'a>(value: &'a Value, line: usize, name: &str) -> Result<&'a Map<String, Value>, Error> {
    value.as_object().ok_or_else(|| Error {
        line,
        reason: format!("{name} must be an object"),
    })
}
fn array<'a>(value: &'a Value, line: usize, name: &str) -> Result<&'a [Value], Error> {
    value.as_array().map(Vec::as_slice).ok_or_else(|| Error {
        line,
        reason: format!("{name} must be an array"),
    })
}
fn string<'a>(value: &'a Value, line: usize, name: &str) -> Result<&'a str, Error> {
    value.as_str().ok_or_else(|| Error {
        line,
        reason: format!("{name} must be a string"),
    })
}
fn boolean(value: &Value, line: usize, name: &str) -> Result<bool, Error> {
    value.as_bool().ok_or_else(|| Error {
        line,
        reason: format!("{name} must be a boolean"),
    })
}
fn usize_value(value: &Value, line: usize, name: &str) -> Result<usize, Error> {
    let value = value.as_u64().ok_or_else(|| Error {
        line,
        reason: format!("{name} must be a nonnegative integer"),
    })?;
    usize::try_from(value).map_err(|_| Error {
        line,
        reason: format!("{name} exceeds the platform index range"),
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
        .ok_or_else(|| Error {
            line,
            reason: "indexed record has no kind".to_owned(),
        })
}
fn text_field<'a>(data: &'a Map<String, Value>, key: &str, line: usize) -> Result<&'a str, Error> {
    string(field(data, key, line)?, line, key)
}
fn nat_field(data: &Map<String, Value>, key: &str, line: usize) -> Result<usize, Error> {
    usize_value(field(data, key, line)?, line, key)
}
fn bool_field(data: &Map<String, Value>, key: &str, line: usize) -> Result<bool, Error> {
    boolean(field(data, key, line)?, line, key)
}
fn fail<T>(line: usize, reason: &str) -> Result<T, Error> {
    Err(Error {
        line,
        reason: reason.to_owned(),
    })
}
