//! Raw, unvalidated Ethane syntax arenas.
//!
//! Deserialization establishes only the representation invariants. It does
//! not establish kinding, typing, equality, or provability.

mod arena;
pub mod builtin;
pub mod init;
mod kernel;
mod resolve;
mod row;
mod syn;
mod table;
pub mod wire;

pub use arena::Arena;
pub use kernel::{
    AX_SUB, BINDER_COUNT, Binder, CheckedArena, ClassicalArena, ClassicalKernel, ClassicalRules,
    Cnf, CnfId, CopyMap, Dnf, DnfId, Kernel, KernelError, Lit, LitError, LitVec, Refutation,
    SubtypeAxiom, ThmId, ThmRef,
};
pub use resolve::{Expr, ResolveError, Resolver, ResolverExt};
pub use row::{KindTag, Sort, Tag, TmTag, TyTag};
pub use syn::{SynFact, SynRel};
pub use table::Table;

use std::{collections::BTreeSet, num::NonZeroI32};

use arena::{Dense, EqColumn};
use covalence_lib_hash::O256;
use row::Row;
use serde::{Deserialize, Serialize};
use syn::{SynFree, SynSlot};

fn next_ref(len: usize) -> Option<Ref> {
    let next = i32::try_from(len).ok()?.checked_add(1)?;
    Ref::new(next)
}

macro_rules! id_type {
    ($(#[$attribute:meta])* $visibility:vis struct $name:ident($storage:ty);) => {
        $(#[$attribute])*
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        #[repr(transparent)]
        $visibility struct $name($storage);

        impl From<$name> for i32 {
            fn from(value: $name) -> Self {
                value.get()
            }
        }

        impl Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                self.get().serialize(serializer)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                let value = i32::deserialize(deserializer)?;
                Self::new(value).ok_or_else(|| serde::de::Error::custom(ZeroId))
            }
        }
    };
}

/// A one-based local definition reference. `Ref(n)` addresses `defs[n - 1]`.
///
/// References are globally bounded by the lossless signed literal wire space:
/// `0 < n < i32::MAX`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Ref(NonZeroI32);

/// A value outside the global local-reference range.
#[derive(Clone, Copy, Debug, Eq, PartialEq, covalence_lib_error::snafu::Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("reference {value} is outside the supported range"))]
pub struct RefError {
    /// Rejected integer.
    pub value: i32,
}

impl Ref {
    #[must_use]
    pub const fn new(value: i32) -> Option<Self> {
        if value <= 0 || value == i32::MAX {
            return None;
        }
        match NonZeroI32::new(value) {
            Some(value) => Some(Self(value)),
            None => None,
        }
    }

    #[must_use]
    pub const fn get(self) -> i32 {
        self.0.get()
    }
}

impl TryFrom<i32> for Ref {
    type Error = RefError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        Self::new(value).ok_or(RefError { value })
    }
}

impl From<Ref> for i32 {
    fn from(value: Ref) -> Self {
        value.get()
    }
}

impl Serialize for Ref {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.get().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Ref {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let value = i32::deserialize(deserializer)?;
        Self::new(value).ok_or_else(|| serde::de::Error::custom(RefError { value }))
    }
}

id_type! {
    /// A one-based index into an arena's import array.
    pub struct ImportId(NonZeroI32);
}

impl ImportId {
    #[must_use]
    pub const fn new(value: i32) -> Option<Self> {
        if value <= 0 {
            return None;
        }
        match NonZeroI32::new(value) {
            Some(value) => Some(Self(value)),
            None => None,
        }
    }

    #[must_use]
    pub const fn get(self) -> i32 {
        self.0.get()
    }
}

impl TryFrom<i32> for ImportId {
    type Error = ZeroId;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        Self::new(value).ok_or(ZeroId)
    }
}

id_type! {
    /// A one-based slot in an arena's syntactic-fact table.
    ///
    /// IDs are ephemeral cache handles. Removing or truncating facts permits
    /// a later insertion to reuse the same ID for a different fact.
    pub struct SynFactId(NonZeroI32);
}

impl SynFactId {
    #[must_use]
    pub const fn new(value: i32) -> Option<Self> {
        if value <= 0 {
            return None;
        }
        match NonZeroI32::new(value) {
            Some(value) => Some(Self(value)),
            None => None,
        }
    }

    #[must_use]
    pub const fn get(self) -> i32 {
        self.0.get()
    }
}

impl TryFrom<i32> for SynFactId {
    type Error = ZeroId;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        Self::new(value).ok_or(ZeroId)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ZeroId;

impl std::fmt::Display for ZeroId {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        output.write_str("references are one-based")
    }
}

impl std::error::Error for ZeroId {}

/// The only link format fixed by this representation layer.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum LinkFormat {
    Cbor,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
enum LinkTag {
    #[serde(rename = "link")]
    Link,
}

/// A lazy BLAKE3-addressed arena import.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Link {
    pub format: LinkFormat,
    pub blake3: O256,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct LinkSerde {
    tag: LinkTag,
    format: LinkFormat,
    blake3: O256,
}

impl Serialize for Link {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        LinkSerde {
            tag: LinkTag::Link,
            format: self.format,
            blake3: self.blake3,
        }
        .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Link {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let link = LinkSerde::deserialize(deserializer)?;
        let LinkTag::Link = link.tag;
        Ok(Self {
            format: link.format,
            blake3: link.blake3,
        })
    }
}

/// One raw import table entry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Import {
    Null,
    Literal(Box<Arena>),
    Link(Link),
}

#[derive(Deserialize, Serialize)]
#[serde(untagged)]
enum ImportSerde {
    Null(Option<Never>),
    Literal(Box<Arena>),
    Link(Link),
}

#[derive(Deserialize, Serialize)]
enum Never {}

impl From<Import> for ImportSerde {
    fn from(value: Import) -> Self {
        match value {
            Import::Null => Self::Null(None),
            Import::Literal(arena) => Self::Literal(arena),
            Import::Link(link) => Self::Link(link),
        }
    }
}

impl From<ImportSerde> for Import {
    fn from(value: ImportSerde) -> Self {
        match value {
            ImportSerde::Null(None) => Self::Null,
            ImportSerde::Null(Some(value)) => match value {},
            ImportSerde::Literal(arena) => Self::Literal(arena),
            ImportSerde::Link(link) => Self::Link(link),
        }
    }
}

impl Serialize for Import {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        ImportSerde::from(self.clone()).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Import {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(ImportSerde::deserialize(deserializer)?.into())
    }
}

/// One atomic ambient predicate.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "tag", deny_unknown_fields)]
pub enum AmbPred {
    #[serde(rename = "arena.ok")]
    ArenaOk { src: ImportId },
    #[serde(rename = "hol.sort")]
    HolSort { src: ImportId, ix: Ref, sort: Ref },
}

mod sealed {
    pub trait Sealed {}
}

/// Read-only operations shared by arena representations.
pub trait ArenaRepr: sealed::Sealed {
    type Ref: Copy + Eq + Ord;

    fn len(&self) -> usize;
    fn tag(&self, reference: Self::Ref) -> Option<Tag>;
    fn eq(&self, reference: Self::Ref) -> Option<Self::Ref>;
    fn sort(&self, reference: Self::Ref) -> Option<Self::Ref>;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl sealed::Sealed for Dense {}

impl ArenaRepr for Dense {
    type Ref = Ref;

    fn len(&self) -> usize {
        self.defs.len()
    }

    fn tag(&self, reference: Ref) -> Option<Tag> {
        self.row(reference).map(Row::tag)
    }

    fn eq(&self, reference: Ref) -> Option<Ref> {
        self.column(&self.eq, reference)
    }

    fn sort(&self, reference: Ref) -> Option<Ref> {
        Dense::sort(self, reference)
    }
}

impl Arena {
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            imports: Vec::new(),
            axs: BTreeSet::new(),
            dense: Dense {
                defs: Vec::new(),
                eq: Vec::new(),
                syn_eq: Vec::new(),
                conv: Vec::new(),
            },
            syn_facts: Vec::new(),
            syn_free: None,
            ctx: BTreeSet::new(),
            amb_pred: Vec::new(),
            amb_ax: BTreeSet::new(),
            amb_ctx: Cnf::empty(),
            amb_thm: ClassicalArena::new(),
            syl: ClassicalArena::new(),
            thm: ClassicalArena::new(),
        }
    }

    /// Returns the address of this arena's current CBOR encoding.
    ///
    /// Mutable arenas recompute their address on every call. [`Table::addr`]
    /// returns the address cached when the table was introduced instead.
    ///
    /// # Panics
    ///
    /// Panics only if the arena's internal Serde implementation rejects
    /// encoding to an in-memory buffer.
    #[must_use]
    pub fn addr(&self) -> O256 {
        let mut bytes = Vec::new();
        wire::serialize(self, &mut bytes)
            .expect("serializing an Ethane arena into memory cannot fail");
        O256::from_bytes(&bytes)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.dense.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.dense.is_empty()
    }

    #[must_use]
    pub fn tag(&self, reference: Ref) -> Option<Tag> {
        self.dense.tag(reference)
    }

    #[must_use]
    pub fn eq(&self, reference: Ref) -> Option<Ref> {
        ArenaRepr::eq(&self.dense, reference)
    }

    /// Returns the parent link in the literal-syntax equality column.
    #[must_use]
    pub fn syn_eq(&self, reference: Ref) -> Option<Ref> {
        self.dense.column(&self.dense.syn_eq, reference)
    }

    /// Returns the parent link in the syntactic-conversion column.
    #[must_use]
    pub fn conv(&self, reference: Ref) -> Option<Ref> {
        self.dense.column(&self.dense.conv, reference)
    }

    #[must_use]
    pub fn sort(&self, reference: Ref) -> Option<Ref> {
        self.dense.sort(reference)
    }

    pub(crate) fn row(&self, reference: Ref) -> Option<&Row> {
        self.dense.row(reference)
    }

    #[must_use]
    pub fn imports(&self) -> &[Import] {
        &self.imports
    }

    #[must_use]
    pub fn axioms(&self) -> impl ExactSizeIterator<Item = &str> {
        self.axs.iter().map(String::as_str)
    }

    #[must_use]
    pub fn context(&self) -> impl ExactSizeIterator<Item = Ref> + '_ {
        self.ctx.iter().copied()
    }

    #[must_use]
    pub fn ambient_predicates(&self) -> &[AmbPred] {
        &self.amb_pred
    }

    #[must_use]
    pub fn ambient_axioms(&self) -> impl ExactSizeIterator<Item = &str> {
        self.amb_ax.iter().map(String::as_str)
    }

    #[must_use]
    pub const fn ambient_context(&self) -> &Cnf {
        &self.amb_ctx
    }

    #[must_use]
    pub const fn ambient_theorems(&self) -> &ClassicalArena {
        &self.amb_thm
    }

    #[must_use]
    pub const fn syllogisms(&self) -> &ClassicalArena {
        &self.syl
    }

    pub(crate) const fn syllogisms_mut(&mut self) -> &mut ClassicalArena {
        &mut self.syl
    }

    #[must_use]
    pub const fn theorems(&self) -> &ClassicalArena {
        &self.thm
    }

    pub(crate) const fn theorems_mut(&mut self) -> &mut ClassicalArena {
        &mut self.thm
    }

    /// Returns one occupied syntactic-fact slot.
    #[must_use]
    pub fn syn_fact(&self, id: SynFactId) -> Option<SynFact> {
        let position = usize::try_from(id.get() - 1).ok()?;
        match self.syn_facts.get(position)? {
            SynSlot::Fact(fact) => Some(*fact),
            SynSlot::Free(_) => None,
        }
    }

    /// Returns all syntactic-fact slots, including removed slots.
    #[must_use]
    pub fn syn_fact_slot_count(&self) -> usize {
        self.syn_facts.len()
    }

    /// Append one raw import entry.
    ///
    /// This is a representation operation, not a trust decision. A checked
    /// layer must resolve and validate every import it relies on.
    pub fn push_import(&mut self, import: Import) -> Option<ImportId> {
        let next = i32::try_from(self.imports.len()).ok()?.checked_add(1)?;
        let source = ImportId::new(next)?;
        self.imports.push(import);
        Some(source)
    }

    /// Add an unvalidated axiom capability name.
    pub fn insert_axiom(&mut self, name: impl Into<String>) {
        self.axs.insert(name.into());
    }

    /// Add an unvalidated Boolean-context reference.
    pub fn insert_context(&mut self, reference: Ref) {
        self.ctx.insert(reference);
    }

    /// Appends an atom and assumes it as a positive ambient unit clause.
    #[must_use]
    pub fn push_ambient_context(&mut self, record: AmbPred) -> bool {
        let Some(next) = self.next_ambient_ref() else {
            return false;
        };
        self.amb_pred.push(record);
        let mut rows = self.amb_ctx.to_rows();
        rows.push(LitVec::from_slice(&[Lit::positive(next.get())]));
        self.amb_ctx = Cnf::new(rows);
        true
    }

    /// Appends an atom and records it as a positive ambient unit theorem.
    #[must_use]
    pub fn push_ambient_theorem(&mut self, record: AmbPred) -> bool {
        let Some(next) = self.next_ambient_ref() else {
            return false;
        };
        self.amb_pred.push(record);
        if self
            .amb_thm
            .insert(
                Cnf::new([]),
                Dnf::new([LitVec::from_slice(&[Lit::positive(next.get())])]),
            )
            .is_err()
        {
            self.amb_pred.pop();
            return false;
        }
        true
    }

    fn next_ambient_ref(&self) -> Option<Ref> {
        next_ref(self.amb_pred.len())
    }

    pub(crate) fn has_definition_capacity(&self) -> bool {
        next_ref(self.dense.defs.len()).is_some()
    }

    /// The ordinary children of one local row.
    #[must_use]
    pub fn children(&self, reference: Ref) -> Option<impl ExactSizeIterator<Item = Ref>> {
        Some(self.dense.row(reference)?.expr().children().into_iter())
    }

    /// The variable or binder name stored by one local row.
    #[must_use]
    pub fn name(&self, reference: Ref) -> Option<u64> {
        match *self.dense.row(reference)?.expr() {
            row::Expr::TyFv { name, .. }
            | row::Expr::TyExists { name, .. }
            | row::Expr::Model { name, .. }
            | row::Expr::TmFv { name, .. } => Some(name),
            _ => None,
        }
    }

    /// The literal value stored by a `tm.bool` row.
    #[must_use]
    pub fn bool_value(&self, reference: Ref) -> Option<bool> {
        match self.dense.row(reference)?.expr() {
            row::Expr::Bool(value) => Some(*value),
            _ => None,
        }
    }

    /// The unary builtin stored by a `tm.op1.v1` row.
    #[must_use]
    pub fn op1(&self, reference: Ref) -> Option<builtin::Op1> {
        match self.dense.row(reference)?.expr() {
            row::Expr::Op1(op, _) => Some(*op),
            _ => None,
        }
    }

    /// The binary builtin stored by a `tm.op2.v1` row.
    #[must_use]
    pub fn op2(&self, reference: Ref) -> Option<builtin::Op2> {
        match self.dense.row(reference)?.expr() {
            row::Expr::Op2(op, ..) => Some(*op),
            _ => None,
        }
    }

    /// The source and foreign reference stored by a proxy row.
    #[must_use]
    pub fn foreign(&self, reference: Ref) -> Option<(ImportId, Ref)> {
        match *self.dense.row(reference)?.expr() {
            row::Expr::TmRef { src, ix }
            | row::Expr::TyRef { src, ix }
            | row::Expr::KindRef { src, ix } => Some((src, ix)),
            _ => None,
        }
    }

    /// Append a raw `kind.star` row.
    pub fn push_kind_star(&mut self) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::KindStar), None)
    }

    /// Append a raw `kind.arr` row.
    pub fn push_kind_arr(&mut self, domain: Ref, codomain: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::KindArr(domain, codomain)), None)
    }

    /// Append a raw `ty.bool` row.
    pub fn push_bool_ty(&mut self) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::BoolTy), None)
    }

    /// Append a raw `ty.arr` row.
    pub fn push_ty_arr(&mut self, domain: Ref, codomain: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyArr(domain, codomain)), None)
    }

    /// Append a raw `ty.app` row.
    pub fn push_ty_app(&mut self, function: Ref, argument: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyApp(function, argument)), None)
    }

    /// Append a raw `ty.lam` row. The first child is the binder variable.
    pub fn push_ty_lam(&mut self, binder: Ref, body: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyLam(binder, body)), None)
    }

    /// Append a raw typed type-variable row.
    pub fn push_ty_fv(&mut self, name: u64, kind: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyFv { name, kind }), None)
    }

    /// Append a raw type-existential proposition row.
    pub fn push_ty_exists(&mut self, name: u64, predicate: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyExists { name, predicate }), None)
    }

    /// Append a raw model-type row.
    pub fn push_model(&mut self, name: u64, predicate: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Model { name, predicate }), None)
    }

    /// Append a raw typed term-variable row.
    pub fn push_tm_fv(&mut self, name: u64, ty: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TmFv { name, ty }), None)
    }

    /// Append a raw `tm.app` row.
    pub fn push_app(&mut self, function: Ref, argument: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::App(function, argument)), None)
    }

    /// Append a raw `tm.lam` row. The first child is the binder variable.
    pub fn push_lam(&mut self, binder: Ref, body: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Lam(binder, body)), None)
    }

    /// Append a raw Boolean literal row.
    pub fn push_bool(&mut self, value: bool) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Bool(value)), None)
    }

    /// Append a raw unary builtin row.
    pub fn push_op1(&mut self, op: builtin::Op1, operand: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Op1(op, operand)), None)
    }

    /// Append a raw binary builtin row.
    pub fn push_op2(&mut self, op: builtin::Op2, left: Ref, right: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Op2(op, left, right)), None)
    }

    /// Append a raw object-language equality row.
    pub fn push_tm_eq(&mut self, left: Ref, right: Ref) -> Option<Ref> {
        let ty = self.sort(left).or_else(|| match self.row(left)?.expr() {
            row::Expr::TmFv { ty, .. } | row::Expr::Eq(ty, ..) | row::Expr::Eps { ty, .. } => {
                Some(*ty)
            }
            _ => None,
        })?;
        self.push_row(Row::new(row::Expr::Eq(ty, left, right)), None)
    }

    /// Append a raw choice row.
    pub fn push_eps(&mut self, ty: Ref, predicate: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Eps { ty, predicate }), None)
    }

    /// Append a raw term proxy into an import.
    pub fn push_tm_ref(&mut self, src: ImportId, ix: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TmRef { src, ix }), None)
    }

    /// Append a raw type proxy into an import.
    pub fn push_ty_ref(&mut self, src: ImportId, ix: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyRef { src, ix }), None)
    }

    /// Append a raw kind proxy into an import.
    pub fn push_kind_ref(&mut self, src: ImportId, ix: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::KindRef { src, ix }), None)
    }

    fn import(&self, source: ImportId) -> Option<&Import> {
        let position = usize::try_from(source.get() - 1).ok()?;
        self.imports.get(position)
    }

    pub(crate) fn push_row(&mut self, row: Row, sort: Option<Ref>) -> Option<Ref> {
        let reference = next_ref(self.dense.defs.len())?;
        self.dense.defs.push(row);
        if let Some(sort) = sort {
            let recorded = self
                .dense
                .set_column(|dense| &mut dense.conv, reference, Some(sort));
            debug_assert!(recorded, "the appended row is resident");
        }
        Some(reference)
    }

    pub(crate) fn has_definition_prefix(&self, prefix: &Self) -> bool {
        let columns_match = |column: &[Option<Ref>], expected: &[Option<Ref>]| {
            (0..prefix.dense.defs.len()).all(|position| {
                column.get(position).copied().flatten() == expected.get(position).copied().flatten()
            })
        };
        self.imports == prefix.imports
            && self.dense.defs.starts_with(&prefix.dense.defs)
            && columns_match(&self.dense.eq, &prefix.dense.eq)
            && columns_match(&self.dense.syn_eq, &prefix.dense.syn_eq)
            && columns_match(&self.dense.conv, &prefix.dense.conv)
            && self.axs == prefix.axs
            && self.ctx == prefix.ctx
            && self.amb_pred == prefix.amb_pred
            && self.amb_ax == prefix.amb_ax
            && self.amb_ctx == prefix.amb_ctx
            && self.amb_thm == prefix.amb_thm
    }

    pub(crate) fn eq_column(&self, column: EqColumn, reference: Ref) -> Option<Ref> {
        match column {
            EqColumn::Syn => self.syn_eq(reference),
            EqColumn::Conv => self.conv(reference),
            EqColumn::Semantic => self.eq(reference),
        }
    }

    pub(crate) fn set_eq_column(
        &mut self,
        column: EqColumn,
        left: Ref,
        right: Option<Ref>,
    ) -> bool {
        match column {
            EqColumn::Syn => self
                .dense
                .set_column(|dense| &mut dense.syn_eq, left, right),
            EqColumn::Conv => self.dense.set_column(|dense| &mut dense.conv, left, right),
            EqColumn::Semantic => self.dense.set_column(|dense| &mut dense.eq, left, right),
        }
    }

    pub(crate) fn push_syn_fact(&mut self, fact: SynFact) -> Option<SynFactId> {
        if let Some(id) = self.syn_free {
            let position = usize::try_from(id.get() - 1).ok()?;
            let slot = self.syn_facts.get_mut(position)?;
            let SynSlot::Free(free) = *slot else {
                return None;
            };
            self.syn_free = free.next;
            *slot = SynSlot::Fact(fact);
            return Some(id);
        }
        let next = i32::try_from(self.syn_facts.len()).ok()?.checked_add(1)?;
        let id = SynFactId::new(next)?;
        self.syn_facts.push(SynSlot::Fact(fact));
        Some(id)
    }

    pub(crate) fn replace_syn_fact(&mut self, id: SynFactId, fact: SynFact) -> bool {
        let Ok(position) = usize::try_from(id.get() - 1) else {
            return false;
        };
        let Some(slot) = self.syn_facts.get_mut(position) else {
            return false;
        };
        match slot {
            SynSlot::Fact(slot) => {
                *slot = fact;
                true
            }
            SynSlot::Free(_) => false,
        }
    }

    /// Removes an occupied syntactic-fact slot and links it into the free list.
    ///
    /// Returns `false` when `id` is absent or already free.
    #[must_use]
    pub fn remove_syn_fact(&mut self, id: SynFactId) -> bool {
        let Ok(position) = usize::try_from(id.get() - 1) else {
            return false;
        };
        let Some(slot) = self.syn_facts.get_mut(position) else {
            return false;
        };
        if matches!(slot, SynSlot::Free(_)) {
            return false;
        }
        *slot = SynSlot::Free(SynFree {
            next: self.syn_free,
        });
        self.syn_free = Some(id);
        true
    }

    /// Retains the first `len` syntactic-fact slots, drops the rest, and
    /// rebuilds the free list over the retained prefix.
    pub fn truncate_syn_facts(&mut self, len: usize) {
        self.syn_facts.truncate(len);
        self.rebuild_syn_free();
    }

    fn rebuild_syn_free(&mut self) {
        self.syn_free = None;
        for position in (0..self.syn_facts.len()).rev() {
            if matches!(self.syn_facts[position], SynSlot::Free(_)) {
                let Some(value) = i32::try_from(position)
                    .ok()
                    .and_then(|position| position.checked_add(1))
                    .and_then(SynFactId::new)
                else {
                    continue;
                };
                self.syn_facts[position] = SynSlot::Free(SynFree {
                    next: self.syn_free,
                });
                self.syn_free = Some(value);
            }
        }
    }

    #[cfg(test)]
    fn from_parts(
        imports: Vec<Import>,
        axs: impl IntoIterator<Item = String>,
        defs: Vec<(Row, Option<Ref>, Option<Ref>)>,
        ctx: impl IntoIterator<Item = Ref>,
        amb_ctx: Vec<AmbPred>,
        amb_thm: Vec<AmbPred>,
    ) -> Self {
        let mut arena = Self {
            imports,
            axs: axs.into_iter().collect(),
            dense: Dense::default(),
            syn_facts: Vec::new(),
            syn_free: None,
            ctx: ctx.into_iter().collect(),
            amb_pred: Vec::new(),
            amb_ax: BTreeSet::new(),
            amb_ctx: Cnf::empty(),
            amb_thm: ClassicalArena::new(),
            syl: ClassicalArena::new(),
            thm: ClassicalArena::new(),
        };
        for (row, sort, eq) in defs {
            let reference = arena.push_row(row, sort).expect("test definitions fit Ref");
            if let Some(eq) = eq {
                assert!(arena.set_eq_column(EqColumn::Semantic, reference, Some(eq)));
            }
        }
        for record in amb_ctx {
            assert!(arena.push_ambient_context(record));
        }
        for record in amb_thm {
            assert!(arena.push_ambient_theorem(record));
        }
        arena
    }
}

#[derive(Clone, Copy, Deserialize, Serialize)]
enum ArenaTag {
    #[serde(rename = "arena")]
    Arena,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct ArenaSerde {
    tag: ArenaTag,
    #[serde(rename = "import")]
    imports: Vec<Import>,
    amb: AmbSerde,
    pred: PredSerde,
    hol: HolSerde,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct AmbSerde {
    pred: Vec<AmbPred>,
    ax: Vec<String>,
    ctx: Cnf,
    thm: ClassicalArena,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct PredSerde {
    syl: ClassicalArena,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct HolSerde {
    defs: Vec<Row>,
    ax: Vec<String>,
    ctx: Vec<Ref>,
    thm: ClassicalArena,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    eq: Vec<Option<Ref>>,
    syn: HolSynSerde,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct HolSynSerde {
    #[serde(rename = "subst1", default, skip_serializing_if = "Vec::is_empty")]
    subst1: Vec<SynSlot>,
    #[serde(
        rename = "subst1_free",
        default,
        skip_serializing_if = "Option::is_none"
    )]
    subst1_free: Option<SynFactId>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    eq: Vec<Option<Ref>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    conv: Vec<Option<Ref>>,
}

impl From<Arena> for ArenaSerde {
    fn from(arena: Arena) -> Self {
        Self {
            tag: ArenaTag::Arena,
            imports: arena.imports,
            amb: AmbSerde {
                pred: arena.amb_pred,
                ax: arena.amb_ax.into_iter().collect(),
                ctx: arena.amb_ctx,
                thm: arena.amb_thm,
            },
            pred: PredSerde { syl: arena.syl },
            hol: HolSerde {
                defs: arena.dense.defs,
                ax: arena.axs.into_iter().collect(),
                ctx: arena.ctx.into_iter().collect(),
                thm: arena.thm,
                eq: arena.dense.eq,
                syn: HolSynSerde {
                    subst1: arena.syn_facts,
                    subst1_free: arena.syn_free,
                    eq: arena.dense.syn_eq,
                    conv: arena.dense.conv,
                },
            },
        }
    }
}

fn normalize_column(column: &mut Vec<Option<Ref>>) {
    while column.last() == Some(&None) {
        column.pop();
    }
}

fn column_is_resident(column: &[Option<Ref>], definitions: usize) -> bool {
    column
        .iter()
        .enumerate()
        .all(|(position, value)| value.is_none() || position < definitions)
}

impl TryFrom<ArenaSerde> for Arena {
    type Error = &'static str;

    fn try_from(arena: ArenaSerde) -> Result<Self, Self::Error> {
        let ArenaTag::Arena = arena.tag;
        let AmbSerde {
            pred,
            ax: amb_ax,
            ctx: amb_ctx,
            thm: amb_thm,
        } = arena.amb;
        let HolSerde {
            defs,
            ax,
            ctx: hol_ctx,
            thm: hol_thm,
            eq,
            mut syn,
        } = arena.hol;
        let mut eq = eq;
        for column in [&eq, &syn.eq, &syn.conv] {
            if !column_is_resident(column, defs.len()) {
                return Err("dense column has a member without a definition row");
            }
        }
        normalize_column(&mut eq);
        normalize_column(&mut syn.eq);
        normalize_column(&mut syn.conv);
        Ok(Self {
            imports: arena.imports,
            axs: ax.into_iter().collect(),
            dense: Dense {
                defs,
                eq,
                syn_eq: syn.eq,
                conv: syn.conv,
            },
            syn_facts: syn.subst1,
            syn_free: syn.subst1_free,
            ctx: hol_ctx.into_iter().collect(),
            amb_pred: pred,
            amb_ax: amb_ax.into_iter().collect(),
            amb_ctx,
            amb_thm,
            syl: arena.pred.syl,
            thm: hol_thm,
        })
    }
}

impl Serialize for Arena {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        ArenaSerde::from(self.clone()).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Arena {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        ArenaSerde::deserialize(deserializer)?
            .try_into()
            .map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use row::Expr;

    const fn reference(value: i32) -> Ref {
        Ref::new(value).unwrap()
    }

    #[test]
    fn members_use_one_based_dense_lookup() {
        let arena = Arena::from_parts(
            vec![],
            [],
            vec![
                (Row::new(Expr::KindStar), None, None),
                (
                    Row::new(Expr::BoolTy),
                    Some(reference(1)),
                    Some(reference(1)),
                ),
            ],
            [],
            vec![],
            vec![],
        );

        assert_eq!(arena.tag(reference(1)), Some(Tag::Kind(KindTag::Star)));
        assert_eq!(arena.eq(reference(1)), None);
        assert_eq!(arena.sort(reference(1)), None);
        assert_eq!(arena.tag(reference(2)), Some(Tag::Ty(TyTag::Bool)));
        assert_eq!(arena.sort(reference(2)), Some(reference(1)));
        assert_eq!(arena.eq(reference(2)), Some(reference(1)));
        assert_eq!(arena.tag(reference(3)), None);
    }

    #[test]
    fn mutable_arena_address_tracks_current_state() {
        let mut arena = Arena::empty();
        let empty = arena.addr();
        assert_eq!(arena.addr(), empty);

        arena.push_kind_star().unwrap();
        assert_ne!(arena.addr(), empty);
    }

    #[test]
    fn references_are_strictly_bounded_by_the_signed_wire_space() {
        let largest = i32::MAX - 1;
        assert_eq!(Ref::new(0), None);
        assert_eq!(Ref::new(largest).unwrap().get(), largest);
        assert_eq!(Ref::new(i32::MAX), None);
        assert_eq!(Ref::new(i32::MIN), None);

        for rejected in [0, i32::MIN, i32::MAX] {
            let mut bytes = Vec::new();
            covalence_lib_cbor::into_writer(&rejected, &mut bytes).unwrap();
            assert!(covalence_lib_cbor::from_reader::<Ref, _>(bytes.as_slice()).is_err());
        }
        assert_eq!(
            next_ref(usize::try_from(i32::MAX - 2).unwrap())
                .unwrap()
                .get(),
            i32::MAX - 1
        );
        assert_eq!(next_ref(usize::try_from(i32::MAX - 1).unwrap()), None);
    }

    #[test]
    fn every_dense_identifier_is_positive_and_i32_sized() {
        assert_eq!(
            std::mem::size_of::<Ref>(),
            std::mem::size_of::<NonZeroI32>()
        );
        assert_eq!(
            std::mem::size_of::<ImportId>(),
            std::mem::size_of::<NonZeroI32>()
        );
        assert_eq!(
            std::mem::size_of::<SynFactId>(),
            std::mem::size_of::<NonZeroI32>()
        );
        for rejected in [i32::MIN, -1, 0] {
            assert!(ImportId::new(rejected).is_none());
            assert!(SynFactId::new(rejected).is_none());
            let mut bytes = Vec::new();
            covalence_lib_cbor::into_writer(&rejected, &mut bytes).unwrap();
            assert!(covalence_lib_cbor::from_reader::<ImportId, _>(bytes.as_slice()).is_err());
            assert!(covalence_lib_cbor::from_reader::<SynFactId, _>(bytes.as_slice()).is_err());
        }
        assert_eq!(ImportId::new(i32::MAX).unwrap().get(), i32::MAX);
        assert_eq!(SynFactId::new(i32::MAX).unwrap().get(), i32::MAX);
    }
}
