//! Raw, unvalidated Ethane syntax arenas.
//!
//! Deserialization establishes only the representation invariants. It does
//! not establish kinding, typing, equality, or provability.

pub mod cas;
mod kernel;
mod resolve;
mod row;
pub mod wire;

pub use kernel::{EqualityIx, Kernel, KernelError, KindIx, TmIx, TyIx};
pub use resolve::{ResolveError, Resolver, TrustedResolver};
pub use row::{KindTag, Sort, Tag, TmTag, TyTag};

use std::{collections::BTreeSet, num::NonZeroU64};

use covalence_lib_hash::O256;
use row::Row;
use serde::{Deserialize, Serialize};

/// A one-based local definition reference. `Ref(n)` addresses `defs[n - 1]`.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(transparent)]
#[serde(transparent)]
pub struct Ref(NonZeroU64);

impl Ref {
    #[must_use]
    pub const fn new(value: u64) -> Option<Self> {
        match NonZeroU64::new(value) {
            Some(value) => Some(Self(value)),
            None => None,
        }
    }

    #[must_use]
    pub const fn get(self) -> u64 {
        self.0.get()
    }
}

impl From<Ref> for u64 {
    fn from(value: Ref) -> Self {
        value.get()
    }
}

impl TryFrom<u64> for Ref {
    type Error = ZeroRef;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        Self::new(value).ok_or(ZeroRef)
    }
}

/// A one-based index into an arena's import array.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(transparent)]
#[serde(transparent)]
pub struct ImportId(NonZeroU64);

impl ImportId {
    #[must_use]
    pub const fn new(value: u64) -> Option<Self> {
        match NonZeroU64::new(value) {
            Some(value) => Some(Self(value)),
            None => None,
        }
    }

    #[must_use]
    pub const fn get(self) -> u64 {
        self.0.get()
    }
}

impl From<ImportId> for u64 {
    fn from(value: ImportId) -> Self {
        value.get()
    }
}

impl TryFrom<u64> for ImportId {
    type Error = ZeroRef;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        Self::new(value).ok_or(ZeroRef)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ZeroRef;

impl std::fmt::Display for ZeroRef {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        output.write_str("references are one-based")
    }
}

impl std::error::Error for ZeroRef {}

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

/// Raw metadata appearing in either the assumption or assertion list.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "tag", deny_unknown_fields)]
pub enum Meta {
    #[serde(rename = "meta.valid")]
    Valid { src: ImportId },
    #[serde(rename = "meta.wf")]
    Wf { src: ImportId, ix: Ref, sort: Ref },
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

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Dense {
    defs: Vec<Row>,
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
        self.row(reference).and_then(Row::eq)
    }

    fn sort(&self, reference: Ref) -> Option<Ref> {
        self.row(reference).and_then(Row::sort)
    }
}

impl Dense {
    fn row(&self, reference: Ref) -> Option<&Row> {
        let position = usize::try_from(reference.get() - 1).ok()?;
        self.defs.get(position)
    }
}

/// A one-based dense Ethane arena.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Arena {
    imports: Vec<Import>,
    axs: BTreeSet<String>,
    dense: Dense,
    ctx: BTreeSet<Ref>,
    assume: Vec<Meta>,
    assert: Vec<Meta>,
}

impl Arena {
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            imports: Vec::new(),
            axs: BTreeSet::new(),
            dense: Dense { defs: Vec::new() },
            ctx: BTreeSet::new(),
            assume: Vec::new(),
            assert: Vec::new(),
        }
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

    #[must_use]
    pub fn sort(&self, reference: Ref) -> Option<Ref> {
        self.dense.sort(reference)
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
    pub fn assumptions(&self) -> &[Meta] {
        &self.assume
    }

    #[must_use]
    pub fn assertions(&self) -> &[Meta] {
        &self.assert
    }

    /// Append one raw import entry.
    ///
    /// This is a representation operation, not a trust decision. A checked
    /// layer must resolve and validate every import it relies on.
    pub fn push_import(&mut self, import: Import) -> Option<ImportId> {
        let next = u64::try_from(self.imports.len()).ok()?.checked_add(1)?;
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

    /// Append unvalidated premise metadata.
    pub fn push_assumption(&mut self, record: Meta) {
        self.assume.push(record);
    }

    /// Append unvalidated conclusion metadata.
    pub fn push_assertion(&mut self, record: Meta) {
        self.assert.push(record);
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
        self.push_row(Row::new(row::Expr::KindStar))
    }

    /// Append a raw `kind.arr` row.
    pub fn push_kind_arr(&mut self, domain: Ref, codomain: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::KindArr(domain, codomain)))
    }

    /// Append a raw `ty.bool` row.
    pub fn push_bool_ty(&mut self) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::BoolTy))
    }

    /// Append a raw `ty.arr` row.
    pub fn push_ty_arr(&mut self, domain: Ref, codomain: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyArr(domain, codomain)))
    }

    /// Append a raw `ty.app` row.
    pub fn push_ty_app(&mut self, function: Ref, argument: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyApp(function, argument)))
    }

    /// Append a raw `ty.lam` row. The first child is the binder variable.
    pub fn push_ty_lam(&mut self, binder: Ref, body: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyLam(binder, body)))
    }

    /// Append a raw typed type-variable row.
    pub fn push_ty_fv(&mut self, name: u64, kind: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyFv { name, kind }))
    }

    /// Append a raw type-existential proposition row.
    pub fn push_ty_exists(&mut self, name: u64, predicate: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyExists { name, predicate }))
    }

    /// Append a raw model-type row.
    pub fn push_model(&mut self, name: u64, predicate: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Model { name, predicate }))
    }

    /// Append a raw typed term-variable row.
    pub fn push_tm_fv(&mut self, name: u64, ty: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TmFv { name, ty }))
    }

    /// Append a raw `tm.app` row.
    pub fn push_app(&mut self, function: Ref, argument: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::App(function, argument)))
    }

    /// Append a raw `tm.lam` row. The first child is the binder variable.
    pub fn push_lam(&mut self, binder: Ref, body: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Lam(binder, body)))
    }

    /// Append a raw Boolean literal row.
    pub fn push_bool(&mut self, value: bool) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Bool(value)))
    }

    /// Append a raw object-language equality row.
    pub fn push_tm_eq(&mut self, left: Ref, right: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Eq(left, right)))
    }

    /// Append a raw choice row.
    pub fn push_eps(&mut self, ty: Ref, predicate: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::Eps { ty, predicate }))
    }

    /// Append a raw term proxy into an import.
    pub fn push_tm_ref(&mut self, src: ImportId, ix: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TmRef { src, ix }))
    }

    /// Append a raw type proxy into an import.
    pub fn push_ty_ref(&mut self, src: ImportId, ix: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::TyRef { src, ix }))
    }

    /// Append a raw kind proxy into an import.
    pub fn push_kind_ref(&mut self, src: ImportId, ix: Ref) -> Option<Ref> {
        self.push_row(Row::new(row::Expr::KindRef { src, ix }))
    }

    fn import(&self, source: ImportId) -> Option<&Import> {
        let position = usize::try_from(source.get() - 1).ok()?;
        self.imports.get(position)
    }

    fn row(&self, reference: Ref) -> Option<&Row> {
        self.dense.row(reference)
    }

    fn push_row(&mut self, row: Row) -> Option<Ref> {
        let next = u64::try_from(self.dense.defs.len()).ok()?.checked_add(1)?;
        let reference = Ref::new(next)?;
        self.dense.defs.push(row);
        Some(reference)
    }

    fn set_eq(&mut self, reference: Ref, right: Ref) -> bool {
        let Ok(position) = usize::try_from(reference.get() - 1) else {
            return false;
        };
        let Some(row) = self.dense.defs.get_mut(position) else {
            return false;
        };
        row.set_eq(right);
        true
    }

    #[cfg(test)]
    fn from_parts(
        imports: Vec<Import>,
        axs: impl IntoIterator<Item = String>,
        defs: Vec<Row>,
        ctx: impl IntoIterator<Item = Ref>,
        assume: Vec<Meta>,
        assert: Vec<Meta>,
    ) -> Self {
        Self {
            imports,
            axs: axs.into_iter().collect(),
            dense: Dense { defs },
            ctx: ctx.into_iter().collect(),
            assume,
            assert,
        }
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
    imports: Vec<Import>,
    axs: Vec<String>,
    defs: Vec<Row>,
    ctx: Vec<Ref>,
    assume: Vec<Meta>,
    assert: Vec<Meta>,
}

impl From<Arena> for ArenaSerde {
    fn from(arena: Arena) -> Self {
        Self {
            tag: ArenaTag::Arena,
            imports: arena.imports,
            axs: arena.axs.into_iter().collect(),
            defs: arena.dense.defs,
            ctx: arena.ctx.into_iter().collect(),
            assume: arena.assume,
            assert: arena.assert,
        }
    }
}

impl From<ArenaSerde> for Arena {
    fn from(arena: ArenaSerde) -> Self {
        let ArenaTag::Arena = arena.tag;
        Self {
            imports: arena.imports,
            axs: arena.axs.into_iter().collect(),
            dense: Dense { defs: arena.defs },
            ctx: arena.ctx.into_iter().collect(),
            assume: arena.assume,
            assert: arena.assert,
        }
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
        Ok(ArenaSerde::deserialize(deserializer)?.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use row::Expr;

    const fn reference(value: u64) -> Ref {
        Ref::new(value).unwrap()
    }

    #[test]
    fn members_use_one_based_dense_lookup() {
        let arena = Arena::from_parts(
            vec![],
            [],
            vec![
                Row::new(Expr::KindStar).with_sort(reference(2)),
                Row::new(Expr::BoolTy)
                    .with_eq(reference(1))
                    .with_sort(reference(2)),
            ],
            [],
            vec![],
            vec![],
        );

        assert_eq!(arena.tag(reference(1)), Some(Tag::Kind(KindTag::Star)));
        assert_eq!(arena.eq(reference(1)), None);
        assert_eq!(arena.sort(reference(1)), Some(reference(2)));
        assert_eq!(arena.tag(reference(2)), Some(Tag::Ty(TyTag::Bool)));
        assert_eq!(arena.eq(reference(2)), Some(reference(1)));
        assert_eq!(arena.tag(reference(3)), None);
    }
}
