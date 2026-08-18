use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::num::NonZeroU32;
use std::sync::Arc;

use covalence_lib_hash::O256;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::SurfaceTag;

pub const MAX_INDEX: u32 = i32::MAX as u32;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct Ix(NonZeroU32);

impl Ix {
    /// # Errors
    /// Returns an error unless the index is representable as a positive `i32`.
    pub const fn new(value: u32) -> Result<Self, ArenaError> {
        if value == 0 {
            Err(ArenaError::ZeroIndex)
        } else if value <= MAX_INDEX {
            match NonZeroU32::new(value) {
                Some(value) => Ok(Self(value)),
                None => Err(ArenaError::ZeroIndex),
            }
        } else {
            Err(ArenaError::IndexTooLarge(value))
        }
    }
    #[must_use]
    pub const fn get(self) -> u32 {
        self.0.get()
    }
}

impl<'de> Deserialize<'de> for Ix {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::new(u32::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Format {
    Blob = 0,
    CborDense = 1,
    CborSparse = 2,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ObjectKind {
    Bytes = 0,
    ImportTable = 1,
    Arena = 2,
    Sequent = 3,
}

macro_rules! numeric_enum_serde {
    ($name:ty, $($value:literal => $variant:path),+ $(,)?) => {
        impl Serialize for $name {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                (*self as u8).serialize(serializer)
            }
        }
        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                match u8::deserialize(deserializer)? {
                    $($value => Ok($variant),)+
                    _ => Err(serde::de::Error::custom("unsupported v0 enum tag")),
                }
            }
        }
    };
}

numeric_enum_serde!(
    Format,
    0 => Format::Blob,
    1 => Format::CborDense,
    2 => Format::CborSparse,
);
numeric_enum_serde!(
    ObjectKind,
    0 => ObjectKind::Bytes,
    1 => ObjectKind::ImportTable,
    2 => ObjectKind::Arena,
    3 => ObjectKind::Sequent,
);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct Link {
    pub addr: O256,
    pub format: Format,
    pub kind: ObjectKind,
}

impl Link {
    #[must_use]
    pub const fn new(addr: O256, format: Format, kind: ObjectKind) -> Self {
        Self { addr, format, kind }
    }
    #[must_use]
    pub const fn address(&self) -> O256 {
        self.addr
    }
    #[must_use]
    pub const fn format(&self) -> Format {
        self.format
    }
    #[must_use]
    pub const fn kind(&self) -> ObjectKind {
        self.kind
    }
}

/// A reference through an import table. Format and object kind are stored at
/// the reference site, never behind the content hash.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct LinkRef {
    pub import: u32,
    pub format: Format,
    pub kind: ObjectKind,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ImportTable {
    addresses: Vec<O256>,
}

impl ImportTable {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            addresses: Vec::new(),
        }
    }
    /// # Errors
    /// Returns an error if the import-table index cannot fit in `u32`.
    pub fn push(&mut self, address: O256) -> Result<u32, ArenaError> {
        let id = u32::try_from(self.addresses.len()).map_err(|_| ArenaError::IndexOverflow)?;
        self.addresses.push(address);
        Ok(id)
    }
    #[must_use]
    pub fn get(&self, id: u32) -> Option<O256> {
        self.addresses.get(id as usize).copied()
    }
    pub fn iter(&self) -> impl Iterator<Item = O256> + '_ {
        self.addresses.iter().copied()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Segment {
    pub start: Ix,
    pub end: Ix,
    pub link: LinkRef,
    pub source_start: Ix,
}

impl Segment {
    /// # Errors
    /// Returns an error for an empty range or source-index overflow.
    pub fn new(start: Ix, end: Ix, link: LinkRef, source_start: Ix) -> Result<Self, ArenaError> {
        if link.kind != ObjectKind::Arena {
            return Err(ArenaError::WrongObjectKind {
                expected: ObjectKind::Arena,
                actual: link.kind,
            });
        }
        if start >= end {
            return Err(ArenaError::EmptySegment);
        }
        let width = end.get() - start.get();
        let source_end = source_start
            .get()
            .checked_add(width - 1)
            .ok_or(ArenaError::IndexOverflow)?;
        Ix::new(source_end)?;
        Ok(Self {
            start,
            end,
            link,
            source_start,
        })
    }
    pub(crate) fn translate(self, index: Ix) -> Option<Ix> {
        (self.start <= index && index < self.end).then(|| {
            Ix::new(self.source_start.get() + index.get() - self.start.get())
                .expect("segment constructor checked translation")
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expr {
    KindStar,
    KindArr { domain: Ix, codomain: Ix },
    TyBool,
    TyArr { domain: Ix, codomain: Ix },
    TyApp { function: Ix, argument: Ix },
    TyLam { domain: Ix, body: Ix },
    TyBv { index: u32 },
    TySub { carrier: Ix, predicate: Ix },
    TyModel { predicate: Ix },
}

/// Simple traversal-oriented wire form. `ix` contains every arena child in
/// constructor order; `var` is present only for variable leaves.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ExprWire {
    tag: String,
    #[serde(default)]
    ix: Vec<Ix>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    var: Option<u32>,
}

impl From<&Expr> for ExprWire {
    fn from(expr: &Expr) -> Self {
        Self {
            tag: expr.tag().to_string(),
            ix: expr.children().collect(),
            var: match expr {
                Expr::TyBv { index } => Some(*index),
                _ => None,
            },
        }
    }
}

impl TryFrom<ExprWire> for Expr {
    type Error = &'static str;

    fn try_from(wire: ExprWire) -> Result<Self, Self::Error> {
        let tag = wire.tag.parse().map_err(|_| "unknown expression tag")?;
        let no_var = wire.var.is_none();
        match (tag, wire.ix.as_slice(), wire.var) {
            (SurfaceTag::KindStar, [], None) => Ok(Self::KindStar),
            (SurfaceTag::KindArr, [domain, codomain], None) => Ok(Self::KindArr {
                domain: *domain,
                codomain: *codomain,
            }),
            (SurfaceTag::TyBool, [], None) => Ok(Self::TyBool),
            (SurfaceTag::TyArr, [domain, codomain], None) => Ok(Self::TyArr {
                domain: *domain,
                codomain: *codomain,
            }),
            (SurfaceTag::TyApp, [function, argument], None) => Ok(Self::TyApp {
                function: *function,
                argument: *argument,
            }),
            (SurfaceTag::TyLam, [domain, body], None) => Ok(Self::TyLam {
                domain: *domain,
                body: *body,
            }),
            (SurfaceTag::TyBv, [], Some(index)) => Ok(Self::TyBv { index }),
            (SurfaceTag::TySub, [carrier, predicate], None) => Ok(Self::TySub {
                carrier: *carrier,
                predicate: *predicate,
            }),
            (SurfaceTag::TyModel, [predicate], None) => Ok(Self::TyModel {
                predicate: *predicate,
            }),
            _ if !no_var => Err("only a variable expression may carry `var`"),
            _ => Err("wrong number of expression children"),
        }
    }
}

impl Serialize for Expr {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        ExprWire::from(self).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Expr {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        ExprWire::deserialize(deserializer)?
            .try_into()
            .map_err(serde::de::Error::custom)
    }
}

impl Expr {
    #[must_use]
    pub const fn tag(&self) -> SurfaceTag {
        match self {
            Self::KindStar => SurfaceTag::KindStar,
            Self::KindArr { .. } => SurfaceTag::KindArr,
            Self::TyBool => SurfaceTag::TyBool,
            Self::TyArr { .. } => SurfaceTag::TyArr,
            Self::TyApp { .. } => SurfaceTag::TyApp,
            Self::TyLam { .. } => SurfaceTag::TyLam,
            Self::TyBv { .. } => SurfaceTag::TyBv,
            Self::TySub { .. } => SurfaceTag::TySub,
            Self::TyModel { .. } => SurfaceTag::TyModel,
        }
    }
    pub fn children(&self) -> impl Iterator<Item = Ix> + '_ {
        let pair = match self {
            Self::KindStar | Self::TyBool | Self::TyBv { .. } => [None, None],
            Self::KindArr { domain, codomain } | Self::TyArr { domain, codomain } => {
                [Some(*domain), Some(*codomain)]
            }
            Self::TyApp { function, argument } => [Some(*function), Some(*argument)],
            Self::TyLam { domain, body } => [Some(*domain), Some(*body)],
            Self::TySub { carrier, predicate } => [Some(*carrier), Some(*predicate)],
            Self::TyModel { predicate } => [Some(*predicate), None],
        };
        pair.into_iter().flatten()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Arena<I = Option<O256>> {
    imports: I,
    segments: Vec<Segment>,
    local_base: u32,
    defs: Vec<Expr>,
}

#[derive(Deserialize)]
struct ArenaWire<I> {
    imports: I,
    segments: Vec<Segment>,
    local_base: u32,
    defs: Vec<Expr>,
}

impl<'de, I: Deserialize<'de>> Deserialize<'de> for Arena<I> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = ArenaWire::<I>::deserialize(deserializer)?;
        let mut arena = Self::new(wire.imports);
        for segment in wire.segments {
            arena
                .add_segment(
                    Segment::new(
                        segment.start,
                        segment.end,
                        segment.link,
                        segment.source_start,
                    )
                    .map_err(serde::de::Error::custom)?,
                )
                .map_err(serde::de::Error::custom)?;
        }
        arena
            .set_local_base(wire.local_base)
            .map_err(serde::de::Error::custom)?;
        for expr in wire.defs {
            arena.push(expr).map_err(serde::de::Error::custom)?;
        }
        Ok(arena)
    }
}

impl<I> Arena<I> {
    #[must_use]
    pub const fn new(imports: I) -> Self {
        Self {
            imports,
            segments: Vec::new(),
            local_base: 1,
            defs: Vec::new(),
        }
    }
    #[must_use]
    pub const fn imports(&self) -> &I {
        &self.imports
    }
    pub fn segments(&self) -> &[Segment] {
        &self.segments
    }
    #[must_use]
    pub const fn local_base(&self) -> u32 {
        self.local_base
    }
    pub fn defs(&self) -> &[Expr] {
        &self.defs
    }
    pub fn map_imports<J>(self, map: impl FnOnce(I) -> J) -> Arena<J> {
        Arena {
            imports: map(self.imports),
            segments: self.segments,
            local_base: self.local_base,
            defs: self.defs,
        }
    }
    /// # Errors
    /// Rejects overlap or changes after local definitions have been added.
    pub fn add_segment(&mut self, segment: Segment) -> Result<(), ArenaError> {
        if !self.defs.is_empty() {
            return Err(ArenaError::SegmentsAfterDefinitions);
        }
        let position = self
            .segments
            .binary_search_by_key(&segment.start, |x| x.start)
            .unwrap_or_else(|position| position);
        if position > 0 && self.segments[position - 1].end > segment.start
            || position < self.segments.len() && self.segments[position].start < segment.end
        {
            return Err(ArenaError::OverlappingSegment);
        }
        self.local_base = self.local_base.max(segment.end.get());
        self.segments.insert(position, segment);
        Ok(())
    }
    /// # Errors
    /// Rejects zero, overflow, a base before a segment, or a late change.
    pub fn set_local_base(&mut self, local_base: u32) -> Result<(), ArenaError> {
        if !self.defs.is_empty() {
            return Err(ArenaError::SegmentsAfterDefinitions);
        }
        if local_base == 0 {
            return Err(ArenaError::ZeroIndex);
        }
        if local_base > MAX_INDEX {
            return Err(ArenaError::IndexTooLarge(local_base));
        }
        let required = self.segments.last().map_or(1, |segment| segment.end.get());
        if local_base < required {
            return Err(ArenaError::LocalBaseBeforeSegment);
        }
        self.local_base = local_base;
        Ok(())
    }
    /// # Errors
    /// Rejects forward references and index exhaustion.
    pub fn push(&mut self, expr: Expr) -> Result<Ix, ArenaError> {
        let offset = u32::try_from(self.defs.len()).map_err(|_| ArenaError::IndexOverflow)?;
        let index = Ix::new(
            self.local_base
                .checked_add(offset)
                .ok_or(ArenaError::IndexOverflow)?,
        )?;
        if let Some(child) = expr.children().find(|child| *child >= index) {
            return Err(ArenaError::ForwardReference {
                parent: index,
                child,
            });
        }
        self.defs.push(expr);
        Ok(index)
    }
    #[must_use]
    pub fn local(&self, index: Ix) -> Option<&Expr> {
        (index.get() >= self.local_base)
            .then(|| index.get() - self.local_base)
            .and_then(|offset| self.defs.get(offset as usize))
    }
}

impl Arena<ImportTable> {
    #[must_use]
    pub fn resolve(&self, index: Ix) -> Resolve<'_> {
        if let Some(expr) = self.local(index) {
            return Resolve::Local(expr);
        }
        let position = self
            .segments
            .partition_point(|segment| segment.start <= index);
        let Some(segment) = position.checked_sub(1).and_then(|i| self.segments.get(i)) else {
            return Resolve::Missing;
        };
        let Some(source) = segment.translate(index) else {
            return Resolve::Missing;
        };
        let Some(address) = self.imports.get(segment.link.import) else {
            return Resolve::Missing;
        };
        Resolve::Lazy {
            link: Link::new(address, segment.link.format, segment.link.kind),
            index: source,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Resolve<'a> {
    Local(&'a Expr),
    Lazy { link: Link, index: Ix },
    Missing,
}

#[derive(Clone, Debug)]
pub struct SharedArena(Arc<CachedArena>);
#[derive(Debug)]
struct CachedArena {
    arena: Arena,
    address: O256,
}

impl SharedArena {
    /// # Errors
    /// Returns an error if the arena cannot be serialized to stable v0 CBOR.
    pub fn new(arena: Arena) -> Result<Self, crate::EncodeError> {
        let bytes = crate::serialize_cbor(&arena)?;
        let address = O256::from_bytes(&bytes);
        Ok(Self(Arc::new(CachedArena { arena, address })))
    }
    #[must_use]
    pub fn arena(&self) -> &Arena {
        &self.0.arena
    }
    #[must_use]
    pub fn address(&self) -> O256 {
        self.0.address
    }
    #[must_use]
    pub fn link(&self) -> Link {
        Link::new(self.address(), Format::CborDense, ObjectKind::Arena)
    }
}

impl Serialize for SharedArena {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.link().serialize(serializer)
    }
}

#[derive(Clone, Debug)]
pub struct SharedImportTable(Arc<CachedImportTable>);
#[derive(Debug)]
struct CachedImportTable {
    table: ImportTable,
    address: O256,
}

impl SharedImportTable {
    /// # Errors
    /// Returns an error if the table cannot be serialized to stable v0 CBOR.
    pub fn new(table: ImportTable) -> Result<Self, crate::EncodeError> {
        let bytes = crate::serialize_cbor(&table)?;
        let address = O256::from_bytes(&bytes);
        Ok(Self(Arc::new(CachedImportTable { table, address })))
    }
    #[must_use]
    pub fn table(&self) -> &ImportTable {
        &self.0.table
    }
    #[must_use]
    pub fn address(&self) -> O256 {
        self.0.address
    }
    #[must_use]
    pub fn link(&self) -> O256 {
        self.address()
    }
}

impl Serialize for SharedImportTable {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.address().serialize(serializer)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ArenaError {
    ZeroIndex,
    IndexTooLarge(u32),
    IndexOverflow,
    EmptySegment,
    OverlappingSegment,
    SegmentsAfterDefinitions,
    ForwardReference {
        parent: Ix,
        child: Ix,
    },
    LocalBaseBeforeSegment,
    WrongObjectKind {
        expected: ObjectKind,
        actual: ObjectKind,
    },
}
impl Display for ArenaError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "invalid HolE arena: {self:?}")
    }
}
impl Error for ArenaError {}
