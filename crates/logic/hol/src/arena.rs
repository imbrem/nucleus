use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::marker::PhantomData;
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
    Cbor = 1,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ObjectKind {
    Bytes = 0,
    ImportTable = 1,
    Arena = 2,
    Theorem = 3,
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

numeric_enum_serde!(Format, 0 => Format::Blob, 1 => Format::Cbor);
numeric_enum_serde!(
    ObjectKind,
    0 => ObjectKind::Bytes,
    1 => ObjectKind::ImportTable,
    2 => ObjectKind::Arena,
    3 => ObjectKind::Theorem,
);

pub trait LinkTarget: 'static {
    const KIND: ObjectKind;
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BytesObject {}
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ImportTableObject {}
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ArenaObject {}
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TheoremObject {}

impl LinkTarget for BytesObject {
    const KIND: ObjectKind = ObjectKind::Bytes;
}
impl LinkTarget for ImportTableObject {
    const KIND: ObjectKind = ObjectKind::ImportTable;
}
impl LinkTarget for ArenaObject {
    const KIND: ObjectKind = ObjectKind::Arena;
}
impl LinkTarget for TheoremObject {
    const KIND: ObjectKind = ObjectKind::Theorem;
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct AnyLink {
    pub addr: O256,
    pub format: Format,
    pub kind: ObjectKind,
}

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Link<T: LinkTarget> {
    addr: O256,
    format: Format,
    target: PhantomData<fn() -> T>,
}

impl<T: LinkTarget> Link<T> {
    #[must_use]
    pub const fn new(addr: O256, format: Format) -> Self {
        Self {
            addr,
            format,
            target: PhantomData,
        }
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
    pub const fn erase(&self) -> AnyLink {
        AnyLink {
            addr: self.addr,
            format: self.format,
            kind: T::KIND,
        }
    }
}

impl<T: LinkTarget> Clone for Link<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T: LinkTarget> Copy for Link<T> {}

impl<T: LinkTarget> TryFrom<AnyLink> for Link<T> {
    type Error = LinkKindError;
    fn try_from(link: AnyLink) -> Result<Self, Self::Error> {
        if link.kind == T::KIND {
            Ok(Self::new(link.addr, link.format))
        } else {
            Err(LinkKindError {
                expected: T::KIND,
                actual: link.kind,
            })
        }
    }
}

impl<T: LinkTarget> Serialize for Link<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.erase().serialize(serializer)
    }
}

impl<'de, T: LinkTarget> Deserialize<'de> for Link<T> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::try_from(AnyLink::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LinkKindError {
    pub expected: ObjectKind,
    pub actual: ObjectKind,
}
impl Display for LinkKindError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "expected {:?} link, found {:?}",
            self.expected, self.actual
        )
    }
}
impl Error for LinkKindError {}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ImportTable {
    links: Vec<AnyLink>,
}

impl ImportTable {
    #[must_use]
    pub const fn new() -> Self {
        Self { links: Vec::new() }
    }
    /// # Errors
    /// Returns an error if the import-table index cannot fit in `u32`.
    pub fn push<T: LinkTarget>(&mut self, link: Link<T>) -> Result<u32, ArenaError> {
        let id = u32::try_from(self.links.len()).map_err(|_| ArenaError::IndexOverflow)?;
        self.links.push(link.erase());
        Ok(id)
    }
    #[must_use]
    pub fn get(&self, id: u32) -> Option<&AnyLink> {
        self.links.get(id as usize)
    }
    pub fn iter(&self) -> impl Iterator<Item = &AnyLink> {
        self.links.iter()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Segment {
    pub start: Ix,
    pub end: Ix,
    pub import: u32,
    pub source_start: Ix,
}

impl Segment {
    /// # Errors
    /// Returns an error for an empty range or source-index overflow.
    pub fn new(start: Ix, end: Ix, import: u32, source_start: Ix) -> Result<Self, ArenaError> {
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
            import,
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

impl Serialize for Expr {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let tag = u32::try_from(u64::from(self.tag())).map_err(serde::ser::Error::custom)?;
        let mut words = vec![tag];
        match self {
            Self::KindStar | Self::TyBool => {}
            Self::KindArr { domain, codomain } | Self::TyArr { domain, codomain } => {
                words.extend([domain.get(), codomain.get()]);
            }
            Self::TyApp { function, argument } => words.extend([function.get(), argument.get()]),
            Self::TyLam { domain, body } => words.extend([domain.get(), body.get()]),
            Self::TyBv { index } => words.push(*index),
            Self::TySub { carrier, predicate } => words.extend([carrier.get(), predicate.get()]),
            Self::TyModel { predicate } => words.push(predicate.get()),
        }
        words.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Expr {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let words = Vec::<u32>::deserialize(deserializer)?;
        let (&tag, children) = words
            .split_first()
            .ok_or_else(|| serde::de::Error::custom("empty expression"))?;
        let tag = SurfaceTag::try_from(u64::from(tag)).map_err(serde::de::Error::custom)?;
        let child = |position: usize| {
            children
                .get(position)
                .copied()
                .ok_or_else(|| serde::de::Error::custom("missing expression child"))
                .and_then(|value| Ix::new(value).map_err(serde::de::Error::custom))
        };
        let no_extra = |expected: usize| {
            if children.len() == expected {
                Ok(())
            } else {
                Err(serde::de::Error::custom("wrong expression arity"))
            }
        };
        Ok(match tag {
            SurfaceTag::KindStar => {
                no_extra(0)?;
                Self::KindStar
            }
            SurfaceTag::KindArr => {
                no_extra(2)?;
                Self::KindArr {
                    domain: child(0)?,
                    codomain: child(1)?,
                }
            }
            SurfaceTag::TyBool => {
                no_extra(0)?;
                Self::TyBool
            }
            SurfaceTag::TyArr => {
                no_extra(2)?;
                Self::TyArr {
                    domain: child(0)?,
                    codomain: child(1)?,
                }
            }
            SurfaceTag::TyApp => {
                no_extra(2)?;
                Self::TyApp {
                    function: child(0)?,
                    argument: child(1)?,
                }
            }
            SurfaceTag::TyLam => {
                no_extra(2)?;
                Self::TyLam {
                    domain: child(0)?,
                    body: child(1)?,
                }
            }
            SurfaceTag::TyBv => {
                no_extra(1)?;
                Self::TyBv { index: children[0] }
            }
            SurfaceTag::TySub => {
                no_extra(2)?;
                Self::TySub {
                    carrier: child(0)?,
                    predicate: child(1)?,
                }
            }
            SurfaceTag::TyModel => {
                no_extra(1)?;
                Self::TyModel {
                    predicate: child(0)?,
                }
            }
            _ => {
                return Err(serde::de::Error::custom(
                    "tag is not a v0 arena type former",
                ));
            }
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Arena<I = Link<ImportTableObject>> {
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
                        segment.import,
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
        let Some(link) = self.imports.get(segment.import) else {
            return Resolve::Missing;
        };
        if link.kind != ObjectKind::Arena {
            return Resolve::WrongKind(link);
        }
        Resolve::Lazy {
            link,
            index: source,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Resolve<'a> {
    Local(&'a Expr),
    Lazy { link: &'a AnyLink, index: Ix },
    WrongKind(&'a AnyLink),
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
    pub fn link(&self) -> Link<ArenaObject> {
        Link::new(self.address(), Format::Cbor)
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
    pub fn link(&self) -> Link<ImportTableObject> {
        Link::new(self.address(), Format::Cbor)
    }
}

impl Serialize for SharedImportTable {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.link().serialize(serializer)
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
    ForwardReference { parent: Ix, child: Ix },
    LocalBaseBeforeSegment,
}
impl Display for ArenaError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "invalid HolE arena: {self:?}")
    }
}
impl Error for ArenaError {}
