use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::num::NonZeroU32;
use std::sync::Arc;

use bytes::Bytes;
use covalence_data_num::Num;
use covalence_lib_hash::O256;
use serde::de::Visitor;
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
                    _ => Err(serde::de::Error::custom("unsupported enum tag")),
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
    /// Insert an address, returning its existing ID when it is already present.
    ///
    /// # Errors
    /// Returns an error if a new import-table index cannot fit in `u32`.
    pub fn push(&mut self, address: O256) -> Result<u32, ArenaError> {
        if let Some(id) = self
            .addresses
            .iter()
            .position(|candidate| *candidate == address)
        {
            return u32::try_from(id).map_err(|_| ArenaError::IndexOverflow);
        }
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
#[serde(try_from = "SegmentWire")]
pub struct Segment {
    start: Ix,
    end: Ix,
    link: LinkRef,
    source_start: Ix,
}

#[derive(Deserialize)]
struct SegmentWire {
    start: Ix,
    end: Ix,
    link: LinkRef,
    source_start: Ix,
}

impl TryFrom<SegmentWire> for Segment {
    type Error = ArenaError;

    fn try_from(wire: SegmentWire) -> Result<Self, Self::Error> {
        Self::new(wire.start, wire.end, wire.link, wire.source_start)
    }
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
    #[must_use]
    pub const fn start(self) -> Ix {
        self.start
    }
    #[must_use]
    pub const fn end(self) -> Ix {
        self.end
    }
    #[must_use]
    pub const fn link(self) -> LinkRef {
        self.link
    }
    #[must_use]
    pub const fn source_start(self) -> Ix {
        self.source_start
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
    /// Lean `Nucleus.Hol.Kind.star`.
    KindStar,
    /// Lean `Nucleus.Hol.Kind.arr`; children are domain and codomain kinds.
    KindArr { domain: Ix, codomain: Ix },
    /// Lean `Nucleus.HolE.Expr.boolTy`.
    TyBool,
    /// Lean `Nucleus.HolE.Expr.arr`.
    TyArr { domain: Ix, codomain: Ix },
    /// Lean `Nucleus.HolE.Expr.tyApp`.
    TyApp { function: Ix, argument: Ix },
    /// Lean `Nucleus.HolE.Expr.tyLam`; `domain` records the bound variable's kind.
    TyLam { domain: Ix, body: Ix },
    /// Lean `Nucleus.HolE.Expr.tyBv` after decoding the heterogeneous index.
    TyBv { index: u32 },
    /// Lean `Nucleus.HolE.Expr.sub`.
    TySub { carrier: Ix, predicate: Ix },
    /// Lean `Nucleus.HolE.Expr.tyExists`.
    TyExists { predicate: Ix },
    /// Lean `Nucleus.HolE.Expr.model`.
    TyModel { predicate: Ix },
    /// Lean `Nucleus.HolE.Expr.bv`.
    TmBv { index: u32 },
    /// Lean `Nucleus.HolE.Expr.fv`; free variables carry their syntactic type.
    TmFv { name: u32, ty: Ix },
    /// Lean `Nucleus.HolE.Expr.app`.
    TmApp { function: Ix, argument: Ix },
    /// Lean `Nucleus.HolE.Expr.lam`.
    TmLam { domain: Ix, body: Ix },
    /// Lean `Nucleus.HolE.Expr.bool`.
    TmBool { value: bool },
    /// Lean `Nucleus.HolE.Expr.eq`; the LCF checker infers the shared operand type.
    TmEq { left: Ix, right: Ix },
    /// Lean `Nucleus.HolE.Expr.eps`.
    TmEps { ty: Ix, predicate: Ix },
    /// Lean `Nucleus.HolE.Expr.abs`.
    TmAbs {
        carrier: Ix,
        predicate: Ix,
        value: Ix,
    },
    /// Lean `Nucleus.HolE.Expr.rep`.
    TmRep {
        carrier: Ix,
        predicate: Ix,
        value: Ix,
    },
    /// Surface conversion. Its LCF interpretation is the source term when its
    /// type equals `target`, and canonical inhabited garbage otherwise.
    TmCast { term: Ix, target: Ix },
    /// Arbitrary-precision natural literal surface sugar. Foundational arenas
    /// define naturals in pure `HolE` and deliberately do not use this node.
    TmNat { value: Num },
    /// Immutable byte-string literal surface sugar.
    TmBytes { value: Bytes },
}

/// Traversal-oriented wire form. `ix` contains every arena child in
/// constructor order; `var` is present only for variable leaves.
#[derive(Serialize, Deserialize)]
struct ExprWire {
    tag: String,
    #[serde(default)]
    ix: Vec<Ix>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    var: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    value: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    data: Option<WireBytes>,
}

struct WireBytes(Vec<u8>);

impl Serialize for WireBytes {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.0)
    }
}

impl<'de> Deserialize<'de> for WireBytes {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct BytesVisitor;
        impl Visitor<'_> for BytesVisitor {
            type Value = WireBytes;

            fn expecting(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
                formatter.write_str("a byte string")
            }
            fn visit_bytes<E: serde::de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
                Ok(WireBytes(value.to_vec()))
            }
            fn visit_byte_buf<E: serde::de::Error>(self, value: Vec<u8>) -> Result<Self::Value, E> {
                Ok(WireBytes(value))
            }
        }
        deserializer.deserialize_bytes(BytesVisitor)
    }
}

impl From<&Expr> for ExprWire {
    fn from(expr: &Expr) -> Self {
        Self {
            tag: expr.tag().to_string(),
            ix: expr.children().collect(),
            var: match expr {
                Expr::TyBv { index } | Expr::TmBv { index } => Some(*index),
                Expr::TmFv { name, .. } => Some(*name),
                _ => None,
            },
            value: match expr {
                Expr::TmBool { value } => Some(*value),
                _ => None,
            },
            data: match expr {
                Expr::TmNat { value } => Some(WireBytes(value.to_canonical_bytes())),
                Expr::TmBytes { value } => Some(WireBytes(value.to_vec())),
                _ => None,
            },
        }
    }
}

impl TryFrom<ExprWire> for Expr {
    type Error = &'static str;

    fn try_from(wire: ExprWire) -> Result<Self, Self::Error> {
        let tag = wire.tag.parse().map_err(|_| "unknown expression tag")?;
        let var = matches!(tag, SurfaceTag::TyBv | SurfaceTag::TmBv | SurfaceTag::TmFv)
            .then_some(wire.var)
            .flatten();
        let value = (tag == SurfaceTag::TmBool).then_some(wire.value).flatten();
        let data = matches!(tag, SurfaceTag::TmNat | SurfaceTag::TmBytes)
            .then_some(wire.data.as_ref().map(|data| data.0.as_slice()))
            .flatten();
        Self::from_parts(tag, &wire.ix, var, value, data)
    }
}

impl Expr {
    /// Build an expression from its traversal-oriented wire components.
    ///
    /// # Errors
    /// Rejects the wrong child arity or a `var` payload on a non-variable tag.
    pub fn from_parts(
        tag: SurfaceTag,
        children: &[Ix],
        var: Option<u32>,
        value: Option<bool>,
        data: Option<&[u8]>,
    ) -> Result<Self, &'static str> {
        if tag == SurfaceTag::TmNat {
            return match (children, var, value, data) {
                ([], None, None, Some(data)) => Num::from_canonical_bytes(data)
                    .map(|value| Self::TmNat { value })
                    .map_err(|_| "non-canonical natural literal"),
                _ => Err("invalid natural literal payload"),
            };
        }
        if tag == SurfaceTag::TmBytes {
            return match (children, var, value, data) {
                ([], None, None, Some(data)) => Ok(Self::TmBytes {
                    value: Bytes::copy_from_slice(data),
                }),
                _ => Err("invalid byte-string literal payload"),
            };
        }
        if data.is_some() {
            return Err("only a literal expression may carry `data`");
        }
        let no_payload = var.is_none() && value.is_none();
        match (tag, children, var, value) {
            (SurfaceTag::KindStar, [], None, None) => Ok(Self::KindStar),
            (SurfaceTag::KindArr, [domain, codomain], None, None) => Ok(Self::KindArr {
                domain: *domain,
                codomain: *codomain,
            }),
            (SurfaceTag::TyBool, [], None, None) => Ok(Self::TyBool),
            (SurfaceTag::TyArr, [domain, codomain], None, None) => Ok(Self::TyArr {
                domain: *domain,
                codomain: *codomain,
            }),
            (SurfaceTag::TyApp, [function, argument], None, None) => Ok(Self::TyApp {
                function: *function,
                argument: *argument,
            }),
            (SurfaceTag::TyLam, [domain, body], None, None) => Ok(Self::TyLam {
                domain: *domain,
                body: *body,
            }),
            (SurfaceTag::TyBv, [], Some(index), None) => Ok(Self::TyBv { index }),
            (SurfaceTag::TySub, [carrier, predicate], None, None) => Ok(Self::TySub {
                carrier: *carrier,
                predicate: *predicate,
            }),
            (SurfaceTag::TyExists, [predicate], None, None) => Ok(Self::TyExists {
                predicate: *predicate,
            }),
            (SurfaceTag::TyModel, [predicate], None, None) => Ok(Self::TyModel {
                predicate: *predicate,
            }),
            (SurfaceTag::TmBv, [], Some(index), None) => Ok(Self::TmBv { index }),
            (SurfaceTag::TmFv, [ty], Some(name), None) => Ok(Self::TmFv { name, ty: *ty }),
            (SurfaceTag::TmApp, [function, argument], None, None) => Ok(Self::TmApp {
                function: *function,
                argument: *argument,
            }),
            (SurfaceTag::TmLam, [domain, body], None, None) => Ok(Self::TmLam {
                domain: *domain,
                body: *body,
            }),
            (SurfaceTag::TmBool, [], None, Some(value)) => Ok(Self::TmBool { value }),
            (SurfaceTag::TmEq, [left, right], None, None) => Ok(Self::TmEq {
                left: *left,
                right: *right,
            }),
            (SurfaceTag::TmEps, [ty, predicate], None, None) => Ok(Self::TmEps {
                ty: *ty,
                predicate: *predicate,
            }),
            (SurfaceTag::TmAbs, [carrier, predicate, value], None, None) => Ok(Self::TmAbs {
                carrier: *carrier,
                predicate: *predicate,
                value: *value,
            }),
            (SurfaceTag::TmRep, [carrier, predicate, value], None, None) => Ok(Self::TmRep {
                carrier: *carrier,
                predicate: *predicate,
                value: *value,
            }),
            (SurfaceTag::TmCast, [term, target], None, None) => Ok(Self::TmCast {
                term: *term,
                target: *target,
            }),
            _ if !no_payload => Err("invalid payload for expression tag"),
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
            Self::TyExists { .. } => SurfaceTag::TyExists,
            Self::TyModel { .. } => SurfaceTag::TyModel,
            Self::TmBv { .. } => SurfaceTag::TmBv,
            Self::TmFv { .. } => SurfaceTag::TmFv,
            Self::TmApp { .. } => SurfaceTag::TmApp,
            Self::TmLam { .. } => SurfaceTag::TmLam,
            Self::TmBool { .. } => SurfaceTag::TmBool,
            Self::TmEq { .. } => SurfaceTag::TmEq,
            Self::TmEps { .. } => SurfaceTag::TmEps,
            Self::TmAbs { .. } => SurfaceTag::TmAbs,
            Self::TmRep { .. } => SurfaceTag::TmRep,
            Self::TmCast { .. } => SurfaceTag::TmCast,
            Self::TmNat { .. } => SurfaceTag::TmNat,
            Self::TmBytes { .. } => SurfaceTag::TmBytes,
        }
    }
    pub fn children(&self) -> impl Iterator<Item = Ix> + '_ {
        let triple = match self {
            Self::KindStar
            | Self::TyBool
            | Self::TyBv { .. }
            | Self::TmBv { .. }
            | Self::TmBool { .. }
            | Self::TmNat { .. }
            | Self::TmBytes { .. } => [None, None, None],
            Self::KindArr { domain, codomain } | Self::TyArr { domain, codomain } => {
                [Some(*domain), Some(*codomain), None]
            }
            Self::TyApp { function, argument } | Self::TmApp { function, argument } => {
                [Some(*function), Some(*argument), None]
            }
            Self::TyLam { domain, body } | Self::TmLam { domain, body } => {
                [Some(*domain), Some(*body), None]
            }
            Self::TySub { carrier, predicate }
            | Self::TmEps {
                ty: carrier,
                predicate,
            } => [Some(*carrier), Some(*predicate), None],
            Self::TyExists { predicate } | Self::TyModel { predicate } => {
                [Some(*predicate), None, None]
            }
            Self::TmFv { ty, .. } => [Some(*ty), None, None],
            Self::TmEq { left, right } => [Some(*left), Some(*right), None],
            Self::TmAbs {
                carrier,
                predicate,
                value,
            }
            | Self::TmRep {
                carrier,
                predicate,
                value,
            } => [Some(*carrier), Some(*predicate), Some(*value)],
            Self::TmCast { term, target } => [Some(*term), Some(*target), None],
        };
        triple.into_iter().flatten()
    }
}

mod storage {
    pub trait Sealed {}
}

/// A trusted choice of arena-vector representation.
///
/// The trait is sealed because arena invariants depend on the two audited
/// implementations: owned vectors and immutable static slices.
pub trait TrustedVec: storage::Sealed {
    type Of<T: 'static>: AsRef<[T]>;
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct OwnedVec;
impl storage::Sealed for OwnedVec {}
impl TrustedVec for OwnedVec {
    type Of<T: 'static> = Vec<T>;
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct StaticVec;
impl storage::Sealed for StaticVec {}
impl TrustedVec for StaticVec {
    type Of<T: 'static> = &'static [T];
}

/// An arena whose two vectors share one audited storage family.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(try_from = "ArenaWire<I>")]
#[serde(bound(serialize = "I: Serialize, V::Of<Segment>: Serialize, V::Of<Expr>: Serialize"))]
#[serde(bound(
    deserialize = "I: Deserialize<'de>, Arena<I, V>: TryFrom<ArenaWire<I>, Error = ArenaError>"
))]
pub struct Arena<I = Option<O256>, V: TrustedVec = OwnedVec> {
    imports: I,
    segments: V::Of<Segment>,
    local_base: u32,
    defs: V::Of<Expr>,
}

/// Immutable, slice-backed specialization used by foundational arenas.
pub type StaticArena<I = Option<O256>> = Arena<I, StaticVec>;

impl<I> Arena<I, StaticVec> {
    /// Construct and validate a slice-backed arena.
    ///
    /// # Errors
    /// Returns the first structural arena error.
    pub fn from_static(
        imports: I,
        segments: &'static [Segment],
        local_base: u32,
        defs: &'static [Expr],
    ) -> Result<Self, ArenaError>
    where
        I: Clone,
    {
        let arena = Self::new_const(imports, segments, local_base, defs);
        arena.validate()?;
        Ok(arena)
    }

    /// Internal constant constructor for audited built-in tables. Every such
    /// value is also passed through [`Self::validate`] in tests.
    pub(crate) const fn new_const(
        imports: I,
        segments: &'static [Segment],
        local_base: u32,
        defs: &'static [Expr],
    ) -> Self {
        Self {
            imports,
            segments,
            local_base,
            defs,
        }
    }

    /// Validate the static table using the owned arena's single checker.
    ///
    /// # Errors
    /// Returns the first structural arena error.
    pub fn validate(&self) -> Result<(), ArenaError>
    where
        I: Clone,
    {
        self.to_owned().map(|_| ())
    }

    /// Decode-compatible owned representation of the same arena.
    ///
    /// # Errors
    /// Returns the first structural arena error.
    pub fn to_owned(&self) -> Result<Arena<I>, ArenaError>
    where
        I: Clone,
    {
        let mut arena = Arena::new(self.imports.clone());
        for segment in self.segments {
            arena.add_segment(*segment)?;
        }
        arena.set_local_base(self.local_base)?;
        for expr in self.defs {
            arena.push(expr.clone())?;
        }
        Ok(arena)
    }
}

/// The canonical static arena with no imports or definitions.
pub const EMPTY_STATIC_ARENA: StaticArena = Arena::new_const(None, &[], 1, &[]);

#[derive(Deserialize)]
struct ArenaWire<I> {
    imports: I,
    segments: Vec<Segment>,
    local_base: u32,
    defs: Vec<Expr>,
}

impl<I> TryFrom<ArenaWire<I>> for Arena<I, OwnedVec> {
    type Error = ArenaError;

    fn try_from(wire: ArenaWire<I>) -> Result<Self, Self::Error> {
        let mut arena = Self::new(wire.imports);
        for segment in wire.segments {
            arena.add_segment(Segment::new(
                segment.start,
                segment.end,
                segment.link,
                segment.source_start,
            )?)?;
        }
        arena.set_local_base(wire.local_base)?;
        for expr in wire.defs {
            arena.push(expr)?;
        }
        Ok(arena)
    }
}

impl<I> Arena<I, OwnedVec> {
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
}

impl<I, V: TrustedVec> Arena<I, V> {
    #[must_use]
    pub const fn imports(&self) -> &I {
        &self.imports
    }
    pub fn segments(&self) -> &[Segment] {
        self.segments.as_ref()
    }
    #[must_use]
    pub const fn local_base(&self) -> u32 {
        self.local_base
    }
    pub fn defs(&self) -> &[Expr] {
        self.defs.as_ref()
    }
    #[must_use]
    pub fn local(&self, index: Ix) -> Option<&Expr> {
        (index.get() >= self.local_base)
            .then(|| index.get() - self.local_base)
            .and_then(|offset| self.defs().get(offset as usize))
    }
}

impl<V: TrustedVec> Arena<ImportTable, V> {
    #[must_use]
    pub fn resolve(&self, index: Ix) -> Resolve<'_> {
        if let Some(expr) = self.local(index) {
            return Resolve::Local(expr);
        }
        let position = self
            .segments()
            .partition_point(|segment| segment.start <= index);
        let Some(segment) = position.checked_sub(1).and_then(|i| self.segments().get(i)) else {
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
    /// Returns an error if the arena cannot be serialized as CBOR.
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
    /// Returns an error if the table cannot be serialized as CBOR.
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
