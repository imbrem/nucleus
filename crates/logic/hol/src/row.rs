//! Private rows for the complete Ethane arena vocabulary, compact literal and
//! builtin rows included.

use std::num::NonZeroI32;

use bytes::Bytes;
use serde::{Deserialize, Serialize, de};
use smallvec::SmallVec;

use crate::{
    ImportId, Ref,
    builtin::{Num1, Num2, Op1, Op2},
};

const MAX_CHILDREN: usize = 3;
pub(crate) const MAX_LITERAL_BYTES: usize = 1024 * 1024;

/// Canonical numeric encodings up to this length are held in the expression.
///
/// Eight bytes is the width of `u64` and `i64`, so only a value wider than 64
/// bits reaches the byte table.
const INLINE_LITERAL_BYTES: usize = 8;

/// A one-based index into an arena's byte table.
///
/// Like [`Ref`], an index may have no entry behind it. The raw arena checks
/// representation only, so a dangling index reads as absent instead of failing
/// at construction.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub(crate) struct Blob(NonZeroI32);

impl Blob {
    /// Addresses the byte-table entry at `position`.
    pub(crate) fn new(position: usize) -> Option<Self> {
        let value = i32::try_from(position).ok()?.checked_add(1)?;
        if value == i32::MAX {
            return None;
        }
        NonZeroI32::new(value).map(Self)
    }

    /// The zero-based byte-table position this index addresses.
    pub(crate) const fn position(self) -> usize {
        // One-based and positive by construction, so the cast cannot lose a sign.
        self.0.get().unsigned_abs() as usize - 1
    }
}
type Fields = (
    Tag,
    Option<SmallVec<[Ref; MAX_CHILDREN]>>,
    Option<Value>,
    Option<ImportId>,
    Option<Ref>,
);

/// One non-recursive, unvalidated Ethane expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Expr {
    KindStar,
    KindArr(Ref, Ref),
    BoolTy,
    TyArr(Ref, Ref),
    /// Type-family application: function and argument.
    TyApp(Ref, Ref),
    /// The children are the type-variable binder and body.
    TyLam(Ref, Ref),
    TyFv {
        name: u64,
        kind: Ref,
    },
    TyExists {
        name: u64,
        predicate: Ref,
    },
    TyForall {
        name: u64,
        predicate: Ref,
    },
    Model {
        name: u64,
        predicate: Ref,
    },
    TmFv {
        name: u64,
        ty: Ref,
    },
    App(Ref, Ref),
    /// The children are the binder variable and body, in that order.
    Lam(Ref, Ref),
    Bool(bool),
    /// Versioned compact byte-string literal. Semantics are supplied by lowering.
    ///
    /// The bytes live in the owning arena's byte table, so two expressions
    /// compare only within one arena. Equal indices name equal bytes, but two
    /// separately interned copies of the same bytes compare unequal.
    Bytes(Blob),
    /// Versioned compact natural literal within 64 bits.
    Nat(u64),
    /// Versioned compact natural literal wider than 64 bits.
    ///
    /// Its canonical unsigned big-endian bytes live in the byte table.
    NatBig(Blob),
    /// Versioned compact signed integer literal within 64 bits.
    Int(i64),
    /// Versioned compact signed integer literal wider than 64 bits.
    ///
    /// Its canonical two's-complement bytes live in the byte table.
    IntBig(Blob),
    /// Versioned compact unary syntax. Semantics are supplied by lowering.
    Op1(Op1, Ref),
    /// Versioned compact binary syntax. Operands are ordered left-to-right.
    Op2(Op2, Ref, Ref),
    /// Versioned compact unary numeric syntax.
    Num1(Num1, Ref),
    /// Versioned compact binary numeric syntax. Operands are left-to-right.
    Num2(Num2, Ref, Ref),
    /// Equality: left and right operands. Their common type is inferred.
    Eq(Ref, Ref, Ref),
    Eps {
        ty: Ref,
        predicate: Ref,
    },
    TmRef {
        src: ImportId,
        ix: Ref,
    },
    TyRef {
        src: ImportId,
        ix: Ref,
    },
    KindRef {
        src: ImportId,
        ix: Ref,
    },
}

impl Expr {
    pub(crate) const fn tag(&self) -> Tag {
        match *self {
            Self::KindStar => Tag::Kind(KindTag::Star),
            Self::KindArr(..) => Tag::Kind(KindTag::Arr),
            Self::BoolTy => Tag::Ty(TyTag::Bool),
            Self::TyArr(..) => Tag::Ty(TyTag::Arr),
            Self::TyApp(..) => Tag::Ty(TyTag::App),
            Self::TyLam(..) => Tag::Ty(TyTag::Lam),
            Self::TyFv { .. } => Tag::Ty(TyTag::Fv),
            Self::TyExists { .. } => Tag::Tm(TmTag::TyExists),
            Self::TyForall { .. } => Tag::Tm(TmTag::TyForall),
            Self::Model { .. } => Tag::Ty(TyTag::Model),
            Self::TmFv { .. } => Tag::Tm(TmTag::Fv),
            Self::App(..) => Tag::Tm(TmTag::App),
            Self::Lam(..) => Tag::Tm(TmTag::Lam),
            Self::Bool(..) => Tag::Tm(TmTag::Bool),
            Self::Bytes(..) => Tag::Tm(TmTag::Bytes),
            Self::Nat(..) | Self::NatBig(..) => Tag::Tm(TmTag::Nat),
            Self::Int(..) | Self::IntBig(..) => Tag::Tm(TmTag::Int),
            Self::Op1(..) => Tag::Tm(TmTag::Op1),
            Self::Op2(..) => Tag::Tm(TmTag::Op2),
            Self::Num1(..) => Tag::Tm(TmTag::Num1),
            Self::Num2(..) => Tag::Tm(TmTag::Num2),
            Self::Eq(..) => Tag::Tm(TmTag::Eq),
            Self::Eps { .. } => Tag::Tm(TmTag::Eps),
            Self::TmRef { .. } => Tag::Tm(TmTag::Ref),
            Self::TyRef { .. } => Tag::Ty(TyTag::Ref),
            Self::KindRef { .. } => Tag::Kind(KindTag::Ref),
        }
    }

    pub(crate) fn children(&self) -> SmallVec<[Ref; MAX_CHILDREN]> {
        match *self {
            Self::KindStar
            | Self::BoolTy
            | Self::Bool(_)
            | Self::Bytes(..)
            | Self::Nat(..)
            | Self::NatBig(..)
            | Self::Int(..)
            | Self::IntBig(..)
            | Self::TmRef { .. }
            | Self::TyRef { .. }
            | Self::KindRef { .. } => SmallVec::new(),
            Self::KindArr(left, right)
            | Self::TyArr(left, right)
            | Self::TyApp(left, right)
            | Self::TyLam(left, right)
            | Self::App(left, right)
            | Self::Lam(left, right)
            | Self::Op2(_, left, right)
            | Self::Num2(_, left, right) => SmallVec::from_slice(&[left, right]),
            Self::Eq(ty, left, right) => SmallVec::from_slice(&[ty, left, right]),
            Self::Op1(_, operand) | Self::Num1(_, operand) => SmallVec::from_slice(&[operand]),
            Self::Eps { ty, predicate } => SmallVec::from_slice(&[ty, predicate]),
            Self::TyFv { kind: child, .. }
            | Self::TyExists {
                predicate: child, ..
            }
            | Self::TyForall {
                predicate: child, ..
            }
            | Self::Model {
                predicate: child, ..
            }
            | Self::TmFv { ty: child, .. } => SmallVec::from_slice(&[child]),
        }
    }
}

/// One raw definition.
///
/// Classifiers and equality links are stored in arena-level dense columns;
/// keeping them out of the row makes the expression table representation
/// independent of which checked relations an arena elects to materialize.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Row {
    expr: Expr,
}

impl Row {
    #[must_use]
    pub(crate) const fn new(expr: Expr) -> Self {
        Self { expr }
    }

    #[must_use]
    pub(crate) const fn tag(&self) -> Tag {
        self.expr.tag()
    }

    pub(crate) const fn expr(&self) -> &Expr {
        &self.expr
    }
}

/// Whether `bytes` is the unique unsigned big-endian encoding of its value.
///
/// Zero is `[0]`; nothing else may carry a leading zero byte.
pub(crate) const fn nat_is_canonical(bytes: &[u8]) -> bool {
    !bytes.is_empty() && (bytes.len() == 1 || bytes[0] != 0)
}

/// Whether `bytes` is the shortest two's-complement encoding of its value.
///
/// A leading byte is redundant when the next byte already carries the sign.
pub(crate) const fn int_is_canonical(bytes: &[u8]) -> bool {
    if bytes.is_empty() {
        return false;
    }
    if bytes.len() == 1 {
        return true;
    }
    !((bytes[0] == 0 && bytes[1] & 0x80 == 0) || (bytes[0] == u8::MAX && bytes[1] & 0x80 != 0))
}

/// The canonical unsigned big-endian encoding of `value`.
pub(crate) fn nat_to_bytes(value: u64) -> Vec<u8> {
    let bytes = value.to_be_bytes();
    let start = bytes.iter().position(|&byte| byte != 0).unwrap_or(7);
    bytes[start..].to_vec()
}

/// The canonical two's-complement big-endian encoding of `value`.
pub(crate) fn int_to_bytes(value: i64) -> Vec<u8> {
    let bytes = value.to_be_bytes();
    let mut start = 0;
    while start + 1 < bytes.len()
        && ((bytes[start] == 0 && bytes[start + 1] & 0x80 == 0)
            || (bytes[start] == u8::MAX && bytes[start + 1] & 0x80 != 0))
    {
        start += 1;
    }
    bytes[start..].to_vec()
}

/// Widens a canonical unsigned encoding of at most eight bytes.
fn nat_from_bytes(bytes: &[u8]) -> u64 {
    let mut widened = [0; INLINE_LITERAL_BYTES];
    widened[INLINE_LITERAL_BYTES - bytes.len()..].copy_from_slice(bytes);
    u64::from_be_bytes(widened)
}

/// Sign-extends a canonical two's-complement encoding of at most eight bytes.
fn int_from_bytes(bytes: &[u8]) -> i64 {
    let sign = if bytes[0] & 0x80 == 0 { 0 } else { u8::MAX };
    let mut widened = [sign; INLINE_LITERAL_BYTES];
    widened[INLINE_LITERAL_BYTES - bytes.len()..].copy_from_slice(bytes);
    i64::from_be_bytes(widened)
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Sort {
    Kind,
    Ty,
    Tm,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum KindTag {
    Star,
    Arr,
    Ref,
}

impl KindTag {
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Star => "kind.star",
            Self::Arr => "kind.arr",
            Self::Ref => "kind.ref",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TyTag {
    Bool,
    Arr,
    App,
    Lam,
    Fv,
    Model,
    Ref,
}

impl TyTag {
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Bool => "ty.bool",
            Self::Arr => "ty.arr",
            Self::App => "ty.app",
            Self::Lam => "ty.lam",
            Self::Fv => "ty.fv",
            Self::Model => "ty.model",
            Self::Ref => "ty.ref",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TmTag {
    TyExists,
    TyForall,
    Fv,
    App,
    Lam,
    Bool,
    Bytes,
    Nat,
    Int,
    Op1,
    Op2,
    Num1,
    Num2,
    Eq,
    Eps,
    Ref,
}

impl TmTag {
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::TyExists => "tm.ty_exists",
            Self::TyForall => "tm.ty_forall",
            Self::Fv => "tm.fv",
            Self::App => "tm.app",
            Self::Lam => "tm.lam",
            Self::Bool => "tm.bool",
            Self::Bytes => "tm.bytes",
            Self::Nat => "tm.nat",
            Self::Int => "tm.int",
            Self::Op1 => crate::builtin::OP1_ROW_TAG,
            Self::Op2 => crate::builtin::OP2_ROW_TAG,
            Self::Num1 => crate::builtin::NUM1_ROW_TAG,
            Self::Num2 => crate::builtin::NUM2_ROW_TAG,
            Self::Eq => "tm.eq",
            Self::Eps => "tm.eps",
            Self::Ref => "tm.ref",
        }
    }
}

/// The stable tag of an Ethane row, split by its declared syntactic sort.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum Tag {
    Kind(KindTag),
    Ty(TyTag),
    Tm(TmTag),
}

impl Tag {
    #[must_use]
    pub const fn sort(self) -> Sort {
        match self {
            Self::Kind(_) => Sort::Kind,
            Self::Ty(_) => Sort::Ty,
            Self::Tm(_) => Sort::Tm,
        }
    }

    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Kind(tag) => tag.name(),
            Self::Ty(tag) => tag.name(),
            Self::Tm(tag) => tag.name(),
        }
    }

    fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "kind.star" => Self::Kind(KindTag::Star),
            "kind.arr" => Self::Kind(KindTag::Arr),
            "kind.ref" => Self::Kind(KindTag::Ref),
            "ty.bool" => Self::Ty(TyTag::Bool),
            "ty.arr" => Self::Ty(TyTag::Arr),
            "ty.app" => Self::Ty(TyTag::App),
            "ty.lam" => Self::Ty(TyTag::Lam),
            "ty.fv" => Self::Ty(TyTag::Fv),
            "ty.model" => Self::Ty(TyTag::Model),
            "ty.ref" => Self::Ty(TyTag::Ref),
            "tm.ty_exists" => Self::Tm(TmTag::TyExists),
            "tm.ty_forall" => Self::Tm(TmTag::TyForall),
            "tm.fv" => Self::Tm(TmTag::Fv),
            "tm.app" => Self::Tm(TmTag::App),
            "tm.lam" => Self::Tm(TmTag::Lam),
            "tm.bool" => Self::Tm(TmTag::Bool),
            "tm.bytes" => Self::Tm(TmTag::Bytes),
            "tm.nat" => Self::Tm(TmTag::Nat),
            "tm.int" => Self::Tm(TmTag::Int),
            crate::builtin::OP1_ROW_TAG => Self::Tm(TmTag::Op1),
            crate::builtin::OP2_ROW_TAG => Self::Tm(TmTag::Op2),
            crate::builtin::NUM1_ROW_TAG => Self::Tm(TmTag::Num1),
            crate::builtin::NUM2_ROW_TAG => Self::Tm(TmTag::Num2),
            "tm.eq" => Self::Tm(TmTag::Eq),
            "tm.eps" => Self::Tm(TmTag::Eps),
            "tm.ref" => Self::Tm(TmTag::Ref),
            _ => return None,
        })
    }
}

impl Serialize for Tag {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.name())
    }
}

impl<'de> Deserialize<'de> for Tag {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let name = String::deserialize(deserializer)?;
        Self::from_name(&name).ok_or_else(|| serde::de::Error::unknown_variant(&name, &[]))
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(untagged)]
enum Value {
    Nat(u64),
    Bool(bool),
    Bytes(#[serde(with = "byte_string")] Vec<u8>),
}

mod byte_string {
    use serde::{Deserializer, Serializer, de};

    pub fn serialize<S>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(bytes)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ByteString;

        impl<'de> de::Visitor<'de> for ByteString {
            type Value = Vec<u8>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a CBOR byte string")
            }

            fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E> {
                Ok(value.to_vec())
            }

            fn visit_borrowed_bytes<E>(self, value: &'de [u8]) -> Result<Self::Value, E> {
                Ok(value.to_vec())
            }

            fn visit_byte_buf<E>(self, value: Vec<u8>) -> Result<Self::Value, E> {
                Ok(value)
            }
        }

        deserializer.deserialize_bytes(ByteString)
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RowSerde {
    tag: Tag,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "bounded_children"
    )]
    ixs: Option<SmallVec<[Ref; MAX_CHILDREN]>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    val: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    src: Option<ImportId>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    ix: Option<Ref>,
}

fn bounded_children<'de, D>(
    deserializer: D,
) -> Result<Option<SmallVec<[Ref; MAX_CHILDREN]>>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    struct ChildrenVisitor;

    impl<'de> de::Visitor<'de> for ChildrenVisitor {
        type Value = Option<SmallVec<[Ref; MAX_CHILDREN]>>;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "an array of at most {MAX_CHILDREN} references")
        }

        fn visit_none<E>(self) -> Result<Self::Value, E> {
            Ok(None)
        }

        fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            deserializer.deserialize_seq(self)
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: de::SeqAccess<'de>,
        {
            let mut children = SmallVec::new();
            while let Some(child) = sequence.next_element()? {
                if children.len() == MAX_CHILDREN {
                    return Err(de::Error::invalid_length(MAX_CHILDREN + 1, &self));
                }
                children.push(child);
            }
            Ok(Some(children))
        }
    }

    deserializer.deserialize_option(ChildrenVisitor)
}

impl Row {
    /// Builds the wire form, resolving any blob against `blobs`.
    ///
    /// # Errors
    ///
    /// Returns an error if the row names a byte-table entry that `blobs` does
    /// not hold. Only a raw arena assembled outside its own constructors can
    /// be in that state; see [`Blob`].
    pub(crate) fn encode(self, blobs: &[Bytes]) -> Result<RowSerde, &'static str> {
        let blob = |blob: Blob| {
            blobs
                .get(blob.position())
                .ok_or("row names a missing byte-table entry")
        };
        let Row { expr } = self;
        let (tag, ixs, val, src, ix) = match expr {
            Expr::Bytes(index) => ordinary(
                Tag::Tm(TmTag::Bytes),
                [],
                Some(Value::Bytes(blob(index)?.to_vec())),
            ),
            Expr::Nat(value) => ordinary(
                Tag::Tm(TmTag::Nat),
                [],
                Some(Value::Bytes(nat_to_bytes(value))),
            ),
            Expr::Int(value) => ordinary(
                Tag::Tm(TmTag::Int),
                [],
                Some(Value::Bytes(int_to_bytes(value))),
            ),
            Expr::NatBig(index) => ordinary(
                Tag::Tm(TmTag::Nat),
                [],
                Some(Value::Bytes(blob(index)?.to_vec())),
            ),
            Expr::IntBig(index) => ordinary(
                Tag::Tm(TmTag::Int),
                [],
                Some(Value::Bytes(blob(index)?.to_vec())),
            ),
            Expr::KindStar => ordinary(Tag::Kind(KindTag::Star), [], None),
            Expr::KindArr(domain, codomain) => {
                ordinary(Tag::Kind(KindTag::Arr), [domain, codomain], None)
            }
            Expr::BoolTy => ordinary(Tag::Ty(TyTag::Bool), [], None),
            Expr::TyArr(domain, codomain) => {
                ordinary(Tag::Ty(TyTag::Arr), [domain, codomain], None)
            }
            Expr::TyApp(function, argument) => {
                ordinary(Tag::Ty(TyTag::App), [function, argument], None)
            }
            Expr::TyLam(binder, body) => ordinary(Tag::Ty(TyTag::Lam), [binder, body], None),
            Expr::TyFv { name, kind } => {
                ordinary(Tag::Ty(TyTag::Fv), [kind], Some(Value::Nat(name)))
            }
            Expr::TyExists { name, predicate } => ordinary(
                Tag::Tm(TmTag::TyExists),
                [predicate],
                Some(Value::Nat(name)),
            ),
            Expr::TyForall { name, predicate } => ordinary(
                Tag::Tm(TmTag::TyForall),
                [predicate],
                Some(Value::Nat(name)),
            ),
            Expr::Model { name, predicate } => {
                ordinary(Tag::Ty(TyTag::Model), [predicate], Some(Value::Nat(name)))
            }
            Expr::TmFv { name, ty } => ordinary(Tag::Tm(TmTag::Fv), [ty], Some(Value::Nat(name))),
            Expr::App(function, argument) => {
                ordinary(Tag::Tm(TmTag::App), [function, argument], None)
            }
            Expr::Lam(binder, body) => ordinary(Tag::Tm(TmTag::Lam), [binder, body], None),
            Expr::Bool(value) => ordinary(Tag::Tm(TmTag::Bool), [], Some(Value::Bool(value))),
            Expr::Op1(op, operand) => ordinary(
                Tag::Tm(TmTag::Op1),
                [operand],
                Some(Value::Nat(u64::from(op.code()))),
            ),
            Expr::Op2(op, left, right) => ordinary(
                Tag::Tm(TmTag::Op2),
                [left, right],
                Some(Value::Nat(u64::from(op.code()))),
            ),
            Expr::Num1(op, operand) => ordinary(
                Tag::Tm(TmTag::Num1),
                [operand],
                Some(Value::Nat(u64::from(op.code()))),
            ),
            Expr::Num2(op, left, right) => ordinary(
                Tag::Tm(TmTag::Num2),
                [left, right],
                Some(Value::Nat(u64::from(op.code()))),
            ),
            Expr::Eq(ty, left, right) => ordinary(Tag::Tm(TmTag::Eq), [ty, left, right], None),
            Expr::Eps { ty, predicate } => ordinary(Tag::Tm(TmTag::Eps), [ty, predicate], None),
            Expr::TmRef { src, ix } => foreign(Tag::Tm(TmTag::Ref), src, ix),
            Expr::TyRef { src, ix } => foreign(Tag::Ty(TyTag::Ref), src, ix),
            Expr::KindRef { src, ix } => foreign(Tag::Kind(KindTag::Ref), src, ix),
        };
        Ok(RowSerde {
            tag,
            ixs,
            val,
            src,
            ix,
        })
    }

    /// Reads the wire form, interning any literal payload into `blobs`.
    ///
    /// A canonical numeric encoding of at most eight bytes is normalized into
    /// the expression itself, so one value has exactly one representation and
    /// re-encoding is byte-identical.
    ///
    /// # Errors
    ///
    /// Returns an error if the fields do not form an Ethane row, if a literal
    /// payload is not canonical, or if it exceeds [`MAX_LITERAL_BYTES`].
    pub(crate) fn decode(row: RowSerde, blobs: &mut Vec<Bytes>) -> Result<Self, &'static str> {
        let Tag::Tm(kind @ (TmTag::Bytes | TmTag::Nat | TmTag::Int)) = row.tag else {
            return Self::decode_ordinary(row);
        };
        let (None, Some(Value::Bytes(value)), None, None) =
            (row.ixs.as_deref(), row.val, row.src, row.ix)
        else {
            return Err("fields do not form a compact literal row");
        };
        if value.len() > MAX_LITERAL_BYTES {
            return Err("compact literal exceeds the size limit");
        }
        let mut intern = |value: Vec<u8>| {
            let index = Blob::new(blobs.len()).ok_or("byte table is exhausted")?;
            blobs.push(Bytes::from(value));
            Ok::<_, &'static str>(index)
        };
        let expression = match kind {
            TmTag::Bytes => Expr::Bytes(intern(value)?),
            TmTag::Nat if !nat_is_canonical(&value) => {
                return Err("natural literal is not canonical");
            }
            TmTag::Nat if value.len() <= INLINE_LITERAL_BYTES => Expr::Nat(nat_from_bytes(&value)),
            TmTag::Nat => Expr::NatBig(intern(value)?),
            TmTag::Int if !int_is_canonical(&value) => {
                return Err("integer literal is not canonical");
            }
            TmTag::Int if value.len() <= INLINE_LITERAL_BYTES => Expr::Int(int_from_bytes(&value)),
            _ => Expr::IntBig(intern(value)?),
        };
        Ok(Self::new(expression))
    }
}

fn ordinary<const N: usize>(tag: Tag, children: [Ref; N], value: Option<Value>) -> Fields {
    let children: SmallVec<_> = children.into_iter().collect();
    let children = (!children.is_empty()).then_some(children);
    (tag, children, value, None, None)
}

const fn foreign(tag: Tag, src: ImportId, ix: Ref) -> Fields {
    (tag, None, None, Some(src), Some(ix))
}

impl Row {
    /// Reads every row whose payload is held entirely in the expression.
    fn decode_ordinary(row: RowSerde) -> Result<Self, &'static str> {
        let expression = match (row.tag, row.ixs.as_deref(), row.val, row.src, row.ix) {
            (Tag::Kind(KindTag::Star), None, None, None, None) => Expr::KindStar,
            (Tag::Kind(KindTag::Arr), Some([domain, codomain]), None, None, None) => {
                Expr::KindArr(*domain, *codomain)
            }
            (Tag::Ty(TyTag::Bool), None, None, None, None) => Expr::BoolTy,
            (Tag::Ty(TyTag::Arr), Some([domain, codomain]), None, None, None) => {
                Expr::TyArr(*domain, *codomain)
            }
            (Tag::Ty(TyTag::App), Some([function, argument]), None, None, None) => {
                Expr::TyApp(*function, *argument)
            }
            (Tag::Ty(TyTag::Lam), Some([binder, body]), None, None, None) => {
                Expr::TyLam(*binder, *body)
            }
            (Tag::Ty(TyTag::Fv), Some([kind]), Some(Value::Nat(name)), None, None) => {
                Expr::TyFv { name, kind: *kind }
            }
            (Tag::Tm(TmTag::TyExists), Some([predicate]), Some(Value::Nat(name)), None, None) => {
                Expr::TyExists {
                    name,
                    predicate: *predicate,
                }
            }
            (Tag::Tm(TmTag::TyForall), Some([predicate]), Some(Value::Nat(name)), None, None) => {
                Expr::TyForall {
                    name,
                    predicate: *predicate,
                }
            }
            (Tag::Ty(TyTag::Model), Some([predicate]), Some(Value::Nat(name)), None, None) => {
                Expr::Model {
                    name,
                    predicate: *predicate,
                }
            }
            (Tag::Tm(TmTag::Fv), Some([ty]), Some(Value::Nat(name)), None, None) => {
                Expr::TmFv { name, ty: *ty }
            }
            (Tag::Tm(TmTag::App), Some([function, argument]), None, None, None) => {
                Expr::App(*function, *argument)
            }
            (Tag::Tm(TmTag::Lam), Some([binder, body]), None, None, None) => {
                Expr::Lam(*binder, *body)
            }
            (Tag::Tm(TmTag::Bool), None, Some(Value::Bool(value)), None, None) => Expr::Bool(value),
            (Tag::Tm(TmTag::Op1), Some([operand]), Some(Value::Nat(code)), None, None) => {
                Expr::Op1(
                    Op1::from_code(u8::try_from(code).map_err(|_| "unknown op1 code")?)
                        .ok_or("unknown op1 code")?,
                    *operand,
                )
            }
            (Tag::Tm(TmTag::Op2), Some([left, right]), Some(Value::Nat(code)), None, None) => {
                Expr::Op2(
                    Op2::from_code(u8::try_from(code).map_err(|_| "unknown op2 code")?)
                        .ok_or("unknown op2 code")?,
                    *left,
                    *right,
                )
            }
            (Tag::Tm(TmTag::Num1), Some([operand]), Some(Value::Nat(code)), None, None) => {
                Expr::Num1(
                    Num1::from_code(u8::try_from(code).map_err(|_| "unknown num1 code")?)
                        .ok_or("unknown num1 code")?,
                    *operand,
                )
            }
            (Tag::Tm(TmTag::Num2), Some([left, right]), Some(Value::Nat(code)), None, None) => {
                Expr::Num2(
                    Num2::from_code(u8::try_from(code).map_err(|_| "unknown num2 code")?)
                        .ok_or("unknown num2 code")?,
                    *left,
                    *right,
                )
            }
            (Tag::Tm(TmTag::Eq), Some([ty, left, right]), None, None, None) => {
                Expr::Eq(*ty, *left, *right)
            }
            (Tag::Tm(TmTag::Eps), Some([ty, predicate]), None, None, None) => Expr::Eps {
                ty: *ty,
                predicate: *predicate,
            },
            (Tag::Tm(TmTag::Ref), None, None, Some(src), Some(ix)) => Expr::TmRef { src, ix },
            (Tag::Ty(TyTag::Ref), None, None, Some(src), Some(ix)) => Expr::TyRef { src, ix },
            (Tag::Kind(KindTag::Ref), None, None, Some(src), Some(ix)) => Expr::KindRef { src, ix },
            _ => return Err("fields do not form an Ethane row"),
        };
        Ok(Self::new(expression))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_lib_cbor::{Value as Cbor, from_reader, into_writer};

    const fn reference(value: i32) -> Ref {
        Ref::new(value).unwrap()
    }

    const fn import(value: i32) -> ImportId {
        ImportId::new(value).unwrap()
    }

    /// One row of every shape, plus the byte table its literal rows index.
    fn all_rows() -> (Vec<Row>, Vec<Bytes>) {
        let one = reference(1);
        let two = reference(2);
        let blobs = vec![
            Bytes::from_static(&[0, 1, 255]),
            // Canonical encodings that need more than sixty-four bits.
            Bytes::from_static(&[1; 33]),
            Bytes::from_static(&[0x80; 33]),
        ];
        let blob = |position| Blob::new(position).unwrap();
        let rows = vec![
            Row::new(Expr::KindStar),
            Row::new(Expr::KindArr(one, two)),
            Row::new(Expr::BoolTy),
            Row::new(Expr::TyArr(one, two)),
            Row::new(Expr::TyApp(one, two)),
            Row::new(Expr::TyLam(one, two)),
            Row::new(Expr::TyFv { name: 2, kind: one }),
            Row::new(Expr::TyExists {
                name: 3,
                predicate: one,
            }),
            Row::new(Expr::TyForall {
                name: 5,
                predicate: one,
            }),
            Row::new(Expr::Model {
                name: 4,
                predicate: one,
            }),
            Row::new(Expr::TmFv { name: 7, ty: one }),
            Row::new(Expr::App(one, two)),
            Row::new(Expr::Lam(one, two)),
            Row::new(Expr::Bool(false)),
            Row::new(Expr::Bool(true)),
            Row::new(Expr::Bytes(blob(0))),
            Row::new(Expr::Nat(1 << 40)),
            Row::new(Expr::NatBig(blob(1))),
            Row::new(Expr::Int(-129)),
            Row::new(Expr::IntBig(blob(2))),
            Row::new(Expr::Op1(Op1::Not, one)),
            Row::new(Expr::Op2(Op2::And, one, two)),
            Row::new(Expr::Eq(one, one, two)),
            Row::new(Expr::Eps {
                ty: one,
                predicate: two,
            }),
            Row::new(Expr::TmRef {
                src: import(1),
                ix: one,
            }),
            Row::new(Expr::TyRef {
                src: import(1),
                ix: one,
            }),
            Row::new(Expr::KindRef {
                src: import(1),
                ix: one,
            }),
        ];
        (rows, blobs)
    }

    /// Encodes one row against a byte table, the way an arena does.
    fn encoded(row: Row, blobs: &[Bytes]) -> Vec<u8> {
        let mut bytes = Vec::new();
        into_writer(&row.encode(blobs).unwrap(), &mut bytes).unwrap();
        bytes
    }

    /// Decodes one row, interning any payload into a fresh byte table.
    fn decoded(bytes: &[u8]) -> Option<(Row, Vec<Bytes>)> {
        let mut blobs = Vec::new();
        let wire = from_reader::<RowSerde, _>(bytes).ok()?;
        let row = Row::decode(wire, &mut blobs).ok()?;
        Some((row, blobs))
    }

    #[test]
    fn every_row_round_trips_to_the_same_bytes() {
        let (rows, blobs) = all_rows();
        for row in rows {
            let bytes = encoded(row, &blobs);
            let (row, blobs) = decoded(&bytes).unwrap();
            assert_eq!(encoded(row, &blobs), bytes);
        }
    }

    #[test]
    fn typed_rows_encode_every_explicit_child() {
        let one = reference(1);
        let two = reference(2);
        for (row, name, children) in [
            (Row::new(Expr::TyApp(one, two)), "ty.app", vec![one, two]),
            (Row::new(Expr::TyLam(one, two)), "ty.lam", vec![one, two]),
            (
                Row::new(Expr::Eq(one, one, two)),
                "tm.eq",
                vec![one, one, two],
            ),
        ] {
            let bytes = encoded(row, &[]);
            let Cbor::Map(fields) = from_reader(bytes.as_slice()).unwrap() else {
                panic!("row must be a CBOR map")
            };
            assert_eq!(
                fields,
                [
                    (Cbor::Text("tag".into()), Cbor::Text(name.into())),
                    (
                        Cbor::Text("ixs".into()),
                        Cbor::Array(
                            children
                                .into_iter()
                                .map(|child| { Cbor::Integer(child.get().into()) })
                                .collect()
                        ),
                    ),
                ]
            );
        }
    }

    #[test]
    fn leaf_rows_omit_the_child_field() {
        for row in [
            Row::new(Expr::KindStar),
            Row::new(Expr::BoolTy),
            Row::new(Expr::Bool(false)),
        ] {
            let bytes = encoded(row, &[]);
            let Cbor::Map(fields) = from_reader(bytes.as_slice()).unwrap() else {
                panic!("row must be a CBOR map")
            };
            assert!(
                fields
                    .iter()
                    .all(|(key, _)| key != &Cbor::Text("ixs".into()))
            );
        }
    }

    #[test]
    fn compact_literals_use_distinct_tags_and_cbor_byte_strings() {
        // Inline and spilled storage must reach the same bytes, so the pair of
        // oversized values below encodes exactly like a small one.
        let blobs = vec![
            Bytes::from_static(&[0, 255]),
            Bytes::from_static(&[1; 9]),
            Bytes::from_static(&[0x80; 9]),
        ];
        let blob = |position| Blob::new(position).unwrap();
        let cases = [
            (Row::new(Expr::Bytes(blob(0))), "tm.bytes", vec![0, 255]),
            (Row::new(Expr::Nat(128)), "tm.nat", vec![128]),
            (Row::new(Expr::Int(128)), "tm.int", vec![0, 128]),
            (Row::new(Expr::Int(-129)), "tm.int", vec![255, 127]),
            (Row::new(Expr::Nat(0)), "tm.nat", vec![0]),
            (Row::new(Expr::Int(0)), "tm.int", vec![0]),
            (Row::new(Expr::Int(-1)), "tm.int", vec![255]),
            (Row::new(Expr::NatBig(blob(1))), "tm.nat", vec![1; 9]),
            (Row::new(Expr::IntBig(blob(2))), "tm.int", vec![0x80; 9]),
        ];
        for (row, tag, payload) in cases {
            let bytes = encoded(row, &blobs);
            let Cbor::Map(fields) = from_reader(bytes.as_slice()).unwrap() else {
                panic!("row must be a CBOR map")
            };
            assert_eq!(
                fields,
                [
                    (Cbor::Text("tag".into()), Cbor::Text(tag.into())),
                    (Cbor::Text("val".into()), Cbor::Bytes(payload)),
                ]
            );
        }
    }

    #[test]
    fn sixty_four_bit_literals_are_held_inline_and_wider_ones_spill() {
        let mut blobs = Vec::new();
        let inline = |bytes: Vec<u8>, tag: &str| {
            let wire = RowSerde {
                tag: Tag::from_name(tag).unwrap(),
                ixs: None,
                val: Some(Value::Bytes(bytes)),
                src: None,
                ix: None,
            };
            Row::decode(wire, &mut Vec::new()).unwrap()
        };
        // Eight bytes is the widest inline form; nine spills to the table.
        assert_eq!(
            inline(vec![255; 8], "tm.nat"),
            Row::new(Expr::Nat(u64::MAX))
        );
        assert_eq!(
            inline(vec![0x7f, 255, 255, 255, 255, 255, 255, 255], "tm.int"),
            Row::new(Expr::Int(i64::MAX))
        );
        assert_eq!(
            inline(vec![0x80, 0, 0, 0, 0, 0, 0, 0], "tm.int"),
            Row::new(Expr::Int(i64::MIN))
        );
        assert!(matches!(
            *inline(vec![1; 9], "tm.nat").expr(),
            Expr::NatBig(..)
        ));
        assert!(matches!(
            *inline(vec![0x80; 9], "tm.int").expr(),
            Expr::IntBig(..)
        ));
        // A byte literal always spills, whatever its length.
        let wire = RowSerde {
            tag: Tag::Tm(TmTag::Bytes),
            ixs: None,
            val: Some(Value::Bytes(vec![7])),
            src: None,
            ix: None,
        };
        assert_eq!(
            Row::decode(wire, &mut blobs).unwrap(),
            Row::new(Expr::Bytes(Blob::new(0).unwrap()))
        );
        assert_eq!(blobs, vec![Bytes::from_static(&[7])]);
    }

    #[test]
    fn inline_numeric_encodings_agree_with_their_canonical_form() {
        for value in [0, 1, 127, 128, 255, 256, u64::MAX, u64::MAX - 1] {
            let bytes = nat_to_bytes(value);
            assert!(nat_is_canonical(&bytes));
            assert_eq!(nat_from_bytes(&bytes), value);
        }
        for value in [0, 1, -1, 127, 128, -128, -129, i64::MAX, i64::MIN] {
            let bytes = int_to_bytes(value);
            assert!(int_is_canonical(&bytes));
            assert_eq!(int_from_bytes(&bytes), value);
        }
    }

    #[test]
    fn compact_numeric_literals_reject_noncanonical_bytes_and_wrong_shapes() {
        for (tag, payload) in [
            ("tm.nat", vec![]),
            ("tm.nat", vec![0, 1]),
            ("tm.int", vec![]),
            ("tm.int", vec![0, 1]),
            ("tm.int", vec![255, 255]),
        ] {
            assert!(decode_bad(vec![
                (Cbor::Text("tag".into()), Cbor::Text(tag.into())),
                (Cbor::Text("val".into()), Cbor::Bytes(payload)),
            ]));
        }
        for tag in ["tm.bytes", "tm.nat", "tm.int"] {
            assert!(decode_bad(vec![
                (Cbor::Text("tag".into()), Cbor::Text(tag.into())),
                (Cbor::Text("val".into()), Cbor::Integer(0.into())),
            ]));
            assert!(decode_bad(vec![
                (Cbor::Text("tag".into()), Cbor::Text(tag.into())),
                (Cbor::Text("ixs".into()), Cbor::Array(Vec::new())),
                (Cbor::Text("val".into()), Cbor::Bytes(vec![0])),
            ]));
        }
    }

    #[test]
    fn compact_literal_size_limit_is_enforced() {
        assert!(decode_bad(vec![
            (Cbor::Text("tag".into()), Cbor::Text("tm.bytes".into())),
            (
                Cbor::Text("val".into()),
                Cbor::Bytes(vec![0; MAX_LITERAL_BYTES + 1]),
            ),
        ]));
    }

    fn decode_bad(fields: Vec<(Cbor, Cbor)>) -> bool {
        let mut bytes = Vec::new();
        into_writer(&Cbor::Map(fields), &mut bytes).unwrap();
        decoded(bytes.as_slice()).is_none()
    }

    #[test]
    fn wrong_arity_payload_and_unknown_fields_are_rejected() {
        assert!(decode_bad(vec![
            (Cbor::Text("tag".into()), Cbor::Text("kind.star".into())),
            (
                Cbor::Text("ixs".into()),
                Cbor::Array(vec![Cbor::Integer(1.into())]),
            ),
        ]));
        // Equality's type is syntax, not a classifier-column lookup.  The
        // former two-child encoding must not silently acquire mutable meaning.
        assert!(decode_bad(vec![
            (Cbor::Text("tag".into()), Cbor::Text("tm.eq".into())),
            (
                Cbor::Text("ixs".into()),
                Cbor::Array(vec![Cbor::Integer(1.into()), Cbor::Integer(2.into())]),
            ),
        ]));
        for (tag, operands, code) in [
            (crate::builtin::OP1_ROW_TAG, vec![1, 2], 0),
            (crate::builtin::OP2_ROW_TAG, vec![1], 0),
            (crate::builtin::OP1_ROW_TAG, vec![1], 1),
            (crate::builtin::OP2_ROW_TAG, vec![1, 2], 3),
            (crate::builtin::OP2_ROW_TAG, vec![1, 2], 256),
        ] {
            assert!(decode_bad(vec![
                (Cbor::Text("tag".into()), Cbor::Text(tag.into())),
                (
                    Cbor::Text("ixs".into()),
                    Cbor::Array(
                        operands
                            .into_iter()
                            .map(|value| Cbor::Integer(value.into()))
                            .collect(),
                    ),
                ),
                (Cbor::Text("val".into()), Cbor::Integer(code.into())),
            ]));
        }
        assert!(decode_bad(vec![
            (Cbor::Text("tag".into()), Cbor::Text("tm.op1.v2".into())),
            (
                Cbor::Text("ixs".into()),
                Cbor::Array(vec![Cbor::Integer(1.into())]),
            ),
            (Cbor::Text("val".into()), Cbor::Integer(0.into())),
        ]));
        assert!(decode_bad(vec![
            (Cbor::Text("tag".into()), Cbor::Text("tm.bool".into())),
            (Cbor::Text("ixs".into()), Cbor::Array(Vec::new())),
            (Cbor::Text("val".into()), Cbor::Integer(0.into())),
        ]));
        assert!(decode_bad(vec![
            (Cbor::Text("tag".into()), Cbor::Text("kind.star".into())),
            (Cbor::Text("ixs".into()), Cbor::Array(Vec::new())),
            (Cbor::Text("unknown".into()), Cbor::Null),
        ]));
    }

    #[test]
    fn zero_and_mixed_reference_fields_are_rejected() {
        assert!(decode_bad(vec![
            (Cbor::Text("tag".into()), Cbor::Text("tm.app".into())),
            (
                Cbor::Text("ixs".into()),
                Cbor::Array(vec![Cbor::Integer(0.into()), Cbor::Integer(1.into())]),
            ),
        ]));
        assert!(decode_bad(vec![
            (Cbor::Text("tag".into()), Cbor::Text("tm.ref".into())),
            (Cbor::Text("src".into()), Cbor::Integer(1.into())),
            (Cbor::Text("ix".into()), Cbor::Integer(1.into())),
            (Cbor::Text("ixs".into()), Cbor::Array(Vec::new())),
        ]));
    }
}
