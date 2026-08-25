//! Private rows for the complete Ethane arena vocabulary.

use serde::{Deserialize, Serialize, de};
use smallvec::SmallVec;

use crate::{
    ImportId, Ref,
    builtin::{Op1, Op2},
};

const MAX_CHILDREN: usize = 3;
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
    /// Versioned compact unary syntax. Semantics are supplied by lowering.
    Op1(Op1, Ref),
    /// Versioned compact binary syntax. Operands are ordered left-to-right.
    Op2(Op2, Ref, Ref),
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
        match self {
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
            Self::Op1(..) => Tag::Tm(TmTag::Op1),
            Self::Op2(..) => Tag::Tm(TmTag::Op2),
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
            | Self::TmRef { .. }
            | Self::TyRef { .. }
            | Self::KindRef { .. } => SmallVec::new(),
            Self::KindArr(left, right)
            | Self::TyArr(left, right)
            | Self::TyApp(left, right)
            | Self::TyLam(left, right)
            | Self::App(left, right)
            | Self::Lam(left, right)
            | Self::Op2(_, left, right) => SmallVec::from_slice(&[left, right]),
            Self::Eq(ty, left, right) => SmallVec::from_slice(&[ty, left, right]),
            Self::Op1(_, operand) => SmallVec::from_slice(&[operand]),
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
#[derive(Clone, Debug, Eq, PartialEq)]
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
    Op1,
    Op2,
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
            Self::Op1 => crate::builtin::OP1_ROW_TAG,
            Self::Op2 => crate::builtin::OP2_ROW_TAG,
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
            crate::builtin::OP1_ROW_TAG => Self::Tm(TmTag::Op1),
            crate::builtin::OP2_ROW_TAG => Self::Tm(TmTag::Op2),
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

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
#[serde(untagged)]
enum Value {
    Nat(u64),
    Bool(bool),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct RowSerde {
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

impl From<Row> for RowSerde {
    fn from(row: Row) -> Self {
        let (tag, ixs, val, src, ix) = match row.expr {
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
            Expr::Eq(ty, left, right) => ordinary(Tag::Tm(TmTag::Eq), [ty, left, right], None),
            Expr::Eps { ty, predicate } => ordinary(Tag::Tm(TmTag::Eps), [ty, predicate], None),
            Expr::TmRef { src, ix } => foreign(Tag::Tm(TmTag::Ref), src, ix),
            Expr::TyRef { src, ix } => foreign(Tag::Ty(TyTag::Ref), src, ix),
            Expr::KindRef { src, ix } => foreign(Tag::Kind(KindTag::Ref), src, ix),
        };
        Self {
            tag,
            ixs,
            val,
            src,
            ix,
        }
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

impl TryFrom<RowSerde> for Row {
    type Error = &'static str;

    fn try_from(row: RowSerde) -> Result<Self, Self::Error> {
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

impl Serialize for Row {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        RowSerde::from(self.clone()).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Row {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        RowSerde::deserialize(deserializer)?
            .try_into()
            .map_err(de::Error::custom)
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

    fn all_rows() -> Vec<Row> {
        let one = reference(1);
        let two = reference(2);
        vec![
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
        ]
    }

    #[test]
    fn every_row_round_trips_through_serde_cbor() {
        for row in all_rows() {
            let mut bytes = Vec::new();
            into_writer(&row, &mut bytes).unwrap();
            assert_eq!(from_reader::<Row, _>(bytes.as_slice()).unwrap(), row);
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
            let mut bytes = Vec::new();
            into_writer(&row, &mut bytes).unwrap();
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
            let mut bytes = Vec::new();
            into_writer(&row, &mut bytes).unwrap();
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

    fn decode_bad(fields: Vec<(Cbor, Cbor)>) -> bool {
        let mut bytes = Vec::new();
        into_writer(&Cbor::Map(fields), &mut bytes).unwrap();
        from_reader::<Row, _>(bytes.as_slice()).is_err()
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
