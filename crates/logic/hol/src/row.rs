//! Private rows for the complete Ethane arena vocabulary.

use serde::{Deserialize, Serialize, de};
use smallvec::SmallVec;

use crate::{ImportId, Ref};

const MAX_CHILDREN: usize = 2;
type Fields = (
    Tag,
    Option<SmallVec<[Ref; MAX_CHILDREN]>>,
    Option<Value>,
    Option<ImportId>,
    Option<Ref>,
);

/// One non-recursive, unvalidated Ethane expression.
#[derive(Clone, Debug, Eq, PartialEq)]
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
    /// Equality: left and right operands. Their common type is inferred.
    Eq(Ref, Ref),
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
            Self::Model { .. } => Tag::Ty(TyTag::Model),
            Self::TmFv { .. } => Tag::Tm(TmTag::Fv),
            Self::App(..) => Tag::Tm(TmTag::App),
            Self::Lam(..) => Tag::Tm(TmTag::Lam),
            Self::Bool(..) => Tag::Tm(TmTag::Bool),
            Self::Eq(..) => Tag::Tm(TmTag::Eq),
            Self::Eps { .. } => Tag::Tm(TmTag::Eps),
            Self::TmRef { .. } => Tag::Tm(TmTag::Ref),
            Self::TyRef { .. } => Tag::Ty(TyTag::Ref),
            Self::KindRef { .. } => Tag::Kind(KindTag::Ref),
        }
    }
}

/// One raw definition and its optional, unvalidated inline members.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Row {
    expr: Expr,
    eq: Option<Ref>,
    sort: Option<Ref>,
}

impl Row {
    #[cfg(test)]
    #[must_use]
    pub(crate) const fn new(expr: Expr) -> Self {
        Self {
            expr,
            eq: None,
            sort: None,
        }
    }

    #[cfg(test)]
    #[must_use]
    pub(crate) const fn with_eq(mut self, reference: Ref) -> Self {
        self.eq = Some(reference);
        self
    }

    #[cfg(test)]
    #[must_use]
    pub(crate) const fn with_sort(mut self, reference: Ref) -> Self {
        self.sort = Some(reference);
        self
    }

    pub(crate) const fn tag(&self) -> Tag {
        self.expr.tag()
    }

    pub(crate) const fn eq(&self) -> Option<Ref> {
        self.eq
    }

    pub(crate) const fn sort(&self) -> Option<Ref> {
        self.sort
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
    Fv,
    App,
    Lam,
    Bool,
    Eq,
    Eps,
    Ref,
}

impl TmTag {
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::TyExists => "tm.ty_exists",
            Self::Fv => "tm.fv",
            Self::App => "tm.app",
            Self::Lam => "tm.lam",
            Self::Bool => "tm.bool",
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
            "tm.fv" => Self::Tm(TmTag::Fv),
            "tm.app" => Self::Tm(TmTag::App),
            "tm.lam" => Self::Tm(TmTag::Lam),
            "tm.bool" => Self::Tm(TmTag::Bool),
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
    #[serde(default, skip_serializing_if = "Option::is_none")]
    ixs: Option<SmallVec<[Ref; MAX_CHILDREN]>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    val: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    src: Option<ImportId>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    ix: Option<Ref>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    eq: Option<Ref>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    sort: Option<Ref>,
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
            Expr::Model { name, predicate } => {
                ordinary(Tag::Ty(TyTag::Model), [predicate], Some(Value::Nat(name)))
            }
            Expr::TmFv { name, ty } => ordinary(Tag::Tm(TmTag::Fv), [ty], Some(Value::Nat(name))),
            Expr::App(function, argument) => {
                ordinary(Tag::Tm(TmTag::App), [function, argument], None)
            }
            Expr::Lam(binder, body) => ordinary(Tag::Tm(TmTag::Lam), [binder, body], None),
            Expr::Bool(value) => ordinary(Tag::Tm(TmTag::Bool), [], Some(Value::Bool(value))),
            Expr::Eq(left, right) => ordinary(Tag::Tm(TmTag::Eq), [left, right], None),
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
            eq: row.eq,
            sort: row.sort,
        }
    }
}

fn ordinary<const N: usize>(tag: Tag, children: [Ref; N], value: Option<Value>) -> Fields {
    (tag, Some(children.into_iter().collect()), value, None, None)
}

const fn foreign(tag: Tag, src: ImportId, ix: Ref) -> Fields {
    (tag, None, None, Some(src), Some(ix))
}

impl TryFrom<RowSerde> for Row {
    type Error = &'static str;

    fn try_from(row: RowSerde) -> Result<Self, Self::Error> {
        let expression = match (row.tag, row.ixs.as_deref(), row.val, row.src, row.ix) {
            (Tag::Kind(KindTag::Star), Some([]), None, None, None) => Expr::KindStar,
            (Tag::Kind(KindTag::Arr), Some([domain, codomain]), None, None, None) => {
                Expr::KindArr(*domain, *codomain)
            }
            (Tag::Ty(TyTag::Bool), Some([]), None, None, None) => Expr::BoolTy,
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
            (Tag::Tm(TmTag::Bool), Some([]), Some(Value::Bool(value)), None, None) => {
                Expr::Bool(value)
            }
            (Tag::Tm(TmTag::Eq), Some([left, right]), None, None, None) => Expr::Eq(*left, *right),
            (Tag::Tm(TmTag::Eps), Some([ty, predicate]), None, None, None) => Expr::Eps {
                ty: *ty,
                predicate: *predicate,
            },
            (Tag::Tm(TmTag::Ref), None, None, Some(src), Some(ix)) => Expr::TmRef { src, ix },
            (Tag::Ty(TyTag::Ref), None, None, Some(src), Some(ix)) => Expr::TyRef { src, ix },
            (Tag::Kind(KindTag::Ref), None, None, Some(src), Some(ix)) => Expr::KindRef { src, ix },
            _ => return Err("fields do not form an Ethane row"),
        };
        Ok(Self {
            expr: expression,
            eq: row.eq,
            sort: row.sort,
        })
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

    const fn reference(value: u64) -> Ref {
        Ref::new(value).unwrap()
    }

    const fn import(value: u64) -> ImportId {
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
            Row::new(Expr::Model {
                name: 4,
                predicate: one,
            }),
            Row::new(Expr::TmFv { name: 7, ty: one }),
            Row::new(Expr::App(one, two)),
            Row::new(Expr::Lam(one, two)),
            Row::new(Expr::Bool(false)),
            Row::new(Expr::Bool(true)),
            Row::new(Expr::Eq(one, two)),
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
    fn inferred_type_rows_have_exactly_two_children() {
        let one = reference(1);
        let two = reference(2);
        for (row, name) in [
            (Row::new(Expr::TyApp(one, two)), "ty.app"),
            (Row::new(Expr::TyLam(one, two)), "ty.lam"),
            (Row::new(Expr::Eq(one, two)), "tm.eq"),
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
                        Cbor::Array(vec![Cbor::Integer(1.into()), Cbor::Integer(2.into())]),
                    ),
                ]
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
