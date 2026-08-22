//! Complete raw row vocabulary for Ethane over numeric names and primitives.

use serde::{Deserialize, Serialize, de};
use smallvec::SmallVec;

const MAX_CHILDREN: usize = 2;

/// One non-recursive Ethane expression row.
///
/// Children are absolute signed arena indices. Names and primitive symbols are
/// opaque numeric identifiers at this representation boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Expr {
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.pair`.
    Pair(i64, i64),
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.kindStar`.
    KindStar,
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.kindArr`.
    KindArr(i64, i64),
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.boolTy`.
    BoolTy,
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.arr`.
    TyArr(i64, i64),
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.tyApp`.
    TyApp(i64, i64),
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.tyLam`.
    TyLam { name: u64, kinds: i64, body: i64 },
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.tyFv`.
    TyFv { name: u64, kind: i64 },
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.tyExists`.
    TyExists { name: u64, predicate: i64 },
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.model`.
    Model { name: u64, predicate: i64 },
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.primFam`.
    PrimFam { symbol: u64, kind: i64 },
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.primTm`.
    PrimTm { symbol: u64 },
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.tmFv`.
    TmFv { name: u64, ty: i64 },
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.app`.
    App(i64, i64),
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.lam`.
    Lam(i64, i64),
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.bool`.
    Bool(bool),
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.eq`.
    Eq { ty: i64, operands: i64 },
    /// Lean: `Nucleus.Hol.Ethane.Dense.Expr.eps`.
    Eps { ty: i64, predicate: i64 },
}

impl Expr {
    pub(crate) const fn tag(&self) -> Tag {
        match self {
            Self::Pair(..) => Tag::Pair,
            Self::KindStar => Tag::KindStar,
            Self::KindArr(..) => Tag::KindArr,
            Self::BoolTy => Tag::BoolTy,
            Self::TyArr(..) => Tag::TyArr,
            Self::TyApp(..) => Tag::TyApp,
            Self::TyLam { .. } => Tag::TyLam,
            Self::TyFv { .. } => Tag::TyFv,
            Self::TyExists { .. } => Tag::TyExists,
            Self::Model { .. } => Tag::Model,
            Self::PrimFam { .. } => Tag::PrimFam,
            Self::PrimTm { .. } => Tag::PrimTm,
            Self::TmFv { .. } => Tag::TmFv,
            Self::App(..) => Tag::App,
            Self::Lam(..) => Tag::Lam,
            Self::Bool(..) => Tag::Bool,
            Self::Eq { .. } => Tag::Eq,
            Self::Eps { .. } => Tag::Eps,
        }
    }
}

/// One raw definition and its optional, unvalidated claims.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Row {
    expr: Expr,
    eq: Option<i64>,
    sort: Option<i64>,
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
    pub(crate) const fn with_eq(mut self, reference: i64) -> Self {
        self.eq = Some(reference);
        self
    }

    #[cfg(test)]
    #[must_use]
    pub(crate) const fn with_sort(mut self, reference: i64) -> Self {
        self.sort = Some(reference);
        self
    }

    pub(crate) const fn tag(&self) -> Tag {
        self.expr.tag()
    }

    pub(crate) const fn eq(&self) -> Option<i64> {
        self.eq
    }

    pub(crate) const fn sort(&self) -> Option<i64> {
        self.sort
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
#[non_exhaustive]
#[derive(Eq, PartialEq)]
pub enum Tag {
    #[serde(rename = "pair")]
    Pair,
    #[serde(rename = "kind.star")]
    KindStar,
    #[serde(rename = "kind.arr")]
    KindArr,
    #[serde(rename = "ty.bool")]
    BoolTy,
    #[serde(rename = "ty.arr")]
    TyArr,
    #[serde(rename = "ty.app")]
    TyApp,
    #[serde(rename = "ty.lam")]
    TyLam,
    #[serde(rename = "ty.fv")]
    TyFv,
    #[serde(rename = "tm.ty_exists")]
    TyExists,
    #[serde(rename = "ty.model")]
    Model,
    #[serde(rename = "fam.prim")]
    PrimFam,
    #[serde(rename = "tm.prim")]
    PrimTm,
    #[serde(rename = "tm.fv")]
    TmFv,
    #[serde(rename = "tm.app")]
    App,
    #[serde(rename = "tm.lam")]
    Lam,
    #[serde(rename = "tm.bool")]
    Bool,
    #[serde(rename = "tm.eq")]
    Eq,
    #[serde(rename = "tm.eps")]
    Eps,
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
    ixs: SmallVec<[i64; MAX_CHILDREN]>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    val: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    eq: Option<i64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    sort: Option<i64>,
}

impl From<Row> for RowSerde {
    fn from(row: Row) -> Self {
        let (tag, ixs, val) = match row.expr {
            Expr::Pair(left, right) => (Tag::Pair, smallvec::smallvec![left, right], None),
            Expr::KindStar => (Tag::KindStar, SmallVec::new(), None),
            Expr::KindArr(domain, codomain) => {
                (Tag::KindArr, smallvec::smallvec![domain, codomain], None)
            }
            Expr::BoolTy => (Tag::BoolTy, SmallVec::new(), None),
            Expr::TyArr(domain, codomain) => {
                (Tag::TyArr, smallvec::smallvec![domain, codomain], None)
            }
            Expr::TyApp(kinds, arguments) => {
                (Tag::TyApp, smallvec::smallvec![kinds, arguments], None)
            }
            Expr::TyLam { name, kinds, body } => (
                Tag::TyLam,
                smallvec::smallvec![kinds, body],
                Some(Value::Nat(name)),
            ),
            Expr::TyFv { name, kind } => {
                (Tag::TyFv, smallvec::smallvec![kind], Some(Value::Nat(name)))
            }
            Expr::TyExists { name, predicate } => (
                Tag::TyExists,
                smallvec::smallvec![predicate],
                Some(Value::Nat(name)),
            ),
            Expr::Model { name, predicate } => (
                Tag::Model,
                smallvec::smallvec![predicate],
                Some(Value::Nat(name)),
            ),
            Expr::PrimFam { symbol, kind } => (
                Tag::PrimFam,
                smallvec::smallvec![kind],
                Some(Value::Nat(symbol)),
            ),
            Expr::PrimTm { symbol } => (Tag::PrimTm, SmallVec::new(), Some(Value::Nat(symbol))),
            Expr::TmFv { name, ty } => (Tag::TmFv, smallvec::smallvec![ty], Some(Value::Nat(name))),
            Expr::App(function, argument) => {
                (Tag::App, smallvec::smallvec![function, argument], None)
            }
            Expr::Lam(variable, body) => (Tag::Lam, smallvec::smallvec![variable, body], None),
            Expr::Bool(value) => (Tag::Bool, SmallVec::new(), Some(Value::Bool(value))),
            Expr::Eq { ty, operands } => (Tag::Eq, smallvec::smallvec![ty, operands], None),
            Expr::Eps { ty, predicate } => (Tag::Eps, smallvec::smallvec![ty, predicate], None),
        };
        Self {
            tag,
            ixs,
            val,
            eq: row.eq,
            sort: row.sort,
        }
    }
}

impl TryFrom<RowSerde> for Row {
    type Error = &'static str;

    fn try_from(row: RowSerde) -> Result<Self, Self::Error> {
        let children = row.ixs.as_slice();
        let expression = match (row.tag, children, row.val) {
            (Tag::Pair, [left, right], None) => Expr::Pair(*left, *right),
            (Tag::KindStar, [], None) => Expr::KindStar,
            (Tag::KindArr, [domain, codomain], None) => Expr::KindArr(*domain, *codomain),
            (Tag::BoolTy, [], None) => Expr::BoolTy,
            (Tag::TyArr, [domain, codomain], None) => Expr::TyArr(*domain, *codomain),
            (Tag::TyApp, [kinds, arguments], None) => Expr::TyApp(*kinds, *arguments),
            (Tag::TyLam, [kinds, body], Some(Value::Nat(name))) => Expr::TyLam {
                name,
                kinds: *kinds,
                body: *body,
            },
            (Tag::TyFv, [kind], Some(Value::Nat(name))) => Expr::TyFv { name, kind: *kind },
            (Tag::TyExists, [predicate], Some(Value::Nat(name))) => Expr::TyExists {
                name,
                predicate: *predicate,
            },
            (Tag::Model, [predicate], Some(Value::Nat(name))) => Expr::Model {
                name,
                predicate: *predicate,
            },
            (Tag::PrimFam, [kind], Some(Value::Nat(symbol))) => Expr::PrimFam {
                symbol,
                kind: *kind,
            },
            (Tag::PrimTm, [], Some(Value::Nat(symbol))) => Expr::PrimTm { symbol },
            (Tag::TmFv, [ty], Some(Value::Nat(name))) => Expr::TmFv { name, ty: *ty },
            (Tag::App, [function, argument], None) => Expr::App(*function, *argument),
            (Tag::Lam, [variable, body], None) => Expr::Lam(*variable, *body),
            (Tag::Bool, [], Some(Value::Bool(value))) => Expr::Bool(value),
            (Tag::Eq, [ty, operands], None) => Expr::Eq {
                ty: *ty,
                operands: *operands,
            },
            (Tag::Eps, [ty, predicate], None) => Expr::Eps {
                ty: *ty,
                predicate: *predicate,
            },
            _ => return Err("tag, child indices, and val do not form an Ethane row"),
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

    fn all_rows() -> Vec<Row> {
        vec![
            Row::new(Expr::Pair(-1, 0)),
            Row::new(Expr::KindStar),
            Row::new(Expr::KindArr(-2, -1)),
            Row::new(Expr::BoolTy),
            Row::new(Expr::TyArr(-2, -1)),
            Row::new(Expr::TyApp(-2, -1)),
            Row::new(Expr::TyLam {
                name: 1,
                kinds: -2,
                body: -1,
            }),
            Row::new(Expr::TyFv { name: 2, kind: -1 }),
            Row::new(Expr::TyExists {
                name: 3,
                predicate: -1,
            }),
            Row::new(Expr::Model {
                name: 4,
                predicate: -1,
            }),
            Row::new(Expr::PrimFam {
                symbol: 5,
                kind: -1,
            }),
            Row::new(Expr::PrimTm { symbol: 6 }),
            Row::new(Expr::TmFv { name: 7, ty: -1 }),
            Row::new(Expr::App(-2, -1)),
            Row::new(Expr::Lam(-2, -1)),
            Row::new(Expr::Bool(false)),
            Row::new(Expr::Bool(true)),
            Row::new(Expr::Eq {
                ty: -2,
                operands: -1,
            }),
            Row::new(Expr::Eps {
                ty: -2,
                predicate: -1,
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
    fn wrong_arity_is_rejected() {
        let bad = Cbor::Map(vec![
            (Cbor::Text("tag".into()), Cbor::Text("kind.star".into())),
            (
                Cbor::Text("ixs".into()),
                Cbor::Array(vec![Cbor::Integer(0.into())]),
            ),
        ]);
        let mut bytes = Vec::new();
        into_writer(&bad, &mut bytes).unwrap();
        assert!(from_reader::<Row, _>(bytes.as_slice()).is_err());
    }
}
