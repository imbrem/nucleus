//! Internal semantic rows and their mechanical Serde representation.

use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

pub(crate) const MAX_CHILDREN: usize = 2;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Expr {
    KindStar,
    BoolTy,
    Bool(bool),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Row {
    pub(crate) expr: Expr,
    pub(crate) eq: Option<i64>,
    pub(crate) sort: Option<i64>,
}

impl Row {
    pub(crate) const fn syntax(expr: Expr) -> Self {
        Self {
            expr,
            eq: None,
            sort: None,
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Tag {
    #[serde(rename = "kind.star")]
    KindStar,
    #[serde(rename = "ty.bool")]
    BoolTy,
    #[serde(rename = "tm.bool.false")]
    BoolFalse,
    #[serde(rename = "tm.bool.true")]
    BoolTrue,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RowSerde {
    pub(crate) tag: Tag,
    pub(crate) ixs: SmallVec<[i64; MAX_CHILDREN]>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) eq: Option<i64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) sort: Option<i64>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Error {
    WrongChildCount { expected: usize, actual: usize },
}

impl From<Row> for RowSerde {
    fn from(row: Row) -> Self {
        let tag = match row.expr {
            Expr::KindStar => Tag::KindStar,
            Expr::BoolTy => Tag::BoolTy,
            Expr::Bool(false) => Tag::BoolFalse,
            Expr::Bool(true) => Tag::BoolTrue,
        };
        Self {
            tag,
            ixs: SmallVec::new(),
            eq: row.eq,
            sort: row.sort,
        }
    }
}

impl TryFrom<RowSerde> for Row {
    type Error = Error;

    fn try_from(row: RowSerde) -> Result<Self, Self::Error> {
        if !row.ixs.is_empty() {
            return Err(Error::WrongChildCount {
                expected: 0,
                actual: row.ixs.len(),
            });
        }
        let expr = match row.tag {
            Tag::KindStar => Expr::KindStar,
            Tag::BoolTy => Expr::BoolTy,
            Tag::BoolFalse => Expr::Bool(false),
            Tag::BoolTrue => Expr::Bool(true),
        };
        Ok(Self {
            expr,
            eq: row.eq,
            sort: row.sort,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serde_view_preserves_row_facts() {
        let row = Row {
            expr: Expr::Bool(true),
            eq: Some(-7),
            sort: Some(i64::MAX),
        };
        assert_eq!(Row::try_from(RowSerde::from(row)), Ok(row));
    }

    #[test]
    fn semantic_conversion_rejects_wrong_arity() {
        let wire = RowSerde {
            tag: Tag::BoolTy,
            ixs: SmallVec::from_slice(&[4]),
            eq: None,
            sort: None,
        };
        assert_eq!(
            Row::try_from(wire),
            Err(Error::WrongChildCount {
                expected: 0,
                actual: 1
            })
        );
    }
}
