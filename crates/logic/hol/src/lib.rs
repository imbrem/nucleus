//! Raw, unvalidated Ethane syntax arenas.
//!
//! This crate fixes the representation boundary only. Deserialization does
//! not establish kinding, typing, equality, or provability.

mod row;
pub mod wire;

pub use row::Tag;

use row::Row;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
enum Parent {}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Dense {
    parent: Option<Parent>,
    offset: i64,
    defs: Vec<Row>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(tag = "tag")]
enum ArenaRepr {
    #[serde(rename = "arena.dense")]
    Dense(Dense),
}

/// A raw Ethane arena.
///
/// The concrete rows are intentionally hidden. The public API observes a row
/// only through an arena-relative signed index.
#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(transparent)]
pub struct Arena(ArenaRepr);

impl Arena {
    /// Returns an empty root dense arena.
    #[must_use]
    pub const fn empty() -> Self {
        Self(ArenaRepr::Dense(Dense {
            parent: None,
            offset: 0,
            defs: Vec::new(),
        }))
    }

    #[must_use]
    pub const fn offset(&self) -> i64 {
        self.dense().offset
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.dense().defs.len()
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.dense().defs.is_empty()
    }

    /// Returns the constructor tag at `index`, if that row is local.
    #[must_use]
    pub fn tag(&self, index: i64) -> Option<Tag> {
        self.row(index).map(Row::tag)
    }

    /// Returns the optional equality member at `index`.
    ///
    /// `None` means either that the row is unavailable or that it has no
    /// equality member.
    #[must_use]
    pub fn eq(&self, index: i64) -> Option<i64> {
        self.row(index).and_then(Row::eq)
    }

    /// Returns the optional sort member at `index`.
    ///
    /// `None` means either that the row is unavailable or that it has no sort
    /// member.
    #[must_use]
    pub fn sort(&self, index: i64) -> Option<i64> {
        self.row(index).and_then(Row::sort)
    }

    const fn dense(&self) -> &Dense {
        match &self.0 {
            ArenaRepr::Dense(arena) => arena,
        }
    }

    fn row(&self, index: i64) -> Option<&Row> {
        let relative = index.checked_sub(self.offset())?;
        let position = usize::try_from(relative).ok()?;
        self.dense().defs.get(position)
    }

    #[cfg(test)]
    fn from_rows(offset: i64, defs: Vec<Row>) -> Self {
        Self(ArenaRepr::Dense(Dense {
            parent: None,
            offset,
            defs,
        }))
    }
}

impl Default for Arena {
    fn default() -> Self {
        Self::empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use row::Expr;

    #[test]
    fn members_are_looked_up_by_absolute_index() {
        let arena = Arena::from_rows(
            -2,
            vec![
                Row::new(Expr::KindStar).with_sort(7),
                Row::new(Expr::BoolTy).with_eq(-2).with_sort(8),
            ],
        );

        assert_eq!(arena.tag(-2), Some(Tag::KindStar));
        assert_eq!(arena.eq(-2), None);
        assert_eq!(arena.sort(-2), Some(7));
        assert_eq!(arena.tag(-1), Some(Tag::BoolTy));
        assert_eq!(arena.eq(-1), Some(-2));
        assert_eq!(arena.sort(-1), Some(8));
        assert_eq!(arena.tag(-3), None);
        assert_eq!(arena.tag(0), None);
    }
}
