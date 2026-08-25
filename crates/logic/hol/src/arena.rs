//! Owned raw arena storage.
//!
//! Rows contain syntax only. Optional classifiers and equality links live in
//! independent dense columns so their representation can evolve without
//! changing expression rows.

use std::collections::BTreeSet;

use crate::{AmbPred, ClassicalArena, Cnf, Import, Ref, SynFactId, row::Row, syn::SynSlot};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Dense {
    pub(crate) defs: Vec<Row>,
    pub(crate) eq: Vec<Option<Ref>>,
    pub(crate) syn_eq: Vec<Option<Ref>>,
    pub(crate) conv: Vec<Option<Ref>>,
    pub(crate) sort: Vec<Option<Ref>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EqColumn {
    Syn,
    Conv,
    Semantic,
}

impl Dense {
    pub(crate) fn row(&self, reference: Ref) -> Option<&Row> {
        let position = usize::try_from(reference.get() - 1).ok()?;
        self.defs.get(position)
    }

    pub(crate) fn position(&self, reference: Ref) -> Option<usize> {
        let position = usize::try_from(reference.get() - 1).ok()?;
        (position < self.defs.len()).then_some(position)
    }

    pub(crate) fn column(&self, column: &[Option<Ref>], reference: Ref) -> Option<Ref> {
        column.get(self.position(reference)?).copied().flatten()
    }

    pub(crate) fn set_column(
        &mut self,
        select: impl FnOnce(&mut Self) -> &mut Vec<Option<Ref>>,
        reference: Ref,
        value: Option<Ref>,
    ) -> bool {
        let Some(position) = self.position(reference) else {
            return false;
        };
        let column = select(self);
        if column.len() <= position {
            column.resize(position + 1, None);
        }
        column[position] = value;
        while column.last() == Some(&None) {
            column.pop();
        }
        true
    }
}

/// A one-based dense Ethane arena.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Arena {
    pub(crate) imports: Vec<Import>,
    pub(crate) axs: BTreeSet<String>,
    pub(crate) dense: Dense,
    pub(crate) syn_facts: Vec<SynSlot>,
    pub(crate) syn_free: Option<SynFactId>,
    pub(crate) ctx: BTreeSet<Ref>,
    pub(crate) amb_pred: Vec<AmbPred>,
    pub(crate) amb_ax: BTreeSet<String>,
    pub(crate) amb_ctx: Cnf,
    pub(crate) amb_thm: ClassicalArena,
    pub(crate) syl: ClassicalArena,
    pub(crate) thm: ClassicalArena,
}
