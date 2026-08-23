//! Cached syntactic, alpha, and conversion facts.

use serde::{Deserialize, Serialize};

use crate::{Ref, SynFactId};

/// The relation asserted by a syntactic fact.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum SynRel {
    /// Literal syntax after substitution.
    Syn,
    /// Alpha-equivalence after substitution.
    Alpha,
    /// Alpha-beta-eta conversion after substitution.
    Conv,
}

impl SynRel {
    /// Whether a fact in `self` may be used where `target` is requested.
    #[must_use]
    pub const fn refines(self, target: Self) -> bool {
        self.rank() <= target.rank()
    }

    const fn rank(self) -> u8 {
        match self {
            Self::Syn => 0,
            Self::Alpha => 1,
            Self::Conv => 2,
        }
    }
}

/// A checked relation between `[val / var] input` and `output`.
///
/// With both endpoints absent this is a direct fact; with both present it is
/// a substitution fact. Half-present endpoints are reserved and currently
/// have no checked meaning. Slots may be absent after removal.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SynFact {
    rel: SynRel,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    var: Option<Ref>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    val: Option<Ref>,
    #[serde(rename = "in")]
    input: Ref,
    #[serde(rename = "out")]
    output: Ref,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct SynFree {
    pub(crate) free: Option<SynFactId>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(untagged)]
pub(crate) enum SynSlot {
    Fact(SynFact),
    Free(SynFree),
}

impl SynFact {
    pub(crate) const fn new(
        rel: SynRel,
        var: Option<Ref>,
        val: Option<Ref>,
        input: Ref,
        output: Ref,
    ) -> Self {
        Self {
            rel,
            var,
            val,
            input,
            output,
        }
    }

    #[must_use]
    pub const fn rel(self) -> SynRel {
        self.rel
    }

    #[must_use]
    pub const fn var(self) -> Option<Ref> {
        self.var
    }

    #[must_use]
    pub const fn val(self) -> Option<Ref> {
        self.val
    }

    #[must_use]
    pub const fn input(self) -> Ref {
        self.input
    }

    #[must_use]
    pub const fn output(self) -> Ref {
        self.output
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relations_form_the_expected_refinement_chain() {
        assert!(SynRel::Syn.refines(SynRel::Syn));
        assert!(SynRel::Syn.refines(SynRel::Alpha));
        assert!(SynRel::Syn.refines(SynRel::Conv));
        assert!(SynRel::Alpha.refines(SynRel::Conv));
        assert!(!SynRel::Conv.refines(SynRel::Alpha));
        assert!(!SynRel::Alpha.refines(SynRel::Syn));
    }

    #[test]
    fn free_slots_use_the_fact_niche() {
        assert_eq!(
            std::mem::size_of::<SynSlot>(),
            std::mem::size_of::<SynFact>()
        );
    }
}
