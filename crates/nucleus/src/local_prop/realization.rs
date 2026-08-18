//! Snapshot-exact structural realization of local propositions.
//!
//! This is the proposition side of a future HOL adapter. Nucleus fixes the
//! Boolean structure as [`BoolRecipe`]; a trusted HOL join must check each free
//! leaf and reconstruct `Not` and complete grouped `All` nodes itself. No safe
//! downstream trait can substitute arbitrary connective semantics.

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU64;
use std::sync::atomic::{AtomicU64, Ordering};

use super::{
    AtomId, CheckerVersion, ContextId, Error as TableError, Fact, Judgement, Literal,
    LocalPropTable, SnapshotId, SourceId, has_cycle,
};

static NEXT_MAPPING: AtomicU64 = AtomicU64::new(1);

/// Process-local identity of one complete reusable realization environment.
///
/// This is a correlation nonce, not a content identity or persistent address.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct MappingId(NonZeroU64);

/// Nucleus-owned Boolean structure for a future trusted HOL reconstruction.
///
/// Callers choose only `Leaf` values for undefined atoms. They cannot choose
/// the meaning of negation or grouped conjunction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BoolRecipe<T> {
    /// Caller-supplied interpretation of one undefined atom.
    Leaf {
        /// Proposition atom represented by this leaf.
        atom: AtomId,
        /// Opaque value which the HOL join must check as a closed Boolean term.
        value: T,
    },
    /// Boolean negation of the structurally realized positive atom.
    Not(Box<Self>),
    /// Complete nonempty grouped conjunction, in canonical table order.
    All(Box<[Self]>),
}

/// Failure to construct or use a realization.
#[derive(Debug)]
pub enum Error {
    /// Proposition storage or validation failed.
    Table(TableError),
    /// A required free atom had no supplied leaf.
    Incomplete(AtomId),
    /// A fact or capability belongs to another proposition kernel.
    ForeignSnapshot,
    /// A fact or capability belongs to an obsolete generation.
    StaleSnapshot,
    /// Fact and capability have different local source identities.
    SourceMismatch,
    /// Fact and capability have different assumption contexts.
    ContextMismatch,
    /// Fact and capability were checked by different checker profiles.
    CheckerMismatch,
    /// Fact and capability name different checked judgements.
    JudgementMismatch,
    /// Fact and capability have different implication endpoints.
    FactMismatch,
    /// No more process-local mapping identities are available.
    MappingIdentityExhausted,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Table(error) => write!(f, "proposition table rejected realization: {error}"),
            Self::Incomplete(atom) => write!(f, "no realization for free atom {}", atom.get()),
            Self::ForeignSnapshot => f.write_str("fact and realization use different kernels"),
            Self::StaleSnapshot => f.write_str("fact or realization uses an obsolete snapshot"),
            Self::SourceMismatch => f.write_str("fact and realization use different sources"),
            Self::ContextMismatch => f.write_str("fact and realization use different contexts"),
            Self::CheckerMismatch => f.write_str("fact and realization use different checkers"),
            Self::JudgementMismatch => f.write_str("fact and realization use different judgements"),
            Self::FactMismatch => f.write_str("fact and realization name different implications"),
            Self::MappingIdentityExhausted => f.write_str("realization identities are exhausted"),
        }
    }
}

impl std::error::Error for Error {}

impl From<TableError> for Error {
    fn from(error: TableError) -> Self {
        Self::Table(error)
    }
}

/// Complete reusable grouped-definition environment for one snapshot/mapping.
///
/// Fields are private. Every defined atom is represented by its complete
/// structural recipe. The same capability can realize multiple directional
/// facts, including both directions needed for equivalence.
///
/// ```compile_fail
/// use covalence_nucleus::local_prop::realization::RealizationEnvironment;
///
/// // Only `LocalPropTable::realize_environment` can mint this capability.
/// let forged: RealizationEnvironment<()> = RealizationEnvironment {};
/// ```
pub struct RealizationEnvironment<T> {
    mapping: MappingId,
    snapshot: SnapshotId,
    source: SourceId,
    context: ContextId,
    recipes: BTreeMap<AtomId, BoolRecipe<T>>,
}

impl<T> RealizationEnvironment<T> {
    /// Returns this process-local mapping correlation identity.
    #[must_use]
    pub const fn mapping(&self) -> MappingId {
        self.mapping
    }

    /// Returns the exact proposition snapshot realized by this capability.
    #[must_use]
    pub const fn snapshot(&self) -> SnapshotId {
        self.snapshot
    }
}

/// Opaque, non-HOL-authoritative structural translation of one checked fact.
///
/// A future trusted HOL rule reconstructs and checks these recipes, then alone
/// may return its existing opaque `Theorem` capability.
///
/// ```compile_fail
/// use covalence_nucleus::local_prop::realization::RealizedImplication;
///
/// // A caller-built recipe cannot be wrapped as a checked implication.
/// let forged: RealizedImplication<()> = RealizedImplication {};
/// ```
pub struct RealizedImplication<T> {
    mapping: MappingId,
    snapshot: SnapshotId,
    source: SourceId,
    context: ContextId,
    checker: CheckerVersion,
    judgement: Judgement,
    premise_literal: Literal,
    conclusion_literal: Literal,
    premise: BoolRecipe<T>,
    conclusion: BoolRecipe<T>,
}

impl<T> RealizedImplication<T> {
    /// Returns the complete mapping identity shared by both endpoints.
    #[must_use]
    pub const fn mapping(&self) -> MappingId {
        self.mapping
    }

    /// Returns the proposition snapshot from which the implication came.
    #[must_use]
    pub const fn snapshot(&self) -> SnapshotId {
        self.snapshot
    }

    /// Returns the checked source identity.
    #[must_use]
    pub const fn source(&self) -> SourceId {
        self.source
    }

    /// Returns the checked empty-context identity.
    #[must_use]
    pub const fn context(&self) -> ContextId {
        self.context
    }

    /// Returns the checker profile which minted the proposition fact.
    #[must_use]
    pub const fn checker(&self) -> CheckerVersion {
        self.checker
    }

    /// Returns the judgement which minted the proposition fact.
    #[must_use]
    pub const fn judgement(&self) -> Judgement {
        self.judgement
    }

    /// Borrows the structural premise recipe.
    #[must_use]
    pub const fn premise(&self) -> &BoolRecipe<T> {
        &self.premise
    }

    /// Borrows the structural conclusion recipe.
    #[must_use]
    pub const fn conclusion(&self) -> &BoolRecipe<T> {
        &self.conclusion
    }
}

impl LocalPropTable {
    /// Realizes the complete current grouped-definition environment.
    ///
    /// `free` supplies opaque leaves only for undefined atoms. All defined
    /// atoms, negative literals, and conjunctions are represented by
    /// Nucleus-owned structural nodes. Extra leaves are retained so later
    /// facts mentioning otherwise unrelated free atoms can share this mapping.
    ///
    /// # Errors
    ///
    /// Rejects invalid/cyclic tables, missing definition dependencies, or
    /// exhausted mapping identities.
    pub fn realize_environment<T: Clone>(
        &self,
        free: &BTreeMap<AtomId, T>,
    ) -> Result<RealizationEnvironment<T>, Error> {
        if has_cycle(&self.connection)? {
            return Err(Error::Table(TableError::InvalidState));
        }
        let definitions = self.definition_map()?;
        let mut recipes = free
            .iter()
            .map(|(&atom, value)| {
                (
                    atom,
                    BoolRecipe::Leaf {
                        atom,
                        value: value.clone(),
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut visiting = BTreeSet::new();
        for &atom in definitions.keys() {
            realize_atom(atom, &definitions, free, &mut recipes, &mut visiting)?;
        }
        let raw = NEXT_MAPPING
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
                next.checked_add(1)
            })
            .map_err(|_| Error::MappingIdentityExhausted)?;
        let mapping = MappingId(NonZeroU64::new(raw).ok_or(Error::MappingIdentityExhausted)?);
        Ok(RealizationEnvironment {
            mapping,
            snapshot: self.snapshot(),
            source: SourceId::LOCAL,
            context: ContextId::EMPTY,
            recipes,
        })
    }

    /// Validates and structurally realizes one fact under a reusable mapping.
    ///
    /// # Errors
    ///
    /// Distinguishes stale/foreign snapshots, source/context mismatch, and
    /// missing endpoint leaves. The output binds checker, judgement, and exact
    /// endpoints for revalidation by the future trusted HOL join.
    pub fn realize_fact<T: Clone>(
        &self,
        fact: &Fact,
        environment: &RealizationEnvironment<T>,
    ) -> Result<RealizedImplication<T>, Error> {
        if environment.snapshot.kernel != self.snapshot().kernel
            || fact.snapshot().kernel != self.snapshot().kernel
        {
            return Err(Error::ForeignSnapshot);
        }
        if environment.snapshot != self.snapshot() || fact.snapshot() != self.snapshot() {
            return Err(Error::StaleSnapshot);
        }
        if environment.source != fact.source() {
            return Err(Error::SourceMismatch);
        }
        if environment.context != fact.context() {
            return Err(Error::ContextMismatch);
        }
        Ok(RealizedImplication {
            mapping: environment.mapping,
            snapshot: environment.snapshot,
            source: fact.source(),
            context: fact.context(),
            checker: fact.checker(),
            judgement: fact.judgement(),
            premise_literal: fact.premise(),
            conclusion_literal: fact.conclusion(),
            premise: realize_literal(fact.premise(), &environment.recipes)?,
            conclusion: realize_literal(fact.conclusion(), &environment.recipes)?,
        })
    }

    /// Revalidates the exact fact/capability binding before a trusted handoff.
    ///
    /// # Errors
    ///
    /// Distinguishes stale/foreign snapshots and every fact-profile mismatch.
    pub fn revalidate_realized<T>(
        &self,
        fact: &Fact,
        realized: &RealizedImplication<T>,
    ) -> Result<(), Error> {
        if realized.snapshot.kernel != self.snapshot().kernel
            || fact.snapshot().kernel != self.snapshot().kernel
        {
            return Err(Error::ForeignSnapshot);
        }
        if realized.snapshot != self.snapshot() || fact.snapshot() != self.snapshot() {
            return Err(Error::StaleSnapshot);
        }
        if realized.source != fact.source() {
            return Err(Error::SourceMismatch);
        }
        if realized.context != fact.context() {
            return Err(Error::ContextMismatch);
        }
        if realized.checker != fact.checker() {
            return Err(Error::CheckerMismatch);
        }
        if realized.judgement != fact.judgement() {
            return Err(Error::JudgementMismatch);
        }
        if realized.premise_literal != fact.premise()
            || realized.conclusion_literal != fact.conclusion()
        {
            return Err(Error::FactMismatch);
        }
        Ok(())
    }

    fn definition_map(&self) -> Result<BTreeMap<AtomId, Vec<Literal>>, TableError> {
        let rows = self.connection.query_all(
            "SELECT premise,conclusion FROM prop_row WHERE source=0 AND reason=0 ORDER BY premise,conclusion",
            &[],
            |row| Ok((row.integer(0)?, row.integer(1)?)),
        )?;
        let mut definitions = BTreeMap::new();
        for (premise, conclusion) in rows {
            let premise = Literal::decode(premise).map_err(|_| TableError::InvalidState)?;
            if premise != Literal::positive(premise.atom()) {
                return Err(TableError::InvalidState);
            }
            let conclusion = Literal::decode(conclusion).map_err(|_| TableError::InvalidState)?;
            definitions
                .entry(premise.atom())
                .or_insert_with(Vec::new)
                .push(conclusion);
        }
        Ok(definitions)
    }
}

fn realize_atom<T: Clone>(
    atom: AtomId,
    definitions: &BTreeMap<AtomId, Vec<Literal>>,
    free: &BTreeMap<AtomId, T>,
    recipes: &mut BTreeMap<AtomId, BoolRecipe<T>>,
    visiting: &mut BTreeSet<AtomId>,
) -> Result<BoolRecipe<T>, Error> {
    if definitions.contains_key(&atom) {
        if let Some(recipe) = recipes.get(&atom)
            && !matches!(recipe, BoolRecipe::Leaf { .. })
        {
            return Ok(recipe.clone());
        }
    } else if let Some(value) = free.get(&atom) {
        return Ok(BoolRecipe::Leaf {
            atom,
            value: value.clone(),
        });
    } else {
        return Err(Error::Incomplete(atom));
    }
    if !visiting.insert(atom) {
        return Err(Error::Table(TableError::InvalidState));
    }
    let conjuncts = definitions.get(&atom).ok_or(Error::Incomplete(atom))?;
    let mut group = Vec::with_capacity(conjuncts.len());
    for literal in conjuncts {
        let positive = realize_atom(literal.atom(), definitions, free, recipes, visiting)?;
        group.push(if literal.negative {
            BoolRecipe::Not(Box::new(positive))
        } else {
            positive
        });
    }
    let recipe = BoolRecipe::All(group.into_boxed_slice());
    visiting.remove(&atom);
    recipes.insert(atom, recipe.clone());
    Ok(recipe)
}

fn realize_literal<T: Clone>(
    literal: Literal,
    recipes: &BTreeMap<AtomId, BoolRecipe<T>>,
) -> Result<BoolRecipe<T>, Error> {
    let positive = recipes
        .get(&literal.atom())
        .cloned()
        .ok_or(Error::Incomplete(literal.atom()))?;
    Ok(if literal.negative {
        BoolRecipe::Not(Box::new(positive))
    } else {
        positive
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::local_prop::Definition;

    fn atom(value: u32) -> AtomId {
        AtomId::new(value).expect("atom")
    }
    fn pos(value: u32) -> Literal {
        Literal::positive(atom(value))
    }
    fn neg(value: u32) -> Literal {
        Literal::negative(atom(value))
    }
    fn leaves(values: &[(u32, &str)]) -> BTreeMap<AtomId, String> {
        values
            .iter()
            .map(|&(atom_id, value)| (atom(atom_id), value.to_owned()))
            .collect()
    }

    #[test]
    fn complete_groups_and_polarity_are_nucleus_owned_structure() {
        let mut table = LocalPropTable::open_in_memory().expect("table");
        table
            .define(Definition::new(atom(2), vec![pos(3)]).expect("definition"))
            .expect("define 2");
        let fact = table
            .define(Definition::new(atom(1), vec![pos(2), neg(4)]).expect("definition"))
            .expect("define 1")
            .into_iter()
            .find(|fact| fact.conclusion() == pos(2))
            .expect("elimination");
        let environment = table
            .realize_environment(&leaves(&[(3, "three"), (4, "four")]))
            .expect("environment");
        let implication = table.realize_fact(&fact, &environment).expect("fact");
        assert_eq!(
            implication.premise(),
            &BoolRecipe::All(
                vec![
                    BoolRecipe::Not(Box::new(BoolRecipe::Leaf {
                        atom: atom(4),
                        value: "four".to_owned(),
                    })),
                    BoolRecipe::All(
                        vec![BoolRecipe::Leaf {
                            atom: atom(3),
                            value: "three".to_owned(),
                        }]
                        .into_boxed_slice(),
                    ),
                ]
                .into_boxed_slice(),
            )
        );
        assert!(matches!(implication.conclusion(), BoolRecipe::All(_)));
    }

    #[test]
    fn arbitrary_connective_semantics_cannot_enter_the_api() {
        // The only caller-controlled values occur at leaves. There is no
        // connective trait to implement and no public capability constructor.
        let mut table = LocalPropTable::open_in_memory().expect("table");
        let fact = table
            .define(Definition::new(atom(1), vec![pos(2)]).expect("definition"))
            .expect("define")
            .remove(0);
        let environment = table
            .realize_environment(&leaves(&[(1, "ignored-defined"), (2, "leaf")]))
            .expect("environment");
        let implication = table.realize_fact(&fact, &environment).expect("fact");
        assert!(matches!(implication.premise(), BoolRecipe::All(_)));
        assert_eq!(
            implication.conclusion(),
            &BoolRecipe::Leaf {
                atom: atom(2),
                value: "leaf".to_owned(),
            }
        );
    }

    #[test]
    fn two_directional_facts_share_one_mapping() {
        let mut table = LocalPropTable::open_in_memory().expect("table");
        let elimination = table
            .define(Definition::new(atom(1), vec![pos(2)]).expect("definition"))
            .expect("define")
            .remove(0);
        let reverse_premise = table.reflexivity(pos(2));
        let introduction = table
            .introduce(pos(2), atom(1), &[reverse_premise])
            .expect("introduction");
        let environment = table
            .realize_environment(&leaves(&[(2, "two")]))
            .expect("environment");
        let forward = table
            .realize_fact(&elimination, &environment)
            .expect("forward");
        let reverse = table
            .realize_fact(&introduction, &environment)
            .expect("reverse");
        assert_eq!(forward.mapping(), environment.mapping());
        assert_eq!(reverse.mapping(), environment.mapping());
        assert_eq!(forward.premise(), reverse.conclusion());
        assert_eq!(forward.conclusion(), reverse.premise());
    }

    #[test]
    fn incomplete_unrelated_definition_environment_is_rejected() {
        let mut table = LocalPropTable::open_in_memory().expect("table");
        table
            .define(Definition::new(atom(10), vec![pos(11)]).expect("definition"))
            .expect("unrelated definition");
        assert!(matches!(
            table.realize_environment::<String>(&BTreeMap::new()),
            Err(Error::Incomplete(missing)) if missing == atom(11)
        ));
    }

    #[test]
    fn foreign_stale_and_fact_profile_mismatches_are_rejected() {
        let mut table = LocalPropTable::open_in_memory().expect("table");
        let foreign = LocalPropTable::open_in_memory().expect("foreign");
        let foreign_fact = foreign.reflexivity(pos(1));
        let environment = table
            .realize_environment(&leaves(&[(1, "one")]))
            .expect("environment");
        assert!(matches!(
            table.realize_fact(&foreign_fact, &environment),
            Err(Error::ForeignSnapshot)
        ));

        let fact = table.reflexivity(pos(1));
        let mut realized = table.realize_fact(&fact, &environment).expect("fact");
        realized.checker = CheckerVersion::LocalImplicationBinaryLratV1;
        assert!(matches!(
            table.revalidate_realized(&fact, &realized),
            Err(Error::CheckerMismatch)
        ));
        realized.checker = fact.checker();
        realized.judgement = Judgement::Transitivity;
        assert!(matches!(
            table.revalidate_realized(&fact, &realized),
            Err(Error::JudgementMismatch)
        ));
        realized.judgement = fact.judgement();
        realized.conclusion_literal = neg(1);
        assert!(matches!(
            table.revalidate_realized(&fact, &realized),
            Err(Error::FactMismatch)
        ));

        table
            .define(Definition::new(atom(2), vec![pos(3)]).expect("definition"))
            .expect("advance snapshot");
        assert!(matches!(
            table.realize_fact(&fact, &environment),
            Err(Error::StaleSnapshot)
        ));
    }

    #[test]
    fn endpoint_free_atom_must_belong_to_the_reusable_mapping() {
        let table = LocalPropTable::open_in_memory().expect("table");
        let environment = table
            .realize_environment::<String>(&BTreeMap::new())
            .expect("empty definitions are complete");
        assert!(matches!(
            table.realize_fact(&table.reflexivity(pos(1)), &environment),
            Err(Error::Incomplete(missing)) if missing == atom(1)
        ));
    }
}
