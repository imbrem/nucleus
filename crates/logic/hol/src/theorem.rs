use std::collections::BTreeMap;

use bitflags::bitflags;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{ArenaObject, ImportTableObject, Link, Prop, Relation, Relations};

bitflags! {
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub(crate) struct TheoremFlags: u8 {
        const PREMISE = 1 << 0;
        const CONCLUSION = 1 << 1;
    }
}

/// A theorem contract interpreted entirely in `arena`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Thm<A = Option<Link<ArenaObject>>, I = Option<Link<ImportTableObject>>> {
    arena: A,
    imports: I,
    theorems: BTreeMap<u32, TheoremFlags>,
    relations: Relations,
}

impl<A, I> Thm<A, I> {
    #[must_use]
    pub fn new(arena: A, imports: I) -> Self {
        Self {
            arena,
            imports,
            theorems: BTreeMap::new(),
            relations: Relations::new(),
        }
    }
    #[must_use]
    pub const fn arena(&self) -> &A {
        &self.arena
    }
    #[must_use]
    pub const fn imports(&self) -> &I {
        &self.imports
    }
    pub fn map_links<B, J>(
        self,
        arena: impl FnOnce(A) -> B,
        imports: impl FnOnce(I) -> J,
    ) -> Thm<B, J> {
        Thm {
            arena: arena(self.arena),
            imports: imports(self.imports),
            theorems: self.theorems,
            relations: self.relations,
        }
    }
    pub fn premise_theorems(&self) -> impl Iterator<Item = u32> + '_ {
        self.theorems
            .iter()
            .filter_map(|(id, flags)| flags.contains(TheoremFlags::PREMISE).then_some(*id))
    }
    pub fn conclusion_theorems(&self) -> impl Iterator<Item = u32> + '_ {
        self.theorems
            .iter()
            .filter_map(|(id, flags)| flags.contains(TheoremFlags::CONCLUSION).then_some(*id))
    }
    /// Materialize the premise side without exposing the packed flag maps.
    #[must_use]
    pub fn premises(&self) -> Prop<A, I>
    where
        A: Clone,
        I: Clone,
    {
        Prop::from_parts(
            self.arena.clone(),
            self.imports.clone(),
            self.premise_theorems(),
            |relation| self.relations.premise_pairs(relation).collect(),
        )
    }
    /// Materialize the conclusion side without exposing the packed flag maps.
    #[must_use]
    pub fn conclusion(&self) -> Prop<A, I>
    where
        A: Clone,
        I: Clone,
    {
        Prop::from_parts(
            self.arena.clone(),
            self.imports.clone(),
            self.conclusion_theorems(),
            |relation| self.relations.conclusion_pairs(relation).collect(),
        )
    }

    /// Construct the private packed representation from its logical pair.
    /// Returns `None` when the two propositions do not share their arena and
    /// import table.
    pub fn from_props(premises: Prop<A, I>, conclusion: Prop<A, I>) -> Option<Self>
    where
        A: Eq,
        I: Eq,
    {
        if premises.arena() != conclusion.arena() || premises.imports() != conclusion.imports() {
            return None;
        }
        let (arena, imports, premise_theorems, premise_relations) = premises.into_parts();
        let (_, _, conclusion_theorems, conclusion_relations) = conclusion.into_parts();
        let mut theorem = Self::new(arena, imports);
        for imported in premise_theorems {
            theorem.assume(imported);
        }
        for imported in conclusion_theorems {
            theorem.conclude(imported);
        }
        for relation in Relation::ALL {
            for (left, right) in premise_relations
                .get(&relation)
                .into_iter()
                .flatten()
                .copied()
            {
                theorem.relations.insert_premise(relation, left, right);
            }
            for (left, right) in conclusion_relations
                .get(&relation)
                .into_iter()
                .flatten()
                .copied()
            {
                theorem.relations.insert_conclusion(relation, left, right);
            }
        }
        Some(theorem)
    }

    /// Regard one proposition as the complete premise side.
    #[must_use]
    pub fn from_premises(premises: Prop<A, I>) -> Self {
        let (arena, imports, theorems, relations) = premises.into_parts();
        let mut theorem = Self::new(arena, imports);
        for imported in theorems {
            theorem.assume(imported);
        }
        for relation in Relation::ALL {
            for (left, right) in relations.get(&relation).into_iter().flatten().copied() {
                theorem.relations.insert_premise(relation, left, right);
            }
        }
        theorem
    }

    /// Regard one proposition as the complete conclusion side.
    #[must_use]
    pub fn from_conclusion(conclusion: Prop<A, I>) -> Self {
        let (arena, imports, theorems, relations) = conclusion.into_parts();
        let mut theorem = Self::new(arena, imports);
        for imported in theorems {
            theorem.conclude(imported);
        }
        for relation in Relation::ALL {
            for (left, right) in relations.get(&relation).into_iter().flatten().copied() {
                theorem.relations.insert_conclusion(relation, left, right);
            }
        }
        theorem
    }

    /// Expose the logical pair of propositions, cloning their shared links.
    #[must_use]
    pub fn into_props(self) -> (Prop<A, I>, Prop<A, I>)
    where
        A: Clone,
        I: Clone,
    {
        let premises = self.premises();
        let conclusion = self.conclusion();
        (premises, conclusion)
    }
    #[must_use]
    pub const fn relations(&self) -> &Relations {
        &self.relations
    }
    #[must_use]
    pub const fn relations_mut(&mut self) -> &mut Relations {
        &mut self.relations
    }
    fn insert_theorem(&mut self, import: u32, flag: TheoremFlags) -> bool {
        let flags = self.theorems.entry(import).or_default();
        let old = *flags;
        flags.insert(flag);
        old != *flags
    }
    pub fn assume(&mut self, theorem: u32) -> bool {
        self.insert_theorem(theorem, TheoremFlags::PREMISE)
    }
    pub fn conclude(&mut self, theorem: u32) -> bool {
        self.insert_theorem(theorem, TheoremFlags::CONCLUSION)
    }
}

impl Thm {
    #[must_use]
    pub fn import_is_theorem(&self, table: &crate::ImportTable, id: u32) -> bool {
        table
            .get(id)
            .is_some_and(|link| link.kind == crate::ObjectKind::Theorem)
    }
}

#[derive(Serialize, Deserialize)]
struct ThmWire<A, I> {
    arena: A,
    imports: I,
    premise_theorems: Vec<u32>,
    conclusion_theorems: Vec<u32>,
    premises: BTreeMap<Relation, Vec<(u32, u32)>>,
    conclusions: BTreeMap<Relation, Vec<(u32, u32)>>,
}

impl<A: Serialize, I: Serialize> Serialize for Thm<A, I> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        ThmWire {
            arena: &self.arena,
            imports: &self.imports,
            premise_theorems: self
                .theorems
                .iter()
                .filter_map(|(id, flags)| flags.contains(TheoremFlags::PREMISE).then_some(*id))
                .collect(),
            conclusion_theorems: self
                .theorems
                .iter()
                .filter_map(|(id, flags)| flags.contains(TheoremFlags::CONCLUSION).then_some(*id))
                .collect(),
            premises: self.relations.wire_side(false),
            conclusions: self.relations.wire_side(true),
        }
        .serialize(serializer)
    }
}

impl<'de, A: Deserialize<'de>, I: Deserialize<'de>> Deserialize<'de> for Thm<A, I> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = ThmWire::<A, I>::deserialize(deserializer)?;
        let mut theorems = BTreeMap::new();
        for id in wire.premise_theorems {
            theorems
                .entry(id)
                .and_modify(|old| *old |= TheoremFlags::PREMISE)
                .or_insert(TheoremFlags::PREMISE);
        }
        for id in wire.conclusion_theorems {
            theorems
                .entry(id)
                .and_modify(|old| *old |= TheoremFlags::CONCLUSION)
                .or_insert(TheoremFlags::CONCLUSION);
        }
        let mut relations = Relations::new();
        relations.insert_wire_side(false, wire.premises);
        relations.insert_wire_side(true, wire.conclusions);
        Ok(Self {
            arena: wire.arena,
            imports: wire.imports,
            theorems,
            relations,
        })
    }
}
