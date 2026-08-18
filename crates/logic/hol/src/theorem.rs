use std::collections::BTreeMap;
use std::sync::Arc;

use bitflags::bitflags;
use covalence_lib_hash::O256;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{Ctx, Format, Link, LinkRef, ObjectKind, Relation, Relations};

bitflags! {
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub(crate) struct SeqFlags: u8 {
        const PREMISE = 1 << 0;
        const CONCLUSION = 1 << 1;
    }
}

/// A sequent contract interpreted entirely in `arena`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Seq<A = Option<LinkRef>, I = Option<O256>> {
    arena: A,
    imports: I,
    sequents: BTreeMap<LinkRef, SeqFlags>,
    relations: Relations,
}

impl<A, I> Seq<A, I> {
    #[must_use]
    pub fn new(arena: A, imports: I) -> Self {
        Self {
            arena,
            imports,
            sequents: BTreeMap::new(),
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
    ) -> Seq<B, J> {
        Seq {
            arena: arena(self.arena),
            imports: imports(self.imports),
            sequents: self.sequents,
            relations: self.relations,
        }
    }
    pub fn premise_sequents(&self) -> impl Iterator<Item = LinkRef> + '_ {
        self.sequents
            .iter()
            .filter_map(|(id, flags)| flags.contains(SeqFlags::PREMISE).then_some(*id))
    }
    pub fn conclusion_sequents(&self) -> impl Iterator<Item = LinkRef> + '_ {
        self.sequents
            .iter()
            .filter_map(|(id, flags)| flags.contains(SeqFlags::CONCLUSION).then_some(*id))
    }
    /// Materialize the premise side without exposing the packed flag maps.
    #[must_use]
    pub fn premises(&self) -> Ctx<A, I>
    where
        A: Clone,
        I: Clone,
    {
        Ctx::from_parts(
            self.arena.clone(),
            self.imports.clone(),
            self.premise_sequents(),
            |relation| self.relations.premise_pairs(relation).collect(),
        )
    }
    /// Materialize the conclusion side without exposing the packed flag maps.
    #[must_use]
    pub fn conclusion(&self) -> Ctx<A, I>
    where
        A: Clone,
        I: Clone,
    {
        Ctx::from_parts(
            self.arena.clone(),
            self.imports.clone(),
            self.conclusion_sequents(),
            |relation| self.relations.conclusion_pairs(relation).collect(),
        )
    }

    /// Repack a compatible pair of contexts. Returns `None` when their arena
    /// or import-table handles disagree.
    pub fn from_contexts(premises: Ctx<A, I>, conclusion: Ctx<A, I>) -> Option<Self>
    where
        A: Eq,
        I: Eq,
    {
        if premises.arena() != conclusion.arena() || premises.imports() != conclusion.imports() {
            return None;
        }
        let (arena, imports, premise_sequents, premise_relations) = premises.into_parts();
        let (_, _, conclusion_sequents, conclusion_relations) = conclusion.into_parts();
        let mut sequent = Self::new(arena, imports);
        for imported in premise_sequents {
            sequent.assume(imported);
        }
        for imported in conclusion_sequents {
            sequent.conclude(imported);
        }
        for relation in Relation::ALL {
            for (left, right) in premise_relations
                .get(&relation)
                .into_iter()
                .flatten()
                .copied()
            {
                sequent.relations.insert_premise(relation, left, right);
            }
            for (left, right) in conclusion_relations
                .get(&relation)
                .into_iter()
                .flatten()
                .copied()
            {
                sequent.relations.insert_conclusion(relation, left, right);
            }
        }
        Some(sequent)
    }

    #[must_use]
    pub fn from_premises(premises: Ctx<A, I>) -> Self {
        let (arena, imports, sequents, relations) = premises.into_parts();
        let mut sequent = Self::new(arena, imports);
        for imported in sequents {
            sequent.assume(imported);
        }
        for relation in Relation::ALL {
            for (left, right) in relations.get(&relation).into_iter().flatten().copied() {
                sequent.relations.insert_premise(relation, left, right);
            }
        }
        sequent
    }

    #[must_use]
    pub fn from_conclusion(conclusion: Ctx<A, I>) -> Self {
        let (arena, imports, sequents, relations) = conclusion.into_parts();
        let mut sequent = Self::new(arena, imports);
        for imported in sequents {
            sequent.conclude(imported);
        }
        for relation in Relation::ALL {
            for (left, right) in relations.get(&relation).into_iter().flatten().copied() {
                sequent.relations.insert_conclusion(relation, left, right);
            }
        }
        sequent
    }

    #[must_use]
    pub fn into_contexts(self) -> (Ctx<A, I>, Ctx<A, I>)
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
    fn insert_sequent(&mut self, import: LinkRef, flag: SeqFlags) -> bool {
        let flags = self.sequents.entry(import).or_default();
        let old = *flags;
        flags.insert(flag);
        old != *flags
    }
    pub fn assume(&mut self, sequent: LinkRef) -> bool {
        self.insert_sequent(sequent, SeqFlags::PREMISE)
    }
    pub fn conclude(&mut self, sequent: LinkRef) -> bool {
        self.insert_sequent(sequent, SeqFlags::CONCLUSION)
    }
}

impl Seq {
    #[must_use]
    pub fn link_ref_is_sequent(&self, table: &crate::ImportTable, link: LinkRef) -> bool {
        link.kind == crate::ObjectKind::Sequent && table.get(link.import).is_some()
    }
}

mod detail {
    use std::collections::BTreeMap;

    use serde::{Deserialize, Serialize};

    use crate::{LinkRef, Relation};

    #[derive(Serialize, Deserialize)]
    pub(super) struct Seq<A, I> {
        pub arena: A,
        pub imports: I,
        pub premise_sequents: Vec<LinkRef>,
        pub conclusion_sequents: Vec<LinkRef>,
        pub premises: BTreeMap<Relation, Vec<(i32, i32)>>,
        pub conclusions: BTreeMap<Relation, Vec<(i32, i32)>>,
    }
}

impl<'a, A, I> From<&'a Seq<A, I>> for detail::Seq<&'a A, &'a I> {
    fn from(sequent: &'a Seq<A, I>) -> Self {
        Self {
            arena: &sequent.arena,
            imports: &sequent.imports,
            premise_sequents: sequent.premise_sequents().collect(),
            conclusion_sequents: sequent.conclusion_sequents().collect(),
            premises: sequent.relations.wire_side(false),
            conclusions: sequent.relations.wire_side(true),
        }
    }
}

impl<A, I> From<detail::Seq<A, I>> for Seq<A, I> {
    fn from(wire: detail::Seq<A, I>) -> Self {
        let mut sequent = Self::new(wire.arena, wire.imports);
        for id in wire.premise_sequents {
            sequent.assume(id);
        }
        for id in wire.conclusion_sequents {
            sequent.conclude(id);
        }
        sequent.relations.insert_wire_side(false, wire.premises);
        sequent.relations.insert_wire_side(true, wire.conclusions);
        sequent
    }
}

impl<A: Serialize, I: Serialize> Serialize for Seq<A, I> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        detail::Seq::from(self).serialize(serializer)
    }
}

impl<'de, A: Deserialize<'de>, I: Deserialize<'de>> Deserialize<'de> for Seq<A, I> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(detail::Seq::<A, I>::deserialize(deserializer)?.into())
    }
}

#[derive(Clone, Debug)]
pub struct SharedSeq(Arc<CachedSeq>);

#[derive(Debug)]
struct CachedSeq {
    sequent: Seq,
    address: O256,
}

impl SharedSeq {
    /// # Errors
    /// Returns an error if the sequent cannot be serialized to stable v0 CBOR.
    pub fn new(sequent: Seq) -> Result<Self, crate::EncodeError> {
        let bytes = crate::serialize_cbor(&sequent)?;
        let address = O256::from_bytes(&bytes);
        Ok(Self(Arc::new(CachedSeq { sequent, address })))
    }
    #[must_use]
    pub fn sequent(&self) -> &Seq {
        &self.0.sequent
    }
    #[must_use]
    pub fn address(&self) -> O256 {
        self.0.address
    }
    #[must_use]
    pub fn link(&self) -> Link {
        Link::new(self.address(), Format::CborSparse, ObjectKind::Sequent)
    }
}

impl Serialize for SharedSeq {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.link().serialize(serializer)
    }
}
