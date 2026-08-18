use std::sync::Arc;

use covalence_lib_hash::O256;
use serde::{Deserialize, Serialize, Serializer};

use crate::relations::CtxBody;
use crate::{Ctx, Format, Link, LinkRef, ObjectKind, Relation, SRef};

/// A sparse sequent with one shared arena/import scope and two ordinary sides.
/// Packed and indexed forms can be derived without changing this interface.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Seq<A = Option<LinkRef>, I = Option<O256>> {
    arena: A,
    imports: I,
    premises: CtxBody,
    conclusion: CtxBody,
}

impl<A, I> Seq<A, I> {
    #[must_use]
    pub const fn new(arena: A, imports: I) -> Self {
        Self {
            arena,
            imports,
            premises: CtxBody::new(),
            conclusion: CtxBody::new(),
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
            premises: self.premises,
            conclusion: self.conclusion,
        }
    }

    pub fn premise_sequents(&self) -> impl Iterator<Item = LinkRef> + '_ {
        self.premises.sequents()
    }

    pub fn conclusion_sequents(&self) -> impl Iterator<Item = LinkRef> + '_ {
        self.conclusion.sequents()
    }

    #[must_use]
    pub fn premises(&self) -> Ctx<A, I>
    where
        A: Clone,
        I: Clone,
    {
        Ctx::from_parts(
            self.arena.clone(),
            self.imports.clone(),
            self.premises.clone(),
        )
    }

    #[must_use]
    pub fn conclusion(&self) -> Ctx<A, I>
    where
        A: Clone,
        I: Clone,
    {
        Ctx::from_parts(
            self.arena.clone(),
            self.imports.clone(),
            self.conclusion.clone(),
        )
    }

    /// Construct a sequent from contexts that share the same arena and import
    /// table. The common scope is stored only once.
    pub fn from_contexts(premises: Ctx<A, I>, conclusion: Ctx<A, I>) -> Option<Self>
    where
        A: Eq,
        I: Eq,
    {
        if premises.arena() != conclusion.arena() || premises.imports() != conclusion.imports() {
            return None;
        }
        let (arena, imports, premises) = premises.into_parts();
        let (_, _, conclusion) = conclusion.into_parts();
        Some(Self {
            arena,
            imports,
            premises,
            conclusion,
        })
    }

    #[must_use]
    pub fn from_premises(premises: Ctx<A, I>) -> Self {
        let (arena, imports, premises) = premises.into_parts();
        Self {
            arena,
            imports,
            premises,
            conclusion: CtxBody::default(),
        }
    }

    #[must_use]
    pub fn from_conclusion(conclusion: Ctx<A, I>) -> Self {
        let (arena, imports, conclusion) = conclusion.into_parts();
        Self {
            arena,
            imports,
            premises: CtxBody::default(),
            conclusion,
        }
    }

    #[must_use]
    pub fn into_contexts(self) -> (Ctx<A, I>, Ctx<A, I>)
    where
        A: Clone,
        I: Clone,
    {
        let premises = Ctx::from_parts(self.arena.clone(), self.imports.clone(), self.premises);
        let conclusion = Ctx::from_parts(self.arena, self.imports, self.conclusion);
        (premises, conclusion)
    }

    pub fn assume(&mut self, sequent: LinkRef) -> bool {
        self.premises.insert_sequent(sequent)
    }

    pub fn conclude(&mut self, sequent: LinkRef) -> bool {
        self.conclusion.insert_sequent(sequent)
    }

    pub fn insert_premise(&mut self, relation: Relation, left: SRef, right: SRef) -> bool {
        self.premises.insert(relation, left, right)
    }

    pub fn insert_conclusion(&mut self, relation: Relation, left: SRef, right: SRef) -> bool {
        self.conclusion.insert(relation, left, right)
    }

    pub fn insert_symmetric_premise(
        &mut self,
        relation: Relation,
        left: SRef,
        right: SRef,
    ) -> bool {
        self.premises.insert_symmetric(relation, left, right)
    }

    pub fn insert_symmetric_conclusion(
        &mut self,
        relation: Relation,
        left: SRef,
        right: SRef,
    ) -> bool {
        self.conclusion.insert_symmetric(relation, left, right)
    }

    #[must_use]
    pub fn contains_premise(&self, relation: Relation, left: SRef, right: SRef) -> bool {
        self.premises.contains(relation, left, right)
    }

    #[must_use]
    pub fn contains_conclusion(&self, relation: Relation, left: SRef, right: SRef) -> bool {
        self.conclusion.contains(relation, left, right)
    }

    pub fn premise_pairs(&self, relation: Relation) -> impl Iterator<Item = (SRef, SRef)> + '_ {
        self.premises.pairs(relation)
    }

    pub fn conclusion_pairs(&self, relation: Relation) -> impl Iterator<Item = (SRef, SRef)> + '_ {
        self.conclusion.pairs(relation)
    }
}

impl Seq {
    #[must_use]
    pub fn link_ref_is_sequent(&self, table: &crate::ImportTable, link: LinkRef) -> bool {
        link.kind == crate::ObjectKind::Sequent && table.get(link.import).is_some()
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
    /// Returns an error if the sequent cannot be serialized as CBOR.
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
