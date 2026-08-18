use std::collections::BTreeMap;
use std::collections::BTreeSet;

use bitflags::bitflags;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{ArenaObject, ImportTableObject, Ix, Link};

type RelationSet = BTreeMap<Relation, BTreeSet<(RelRef, RelRef)>>;
type PropParts<A, I> = (A, I, BTreeSet<u32>, RelationSet);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImportId(u32);
impl ImportId {
    #[must_use]
    pub const fn new(value: u32) -> Self {
        Self(value)
    }
    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }
}

/// A relation endpoint encoded as a signed arena literal in one `u32`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RelRef(u32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RelRefView {
    Null,
    Pos(Ix),
    Neg(Ix),
}

impl RelRef {
    pub const NULL: Self = Self(0);
    #[must_use]
    pub const fn pos(value: Ix) -> Self {
        Self(value.get())
    }
    #[must_use]
    pub const fn neg(value: Ix) -> Self {
        Self(value.get().wrapping_neg())
    }
    #[must_use]
    pub const fn from_raw(value: u32) -> Self {
        Self(value)
    }
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
    #[must_use]
    pub fn view(self) -> RelRefView {
        let signed = self.0.cast_signed();
        if signed == 0 || signed == i32::MIN {
            RelRefView::Null
        } else if signed > 0 {
            Ix::new(signed.cast_unsigned()).map_or(RelRefView::Null, RelRefView::Pos)
        } else {
            Ix::new(signed.unsigned_abs()).map_or(RelRefView::Null, RelRefView::Neg)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Relation {
    SynEq = 0,
    ConvEq = 1,
    TyEq = 2,
    HasTy = 3,
    Imp = 4,
    Eq = 5,
    HasKind = 6,
    Ne = 7,
}

impl Relation {
    pub const ALL: [Self; 8] = [
        Self::SynEq,
        Self::ConvEq,
        Self::TyEq,
        Self::HasTy,
        Self::Imp,
        Self::Eq,
        Self::HasKind,
        Self::Ne,
    ];
    #[must_use]
    pub const fn is_symmetric(self) -> bool {
        matches!(
            self,
            Self::SynEq | Self::ConvEq | Self::TyEq | Self::Eq | Self::Ne
        )
    }
    pub(crate) const fn flag(self) -> RelationFlags {
        RelationFlags::from_bits_retain(1 << self as u8)
    }
}

impl TryFrom<u8> for Relation {
    type Error = u8;
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::ALL.get(usize::from(value)).copied().ok_or(value)
    }
}

impl Serialize for Relation {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        (*self as u8).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Relation {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::try_from(u8::deserialize(deserializer)?)
            .map_err(|_| serde::de::Error::custom("unsupported relation"))
    }
}

bitflags! {
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub(crate) struct RelationFlags: u8 {
        const SYN_EQ = 1 << 0; const CONV_EQ = 1 << 1; const TY_EQ = 1 << 2;
        const HAS_TY = 1 << 3; const IMP = 1 << 4; const EQ = 1 << 5;
        const HAS_KIND = 1 << 6; const NE = 1 << 7;
    }
}

/// Sparse relations with `(premise, conclusion)` masks at each oriented pair.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Relations {
    pairs: BTreeMap<(RelRef, RelRef), (RelationFlags, RelationFlags)>,
}

/// One side of a theorem: imported theorems and oriented relation facts.
///
/// The fields are private so the packed representation can change without
/// changing the logical API or canonical CBOR format.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Prop<A = Option<Link<ArenaObject>>, I = Option<Link<ImportTableObject>>> {
    arena: A,
    imports: I,
    theorems: BTreeSet<u32>,
    relations: RelationSet,
}

impl<A, I> Prop<A, I> {
    #[must_use]
    pub const fn new(arena: A, imports: I) -> Self {
        Self {
            arena,
            imports,
            theorems: BTreeSet::new(),
            relations: BTreeMap::new(),
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

    pub fn insert_theorem(&mut self, theorem: u32) -> bool {
        self.theorems.insert(theorem)
    }

    pub fn insert(&mut self, relation: Relation, left: RelRef, right: RelRef) -> bool {
        self.relations
            .entry(relation)
            .or_default()
            .insert((left, right))
    }

    /// # Panics
    /// Panics when `relation` is directional.
    pub fn insert_symmetric(&mut self, relation: Relation, left: RelRef, right: RelRef) -> bool {
        assert!(
            relation.is_symmetric(),
            "directional relation passed as symmetric"
        );
        let forward = self.insert(relation, left, right);
        let reverse = left != right && self.insert(relation, right, left);
        forward || reverse
    }

    #[must_use]
    pub fn contains(&self, relation: Relation, left: RelRef, right: RelRef) -> bool {
        self.relations
            .get(&relation)
            .is_some_and(|pairs| pairs.contains(&(left, right)))
    }

    pub fn theorems(&self) -> impl Iterator<Item = u32> + '_ {
        self.theorems.iter().copied()
    }

    pub fn pairs(&self, relation: Relation) -> impl Iterator<Item = (RelRef, RelRef)> + '_ {
        self.relations.get(&relation).into_iter().flatten().copied()
    }

    pub(crate) fn into_parts(self) -> PropParts<A, I> {
        (self.arena, self.imports, self.theorems, self.relations)
    }

    pub(crate) fn from_parts(
        arena: A,
        imports: I,
        theorems: impl IntoIterator<Item = u32>,
        relations: impl Fn(Relation) -> Vec<(RelRef, RelRef)>,
    ) -> Self {
        let mut proposition = Self::new(arena, imports);
        proposition.theorems.extend(theorems);
        for relation in Relation::ALL {
            proposition
                .relations
                .entry(relation)
                .or_default()
                .extend(relations(relation));
        }
        proposition.relations.retain(|_, pairs| !pairs.is_empty());
        proposition
    }
}

impl Relations {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pairs: BTreeMap::new(),
        }
    }
    fn insert_side(
        &mut self,
        conclusion: bool,
        relation: Relation,
        left: RelRef,
        right: RelRef,
    ) -> bool {
        let flags = self.pairs.entry((left, right)).or_default();
        let side = if conclusion {
            &mut flags.1
        } else {
            &mut flags.0
        };
        let old = *side;
        side.insert(relation.flag());
        old != *side
    }
    pub fn insert_premise(&mut self, relation: Relation, left: RelRef, right: RelRef) -> bool {
        self.insert_side(false, relation, left, right)
    }
    pub fn insert_conclusion(&mut self, relation: Relation, left: RelRef, right: RelRef) -> bool {
        self.insert_side(true, relation, left, right)
    }
    fn insert_symmetric(
        &mut self,
        conclusion: bool,
        relation: Relation,
        left: RelRef,
        right: RelRef,
    ) -> bool {
        assert!(
            relation.is_symmetric(),
            "directional relation passed as symmetric"
        );
        let forward = self.insert_side(conclusion, relation, left, right);
        let reverse = left != right && self.insert_side(conclusion, relation, right, left);
        forward || reverse
    }
    pub fn insert_symmetric_premise(
        &mut self,
        relation: Relation,
        left: RelRef,
        right: RelRef,
    ) -> bool {
        self.insert_symmetric(false, relation, left, right)
    }
    pub fn insert_symmetric_conclusion(
        &mut self,
        relation: Relation,
        left: RelRef,
        right: RelRef,
    ) -> bool {
        self.insert_symmetric(true, relation, left, right)
    }
    #[must_use]
    pub fn contains_premise(&self, relation: Relation, left: RelRef, right: RelRef) -> bool {
        self.pairs
            .get(&(left, right))
            .is_some_and(|flags| flags.0.contains(relation.flag()))
    }
    #[must_use]
    pub fn contains_conclusion(&self, relation: Relation, left: RelRef, right: RelRef) -> bool {
        self.pairs
            .get(&(left, right))
            .is_some_and(|flags| flags.1.contains(relation.flag()))
    }
    pub(crate) fn pairs(
        &self,
    ) -> impl Iterator<Item = ((RelRef, RelRef), (RelationFlags, RelationFlags))> + '_ {
        self.pairs.iter().map(|(pair, flags)| (*pair, *flags))
    }

    pub fn premise_pairs(&self, relation: Relation) -> impl Iterator<Item = (RelRef, RelRef)> + '_ {
        self.pairs()
            .filter_map(move |(pair, flags)| flags.0.contains(relation.flag()).then_some(pair))
    }
    pub fn conclusion_pairs(
        &self,
        relation: Relation,
    ) -> impl Iterator<Item = (RelRef, RelRef)> + '_ {
        self.pairs()
            .filter_map(move |(pair, flags)| flags.1.contains(relation.flag()).then_some(pair))
    }
    pub(crate) fn wire_side(&self, conclusion: bool) -> BTreeMap<Relation, Vec<(u32, u32)>> {
        Relation::ALL
            .into_iter()
            .filter_map(|relation| {
                let pairs = if conclusion {
                    self.conclusion_pairs(relation)
                        .map(|(a, b)| (a.raw(), b.raw()))
                        .collect::<Vec<_>>()
                } else {
                    self.premise_pairs(relation)
                        .map(|(a, b)| (a.raw(), b.raw()))
                        .collect::<Vec<_>>()
                };
                (!pairs.is_empty()).then_some((relation, pairs))
            })
            .collect()
    }
    pub(crate) fn insert_wire_side(
        &mut self,
        conclusion: bool,
        relations: BTreeMap<Relation, Vec<(u32, u32)>>,
    ) {
        for (relation, pairs) in relations {
            for (left, right) in pairs {
                self.insert_side(
                    conclusion,
                    relation,
                    RelRef::from_raw(left),
                    RelRef::from_raw(right),
                );
            }
        }
    }
}
