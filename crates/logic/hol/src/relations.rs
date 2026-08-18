use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt::{self, Display, Formatter};

use covalence_lib_hash::O256;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{Ix, LinkRef};

type RelationSet = BTreeMap<Relation, BTreeSet<(SRef, SRef)>>;

/// A signed arena reference used as a relation endpoint.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct SRef(i32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidSRef;

impl Display for InvalidSRef {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str("i32::MIN is reserved and is not a signed arena reference")
    }
}

impl Error for InvalidSRef {}

impl<'de> Deserialize<'de> for SRef {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::from_raw(i32::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SRefView {
    Null,
    Pos(Ix),
    Neg(Ix),
}

impl SRef {
    pub const NULL: Self = Self(0);
    #[must_use]
    pub const fn pos(value: Ix) -> Self {
        Self(value.get().cast_signed())
    }
    #[must_use]
    pub const fn neg(value: Ix) -> Self {
        Self(-value.get().cast_signed())
    }
    /// # Errors
    /// Returns an error for `i32::MIN`, the sole signed value that is neither
    /// zero nor the positive or negative image of an [`Ix`].
    pub const fn from_raw(value: i32) -> Result<Self, InvalidSRef> {
        if value == i32::MIN {
            Err(InvalidSRef)
        } else {
            Ok(Self(value))
        }
    }
    #[must_use]
    pub const fn raw(self) -> i32 {
        self.0
    }
    #[must_use]
    pub fn view(self) -> SRefView {
        match self.0.cmp(&0) {
            Ordering::Equal => SRefView::Null,
            Ordering::Greater => {
                let Ok(reference) = Ix::new(self.0.cast_unsigned()) else {
                    unreachable!("positive i32 is an Ix")
                };
                SRefView::Pos(reference)
            }
            Ordering::Less => {
                let Ok(reference) = Ix::new(self.0.unsigned_abs()) else {
                    unreachable!("SRef excludes i32::MIN")
                };
                SRefView::Neg(reference)
            }
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

/// One unpacked logical side. This is the complete v2 sparse representation;
/// indexes such as E-classes can be derived outside the trusted core later.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub(crate) struct CtxBody {
    sequents: BTreeSet<LinkRef>,
    relations: RelationSet,
}

impl CtxBody {
    pub(crate) const fn new() -> Self {
        Self {
            sequents: BTreeSet::new(),
            relations: BTreeMap::new(),
        }
    }

    pub(crate) fn insert_sequent(&mut self, sequent: LinkRef) -> bool {
        self.sequents.insert(sequent)
    }

    pub(crate) fn insert(&mut self, relation: Relation, left: SRef, right: SRef) -> bool {
        self.relations
            .entry(relation)
            .or_default()
            .insert((left, right))
    }

    pub(crate) fn insert_symmetric(&mut self, relation: Relation, left: SRef, right: SRef) -> bool {
        assert!(
            relation.is_symmetric(),
            "directional relation passed as symmetric"
        );
        let forward = self.insert(relation, left, right);
        let reverse = left != right && self.insert(relation, right, left);
        forward || reverse
    }

    pub(crate) fn contains(&self, relation: Relation, left: SRef, right: SRef) -> bool {
        self.relations
            .get(&relation)
            .is_some_and(|pairs| pairs.contains(&(left, right)))
    }

    pub(crate) fn sequents(&self) -> impl Iterator<Item = LinkRef> + '_ {
        self.sequents.iter().copied()
    }

    pub(crate) fn pairs(&self, relation: Relation) -> impl Iterator<Item = (SRef, SRef)> + '_ {
        self.relations.get(&relation).into_iter().flatten().copied()
    }
}

/// One heterogeneous logical side, interpreted in one arena and import table.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Ctx<A = Option<LinkRef>, I = Option<O256>> {
    arena: A,
    imports: I,
    body: CtxBody,
}

impl<A, I> Ctx<A, I> {
    #[must_use]
    pub const fn new(arena: A, imports: I) -> Self {
        Self {
            arena,
            imports,
            body: CtxBody::new(),
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

    pub fn insert_sequent(&mut self, sequent: LinkRef) -> bool {
        self.body.insert_sequent(sequent)
    }

    pub fn insert(&mut self, relation: Relation, left: SRef, right: SRef) -> bool {
        self.body.insert(relation, left, right)
    }

    /// # Panics
    /// Panics when `relation` is directional.
    pub fn insert_symmetric(&mut self, relation: Relation, left: SRef, right: SRef) -> bool {
        self.body.insert_symmetric(relation, left, right)
    }

    #[must_use]
    pub fn contains(&self, relation: Relation, left: SRef, right: SRef) -> bool {
        self.body.contains(relation, left, right)
    }

    pub fn sequents(&self) -> impl Iterator<Item = LinkRef> + '_ {
        self.body.sequents()
    }

    pub fn pairs(&self, relation: Relation) -> impl Iterator<Item = (SRef, SRef)> + '_ {
        self.body.pairs(relation)
    }

    pub(crate) fn into_parts(self) -> (A, I, CtxBody) {
        (self.arena, self.imports, self.body)
    }

    pub(crate) const fn from_parts(arena: A, imports: I, body: CtxBody) -> Self {
        Self {
            arena,
            imports,
            body,
        }
    }
}
