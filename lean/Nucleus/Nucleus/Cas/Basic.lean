import Nucleus.Bytes
import Nucleus.O256
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Checked content-addressed facts

This file is a deliberately small LCF theory for whole content-addressed
objects. A `CasAssertion` is ordinary, unchecked data. Given a
`Name Bytes O256` instance, a `CasPair` also carries a proof that the instance
maps its blob to its hash; these checked pairs are the atoms of a finite `Cas`.

`Cas` is a finite relation, rather than a map from hashes to blobs.  It can
therefore retain and expose a hash collision.  Stores and lookup procedures are
outside this theory: they may be untrusted as long as checked pairs can only be
obtained by satisfying the validity proposition below.
-/

namespace Nucleus

/-- A content-addressing strategy from data to names. -/
class Name (Data : Type u) (Hash : Type v) where
  name : Data → Hash

/-- An unchecked claim that `blob` has content address `hash`. -/
@[ext]
structure CasAssertion where
  hash : O256
  blob : Bytes
  deriving DecidableEq

namespace CasAssertion

/-- The sole proposition enforced by a checked whole-object fact. -/
def Valid [Name Bytes O256] (assertion : CasAssertion) : Prop :=
  Name.name assertion.blob = assertion.hash

instance [Name Bytes O256] (assertion : CasAssertion) :
    Decidable assertion.Valid := by
  unfold Valid
  infer_instance

end CasAssertion

/--
The checked `(hash, blob)` atom from which a content-addressed store is made.

The `valid` field is proof data: extracting the runtime assertion forgets it,
while constructing a pair requires establishing the naming equation.
-/
structure CasPair [Name Bytes O256] where
  assertion : CasAssertion
  valid : assertion.Valid

namespace CasPair

variable [Name Bytes O256]

/-- The content address exposed by a checked pair. -/
def hash (pair : CasPair) : O256 := pair.assertion.hash

/-- The complete blob exposed by a checked pair. -/
def blob (pair : CasPair) : Bytes := pair.assertion.blob

theorem valid_hash (pair : CasPair) : Name.name pair.blob = pair.hash :=
  pair.valid

/-- Introduce a checked fact by computing its address from the complete blob. -/
def ofBlob (blob : Bytes) : CasPair where
  assertion := { hash := Name.name blob, blob }
  valid := rfl

@[simp] theorem ofBlob_hash (blob : Bytes) : (ofBlob blob).hash = Name.name blob := rfl

@[simp] theorem ofBlob_blob (blob : Bytes) : (ofBlob blob).blob = blob := rfl

/-- Checked pairs are equal when their observable assertions are equal. -/
@[ext]
theorem ext {left right : CasPair} (equal : left.assertion = right.assertion) :
    left = right := by
  cases left
  cases right
  cases equal
  rfl

instance : DecidableEq CasPair := fun left right ↦
  if equal : left.assertion = right.assertion then
    isTrue (ext equal)
  else
    isFalse fun pairsEqual ↦ equal (congrArg CasPair.assertion pairsEqual)

theorem ext_of_hash_eq_of_blob_eq {left right : CasPair}
    (hashEqual : left.hash = right.hash) (blobEqual : left.blob = right.blob) :
    left = right := by
  apply ext
  apply CasAssertion.ext <;> assumption

end CasPair

namespace CasAssertion

variable [Name Bytes O256]

/--
Check an ordinary assertion.  This is the LCF elimination boundary for
unchecked whole-object data.
-/
def check? (assertion : CasAssertion) : Option CasPair :=
  if valid : assertion.Valid then
    some ⟨assertion, valid⟩
  else
    none

@[simp] theorem check?_isSome (assertion : CasAssertion) :
    assertion.check?.isSome = decide assertion.Valid := by
  by_cases valid : assertion.Valid <;> simp [check?, valid]

theorem check?_sound {assertion : CasAssertion} {pair : CasPair}
    (checked : assertion.check? = some pair) :
    pair.assertion = assertion := by
  unfold check? at checked
  split at checked
  · rename_i valid
    have pairEqual : (⟨assertion, valid⟩ : CasPair) = pair :=
      Option.some.inj checked
    rw [← pairEqual]
  · contradiction

theorem check?_complete {assertion : CasAssertion} (valid : assertion.Valid) :
    ∃ pair, assertion.check? = some pair := by
  exact ⟨⟨assertion, valid⟩, by simp [check?, valid]⟩

theorem valid_of_check? {assertion : CasAssertion} {pair : CasPair}
    (checked : assertion.check? = some pair) :
    assertion.Valid := by
  rw [← check?_sound checked]
  exact pair.valid

end CasAssertion

/-- A finite relation of checked pairs.  Distinct colliding pairs are retained. -/
@[ext]
structure Cas [Name Bytes O256] where
  pairs : Finset CasPair
  deriving DecidableEq

namespace Cas

variable [Name Bytes O256]

instance : Membership CasPair Cas :=
  ⟨fun cas pair ↦ pair ∈ cas.pairs⟩

@[simp] theorem mem_iff_mem_pairs {pair : CasPair} {cas : Cas} :
    pair ∈ cas ↔ pair ∈ cas.pairs :=
  Iff.rfl

/-- The empty finite CAS. -/
def empty : Cas := ⟨∅⟩

instance : EmptyCollection Cas := ⟨empty⟩

/-- The CAS containing exactly one checked pair. -/
def singleton (pair : CasPair) : Cas := ⟨{pair}⟩

instance : Singleton CasPair Cas := ⟨singleton⟩

/-- Insert a checked pair.  An existing colliding pair is not overwritten. -/
def insert (cas : Cas) (pair : CasPair) : Cas :=
  ⟨{pair} ∪ cas.pairs⟩

instance : Insert CasPair Cas := ⟨fun pair cas ↦ cas.insert pair⟩

/-- Union two finite CAS relations. -/
def union (left right : Cas) : Cas :=
  ⟨left.pairs ∪ right.pairs⟩

instance : Union Cas := ⟨union⟩

/-- Keep precisely the checked pairs satisfying `predicate`. -/
def restrict (cas : Cas) (predicate : CasPair → Prop)
    [DecidablePred predicate] : Cas :=
  ⟨cas.pairs.filter predicate⟩

@[simp] theorem not_mem_empty (pair : CasPair) : pair ∉ empty := by
  simp [empty]

@[simp] theorem mem_singleton {left right : CasPair} :
    left ∈ singleton right ↔ left = right := by
  simp [singleton]

@[simp] theorem mem_insert {left right : CasPair} {cas : Cas} :
    left ∈ cas.insert right ↔ left = right ∨ left ∈ cas := by
  simp [insert]

@[simp] theorem mem_union {pair : CasPair} {left right : Cas} :
    pair ∈ left.union right ↔ pair ∈ left ∨ pair ∈ right := by
  simp [union]

@[simp] theorem mem_restrict {pair : CasPair} {cas : Cas}
    {predicate : CasPair → Prop} [DecidablePred predicate] :
    pair ∈ cas.restrict predicate ↔ pair ∈ cas ∧ predicate pair := by
  simp [restrict]

theorem ext_members {left right : Cas}
    (members : ∀ pair, pair ∈ left ↔ pair ∈ right) : left = right := by
  apply Cas.ext
  exact Finset.ext fun pair ↦ members pair

@[simp] theorem empty_union (cas : Cas) : empty.union cas = cas := by
  apply Cas.ext
  simp [union, empty]

@[simp] theorem union_empty (cas : Cas) : cas.union empty = cas := by
  apply Cas.ext
  simp [union, empty]

theorem union_comm (left right : Cas) : left.union right = right.union left := by
  apply Cas.ext
  exact Finset.union_comm left.pairs right.pairs

theorem union_assoc (first second third : Cas) :
    (first.union second).union third = first.union (second.union third) := by
  apply Cas.ext
  exact Finset.union_assoc first.pairs second.pairs third.pairs

@[simp] theorem union_self (cas : Cas) : cas.union cas = cas := by
  apply Cas.ext
  exact Finset.union_self cas.pairs

/-- Two checked pairs witness a collision when only their address agrees. -/
def HasCollision (cas : Cas) : Prop :=
  ∃ left ∈ cas, ∃ right ∈ cas,
    left.hash = right.hash ∧ left.blob ≠ right.blob

/-- Collision-freedom is a property of a CAS, not part of its representation. -/
def CollisionFree (cas : Cas) : Prop := ¬ cas.HasCollision

theorem collisionFree_iff_pairwise (cas : Cas) :
    cas.CollisionFree ↔
      ∀ {left right}, left ∈ cas → right ∈ cas →
        left.hash = right.hash → left.blob = right.blob := by
  constructor
  · intro collisionFree left right leftMem rightMem hashEqual
    by_contra blobDifferent
    exact collisionFree ⟨left, leftMem, right, rightMem, hashEqual, blobDifferent⟩
  · intro agree collision
    rcases collision with ⟨left, leftMem, right, rightMem, hashEqual, blobDifferent⟩
    exact blobDifferent (agree leftMem rightMem hashEqual)

@[simp] theorem collisionFree_empty : empty.CollisionFree := by
  rw [collisionFree_iff_pairwise]
  intro left _ leftMem
  simp [empty] at leftMem

@[simp] theorem collisionFree_singleton (pair : CasPair) :
    (singleton pair).CollisionFree := by
  rw [collisionFree_iff_pairwise]
  intro left right leftMem rightMem _
  have leftEqual : left = pair := mem_singleton.mp leftMem
  have rightEqual : right = pair := mem_singleton.mp rightMem
  rw [leftEqual, rightEqual]

/-- `pair` agrees with every same-address pair already in `cas`. -/
def CompatibleWith (cas : Cas) (pair : CasPair) : Prop :=
  ∀ other ∈ cas, other.hash = pair.hash → other.blob = pair.blob

/-- Two CASes have no cross-collision.  Either CAS may still collide internally. -/
def Compatible (left right : Cas) : Prop :=
  ∀ leftPair ∈ left, ∀ rightPair ∈ right,
    leftPair.hash = rightPair.hash → leftPair.blob = rightPair.blob

theorem compatible_symm {left right : Cas} :
    left.Compatible right ↔ right.Compatible left := by
  constructor
  · intro compatible rightPair rightMem leftPair leftMem hashEqual
    exact (compatible leftPair leftMem rightPair rightMem hashEqual.symm).symm
  · intro compatible leftPair leftMem rightPair rightMem hashEqual
    exact (compatible rightPair rightMem leftPair leftMem hashEqual.symm).symm

theorem compatible_singleton_right {cas : Cas} {pair : CasPair} :
    cas.Compatible (singleton pair) ↔ cas.CompatibleWith pair := by
  simp only [Compatible, CompatibleWith, mem_singleton]
  constructor
  · intro compatible other otherMem hashEqual
    exact compatible other otherMem pair rfl hashEqual
  · intro compatible other otherMem singletonPair singletonMem hashEqual
    subst singletonPair
    exact compatible other otherMem hashEqual

theorem compatible_singleton_left {cas : Cas} {pair : CasPair} :
    (singleton pair).Compatible cas ↔ cas.CompatibleWith pair := by
  rw [compatible_symm, compatible_singleton_right]

theorem compatibleWith_of_mem {cas : Cas} {pair : CasPair}
    (collisionFree : cas.CollisionFree)
    (member : pair ∈ cas) : cas.CompatibleWith pair := by
  rw [collisionFree_iff_pairwise] at collisionFree
  intro other otherMem hashEqual
  exact collisionFree otherMem member hashEqual

theorem collisionFree_insert_iff (cas : Cas) (pair : CasPair) :
    (cas.insert pair).CollisionFree ↔ cas.CollisionFree ∧ cas.CompatibleWith pair := by
  simp only [collisionFree_iff_pairwise]
  constructor
  · intro agree
    constructor
    · intro left right leftMem rightMem hashEqual
      exact agree (mem_insert.mpr (Or.inr leftMem))
        (mem_insert.mpr (Or.inr rightMem)) hashEqual
    · intro other otherMem hashEqual
      exact agree (mem_insert.mpr (Or.inr otherMem))
        (mem_insert.mpr (Or.inl rfl)) hashEqual
  · rintro ⟨collisionFree, compatible⟩ left right leftMem rightMem hashEqual
    rcases mem_insert.mp leftMem with leftEqual | leftMem
    · rcases mem_insert.mp rightMem with rightEqual | rightMem
      · rw [leftEqual, rightEqual]
      · exact (congrArg CasPair.blob leftEqual).trans
          (compatible right rightMem
            (hashEqual.symm.trans (congrArg CasPair.hash leftEqual))).symm
    · rcases mem_insert.mp rightMem with rightEqual | rightMem
      · exact (compatible left leftMem
          (hashEqual.trans (congrArg CasPair.hash rightEqual))).trans
          (congrArg CasPair.blob rightEqual).symm
      · exact collisionFree leftMem rightMem hashEqual

theorem collisionFree_union_iff (left right : Cas) :
    (left.union right).CollisionFree ↔
      left.CollisionFree ∧ right.CollisionFree ∧ left.Compatible right := by
  simp only [collisionFree_iff_pairwise]
  constructor
  · intro agree
    refine ⟨?_, ?_, ?_⟩
    · intro first second firstMem secondMem hashEqual
      exact agree (mem_union.mpr (Or.inl firstMem))
        (mem_union.mpr (Or.inl secondMem)) hashEqual
    · intro first second firstMem secondMem hashEqual
      exact agree (mem_union.mpr (Or.inr firstMem))
        (mem_union.mpr (Or.inr secondMem)) hashEqual
    · intro leftPair leftMem rightPair rightMem hashEqual
      exact agree (mem_union.mpr (Or.inl leftMem))
        (mem_union.mpr (Or.inr rightMem)) hashEqual
  · rintro ⟨leftFree, rightFree, compatible⟩ first second firstMem secondMem hashEqual
    rcases mem_union.mp firstMem with firstLeft | firstRight
    · rcases mem_union.mp secondMem with secondLeft | secondRight
      · exact leftFree firstLeft secondLeft hashEqual
      · exact compatible first firstLeft second secondRight hashEqual
    · rcases mem_union.mp secondMem with secondLeft | secondRight
      · exact (compatible second secondLeft first firstRight hashEqual.symm).symm
      · exact rightFree firstRight secondRight hashEqual

/-- Collision witnesses survive inclusion into a larger CAS. -/
theorem hasCollision_mono {small large : Cas}
    (subset : ∀ pair, pair ∈ small → pair ∈ large)
    (collision : small.HasCollision) : large.HasCollision := by
  rcases collision with ⟨left, leftMem, right, rightMem, hashEqual, blobDifferent⟩
  exact ⟨left, subset left leftMem, right, subset right rightMem,
    hashEqual, blobDifferent⟩

theorem hasCollision_union_left {left right : Cas}
    (collision : left.HasCollision) : (left.union right).HasCollision :=
  hasCollision_mono (fun _ member ↦ mem_union.mpr (Or.inl member)) collision

theorem hasCollision_union_right {left right : Cas}
    (collision : right.HasCollision) : (left.union right).HasCollision :=
  hasCollision_mono (fun _ member ↦ mem_union.mpr (Or.inr member)) collision

/-- Relational lookup deliberately exposes every colliding answer. -/
def Lookup (cas : Cas) (hash : O256) (blob : Bytes) : Prop :=
  ∃ pair ∈ cas, pair.hash = hash ∧ pair.blob = blob

theorem lookup_of_mem {cas : Cas} {pair : CasPair} (member : pair ∈ cas) :
    cas.Lookup pair.hash pair.blob :=
  ⟨pair, member, rfl, rfl⟩

/-- Every lookup result satisfies the naming equation. -/
theorem lookup_valid {cas : Cas} {hash : O256} {blob : Bytes}
    (found : cas.Lookup hash blob) : Name.name blob = hash := by
  rcases found with ⟨pair, _, hashEqual, blobEqual⟩
  rw [← hashEqual, ← blobEqual]
  exact pair.valid_hash

/-- A collision-free CAS has at most one blob at any address. -/
theorem lookup_functional {cas : Cas} (collisionFree : cas.CollisionFree)
    {hash : O256} {leftBlob rightBlob : Bytes}
    (leftLookup : cas.Lookup hash leftBlob)
    (rightLookup : cas.Lookup hash rightBlob) : leftBlob = rightBlob := by
  rw [collisionFree_iff_pairwise] at collisionFree
  rcases leftLookup with ⟨left, leftMem, leftHash, leftBlobEq⟩
  rcases rightLookup with ⟨right, rightMem, rightHash, rightBlobEq⟩
  rw [← leftBlobEq, ← rightBlobEq]
  exact collisionFree leftMem rightMem (leftHash.trans rightHash.symm)

/-- Lookup is functional exactly when the represented finite relation is collision-free. -/
theorem collisionFree_iff_lookup_functional (cas : Cas) :
    cas.CollisionFree ↔
      ∀ {hash leftBlob rightBlob},
        cas.Lookup hash leftBlob → cas.Lookup hash rightBlob → leftBlob = rightBlob := by
  constructor
  · exact fun collisionFree _ _ _ ↦ lookup_functional collisionFree
  · intro functional collision
    rcases collision with ⟨left, leftMem, right, rightMem, hashEqual, blobDifferent⟩
    apply blobDifferent
    apply functional (hash := left.hash) (lookup_of_mem leftMem)
    exact ⟨right, rightMem, hashEqual.symm, rfl⟩

end Cas

end Nucleus
