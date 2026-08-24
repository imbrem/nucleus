import Nucleus.Hol.Ethane.LogicalOpcode

/-!
# Canonical signed classical sequents

This file specifies the semantic contract for compact checked theorems.  A
`PropId` is a nonzero signed integer.  Deliberately following the kernel wire
contract, a negative integer denotes the positive proposition and a positive
integer denotes its negation. Each theorem directly owns two small canonical
arrays; there is no proposition-set identity or interning table.
-/

namespace Nucleus.Hol.Ethane.ClassicalSequent

open Nucleus.Hol.Ethane

/-- A signed reference to a Boolean term.  Negative is positive polarity.  Its
magnitude is globally bounded by the same strict limit as `OneBased.Ref`. -/
abbrev PropId := { value : Int //
  value ≠ 0 ∧ value.natAbs < OneBased.Ref.maxExclusive }

/-- The referenced one-based term index, with polarity erased. -/
def PropId.ref (id : PropId) : Nat := id.val.natAbs

/-- Flip polarity without changing the referenced term. -/
def PropId.neg (id : PropId) : PropId :=
  ⟨-id.val, by omega, by simpa using id.property.2⟩

/-- Total positive-polarity conversion from the globally bounded local ref. -/
def PropId.positive (reference : OneBased.Ref) : PropId :=
  ⟨-Int.ofNat reference.val.toNat, by
    constructor
    · have natNonzero : reference.val.toNat ≠ 0 := by
        intro zero
        apply reference.property.1
        exact UInt64.toNat_inj.mp (by simpa using zero)
      simpa using natNonzero
    · simpa using reference.property.2⟩

@[simp] theorem PropId.positive_val (reference : OneBased.Ref) :
    (PropId.positive reference).val = -Int.ofNat reference.val.toNat := rfl

@[simp] theorem PropId.positive_ref (reference : OneBased.Ref) :
    (PropId.positive reference).ref = reference.val.toNat := by
  simp [PropId.positive, PropId.ref]

@[simp] theorem PropId.neg_val (id : PropId) : id.neg.val = -id.val := rfl

@[simp] theorem PropId.neg_neg (id : PropId) : id.neg.neg = id := by
  apply Subtype.ext
  simp [PropId.neg]

/-- Canonical proposition sets. `Finset.sort` supplies their unique wire list. -/
abbrev PropSet := Finset PropId

/-- The unique sorted, duplicate-free list representation of a proposition set. -/
def PropSet.toList (set : PropSet) : List PropId := set.sort (· ≤ ·)

theorem PropSet.toList_sorted (set : PropSet) : set.toList.SortedLT :=
  Finset.sortedLT_sort set

theorem PropSet.toList_nodup (set : PropSet) : set.toList.Nodup :=
  Finset.sort_nodup set (· ≤ ·)

@[simp] theorem PropSet.mem_toList (id : PropId) (set : PropSet) :
    id ∈ set.toList ↔ id ∈ set := Finset.mem_sort _

theorem PropSet.toList_injective : Function.Injective PropSet.toList := by
  intro left right equal
  ext id
  have membership : id ∈ left.toList ↔ id ∈ right.toList := by rw [equal]
  simpa only [PropSet.mem_toList] using membership

/-- Canonical merge used by every binary theorem rule. -/
def PropSet.merge (left right : PropSet) : PropSet := left ∪ right

@[simp] theorem PropSet.mem_merge (id : PropId) (left right : PropSet) :
    id ∈ left.merge right ↔ id ∈ left ∨ id ∈ right := by simp [PropSet.merge]

theorem PropSet.merge_comm (left right : PropSet) : left.merge right = right.merge left := by
  simp [PropSet.merge, Finset.union_comm]

theorem PropSet.merge_assoc (first second third : PropSet) :
    (first.merge second).merge third = first.merge (second.merge third) := by
  simp [PropSet.merge, Finset.union_assoc]

@[simp] theorem PropSet.merge_self (set : PropSet) : set.merge set = set := by
  simp [PropSet.merge]

theorem PropSet.merge_wire_unique {left right merged : PropSet}
    (equal : merged = left.merge right) :
    merged.toList = (left.merge right).toList := congrArg PropSet.toList equal

/-! ## Direct theorem storage

`CanonicalArray` is the proof-level counterpart of `SmallVec<[PropId; 2]>`:
the inline capacity is operationally irrelevant, while sortedness and absence
of duplicates are semantic representation invariants.
-/

structure CanonicalArray where
  values : List PropId
  sorted : values.SortedLT
  nodup : values.Nodup

def CanonicalArray.asSet (array : CanonicalArray) : PropSet := array.values.toFinset

@[simp] theorem CanonicalArray.mem_asSet (id : PropId) (array : CanonicalArray) :
    id ∈ array.asSet ↔ id ∈ array.values := by simp [CanonicalArray.asSet]

/-- A Rust `Thm`: both canonical sides are owned directly by the row. -/
structure Thm where
  premises : CanonicalArray
  conclusions : CanonicalArray

/-- Ephemeral one-based theorem handle, exactly bounded like Rust's
`NonZeroU64`; its vector position may be reused. -/
def ThmId := { value : UInt64 // value ≠ 0 }

deriving instance DecidableEq for ThmId

namespace ThmId

def ofUInt64? (value : UInt64) : Option ThmId :=
  if nonzero : value ≠ 0 then some ⟨value, nonzero⟩ else none

def position (id : ThmId) : Nat := id.val.toNat - 1

theorem position_injective : Function.Injective position := by
  intro left right equal
  apply Subtype.ext
  apply UInt64.toNat_inj.mp
  have leftPositive : 0 < left.val.toNat := by
    apply Nat.pos_of_ne_zero
    intro zero
    apply left.property
    exact UInt64.toNat_inj.mp (by simpa using zero)
  have rightPositive : 0 < right.val.toNat := by
    apply Nat.pos_of_ne_zero
    intro zero
    apply right.property
    exact UInt64.toNat_inj.mp (by simpa using zero)
  simp only [position] at equal
  omega

end ThmId

/-- The actual storage shape: theorem vector, parallel live bitmap, and a
free-list of reusable one-based handles. -/
structure ThmStore where
  thms : List Thm
  live : List Bool
  free : List ThmId

def ThmStore.lookup (store : ThmStore) (id : ThmId) : Option Thm :=
  let position := id.position
  match store.thms[position]?, store.live[position]? with
  | some fact, some true => some fact
  | _, _ => none

def ThmStore.WellFormed (store : ThmStore) : Prop :=
  store.thms.length = store.live.length ∧
    store.free.Nodup ∧ ∀ id ∈ store.free,
      id.position < store.thms.length ∧ store.lookup id = none

/-- Concrete Rust-style deletion of one checked handle. The free list is
represented top-first, corresponding to `Vec::push` followed by `Vec::pop`. -/
def ThmStore.delete? (store : ThmStore) (id : ThmId) : Option ThmStore :=
  if store.lookup id |>.isSome then
    some { store with live := store.live.set id.position false, free := id :: store.free }
  else none

/-- Concrete reuse of the most recently freed slot. This is the occupied-slot
branch of Rust `push_thm`; fresh append is orthogonal to reuse soundness. -/
def ThmStore.reuse? (store : ThmStore) (replacement : Thm) : Option (ThmId × ThmStore) :=
  match store.free with
  | [] => none
  | id :: rest =>
      if id.position < store.thms.length ∧ id.position < store.live.length then
        some (id, {
          store with
          thms := store.thms.set id.position replacement
          live := store.live.set id.position true
          free := rest })
      else none

/-- Transactional in-place mutation used only by production `weaken`,
`not_left`, and `not_right`. A missing/dead handle leaves no successor state;
the checked canonical replacement is committed atomically. -/
def ThmStore.mutate? (store : ThmStore) (id : ThmId) (replacement : Thm) : Option ThmStore :=
  if store.lookup id |>.isSome then
    some { store with thms := store.thms.set id.position replacement }
  else none

/-- Persistent theorem copy into a removed slot. The fresh-append allocation
case has the same logical contract and differs only in vector growth. -/
def ThmStore.copyReuse? (store : ThmStore) (source : ThmId) : Option (ThmId × ThmStore) :=
  store.lookup source |>.bind store.reuse?

/-- Concrete bounded fresh-append allocation used when the free list is empty. -/
def ThmStore.append? (store : ThmStore) (replacement : Thm) : Option (ThmId × ThmStore) := do
  if !store.free.isEmpty then none else pure ()
  let id ← ThmId.ofUInt64? (UInt64.ofNat (store.thms.length + 1))
  if id.position = store.thms.length then
    some (id, { store with
      thms := store.thms ++ [replacement]
      live := store.live ++ [true] })
  else none

def ThmStore.copyFresh? (store : ThmStore) (source : ThmId) : Option (ThmId × ThmStore) :=
  store.lookup source |>.bind store.append?

/-- Single-theorem removal with the public Boolean result. -/
def ThmStore.removeTheorem (store : ThmStore) (id : ThmId) : Bool × ThmStore :=
  match store.delete? id with
  | some after => (true, after)
  | none => (false, store)

/-- A compact theorem row: `prem |- conc`. -/
structure Sequent where
  prem : PropSet
  conc : PropSet
  deriving DecidableEq

/-- A valuation assigns truth to the underlying (unsigned) Boolean term refs. -/
abbrev Valuation := Nat → Prop

/-- Interpret the intentionally inverted signed representation. -/
def PropId.eval (valuation : Valuation) (id : PropId) : Prop :=
  if id.val < 0 then valuation id.ref else ¬valuation id.ref

@[simp] theorem PropId.eval_positive (valuation : Valuation) (reference : OneBased.Ref) :
    (PropId.positive reference).eval valuation ↔ valuation reference.val.toNat := by
  have positive : 0 < reference.val.toNat := by
    apply Nat.pos_of_ne_zero
    intro zero
    apply reference.property.1
    exact UInt64.toNat_inj.mp (by simpa using zero)
  simp [PropId.eval, PropId.positive, PropId.ref, positive]

@[simp] theorem PropId.eval_neg (valuation : Valuation) (id : PropId) :
    id.neg.eval valuation ↔ ¬id.eval valuation := by
  by_cases negative : id.val < 0
  · have notNegative : ¬ id.neg.val < 0 := by simp [PropId.neg]; omega
    simp only [PropId.eval]
    have sameRef : id.neg.ref = id.ref := by simp [PropId.ref, PropId.neg]
    rw [if_neg notNegative, if_pos negative, sameRef]
  · have idPositive : 0 < id.val := by
      exact lt_of_le_of_ne (Int.le_of_not_gt negative) (Ne.symm id.property.1)
    have negNegative : id.neg.val < 0 := by simp [PropId.neg]; omega
    simp only [PropId.eval]
    have sameRef : id.neg.ref = id.ref := by simp [PropId.ref, PropId.neg]
    rw [if_pos negNegative, if_neg negative, sameRef]
    exact Classical.not_not.symm

/-- Classical validity of the compact sequent. -/
def Holds (valuation : Valuation) (sequent : Sequent) : Prop :=
  (∀ id ∈ sequent.prem, id.eval valuation) → ∃ id ∈ sequent.conc, id.eval valuation

/-- Kernel soundness of one sequent. -/
def Sound (sequent : Sequent) : Prop := ∀ valuation, Holds valuation sequent

/-- Soundness relative to the valuations admitted by a checked arena. -/
def SoundUnder (admissible : Valuation → Prop) (sequent : Sequent) : Prop :=
  ∀ valuation, admissible valuation → Holds valuation sequent

theorem soundUnder_of_sound {admissible : Valuation → Prop} {sequent : Sequent}
    (sound : Sound sequent) : SoundUnder admissible sequent := by
  intro valuation _allowed
  exact sound valuation

def Thm.sequent (fact : Thm) : Sequent :=
  ⟨fact.premises.asSet, fact.conclusions.asSet⟩

def Thm.Sound (fact : Thm) : Prop :=
  Nucleus.Hol.Ethane.ClassicalSequent.Sound fact.sequent

def Thm.SoundUnder (admissible : Valuation → Prop) (fact : Thm) : Prop :=
  Nucleus.Hol.Ethane.ClassicalSequent.SoundUnder admissible fact.sequent

/-- Every row currently selected by the bitmap is true. Dead vector contents
and free-list order carry no logical meaning. -/
def ThmStore.LiveSoundUnder (admissible : Valuation → Prop) (store : ThmStore) : Prop :=
  ∀ id fact, store.lookup id = some fact → fact.SoundUnder admissible

def ThmStore.LiveSound (store : ThmStore) : Prop :=
  store.LiveSoundUnder (fun _valuation => True)

/-- Deletion preserves truth because it can only make prior lookups absent. -/
theorem deletion_preserves_live_sound {admissible : Valuation → Prop}
    {before after : ThmStore}
    (sound : before.LiveSoundUnder admissible)
    (onlyRemoves : ∀ id fact, after.lookup id = some fact →
      before.lookup id = some fact) :
    after.LiveSoundUnder admissible := by
  intro id fact live
  exact sound id fact (onlyRemoves id fact live)

/-- Reusing a free slot preserves truth when the replacement row is checked
and every other live vector position retains its previous lookup. -/
theorem reuse_preserves_live_sound {admissible : Valuation → Prop}
    {before after : ThmStore} (reused : ThmId)
    (replacement : Thm) (beforeSound : before.LiveSoundUnder admissible)
    (replacementSound : replacement.SoundUnder admissible)
    (inserted : after.lookup reused = some replacement)
    (preserved : ∀ id, id ≠ reused → after.lookup id = before.lookup id) :
    after.LiveSoundUnder admissible := by
  intro id fact live
  by_cases same : id = reused
  · subst id
    have equal : replacement = fact := Option.some.inj (inserted.symm.trans live)
    subst fact
    exact replacementSound
  · exact beforeSound id fact ((preserved id same).symm.trans live)

set_option maxRecDepth 2000 in
/-- The concrete bitmap/free-list deletion cannot create a new live lookup. -/
theorem delete?_only_removes {before after : ThmStore} {deleted : ThmId}
    (result : before.delete? deleted = some after) :
    ∀ id fact, after.lookup id = some fact → before.lookup id = some fact := by
  intro id fact live
  simp only [ThmStore.delete?] at result
  split at result
  next present =>
    simp only [Option.some.injEq] at result
    subst after
    simp only [ThmStore.lookup] at live ⊢
    by_cases same : id.position = deleted.position
    · rw [List.getElem?_set] at live
      simp only [same, ↓reduceIte] at live
      split at live <;> simp_all
    · rw [List.getElem?_set] at live
      simp only [Ne.symm same, ↓reduceIte] at live
      exact live
  next absent => contradiction

/-- Concrete checked deletion preserves every live theorem's truth. -/
theorem delete?_preserves_live_sound {admissible : Valuation → Prop}
    {before after : ThmStore} {deleted : ThmId}
    (sound : before.LiveSoundUnder admissible)
    (result : before.delete? deleted = some after) :
    after.LiveSoundUnder admissible :=
  deletion_preserves_live_sound sound (delete?_only_removes result)

/-- Concrete LIFO free-slot reuse preserves every live theorem's truth. -/
theorem reuse?_preserves_live_sound {admissible : Valuation → Prop}
    {before after : ThmStore} {reused : ThmId}
    {replacement : Thm} (beforeSound : before.LiveSoundUnder admissible)
    (replacementSound : replacement.SoundUnder admissible)
    (result : before.reuse? replacement = some (reused, after)) :
    after.LiveSoundUnder admissible := by
  simp only [ThmStore.reuse?] at result
  split at result
  next => contradiction
  next top rest equalFree =>
    split at result
    next inBounds =>
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      intro id fact live
      simp only [ThmStore.lookup] at live ⊢
      by_cases samePosition : id.position = top.position
      · have same : id = top := ThmId.position_injective samePosition
        subst id
        rw [List.getElem?_set, List.getElem?_set] at live
        simp only [↓reduceIte, inBounds.1, inBounds.2, Option.some.injEq] at live
        subst fact
        exact replacementSound
      · rw [List.getElem?_set, List.getElem?_set] at live
        simp only [Ne.symm samePosition, ↓reduceIte] at live
        exact beforeSound id fact live
    next => contradiction

/-- A successful transactional in-place rule preserves every live theorem.
This single storage theorem applies to `weaken`, `not_left`, and `not_right`;
their calculus theorems supply `replacementSound`. -/
theorem mutate?_preserves_live_sound {admissible : Valuation → Prop}
    {before after : ThmStore} {id : ThmId} {replacement : Thm}
    (beforeSound : before.LiveSoundUnder admissible)
    (replacementSound : replacement.SoundUnder admissible)
    (result : before.mutate? id replacement = some after) :
    after.LiveSoundUnder admissible := by
  simp only [ThmStore.mutate?] at result
  split at result
  next liveTarget =>
    simp only [Option.some.injEq] at result
    subst after
    intro queried fact live
    simp only [ThmStore.lookup] at live ⊢
    by_cases samePosition : queried.position = id.position
    · have same : queried = id := ThmId.position_injective samePosition
      subst queried
      rw [List.getElem?_set] at live
      simp only [↓reduceIte] at live
      have inBounds : id.position < before.thms.length := by
        by_contra outOfBounds
        simp [outOfBounds] at live
      simp only [inBounds] at live
      split at live <;> simp_all
    · rw [List.getElem?_set] at live
      simp only [Ne.symm samePosition, ↓reduceIte] at live
      exact beforeSound queried fact live
  next => contradiction

/-- Copying a live theorem into the next reusable slot preserves all live
truth, while retaining the source handle for persistent consumers. -/
theorem copyReuse?_preserves_live_sound {admissible : Valuation → Prop}
    {before after : ThmStore} {source copied : ThmId}
    (beforeSound : before.LiveSoundUnder admissible)
    (result : before.copyReuse? source = some (copied, after)) :
    after.LiveSoundUnder admissible := by
  unfold ThmStore.copyReuse? at result
  cases found : before.lookup source with
  | none => simp [found] at result
  | some fact =>
      simp only [found, Option.bind_some] at result
      exact reuse?_preserves_live_sound beforeSound (beforeSound source fact found) result

theorem copyReuse?_distinct_and_preserves_source {before after : ThmStore}
    {source copied : ThmId} {fact : Thm} (wellFormed : before.WellFormed)
    (found : before.lookup source = some fact)
    (result : before.copyReuse? source = some (copied, after)) :
    copied ≠ source ∧ after.lookup source = some fact := by
  rcases wellFormed with ⟨_lengths, freeNodup, freeDead⟩
  unfold ThmStore.copyReuse? at result
  simp only [found, Option.bind_some] at result
  unfold ThmStore.reuse? at result
  cases freeShape : before.free with
  | nil => simp [freeShape] at result
  | cons top rest =>
      simp only [freeShape] at result
      split at result
      next inBounds =>
        simp only [Option.some.injEq, Prod.mk.injEq] at result
        rcases result with ⟨rfl, rfl⟩
        have different : top ≠ source := by
          intro equal
          subst top
          have dead := (freeDead source (by simp [freeShape])).2
          rw [found] at dead
          contradiction
        constructor
        · exact different
        · simp only [ThmStore.lookup]
          have positions : source.position ≠ top.position := by
            intro equal
            exact different (ThmId.position_injective equal.symm)
          rw [List.getElem?_set, List.getElem?_set]
          simp only [Ne.symm positions, ↓reduceIte]
          simpa only [ThmStore.lookup] using found
      next => contradiction

theorem copyReuse?_preserves_wellFormed {before after : ThmStore}
    {source copied : ThmId} (wellFormed : before.WellFormed)
    (result : before.copyReuse? source = some (copied, after)) : after.WellFormed := by
  rcases wellFormed with ⟨lengths, freeNodup, freeDead⟩
  unfold ThmStore.copyReuse? at result
  cases found : before.lookup source with
  | none => simp [found] at result
  | some fact =>
      simp only [found, Option.bind_some] at result
      unfold ThmStore.reuse? at result
      cases freeShape : before.free with
      | nil => simp [freeShape] at result
      | cons top rest =>
          simp only [freeShape] at result
          split at result
          next inBounds =>
            simp only [Option.some.injEq, Prod.mk.injEq] at result
            rcases result with ⟨rfl, rfl⟩
            constructor
            · simpa using lengths
            constructor
            · simpa [freeShape] using freeNodup.tail
            · intro id member
              have old := freeDead id (by simp [freeShape, member])
              constructor
              · simpa using old.1
              · simp only [ThmStore.lookup]
                have different : id ≠ top := by
                  intro equal
                  subst id
                  have := freeNodup
                  simp [freeShape, member] at this
                have positions : id.position ≠ top.position := fun equal =>
                  different (ThmId.position_injective equal)
                rw [List.getElem?_set, List.getElem?_set]
                simp only [Ne.symm positions, ↓reduceIte]
                simpa only [ThmStore.lookup] using old.2
          next => contradiction

theorem freshAppend_distinct_and_preserves_source {before : ThmStore}
    {source copied : ThmId} {fact : Thm} (found : before.lookup source = some fact)
    (freshPosition : copied.position = before.thms.length) :
    copied ≠ source ∧
      ({ before with thms := before.thms ++ [fact], live := before.live ++ [true] }).lookup source =
        some fact := by
  have sourceBound : source.position < before.thms.length := by
    by_contra outOfBounds
    simp [ThmStore.lookup, outOfBounds] at found
  have sourceLiveBound : source.position < before.live.length := by
    by_contra outOfBounds
    simp [ThmStore.lookup, outOfBounds] at found
  constructor
  · intro equal
    have positions := congrArg ThmId.position equal
    omega
  · simpa [ThmStore.lookup, List.getElem?_append, sourceBound, sourceLiveBound] using found

theorem freshAppend_preserves_wellFormed {before : ThmStore} {fact : Thm}
    (wellFormed : before.WellFormed) (freeEmpty : before.free = []) :
    ({ before with thms := before.thms ++ [fact], live := before.live ++ [true] }).WellFormed := by
  rcases wellFormed with ⟨lengths, _freeNodup, _freeDead⟩
  constructor
  · simp [lengths]
  · simp [freeEmpty]

theorem freshAppend_preserves_live_sound {admissible : Valuation → Prop}
    {before : ThmStore} {fact : Thm} (lengths : before.thms.length = before.live.length)
    (beforeSound : before.LiveSoundUnder admissible) (factSound : fact.SoundUnder admissible) :
    ({ before with thms := before.thms ++ [fact], live := before.live ++ [true] }).LiveSoundUnder
      admissible := by
  intro id row live
  simp only [ThmStore.lookup] at live
  by_cases old : id.position < before.thms.length
  · have oldLive : id.position < before.live.length := by omega
    simpa [List.getElem?_append, old, oldLive] using beforeSound id row (by
      simpa [ThmStore.lookup, List.getElem?_append, old, oldLive] using live)
  · have position : id.position = before.thms.length := by
      by_contra different
      have beyond : before.thms.length + 1 ≤ id.position := by omega
      have rowMissing : (before.thms ++ [fact])[id.position]? = none := by
        rw [List.getElem?_eq_none]
        simp
        omega
      simp [rowMissing] at live
    simp [position, lengths] at live
    simpa [live] using factSound

theorem identity {admissible : Valuation → Prop} (id : PropId) :
    SoundUnder admissible ⟨{id}, {id}⟩ := by
  intro valuation _allowed premises
  exact ⟨id, by simp, premises id (by simp)⟩

theorem weaken {admissible : Valuation → Prop} {source target : Sequent}
    (sound : SoundUnder admissible source)
    (prem : source.prem ⊆ target.prem) (conc : source.conc ⊆ target.conc) :
    SoundUnder admissible target := by
  intro valuation allowed targetPremises
  obtain ⟨id, member, truth⟩ := sound valuation allowed fun id member =>
    targetPremises id (prem member)
  exact ⟨id, conc member, truth⟩

/-- Gentzen cut: remove the same signed proposition from the left conclusion
and the right premise. -/
theorem cut {admissible : Valuation → Prop} (pivot : PropId) {left right : Sequent}
    (leftSound : SoundUnder admissible left) (rightSound : SoundUnder admissible right)
    (_leftPivot : pivot ∈ left.conc) (_rightPivot : pivot ∈ right.prem) :
    SoundUnder admissible ⟨left.prem ∪ right.prem.erase pivot,
      left.conc.erase pivot ∪ right.conc⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := leftSound valuation allowed fun id member =>
    premises id (by simp [member])
  by_cases same : id = pivot
  · subst id
    obtain ⟨rightId, rightMember, rightTruth⟩ := rightSound valuation allowed (by
      intro id member
      by_cases pivotMember : id = pivot
      · subst id
        exact truth
      · exact premises id (by simp [member, pivotMember]))
    exact ⟨rightId, by simp [rightMember], rightTruth⟩
  · exact ⟨id, by simp [member, same], truth⟩

/-- Cut/resolution on complementary signed references. -/
theorem resolution {admissible : Valuation → Prop} (pivot : PropId) {left right : Sequent}
    (leftSound : SoundUnder admissible left) (rightSound : SoundUnder admissible right)
    (_leftPivot : pivot ∈ left.conc) (_rightPivot : pivot.neg ∈ right.conc) :
    SoundUnder admissible ⟨left.prem ∪ right.prem,
      left.conc.erase pivot ∪ right.conc.erase pivot.neg⟩ := by
  intro valuation allowed premises
  by_cases pivotTrue : pivot.eval valuation
  · obtain ⟨id, member, truth⟩ := rightSound valuation allowed (by
      intro id member
      exact premises id (by simp [member]))
    by_cases same : id = pivot.neg
    · subst id
      exact ((PropId.eval_neg valuation pivot).mp truth pivotTrue).elim
    · exact ⟨id, by simp [member, same], truth⟩
  · obtain ⟨id, member, truth⟩ := leftSound valuation allowed (by
      intro id member
      exact premises id (by simp [member]))
    by_cases same : id = pivot
    · subst id
      exact (pivotTrue truth).elim
    · exact ⟨id, by simp [member, same], truth⟩

/-! The following equations are precisely what opcode lowering must establish
for a parent row and its operand rows.  They mention the registry's actual
`Op1` and `Op2` types rather than duplicating an opcode vocabulary. -/

/-- A valuation of local Boolean term references that respects the actual
checked expressions resolved from a production OneBased arena. This is the
semantic invariant maintained by opcode lowering, stated at the exact rows
queried by Rust `signed_bool_value` and `require_binary`. -/
structure ArenaValuation (arena : OneBased.Arena) (valuation : Valuation) : Prop where
  boolRow : ∀ reference value,
    (arena.row? reference).map (·.expr) = some (.bool value) →
      (valuation reference.val.toNat ↔ value = true)
  op1Row : ∀ parent op operand,
    (arena.row? parent).map (·.expr) = some (.op1 op operand) →
      (valuation parent.val.toNat ↔ match op with
        | .not => ¬valuation operand.val.toNat)
  op2Row : ∀ parent op left right,
    (arena.row? parent).map (·.expr) = some (.op2 op left right) →
      (valuation parent.val.toNat ↔ match op with
        | .and => valuation left.val.toNat ∧ valuation right.val.toNat
        | .or => valuation left.val.toNat ∨ valuation right.val.toNat
        | .imp => valuation left.val.toNat → valuation right.val.toNat)

def ArenaSound (arena : OneBased.Arena) (sequent : Sequent) : Prop :=
  SoundUnder (ArenaValuation arena) sequent

def Thm.ArenaSound (arena : OneBased.Arena) (fact : Thm) : Prop :=
  fact.SoundUnder (ArenaValuation arena)

def ThmStore.ArenaLiveSound (arena : OneBased.Arena) (store : ThmStore) : Prop :=
  store.LiveSoundUnder (ArenaValuation arena)

/-- Exact row predicate checked for a compact unary opcode. -/
def CheckedOp1 (arena : OneBased.Arena) (parent : OneBased.Ref)
    (op : Builtin.Op1) (operand : OneBased.Ref) : Prop :=
  (arena.row? parent).map (·.expr) = some (.op1 op operand)

/-- Exact row predicate checked for a compact binary opcode. -/
def CheckedOp2 (arena : OneBased.Arena) (parent : OneBased.Ref)
    (op : Builtin.Op2) (left right : OneBased.Ref) : Prop :=
  (arena.row? parent).map (·.expr) = some (.op2 op left right)

/-- Exact row predicate checked for an inline Boolean constant. -/
def CheckedBool (arena : OneBased.Arena) (reference : OneBased.Ref) (value : Bool) : Prop :=
  (arena.row? reference).map (·.expr) = some (.bool value)

def Op1Equation (valuation : Valuation) (parent : PropId)
    (op : Builtin.Op1) (operand : PropId) : Prop :=
  parent.eval valuation ↔ match op with | .not => ¬operand.eval valuation

def Op2Equation (valuation : Valuation) (parent : PropId)
    (op : Builtin.Op2) (left right : PropId) : Prop :=
  parent.eval valuation ↔ match op with
    | .and => left.eval valuation ∧ right.eval valuation
    | .or => left.eval valuation ∨ right.eval valuation
    | .imp => left.eval valuation → right.eval valuation

/-- Semantic bridge for a checked `tm.bool false` row. -/
def FalseEquation (valuation : Valuation) (falsehood : PropId) : Prop :=
  ¬falsehood.eval valuation

/-- Semantic bridge for a checked `tm.bool true` row. -/
def TrueEquation (valuation : Valuation) (truth : PropId) : Prop :=
  truth.eval valuation

theorem checkedOp1_equation {arena : OneBased.Arena} {valuation : Valuation}
    (respects : ArenaValuation arena valuation) {parent operand : OneBased.Ref}
    {op : Builtin.Op1} (checked : CheckedOp1 arena parent op operand) :
    Op1Equation valuation (PropId.positive parent) op (PropId.positive operand) := by
  simpa [Op1Equation] using respects.op1Row parent op operand checked

theorem checkedOp2_equation {arena : OneBased.Arena} {valuation : Valuation}
    (respects : ArenaValuation arena valuation) {parent left right : OneBased.Ref}
    {op : Builtin.Op2} (checked : CheckedOp2 arena parent op left right) :
    Op2Equation valuation (PropId.positive parent) op
      (PropId.positive left) (PropId.positive right) := by
  simpa [Op2Equation] using
    respects.op2Row parent op left right checked

theorem checkedFalse_equation {arena : OneBased.Arena} {valuation : Valuation}
    (respects : ArenaValuation arena valuation) {reference : OneBased.Ref}
    (checked : CheckedBool arena reference false) :
    FalseEquation valuation (PropId.positive reference) := by
  have meaning := respects.boolRow reference false checked
  simpa [FalseEquation] using meaning

theorem checkedTrue_equation {arena : OneBased.Arena} {valuation : Valuation}
    (respects : ArenaValuation arena valuation) {reference : OneBased.Ref}
    (checked : CheckedBool arena reference true) :
    TrueEquation valuation (PropId.positive reference) := by
  have meaning := respects.boolRow reference true checked
  simpa [TrueEquation] using meaning

theorem falseLeft {admissible : Valuation → Prop} (falsehood : PropId)
    (equation : ∀ valuation, admissible valuation → FalseEquation valuation falsehood) :
    SoundUnder admissible ⟨{falsehood}, ∅⟩ := by
  intro valuation allowed premises
  exact (equation valuation allowed (premises falsehood (by simp))).elim

theorem trueRight {admissible : Valuation → Prop} (truth : PropId)
    (equation : ∀ valuation, admissible valuation → TrueEquation valuation truth) :
    SoundUnder admissible ⟨∅, {truth}⟩ := by
  intro valuation allowed _
  exact ⟨truth, by simp, equation valuation allowed⟩

/-! ## Exact checked Gentzen rule correspondence

| Rust kernel method | Lean soundness theorem |
| --- | --- |
| `identity` | `identity` |
| `weaken` | `weaken` |
| `cut` | `cut` |
| `resolve` | `resolution` |
| `false_left` / `true_right` | `checkedFalseLeft` / `checkedTrueRight` |
| `not_left` / `not_right` | `polarityLeft` / `polarityRight` |
| `and_left` / `and_right` | `checkedAndLeft` / `checkedAndRight` |
| `or_left` / `or_right` | `checkedOrLeft` / `checkedOrRight` |
| `imp_left` / `imp_right` | `checkedImpLeft` / `checkedImpRight` |
| `expand_conclusion` | `checked*Conclusion*` normalized signed bridges |
| `flatten_conclusion` / `fold_conclusion` | `flattenConclusion` / `foldConclusion` |
| `flatten_premise` / `fold_premise` | `flattenPremise` / `foldPremise` |

`polarityLeft` and `polarityRight` are the signed turnstile-transfer rules in
the Rust API.  They are intentionally distinct from `opcodeNotLeft` and
`opcodeNotRight`, which introduce a compact `tm.not` parent after its checked
row has established the corresponding semantic equation. Binary rules
deliberately allow different contexts and merge them by canonical set union,
matching the Rust API.
-/

/-- Rust `Kernel::not_left`: move an arbitrary signed conclusion across the
turnstile, complementing its `PropId` polarity. -/
theorem polarityLeft {admissible : Valuation → Prop} {proposition : PropId}
    {prem conc : PropSet} (source : SoundUnder admissible ⟨prem, insert proposition conc⟩) :
    SoundUnder admissible ⟨insert proposition.neg prem, conc⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := source valuation allowed fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · have complement := premises id.neg (by simp)
    exact ((PropId.eval_neg valuation id).mp complement truth).elim
  · exact ⟨id, member, truth⟩

/-- Rust `Kernel::not_right`: move an arbitrary signed premise across the
turnstile, complementing its `PropId` polarity. -/
theorem polarityRight {admissible : Valuation → Prop} {proposition : PropId}
    {prem conc : PropSet} (source : SoundUnder admissible ⟨insert proposition prem, conc⟩) :
    SoundUnder admissible ⟨prem, insert proposition.neg conc⟩ := by
  intro valuation allowed premises
  by_cases truth : proposition.eval valuation
  · obtain ⟨id, member, valid⟩ := source valuation allowed (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact truth
      · exact premises id member)
    exact ⟨id, by simp [member], valid⟩
  · exact ⟨proposition.neg, by simp, (PropId.eval_neg valuation proposition).mpr truth⟩

/-- Introduce a checked compact `tm.not` parent on the left. This is not the
signed-polarity transfer performed by Rust `Kernel::not_left`. -/
theorem opcodeNotLeft {admissible : Valuation → Prop} {parent operand : PropId}
    {prem conc : PropSet}
    (source : SoundUnder admissible ⟨prem, insert operand conc⟩)
    (equation : ∀ valuation, admissible valuation → Op1Equation valuation parent .not operand) :
    SoundUnder admissible ⟨insert parent prem, conc⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := source valuation allowed fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · exact ((equation valuation allowed).mp (premises parent (by simp)) truth).elim
  · exact ⟨id, member, truth⟩

/-- Introduce a checked compact `tm.not` parent on the right. This is not the
signed-polarity transfer performed by Rust `Kernel::not_right`. -/
theorem opcodeNotRight {admissible : Valuation → Prop} {parent operand : PropId}
    {prem conc : PropSet}
    (source : SoundUnder admissible ⟨insert operand prem, conc⟩)
    (equation : ∀ valuation, admissible valuation → Op1Equation valuation parent .not operand) :
    SoundUnder admissible ⟨prem, insert parent conc⟩ := by
  intro valuation allowed premises
  by_cases operandTruth : operand.eval valuation
  · obtain ⟨id, member, truth⟩ := source valuation allowed (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact operandTruth
      · exact premises id member)
    exact ⟨id, by simp [member], truth⟩
  · exact ⟨parent, by simp, (equation valuation allowed).mpr operandTruth⟩

theorem andLeft {admissible : Valuation → Prop} {parent left right : PropId} {prem conc : PropSet}
    (source : SoundUnder admissible ⟨insert left (insert right prem), conc⟩)
    (equation : ∀ valuation, admissible valuation → Op2Equation valuation parent .and left right) :
    SoundUnder admissible ⟨insert parent prem, conc⟩ := by
  intro valuation allowed premises
  apply source valuation allowed
  intro id member
  simp only [Finset.mem_insert] at member
  rcases member with rfl | rfl | member
  · exact ((equation valuation allowed).mp (premises parent (by simp))).1
  · exact ((equation valuation allowed).mp (premises parent (by simp))).2
  · exact premises id (by simp [member])

theorem andRight {admissible : Valuation → Prop} {parent left right : PropId}
    {leftPrem leftConc rightPrem rightConc : PropSet}
    (leftSource : SoundUnder admissible ⟨leftPrem, insert left leftConc⟩)
    (rightSource : SoundUnder admissible ⟨rightPrem, insert right rightConc⟩)
    (equation : ∀ valuation, admissible valuation → Op2Equation valuation parent .and left right) :
    SoundUnder admissible ⟨leftPrem ∪ rightPrem, insert parent (leftConc ∪ rightConc)⟩ := by
  intro valuation allowed premises
  obtain ⟨leftId, leftMember, leftTruth⟩ := leftSource valuation allowed fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at leftMember
  rcases leftMember with rfl | leftMember
  · obtain ⟨rightId, rightMember, rightTruth⟩ := rightSource valuation allowed fun id member =>
      premises id (by simp [member])
    simp only [Finset.mem_insert] at rightMember
    rcases rightMember with rfl | rightMember
    · exact ⟨parent, by simp, (equation valuation allowed).mpr ⟨leftTruth, rightTruth⟩⟩
    · exact ⟨rightId, by simp [rightMember], rightTruth⟩
  · exact ⟨leftId, by simp [leftMember], leftTruth⟩

theorem orLeft {admissible : Valuation → Prop} {parent left right : PropId}
    {leftPrem leftConc rightPrem rightConc : PropSet}
    (leftSource : SoundUnder admissible ⟨insert left leftPrem, leftConc⟩)
    (rightSource : SoundUnder admissible ⟨insert right rightPrem, rightConc⟩)
    (equation : ∀ valuation, admissible valuation → Op2Equation valuation parent .or left right) :
    SoundUnder admissible ⟨insert parent (leftPrem ∪ rightPrem), leftConc ∪ rightConc⟩ := by
  intro valuation allowed premises
  rcases (equation valuation allowed).mp (premises parent (by simp)) with leftTruth | rightTruth
  · obtain ⟨id, member, truth⟩ := leftSource valuation allowed (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact leftTruth
      · exact premises id (by simp [member]))
    exact ⟨id, by simp [member], truth⟩
  · obtain ⟨id, member, truth⟩ := rightSource valuation allowed (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact rightTruth
      · exact premises id (by simp [member]))
    exact ⟨id, by simp [member], truth⟩

theorem orRight {admissible : Valuation → Prop} {parent left right : PropId} {prem conc : PropSet}
    (source : SoundUnder admissible ⟨prem, insert left (insert right conc)⟩)
    (equation : ∀ valuation, admissible valuation → Op2Equation valuation parent .or left right) :
    SoundUnder admissible ⟨prem, insert parent conc⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := source valuation allowed premises
  simp only [Finset.mem_insert] at member
  rcases member with rfl | rfl | member
  · exact ⟨parent, by simp, (equation valuation allowed).mpr (Or.inl truth)⟩
  · exact ⟨parent, by simp, (equation valuation allowed).mpr (Or.inr truth)⟩
  · exact ⟨id, by simp [member], truth⟩

theorem impLeft {admissible : Valuation → Prop} {parent left right : PropId}
    {leftPrem leftConc rightPrem rightConc : PropSet}
    (leftSource : SoundUnder admissible ⟨leftPrem, insert left leftConc⟩)
    (rightSource : SoundUnder admissible ⟨insert right rightPrem, rightConc⟩)
    (equation : ∀ valuation, admissible valuation → Op2Equation valuation parent .imp left right) :
    SoundUnder admissible ⟨insert parent (leftPrem ∪ rightPrem), leftConc ∪ rightConc⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := leftSource valuation allowed fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · have rightTruth := (equation valuation allowed).mp (premises parent (by simp)) truth
    obtain ⟨id, member, valid⟩ := rightSource valuation allowed (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact rightTruth
      · exact premises id (by simp [member]))
    exact ⟨id, by simp [member], valid⟩
  · exact ⟨id, by simp [member], truth⟩

theorem impRight {admissible : Valuation → Prop} {parent left right : PropId} {prem conc : PropSet}
    (source : SoundUnder admissible ⟨insert left prem, insert right conc⟩)
    (equation : ∀ valuation, admissible valuation → Op2Equation valuation parent .imp left right) :
    SoundUnder admissible ⟨prem, insert parent conc⟩ := by
  intro valuation allowed premises
  by_cases leftTruth : left.eval valuation
  · obtain ⟨id, member, truth⟩ := source valuation allowed (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact leftTruth
      · exact premises id member)
    simp only [Finset.mem_insert] at member
    rcases member with rfl | member
    · exact ⟨parent, by simp, (equation valuation allowed).mpr fun _ => truth⟩
    · exact ⟨id, by simp [member], truth⟩
  · exact ⟨parent, by simp, (equation valuation allowed).mpr fun truth => (leftTruth truth).elim⟩

/-! End-to-end wrappers: an exact checked OneBased row supplies the semantic
equation under every arena-admissible valuation. No universal equation over
arbitrary, row-incoherent valuations is assumed. -/

theorem checkedFalseLeft {arena : OneBased.Arena} {reference : OneBased.Ref}
    (checked : CheckedBool arena reference false) :
    ArenaSound arena ⟨{PropId.positive reference}, ∅⟩ :=
  falseLeft _ (fun _valuation respects => checkedFalse_equation respects checked)

theorem checkedTrueRight {arena : OneBased.Arena} {reference : OneBased.Ref}
    (checked : CheckedBool arena reference true) :
    ArenaSound arena ⟨∅, {PropId.positive reference}⟩ :=
  trueRight _ (fun _valuation respects => checkedTrue_equation respects checked)

/-- Rust also recognizes the complemented encoding of false: `¬true`. -/
theorem checkedNegatedTrueFalseLeft {arena : OneBased.Arena} {reference : OneBased.Ref}
    (checked : CheckedBool arena reference true) :
    ArenaSound arena ⟨{(PropId.positive reference).neg}, ∅⟩ :=
  falseLeft _ (fun valuation respects => by
    intro negatedTrue
    exact (PropId.eval_neg valuation (PropId.positive reference)).mp negatedTrue
      (checkedTrue_equation respects checked))

/-- Rust also recognizes the complemented encoding of true: `¬false`. -/
theorem checkedNegatedFalseTrueRight {arena : OneBased.Arena} {reference : OneBased.Ref}
    (checked : CheckedBool arena reference false) :
    ArenaSound arena ⟨∅, {(PropId.positive reference).neg}⟩ :=
  trueRight _ (fun valuation respects =>
    (PropId.eval_neg valuation (PropId.positive reference)).mpr
      (checkedFalse_equation respects checked))

theorem checkedAndLeft {arena : OneBased.Arena} {parent left right : OneBased.Ref}
    {prem conc : PropSet}
    (source : ArenaSound arena
      ⟨insert (PropId.positive left) (insert (PropId.positive right) prem), conc⟩)
    (checked : CheckedOp2 arena parent .and left right) :
    ArenaSound arena ⟨insert (PropId.positive parent) prem, conc⟩ :=
  andLeft source (fun _valuation respects => checkedOp2_equation respects checked)

theorem checkedAndRight {arena : OneBased.Arena} {parent left right : OneBased.Ref}
    {leftPrem leftConc rightPrem rightConc : PropSet}
    (leftSource : ArenaSound arena ⟨leftPrem, insert (PropId.positive left) leftConc⟩)
    (rightSource : ArenaSound arena ⟨rightPrem, insert (PropId.positive right) rightConc⟩)
    (checked : CheckedOp2 arena parent .and left right) :
    ArenaSound arena
      ⟨leftPrem ∪ rightPrem, insert (PropId.positive parent) (leftConc ∪ rightConc)⟩ :=
  andRight leftSource rightSource
    (fun _valuation respects => checkedOp2_equation respects checked)

theorem checkedOrLeft {arena : OneBased.Arena} {parent left right : OneBased.Ref}
    {leftPrem leftConc rightPrem rightConc : PropSet}
    (leftSource : ArenaSound arena ⟨insert (PropId.positive left) leftPrem, leftConc⟩)
    (rightSource : ArenaSound arena ⟨insert (PropId.positive right) rightPrem, rightConc⟩)
    (checked : CheckedOp2 arena parent .or left right) :
    ArenaSound arena
      ⟨insert (PropId.positive parent) (leftPrem ∪ rightPrem), leftConc ∪ rightConc⟩ :=
  orLeft leftSource rightSource
    (fun _valuation respects => checkedOp2_equation respects checked)

theorem checkedOrRight {arena : OneBased.Arena} {parent left right : OneBased.Ref}
    {prem conc : PropSet}
    (source : ArenaSound arena
      ⟨prem, insert (PropId.positive left) (insert (PropId.positive right) conc)⟩)
    (checked : CheckedOp2 arena parent .or left right) :
    ArenaSound arena ⟨prem, insert (PropId.positive parent) conc⟩ :=
  orRight source (fun _valuation respects => checkedOp2_equation respects checked)

theorem checkedImpLeft {arena : OneBased.Arena} {parent left right : OneBased.Ref}
    {leftPrem leftConc rightPrem rightConc : PropSet}
    (leftSource : ArenaSound arena ⟨leftPrem, insert (PropId.positive left) leftConc⟩)
    (rightSource : ArenaSound arena ⟨insert (PropId.positive right) rightPrem, rightConc⟩)
    (checked : CheckedOp2 arena parent .imp left right) :
    ArenaSound arena
      ⟨insert (PropId.positive parent) (leftPrem ∪ rightPrem), leftConc ∪ rightConc⟩ :=
  impLeft leftSource rightSource
    (fun _valuation respects => checkedOp2_equation respects checked)

theorem checkedImpRight {arena : OneBased.Arena} {parent left right : OneBased.Ref}
    {prem conc : PropSet}
    (source : ArenaSound arena
      ⟨insert (PropId.positive left) prem, insert (PropId.positive right) conc⟩)
    (checked : CheckedOp2 arena parent .imp left right) :
    ArenaSound arena ⟨prem, insert (PropId.positive parent) conc⟩ :=
  impRight source (fun _valuation respects => checkedOp2_equation respects checked)

/-! ## Exact normalized conclusion expansion

Rust `expand_conclusion` replaces one signed formula by a canonical set of
signed formulas.  The following rule captures that operation directly (all
replacements stay on the right), unlike the ordinary implication sequent rule.
-/

set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

theorem replaceConclusion {admissible : Valuation → Prop} {formula : PropId}
    {prem rest replacements : PropSet}
    (source : SoundUnder admissible ⟨prem, insert formula rest⟩)
    (equation : ∀ valuation, admissible valuation →
      formula.eval valuation → ∃ id ∈ replacements, id.eval valuation) :
    SoundUnder admissible ⟨prem, replacements ∪ rest⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := source valuation allowed premises
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · obtain ⟨replacement, replacementMember, replacementTruth⟩ :=
      equation valuation allowed truth
    exact ⟨replacement, by simp [replacementMember], replacementTruth⟩
  · exact ⟨id, by simp [member], truth⟩

theorem checkedFalseConclusion {arena : OneBased.Arena} {reference : OneBased.Ref}
    {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive reference) rest⟩)
    (checked : CheckedBool arena reference false) : ArenaSound arena ⟨prem, rest⟩ := by
  simpa only [ArenaSound, Finset.empty_union] using
    replaceConclusion (replacements := ∅) source (fun valuation respects => by
    intro truth
    exact (checkedFalse_equation (valuation := valuation) respects checked truth).elim)

theorem checkedNegatedTrueConclusion {arena : OneBased.Arena} {reference : OneBased.Ref}
    {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive reference).neg rest⟩)
    (checked : CheckedBool arena reference true) : ArenaSound arena ⟨prem, rest⟩ := by
  simpa only [ArenaSound, Finset.empty_union] using
    replaceConclusion (replacements := ∅) source (fun valuation respects truth => by
      have negated := (PropId.eval_neg valuation (PropId.positive reference)).mp truth
      exact (negated (checkedTrue_equation respects checked)).elim)

theorem checkedOrConclusion {arena : OneBased.Arena} {parent left right : OneBased.Ref}
    {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent) rest⟩)
    (checked : CheckedOp2 arena parent .or left right) :
    ArenaSound arena ⟨prem, {PropId.positive left, PropId.positive right} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp2_equation (valuation := valuation) respects checked
    simp only [Op2Equation] at equation
    rw [equation]
    simp <;> tauto)

theorem checkedAndConclusionLeft {arena : OneBased.Arena}
    {parent selected other : OneBased.Ref} {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent) rest⟩)
    (checked : CheckedOp2 arena parent .and selected other) :
    ArenaSound arena ⟨prem, {PropId.positive selected} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp2_equation (valuation := valuation) respects checked
    simp only [Op2Equation] at equation
    rw [equation]
    simp <;> tauto)

theorem checkedAndConclusionRight {arena : OneBased.Arena}
    {parent left right : OneBased.Ref} {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent) rest⟩)
    (checked : CheckedOp2 arena parent .and left right) :
    ArenaSound arena ⟨prem, {PropId.positive right} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp2_equation (valuation := valuation) respects checked
    simp only [Op2Equation] at equation
    rw [equation]
    simp <;> tauto)

theorem checkedImpConclusion {arena : OneBased.Arena} {parent left right : OneBased.Ref}
    {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent) rest⟩)
    (checked : CheckedOp2 arena parent .imp left right) :
    ArenaSound arena
      ⟨prem, {(PropId.positive left).neg, PropId.positive right} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp2_equation (valuation := valuation) respects checked
    simp only [Op2Equation] at equation
    rw [equation]
    simp [PropId.eval_neg] <;> tauto)

theorem checkedNotConclusion {arena : OneBased.Arena} {parent operand : OneBased.Ref}
    {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent) rest⟩)
    (checked : CheckedOp1 arena parent .not operand) :
    ArenaSound arena ⟨prem, {(PropId.positive operand).neg} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp1_equation (valuation := valuation) respects checked
    simp only [Op1Equation] at equation
    rw [equation]
    simp [PropId.eval_neg] <;> tauto)

theorem checkedNegatedNotConclusion {arena : OneBased.Arena}
    {parent operand : OneBased.Ref} {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent).neg rest⟩)
    (checked : CheckedOp1 arena parent .not operand) :
    ArenaSound arena ⟨prem, {PropId.positive operand} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp1_equation (valuation := valuation) respects checked
    simp only [Op1Equation] at equation
    rw [PropId.eval_neg, equation]
    simp <;> tauto)

theorem checkedNegatedAndConclusion {arena : OneBased.Arena}
    {parent left right : OneBased.Ref} {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent).neg rest⟩)
    (checked : CheckedOp2 arena parent .and left right) :
    ArenaSound arena
      ⟨prem, {(PropId.positive left).neg, (PropId.positive right).neg} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp2_equation (valuation := valuation) respects checked
    simp only [Op2Equation] at equation
    rw [PropId.eval_neg, equation]
    simp [PropId.eval_neg] <;> tauto)

theorem checkedNegatedOrConclusionLeft {arena : OneBased.Arena}
    {parent selected other : OneBased.Ref} {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent).neg rest⟩)
    (checked : CheckedOp2 arena parent .or selected other) :
    ArenaSound arena ⟨prem, {(PropId.positive selected).neg} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp2_equation (valuation := valuation) respects checked
    simp only [Op2Equation] at equation
    rw [PropId.eval_neg, equation]
    simp [PropId.eval_neg] <;> tauto)

theorem checkedNegatedOrConclusionRight {arena : OneBased.Arena}
    {parent left right : OneBased.Ref} {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent).neg rest⟩)
    (checked : CheckedOp2 arena parent .or left right) :
    ArenaSound arena ⟨prem, {(PropId.positive right).neg} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp2_equation (valuation := valuation) respects checked
    simp only [Op2Equation] at equation
    rw [PropId.eval_neg, equation]
    simp [PropId.eval_neg] <;> tauto)

theorem checkedNegatedImpLeftBranch {arena : OneBased.Arena}
    {parent left right : OneBased.Ref} {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent).neg rest⟩)
    (checked : CheckedOp2 arena parent .imp left right) :
    ArenaSound arena ⟨prem, {PropId.positive left} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp2_equation (valuation := valuation) respects checked
    simp only [Op2Equation] at equation
    rw [PropId.eval_neg, equation]
    simp <;> tauto)

theorem checkedNegatedImpRightBranch {arena : OneBased.Arena}
    {parent left right : OneBased.Ref} {prem rest : PropSet}
    (source : ArenaSound arena ⟨prem, insert (PropId.positive parent).neg rest⟩)
    (checked : CheckedOp2 arena parent .imp left right) :
    ArenaSound arena ⟨prem, {(PropId.positive right).neg} ∪ rest⟩ :=
  replaceConclusion source (fun valuation respects => by
    have equation := checkedOp2_equation (valuation := valuation) respects checked
    simp only [Op2Equation] at equation
    rw [PropId.eval_neg, equation]
    simp [PropId.eval_neg] <;> tauto)

/-- Expand conjunction in the premise. -/
theorem andPrem {admissible : Valuation → Prop} {parent left right : PropId}
    {rest conc : PropSet} (source : SoundUnder admissible ⟨insert parent rest, conc⟩)
    (equation : ∀ valuation, admissible valuation →
      Op2Equation valuation parent .and left right) :
    SoundUnder admissible ⟨insert left (insert right rest), conc⟩ := by
  intro valuation allowed premises
  apply source valuation allowed
  intro id member
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · exact (equation valuation allowed).mpr
      ⟨premises left (by simp), premises right (by simp)⟩
  · exact premises id (by simp [member])

/-- The branch-selecting one-step RHS projection used by
`Kernel::expand_conclusion` for conjunction. -/
theorem andConcBranch {admissible : Valuation → Prop}
    {parent selected other : PropId} {prem rest : PropSet}
    (source : SoundUnder admissible ⟨prem, insert parent rest⟩)
    (equation : ∀ valuation, admissible valuation →
      Op2Equation valuation parent .and selected other) :
    SoundUnder admissible ⟨prem, insert selected rest⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := source valuation allowed premises
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · exact ⟨selected, by simp, ((equation valuation allowed).mp truth).1⟩
  · exact ⟨id, by simp [member], truth⟩

/-- Expand disjunction in the conclusion. -/
theorem orConc {admissible : Valuation → Prop} {parent left right : PropId}
    {prem rest : PropSet} (source : SoundUnder admissible ⟨prem, insert parent rest⟩)
    (equation : ∀ valuation, admissible valuation →
      Op2Equation valuation parent .or left right) :
    SoundUnder admissible ⟨prem, insert left (insert right rest)⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := source valuation allowed premises
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · rcases (equation valuation allowed).mp truth with leftTruth | rightTruth
    · exact ⟨left, by simp, leftTruth⟩
    · exact ⟨right, by simp, rightTruth⟩
  · exact ⟨id, by simp [member], truth⟩

/-- Expand conjunction in the conclusion.  Both branches are required. -/
theorem andConc {admissible : Valuation → Prop} {parent left right : PropId}
    {prem rest : PropSet} (leftSource : SoundUnder admissible ⟨prem, insert left rest⟩)
    (rightSource : SoundUnder admissible ⟨prem, insert right rest⟩)
    (equation : ∀ valuation, admissible valuation →
      Op2Equation valuation parent .and left right) :
    SoundUnder admissible ⟨prem, insert parent rest⟩ := by
  intro valuation allowed premises
  obtain ⟨leftId, leftMember, leftTruth⟩ := leftSource valuation allowed premises
  obtain ⟨rightId, rightMember, rightTruth⟩ := rightSource valuation allowed premises
  simp only [Finset.mem_insert] at leftMember rightMember
  rcases leftMember with rfl | leftMember
  · rcases rightMember with rfl | rightMember
    · exact ⟨parent, by simp, (equation valuation allowed).mpr ⟨leftTruth, rightTruth⟩⟩
    · exact ⟨rightId, by simp [rightMember], rightTruth⟩
  · exact ⟨leftId, by simp [leftMember], leftTruth⟩

/-- Expand disjunction in a premise.  Both branches are required. -/
theorem orPrem {admissible : Valuation → Prop} {parent left right : PropId}
    {rest conc : PropSet} (leftSource : SoundUnder admissible ⟨insert left rest, conc⟩)
    (rightSource : SoundUnder admissible ⟨insert right rest, conc⟩)
    (equation : ∀ valuation, admissible valuation →
      Op2Equation valuation parent .or left right) :
    SoundUnder admissible ⟨insert parent rest, conc⟩ := by
  intro valuation allowed premises
  have parentTruth := premises parent (by simp)
  rcases (equation valuation allowed).mp parentTruth with leftTruth | rightTruth
  · exact leftSource valuation allowed (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact leftTruth
      · exact premises id (by simp [member]))
  · exact rightSource valuation allowed (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact rightTruth
      · exact premises id (by simp [member]))

/-- Expand implication in the conclusion (`p -> q` becomes `p |- q`). -/
theorem impConc {admissible : Valuation → Prop} {parent left right : PropId}
    {prem rest : PropSet} (source : SoundUnder admissible ⟨prem, insert parent rest⟩)
    (equation : ∀ valuation, admissible valuation →
      Op2Equation valuation parent .imp left right) :
    SoundUnder admissible ⟨insert left prem, insert right rest⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := source valuation allowed fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · exact ⟨right, by simp, (equation valuation allowed).mp truth (premises left (by simp))⟩
  · exact ⟨id, by simp [member], truth⟩

/-- Expand implication in a premise.  This is the classical two-branch rule. -/
theorem impPrem {admissible : Valuation → Prop} {parent left right : PropId}
    {rest conc : PropSet} (antecedent : SoundUnder admissible ⟨rest, insert left conc⟩)
    (consequent : SoundUnder admissible ⟨insert right rest, conc⟩)
    (equation : ∀ valuation, admissible valuation →
      Op2Equation valuation parent .imp left right) :
    SoundUnder admissible ⟨insert parent rest, conc⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := antecedent valuation allowed fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · have rightTruth := (equation valuation allowed).mp (premises parent (by simp)) truth
    exact consequent valuation allowed (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact rightTruth
      · exact premises id (by simp [member]))
  · exact ⟨id, member, truth⟩

/-- Expand negation in a premise by moving its operand to the conclusion. -/
theorem notPrem {admissible : Valuation → Prop} {parent operand : PropId}
    {rest conc : PropSet} (source : SoundUnder admissible ⟨insert parent rest, conc⟩)
    (equation : ∀ valuation, admissible valuation →
      Op1Equation valuation parent .not operand) :
    SoundUnder admissible ⟨rest, insert operand conc⟩ := by
  intro valuation allowed premises
  by_cases truth : operand.eval valuation
  · exact ⟨operand, by simp, truth⟩
  · obtain ⟨id, member, valid⟩ := source valuation allowed (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact (equation valuation allowed).mpr truth
      · exact premises id member)
    exact ⟨id, by simp [member], valid⟩

/-- Expand negation in a conclusion by moving its operand to the premise. -/
theorem notConc {admissible : Valuation → Prop} {parent operand : PropId}
    {prem rest : PropSet} (source : SoundUnder admissible ⟨prem, insert parent rest⟩)
    (equation : ∀ valuation, admissible valuation →
      Op1Equation valuation parent .not operand) :
    SoundUnder admissible ⟨insert operand prem, rest⟩ := by
  intro valuation allowed premises
  obtain ⟨id, member, truth⟩ := source valuation allowed fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · exact ((equation valuation allowed).mp truth (premises operand (by simp))).elim
  · exact ⟨id, member, truth⟩

/-- A recursively expanded proposition set, characterized semantically. -/
structure Flattening (valuation : Valuation) (source flat : PropSet) where
  all_iff : (∀ id ∈ source, id.eval valuation) ↔ ∀ id ∈ flat, id.eval valuation
  any_iff : (∃ id ∈ source, id.eval valuation) ↔ ∃ id ∈ flat, id.eval valuation

/-- Recursive AND/OR flattening preserves a theorem row.  The executable
walker need only establish the two local `Flattening` invariants. -/
theorem flatten {admissible : Valuation → Prop} {source : Sequent} {prem conc : PropSet}
    (sound : SoundUnder admissible source)
    (premises : ∀ valuation, admissible valuation → Flattening valuation source.prem prem)
    (conclusions : ∀ valuation, admissible valuation → Flattening valuation source.conc conc) :
    SoundUnder admissible ⟨prem, conc⟩ := by
  intro valuation allowed flatPremises
  have sourcePremises := (premises valuation allowed).all_iff.mpr flatPremises
  exact (conclusions valuation allowed).any_iff.mp (sound valuation allowed sourcePremises)

/-- Recursive folding is the inverse semantic direction of `flatten`.  An
executable opcode walker may fold any tree for which it returns these local
all/any invariants. -/
theorem fold {admissible : Valuation → Prop} {source : Sequent} {prem conc : PropSet}
    (sound : SoundUnder admissible ⟨prem, conc⟩)
    (premises : ∀ valuation, admissible valuation → Flattening valuation source.prem prem)
    (conclusions : ∀ valuation, admissible valuation → Flattening valuation source.conc conc) :
    SoundUnder admissible source := by
  intro valuation allowed sourcePremises
  have flatPremises := (premises valuation allowed).all_iff.mp sourcePremises
  exact (conclusions valuation allowed).any_iff.mpr (sound valuation allowed flatPremises)

/-- Exact semantic contract of `Kernel::flatten_conclusion`. -/
theorem flattenConclusion {admissible : Valuation → Prop} {prem source flat : PropSet}
    (sound : SoundUnder admissible ⟨prem, source⟩)
    (expansion : ∀ valuation, admissible valuation → Flattening valuation source flat) :
    SoundUnder admissible ⟨prem, flat⟩ :=
  flatten sound (fun _valuation _allowed => ⟨Iff.rfl, Iff.rfl⟩) expansion

/-- Exact semantic contract of `Kernel::fold_conclusion`. -/
theorem foldConclusion {admissible : Valuation → Prop} {prem source flat : PropSet}
    (sound : SoundUnder admissible ⟨prem, flat⟩)
    (expansion : ∀ valuation, admissible valuation → Flattening valuation source flat) :
    SoundUnder admissible ⟨prem, source⟩ :=
  fold sound (fun _valuation _allowed => ⟨Iff.rfl, Iff.rfl⟩) expansion

/-- Exact semantic contract of `Kernel::flatten_premise`. -/
theorem flattenPremise {admissible : Valuation → Prop} {source flat conc : PropSet}
    (sound : SoundUnder admissible ⟨source, conc⟩)
    (expansion : ∀ valuation, admissible valuation → Flattening valuation source flat) :
    SoundUnder admissible ⟨flat, conc⟩ :=
  flatten sound expansion (fun _valuation _allowed => ⟨Iff.rfl, Iff.rfl⟩)

/-- Exact semantic contract of `Kernel::fold_premise`. -/
theorem foldPremise {admissible : Valuation → Prop} {source flat conc : PropSet}
    (sound : SoundUnder admissible ⟨flat, conc⟩)
    (expansion : ∀ valuation, admissible valuation → Flattening valuation source flat) :
    SoundUnder admissible ⟨source, conc⟩ :=
  fold sound expansion (fun _valuation _allowed => ⟨Iff.rfl, Iff.rfl⟩)

/-- An empty conclusion is exactly a refutation of the premise conjunction. -/
theorem emptyConclusion_iff (prem : PropSet) :
    Sound ⟨prem, ∅⟩ ↔ ∀ valuation, ¬∀ id ∈ prem, id.eval valuation := by
  simp [Sound, Holds]

theorem contradiction (id : PropId) : Sound ⟨{id, id.neg}, ∅⟩ := by
  intro valuation premises
  have positive := premises id (by simp)
  have negative := premises id.neg (by simp)
  exact ((PropId.eval_neg valuation id).mp negative positive).elim

/-! Focused executable examples pin the inverted sign and canonical set wire
shape. -/

private def testId : PropId := ⟨-1, by decide, by decide⟩
private def testThmId : ThmId := ⟨1, by decide⟩
private def testThmId2 : ThmId := ⟨2, by decide⟩
private def testArray : CanonicalArray := ⟨[testId], by decide, by decide⟩
private def testFact : Thm := ⟨testArray, testArray⟩
private def testLiveStore : ThmStore := ⟨[testFact], [true], []⟩
private def testDeadStore : ThmStore := ⟨[testFact], [false], [testThmId]⟩
private def testCopySource : ThmStore :=
  ⟨[testFact, testFact], [true, false], [testThmId2]⟩
private def testCopyResult : ThmStore :=
  ⟨[testFact, testFact], [true, true], []⟩

example : testId.ref = 1 := rfl
example : testId.neg.val = 1 := rfl
example : PropId.positive LogicalOpcode.Raw.one = testId := by decide
example : testId ∈ ({testId, testId, testId.neg} : PropSet).toList := by simp
example : ({testId, testId, testId.neg} : PropSet).toList.Nodup :=
  PropSet.toList_nodup _

example : Sound ⟨{testId, testId.neg}, ∅⟩ := contradiction testId

example : testLiveStore.lookup testThmId = some testFact := rfl
example : testLiveStore.delete? testThmId = some testDeadStore := rfl
example : testLiveStore.removeTheorem testThmId = (true, testDeadStore) := rfl
example : testDeadStore.removeTheorem testThmId = (false, testDeadStore) := rfl
example : testDeadStore.lookup testThmId = none := rfl
example : testDeadStore.reuse? testFact = some (testThmId, testLiveStore) := rfl
example : testLiveStore.mutate? testThmId testFact = some testLiveStore := rfl
example : testCopySource.copyReuse? testThmId = some (testThmId2, testCopyResult) := rfl
example : testLiveStore.copyFresh? testThmId = some (testThmId2, testCopyResult) := rfl
private theorem testFact_sound : testFact.Sound := by
  intro valuation premises
  exact ⟨testId, by simp [testFact, testArray, Thm.sequent,
    CanonicalArray.asSet], premises testId (by simp [testFact, testArray,
      Thm.sequent, CanonicalArray.asSet])⟩

example (source : Sound ⟨∅, {testId}⟩) : Sound ⟨{testId.neg}, ∅⟩ :=
  fun valuation => polarityLeft (admissible := fun _ => True) (proposition := testId)
    (prem := ∅) (conc := ∅) (soundUnder_of_sound source) valuation trivial

example (source : Sound ⟨{testId}, ∅⟩) : Sound ⟨∅, {testId.neg}⟩ :=
  fun valuation => polarityRight (admissible := fun _ => True) (proposition := testId)
    (prem := ∅) (conc := ∅) (soundUnder_of_sound source) valuation trivial

/-! Compositional regressions: checked opcode theorems remain consumable by
the same structural, polarity, and resolution rules used during LRAT replay. -/

example {arena : OneBased.Arena} {parent left right : OneBased.Ref}
    (checked : CheckedOp2 arena parent .and left right) :
    ArenaSound arena
      ⟨insert (PropId.positive parent).neg
        ({PropId.positive left} ∪ {PropId.positive right}), ∅⟩ := by
  have conjunction := checkedAndRight
    (leftPrem := {PropId.positive left}) (leftConc := ∅)
    (rightPrem := {PropId.positive right}) (rightConc := ∅)
    (identity (admissible := ArenaValuation arena) (PropId.positive left))
    (identity (admissible := ArenaValuation arena) (PropId.positive right)) checked
  simpa [ArenaSound] using polarityLeft conjunction

example {arena : OneBased.Arena} {parent left right : OneBased.Ref}
    {otherPrem otherConc : PropSet}
    (checked : CheckedOp2 arena parent .and left right)
    (complement : ArenaSound arena
      ⟨otherPrem, insert (PropId.positive parent).neg otherConc⟩) :
    ArenaSound arena
      ⟨({PropId.positive left} ∪ {PropId.positive right}) ∪ otherPrem,
        otherConc.erase (PropId.positive parent).neg⟩ := by
  have conjunction := checkedAndRight
    (leftPrem := {PropId.positive left}) (leftConc := ∅)
    (rightPrem := {PropId.positive right}) (rightConc := ∅)
    (identity (admissible := ArenaValuation arena) (PropId.positive left))
    (identity (admissible := ArenaValuation arena) (PropId.positive right)) checked
  simpa [ArenaSound] using
    resolution (PropId.positive parent) conjunction complement (by simp) (by simp)

end Nucleus.Hol.Ethane.ClassicalSequent
