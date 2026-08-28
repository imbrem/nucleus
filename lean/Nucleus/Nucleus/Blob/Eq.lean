import Nucleus.Blob.Expr

/-!
# Blob equality

`BlobEq` is an unchecked claim that two blob expressions describe the same byte
string, and `BlobEq.Valid` is the sole proposition a checked equality enforces:
the two sides have the *same denotation in every model*.  Quantifying over
models, rather than evaluating in one, is what makes the equation a claim about
the store instead of a claim about a particular reading of it.

## The weak, Kleene reading

`Valid` is an equation between `Option Bytes`, so two expressions that are
undefined in every model count as equal.  That is deliberate.  It keeps
`BlobEqFact.refl` total — no expression has to be shown defined before it is
equal to itself — and the junk stays junk, because undefinedness propagates
outwards through `cat` and `slice` rather than escaping into a false equality
between defined values.

The strong alternative, demanding that both sides also be *defined*, is a
considered option and is not taken.  It would cost a total reflexivity rule:
`refl (voidSlice 0)` would become underivable, and every congruence rule would
have to thread a definedness premise to reconstruct it.  The price of the weak
reading is milder and is paid in exactly one place — a refutation may never be
read off two undefined sides, which is why `BlobExpr.length?` bounds-checks and
why `BlobExpr.cmpLength?` short-circuits on an unknown length.

## The standing assumption

Refuting an equation means exhibiting a model in which the two sides differ, so
*every* refutation in this file is sound only relative to the existence of at
least one model — which `Nucleus.Cas.nonempty_model_iff_collisionFree` says is
exactly collision-freedom.  Under a collision there are no models, `Valid` holds
vacuously of every equation, and the calculus is unsound.  The hypothesis is
carried once, as the section variable `standing : Nonempty (Model cas)` of
`section Refutation`; no individual rule restates it.  Everything outside that
section — reflexivity, symmetry, transitivity, both congruences and all four
cancellation rules — needs no such hypothesis at all.

## Digest disequality

Distinct digests now *refute*.  `Nucleus.Model` is injective, so `h₁ ≠ h₂` gives
`σ h₁ ≠ σ h₂` in every model at once; the two sides differ *everywhere* rather
than merely somewhere, and no separating model has to be constructed.  This is
the branch `BlobEq.decide?` gained, and `BlobEq.not_valid_of_blake3` is its two
line justification.  Equal digests still go to reflexivity.

## What has no converse

`BlobEqFact` is the LCF wrapper over the proposition, and every one of its rules
is a theorem in this file applied to its premises.  The Cat trap stands: a
concatenation does not remember where it was split, so no rule may ever conclude
`false` from a structural mismatch of a `cat`, and `BlobEq.decide?` has no such
branch.  Cancellation and n-ary distinctness stay deferred at their seams.

The single most surprising fact in the file is the asymmetry of cancellation.
Agreeing head lengths cancel the *tails* unconditionally but cancel the heads
only when a tail denotes something; without that extra premise the rule is
false, because two concatenations with undefined tails are equal whatever their
heads are.  `exists_valid_cat_of_head_lengths_of_heads_not_valid` pins it.
-/

namespace Nucleus

/-- Case analysis on a possibly-undefined value, phrased as a disjunction so
that splitting a denotation leaves the goal mentioning the *expression* whose
denotation was split. -/
theorem eq_none_or_exists_eq_some {α : Type*} (value : Option α) :
    value = none ∨ ∃ item, value = some item := by
  cases value with
  | none => exact Or.inl rfl
  | some item => exact Or.inr ⟨item, rfl⟩

/--
Two possibly-undefined values agree exactly when they have the same defined
values.

This is the bridge from the equational reading of `BlobEq.Valid` back to the
older two-way-implication reading: `Option` equality *is* mutual implication,
once undefinedness is allowed to match undefinedness.
-/
theorem option_eq_of_eq_some {α : Type*} {left right : Option α}
    (forward : ∀ item, left = some item → right = some item)
    (backward : ∀ item, right = some item → left = some item) : left = right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some item => exact absurd (backward item rfl) (by simp)
  | some item => exact (forward item rfl).symm

/--
An unchecked claim that two expressions denote the same byte string.

This is ordinary data, in the same sense as `CasAssertion`: the trust boundary
is the checked fact built from `Valid`, never this structure.
-/
@[ext]
structure BlobEq where
  lhs : BlobExpr
  rhs : BlobExpr
  deriving DecidableEq

namespace BlobEq

section Semantics

variable [Name Bytes O256] {cas : Cas}

/--
The sole proposition enforced by a checked blob equality: the two sides have the
same denotation in every model of `cas`.

Equality of `Option Bytes` is the weak, Kleene reading — two expressions
undefined everywhere are equal — for the reasons the file header gives.
-/
def Valid (equation : BlobEq) (cas : Cas) : Prop :=
  ∀ model : Model cas, equation.lhs.denote model = equation.rhs.denote model

/-- `Valid` on an equation given by its two sides, with the projections gone.
Every proof below about a constructed equation starts here. -/
theorem valid_mk_iff {lhs rhs : BlobExpr} :
    (BlobEq.mk lhs rhs).Valid cas ↔ ∀ model : Model cas, lhs.denote model = rhs.denote model :=
  Iff.rfl

/-- RULE: reflexivity.  Unconditional, and needing no definedness: it holds for
an out-of-range slice exactly as it holds for a literal. -/
theorem valid_refl (expr : BlobExpr) : (BlobEq.mk expr expr).Valid cas := fun _ ↦ rfl

theorem valid_symm {equation : BlobEq} (valid : equation.Valid cas) :
    (BlobEq.mk equation.rhs equation.lhs).Valid cas := fun model ↦ (valid model).symm

/-- Transitivity needs the shared middle expression, and nothing else — in
particular no collision-freedom, since it never has to produce a model. -/
theorem valid_trans {first second : BlobEq} (firstValid : first.Valid cas)
    (secondValid : second.Valid cas) (shared : first.rhs = second.lhs) :
    (BlobEq.mk first.lhs second.rhs).Valid cas := by
  rw [valid_mk_iff]
  intro model
  rw [firstValid model, shared]
  exact secondValid model

/-- Symmetry on an equation given by its two sides.  Convenient wherever the
equation is built from components rather than projected out of a fact. -/
theorem valid_mk_symm {lhs rhs : BlobExpr} (valid : (BlobEq.mk lhs rhs).Valid cas) :
    (BlobEq.mk rhs lhs).Valid cas := fun model ↦ (valid model).symm

/-- Two expressions undefined in every model are equal.  This is the weak
reading in one line, and it is why a length disagreement can only refute once
*both* lengths are known. -/
theorem valid_of_undefined {equation : BlobEq}
    (lhsUndefined : ∀ model : Model cas, equation.lhs.denote model = none)
    (rhsUndefined : ∀ model : Model cas, equation.rhs.denote model = none) :
    equation.Valid cas := fun model ↦ (lhsUndefined model).trans (rhsUndefined model).symm

/--
RULE: congruence for concatenation.

Total, and sound because `BlobExpr.denote` at a `cat` node is a function of what
its two operands denote — undefinedness included.  It gives equality and only
equality: there is no converse, and none may be added, because a concatenation
does not remember where it was split; see `exists_valid_cat_of_operands_ne`.
-/
theorem valid_cat {leftHead leftTail rightHead rightTail : BlobExpr}
    (heads : (BlobEq.mk leftHead rightHead).Valid cas)
    (tails : (BlobEq.mk leftTail rightTail).Valid cas) :
    (BlobEq.mk (.cat leftHead leftTail) (.cat rightHead rightTail)).Valid cas := by
  rw [valid_mk_iff]
  intro model
  have headsEqual : leftHead.denote model = rightHead.denote model := heads model
  have tailsEqual : leftTail.denote model = rightTail.denote model := tails model
  rw [BlobExpr.denote_cat, BlobExpr.denote_cat, headsEqual, tailsEqual]

/--
RULE: congruence for slicing.

Total, and sound because `Bytes.slice?` is a *function*: equal subjects give
equal results, and out of range on one side is out of range on the other.  The
rule takes one span for both sides, which makes the unsound "a different span on
each side" shape unrepresentable.
-/
theorem valid_slice {lhs rhs : BlobExpr} (subjects : (BlobEq.mk lhs rhs).Valid cas)
    (span : BlobSpan) : (BlobEq.mk (.slice lhs span) (.slice rhs span)).Valid cas := by
  rw [valid_mk_iff]
  intro model
  have subjectsEqual : lhs.denote model = rhs.denote model := subjects model
  rw [BlobExpr.denote_slice, BlobExpr.denote_slice, subjectsEqual]

/-- Congruence for slicing through the whole-span normalisation. -/
theorem valid_sliceOf {lhs rhs : BlobExpr} (subjects : (BlobEq.mk lhs rhs).Valid cas)
    (span : BlobSpan) : (BlobEq.mk (lhs.sliceOf span) (rhs.sliceOf span)).Valid cas := by
  rw [valid_mk_iff]
  intro model
  have sliced : (BlobExpr.slice lhs span).denote model = (BlobExpr.slice rhs span).denote model :=
    valid_slice subjects span model
  rw [BlobExpr.denote_sliceOf, BlobExpr.denote_sliceOf]
  exact sliced

/--
Two expressions that evaluate to the same byte string are equal.

This is the soundness of the evaluation rule.  `BlobExpr.eval?` pins the
denotation in every model, so agreement of two successful evaluations settles
the equality outright, with no definedness side condition and no model
construction.
-/
theorem valid_of_eval? {equation : BlobEq} {value : Bytes}
    (lhsEval : equation.lhs.eval? = some value) (rhsEval : equation.rhs.eval? = some value) :
    equation.Valid cas := fun model ↦
  (BlobExpr.eval?_sound lhsEval model).trans (BlobExpr.eval?_sound rhsEval model).symm

/-!
### Cancellation

Cancellation is the one family of rules that reads a *computed* precondition
rather than just the shape of its premise, and the precondition is not
decoration.  A concatenation does not remember where it was split, so an agreed
length on one side is the only thing that recovers the split point.

Two agreed lengths of `none` are not an agreement: `BlobExpr.cmpLength?` answers
`none` there, and the rules below demand `some` on *both* sides for exactly that
reason.

The asymmetry between the two conclusions is real and is easy to get wrong.
Agreement on the heads gives the tails unconditionally, but gives the *heads*
only when the tails denote something — otherwise both concatenations are
undefined, the equality holds under the weak reading, and the heads are
unconstrained.  See `exists_valid_cat_of_head_lengths_of_heads_not_valid`, which
is the counterexample to the naive form of the rule.

None of these rules needs the standing assumption: each one is proved inside a
model that has already been handed to it.
-/

/-- The core cancellation step, given agreeing head lengths: a denotation of the
left concatenation transfers componentwise to the right one, in whichever model
it was taken. -/
theorem denote_cancel_of_head_lengths {lhsHead lhsTail rhsHead rhsTail : BlobExpr} {count : Nat}
    (valid : (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas)
    (lhsKnown : lhsHead.length? = some count) (rhsKnown : rhsHead.length? = some count)
    {model : Model cas} {head tail : Bytes} (headDenote : lhsHead.denote model = some head)
    (tailDenote : lhsTail.denote model = some tail) :
    rhsHead.denote model = some head ∧ rhsTail.denote model = some tail := by
  have combined : (BlobExpr.cat lhsHead lhsTail).denote model = some (head.append tail) := by
    rw [BlobExpr.denote_cat, headDenote, Option.bind_some, tailDenote, Option.map_some]
  have step : (BlobExpr.cat lhsHead lhsTail).denote model
      = (BlobExpr.cat rhsHead rhsTail).denote model := valid model
  have transferred : (BlobExpr.cat rhsHead rhsTail).denote model = some (head.append tail) :=
    step.symm.trans combined
  obtain ⟨otherHead, otherHeadDenote⟩ := BlobExpr.denote_isSome_of_length? rhsKnown model
  rcases eq_none_or_exists_eq_some (rhsTail.denote model) with
    tailNone | ⟨otherTail, otherTailDenote⟩
  · rw [BlobExpr.denote_cat, otherHeadDenote, Option.bind_some, tailNone] at transferred
    simp at transferred
  · rw [BlobExpr.denote_cat, otherHeadDenote, Option.bind_some, otherTailDenote,
      Option.map_some] at transferred
    obtain ⟨headsEqual, tailsEqual⟩ := Bytes.append_inj (Option.some.inj transferred)
      (by rw [BlobExpr.length_of_length? rhsKnown otherHeadDenote,
        BlobExpr.length_of_length? lhsKnown headDenote])
    exact ⟨by rw [otherHeadDenote, headsEqual], by rw [otherTailDenote, tailsEqual]⟩

/-- The core cancellation step, given agreeing tail lengths. -/
theorem denote_cancel_of_tail_lengths {lhsHead lhsTail rhsHead rhsTail : BlobExpr} {count : Nat}
    (valid : (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas)
    (lhsKnown : lhsTail.length? = some count) (rhsKnown : rhsTail.length? = some count)
    {model : Model cas} {head tail : Bytes} (headDenote : lhsHead.denote model = some head)
    (tailDenote : lhsTail.denote model = some tail) :
    rhsHead.denote model = some head ∧ rhsTail.denote model = some tail := by
  have combined : (BlobExpr.cat lhsHead lhsTail).denote model = some (head.append tail) := by
    rw [BlobExpr.denote_cat, headDenote, Option.bind_some, tailDenote, Option.map_some]
  have step : (BlobExpr.cat lhsHead lhsTail).denote model
      = (BlobExpr.cat rhsHead rhsTail).denote model := valid model
  have transferred : (BlobExpr.cat rhsHead rhsTail).denote model = some (head.append tail) :=
    step.symm.trans combined
  obtain ⟨otherTail, otherTailDenote⟩ := BlobExpr.denote_isSome_of_length? rhsKnown model
  rcases eq_none_or_exists_eq_some (rhsHead.denote model) with
    headNone | ⟨otherHead, otherHeadDenote⟩
  · rw [BlobExpr.denote_cat, headNone] at transferred
    simp at transferred
  · rw [BlobExpr.denote_cat, otherHeadDenote, Option.bind_some, otherTailDenote,
      Option.map_some] at transferred
    obtain ⟨headsEqual, tailsEqual⟩ := Bytes.append_inj' (Option.some.inj transferred)
      (by rw [BlobExpr.length_of_length? rhsKnown otherTailDenote,
        BlobExpr.length_of_length? lhsKnown tailDenote])
    exact ⟨by rw [otherHeadDenote, headsEqual], by rw [otherTailDenote, tailsEqual]⟩

/--
RULE: cancel the tails, given agreeing head lengths.

Unconditional in the tails: the known head lengths already certify that both
heads denote something, which is the witness the argument needs.
-/
theorem valid_cancel_tails_of_head_lengths {lhsHead lhsTail rhsHead rhsTail : BlobExpr}
    {count : Nat} (valid : (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas)
    (lhsKnown : lhsHead.length? = some count) (rhsKnown : rhsHead.length? = some count) :
    (BlobEq.mk lhsTail rhsTail).Valid cas := by
  rw [valid_mk_iff]
  intro model
  refine option_eq_of_eq_some ?_ ?_
  · intro tail tailDenote
    obtain ⟨head, headDenote⟩ := BlobExpr.denote_isSome_of_length? lhsKnown model
    exact (denote_cancel_of_head_lengths valid lhsKnown rhsKnown headDenote tailDenote).2
  · intro tail tailDenote
    obtain ⟨head, headDenote⟩ := BlobExpr.denote_isSome_of_length? rhsKnown model
    exact (denote_cancel_of_head_lengths (valid_mk_symm valid) rhsKnown lhsKnown headDenote
      tailDenote).2

/--
RULE: cancel the heads, given agreeing head lengths *and* a tail that denotes.

The extra hypothesis is not slack.  Without it the rule is false: two
concatenations whose tails are undefined are equal whatever their heads are.
-/
theorem valid_cancel_heads_of_head_lengths {lhsHead lhsTail rhsHead rhsTail : BlobExpr}
    {count tailCount : Nat}
    (valid : (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas)
    (lhsKnown : lhsHead.length? = some count) (rhsKnown : rhsHead.length? = some count)
    (tailKnown : lhsTail.length? = some tailCount) : (BlobEq.mk lhsHead rhsHead).Valid cas := by
  have tailsValid := valid_cancel_tails_of_head_lengths valid lhsKnown rhsKnown
  rw [valid_mk_iff]
  intro model
  refine option_eq_of_eq_some ?_ ?_
  · intro head headDenote
    obtain ⟨tail, tailDenote⟩ := BlobExpr.denote_isSome_of_length? tailKnown model
    exact (denote_cancel_of_head_lengths valid lhsKnown rhsKnown headDenote tailDenote).1
  · intro head headDenote
    obtain ⟨tail, tailDenote⟩ := BlobExpr.denote_isSome_of_length? tailKnown model
    have tailsEqual : lhsTail.denote model = rhsTail.denote model := tailsValid model
    exact (denote_cancel_of_head_lengths (valid_mk_symm valid) rhsKnown lhsKnown headDenote
      (tailsEqual.symm.trans tailDenote)).1

/-- RULE: cancel the heads, given agreeing tail lengths.  The mirror image of
`valid_cancel_tails_of_head_lengths`, and equally unconditional. -/
theorem valid_cancel_heads_of_tail_lengths {lhsHead lhsTail rhsHead rhsTail : BlobExpr}
    {count : Nat} (valid : (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas)
    (lhsKnown : lhsTail.length? = some count) (rhsKnown : rhsTail.length? = some count) :
    (BlobEq.mk lhsHead rhsHead).Valid cas := by
  rw [valid_mk_iff]
  intro model
  refine option_eq_of_eq_some ?_ ?_
  · intro head headDenote
    obtain ⟨tail, tailDenote⟩ := BlobExpr.denote_isSome_of_length? lhsKnown model
    exact (denote_cancel_of_tail_lengths valid lhsKnown rhsKnown headDenote tailDenote).1
  · intro head headDenote
    obtain ⟨tail, tailDenote⟩ := BlobExpr.denote_isSome_of_length? rhsKnown model
    exact (denote_cancel_of_tail_lengths (valid_mk_symm valid) rhsKnown lhsKnown headDenote
      tailDenote).1

/-- RULE: cancel the tails, given agreeing tail lengths *and* a head that
denotes.  The mirror image of `valid_cancel_heads_of_head_lengths`, with the
same non-negotiable definedness side condition. -/
theorem valid_cancel_tails_of_tail_lengths {lhsHead lhsTail rhsHead rhsTail : BlobExpr}
    {count headCount : Nat}
    (valid : (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas)
    (lhsKnown : lhsTail.length? = some count) (rhsKnown : rhsTail.length? = some count)
    (headKnown : lhsHead.length? = some headCount) : (BlobEq.mk lhsTail rhsTail).Valid cas := by
  have headsValid := valid_cancel_heads_of_tail_lengths valid lhsKnown rhsKnown
  rw [valid_mk_iff]
  intro model
  refine option_eq_of_eq_some ?_ ?_
  · intro tail tailDenote
    obtain ⟨head, headDenote⟩ := BlobExpr.denote_isSome_of_length? headKnown model
    exact (denote_cancel_of_tail_lengths valid lhsKnown rhsKnown headDenote tailDenote).2
  · intro tail tailDenote
    obtain ⟨head, headDenote⟩ := BlobExpr.denote_isSome_of_length? headKnown model
    have headsEqual : lhsHead.denote model = rhsHead.denote model := headsValid model
    exact (denote_cancel_of_tail_lengths (valid_mk_symm valid) rhsKnown lhsKnown
      (headsEqual.symm.trans headDenote) tailDenote).2

/--
THE GENERAL CANCELLATION RULE, given agreeing head lengths: both conclusions at
once.

This is the shape the deferred Rust seam should take, and the shape of the
hypotheses is the whole content.  `cat a b = cat c d` together with
`len a = len c` gives `b = d` outright, but gives `a = c` only once some *tail*
is known to denote.  Dropping `tailKnown` does not weaken the rule, it falsifies
it: `exists_valid_cat_of_head_lengths_of_heads_not_valid` exhibits equal
concatenations with equal known head lengths and unequal heads.
-/
theorem valid_cancel_of_head_lengths {lhsHead lhsTail rhsHead rhsTail : BlobExpr}
    {count tailCount : Nat}
    (valid : (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas)
    (lhsKnown : lhsHead.length? = some count) (rhsKnown : rhsHead.length? = some count)
    (tailKnown : lhsTail.length? = some tailCount) :
    (BlobEq.mk lhsHead rhsHead).Valid cas ∧ (BlobEq.mk lhsTail rhsTail).Valid cas :=
  ⟨valid_cancel_heads_of_head_lengths valid lhsKnown rhsKnown tailKnown,
    valid_cancel_tails_of_head_lengths valid lhsKnown rhsKnown⟩

/--
THE GENERAL CANCELLATION RULE, given agreeing tail lengths: both conclusions at
once.  The mirror image, with the definedness premise on the other side, and
`exists_valid_cat_of_tail_lengths_of_tails_not_valid` is the matching proof that
it cannot be dropped.
-/
theorem valid_cancel_of_tail_lengths {lhsHead lhsTail rhsHead rhsTail : BlobExpr}
    {count headCount : Nat}
    (valid : (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas)
    (lhsKnown : lhsTail.length? = some count) (rhsKnown : rhsTail.length? = some count)
    (headKnown : lhsHead.length? = some headCount) :
    (BlobEq.mk lhsHead rhsHead).Valid cas ∧ (BlobEq.mk lhsTail rhsTail).Valid cas :=
  ⟨valid_cancel_heads_of_tail_lengths valid lhsKnown rhsKnown,
    valid_cancel_tails_of_tail_lengths valid lhsKnown rhsKnown headKnown⟩

/-- The general rule on the `BlobExpr.cmpLength?` shape the decision procedure
tests, rather than on two separate length certificates.  `some .eq` already
carries both, by `BlobExpr.exists_length?_of_cmpLength?_eq`. -/
theorem valid_cancel_of_cmpLength?_heads {lhsHead lhsTail rhsHead rhsTail : BlobExpr}
    {tailCount : Nat}
    (valid : (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas)
    (agree : lhsHead.cmpLength? rhsHead = some .eq)
    (tailKnown : lhsTail.length? = some tailCount) :
    (BlobEq.mk lhsHead rhsHead).Valid cas ∧ (BlobEq.mk lhsTail rhsTail).Valid cas := by
  obtain ⟨_, lhsKnown, rhsKnown⟩ := BlobExpr.exists_length?_of_cmpLength?_eq agree
  exact valid_cancel_of_head_lengths valid lhsKnown rhsKnown tailKnown

/-- The mirror of `valid_cancel_of_cmpLength?_heads`, on agreeing tail lengths. -/
theorem valid_cancel_of_cmpLength?_tails {lhsHead lhsTail rhsHead rhsTail : BlobExpr}
    {headCount : Nat}
    (valid : (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas)
    (agree : lhsTail.cmpLength? rhsTail = some .eq)
    (headKnown : lhsHead.length? = some headCount) :
    (BlobEq.mk lhsHead rhsHead).Valid cas ∧ (BlobEq.mk lhsTail rhsTail).Valid cas := by
  obtain ⟨_, lhsKnown, rhsKnown⟩ := BlobExpr.exists_length?_of_cmpLength?_eq agree
  exact valid_cancel_of_tail_lengths valid lhsKnown rhsKnown headKnown

/-- Cancelling a syntactically shared head.  A corollary of the general rule
with both head lengths supplied by the one shared expression — and the shared
expression still has to have a known length, since a shared head that is
undefined constrains nothing. -/
theorem valid_cancel_same_head {shared lhsTail rhsTail : BlobExpr} {count : Nat}
    (valid : (BlobEq.mk (.cat shared lhsTail) (.cat shared rhsTail)).Valid cas)
    (known : shared.length? = some count) : (BlobEq.mk lhsTail rhsTail).Valid cas :=
  valid_cancel_tails_of_head_lengths valid known known

/-- Cancelling a syntactically shared tail. -/
theorem valid_cancel_same_tail {lhsHead rhsHead shared : BlobExpr} {count : Nat}
    (valid : (BlobEq.mk (.cat lhsHead shared) (.cat rhsHead shared)).Valid cas)
    (known : shared.length? = some count) : (BlobEq.mk lhsHead rhsHead).Valid cas :=
  valid_cancel_heads_of_tail_lengths valid known known

end Semantics

/-!
## Refutation, and the standing assumption

Everything from here to the end of the section refutes rather than proves, and a
refutation is a model in which the two sides differ.  The existence of one model
is therefore the shared hypothesis of the whole section, carried as the single
instance variable `standing` and stated nowhere else;
`Nucleus.Cas.nonempty_model_iff_collisionFree` turns a `CollisionFree` store into
it.  Under a collision every statement below is vacuously false in the sense
that its conclusion `¬ Valid` is unavailable — which is the honest form of "the
calculus is unsound under a collision".
-/

section Refutation

variable [Name Bytes O256] {cas : Cas} [standing : Nonempty (Model cas)]

/--
RULE: distinct digests refute.

This is the branch the model semantics added, and its justification is immediate
from `Model.injective`: `σ` picks *the* blob an address names, so two distinct
addresses are sent to two distinct blobs in **every** model.  No separating
model is constructed; the standing assumption supplies the only model this proof
needs, and it needs it only because `¬ Valid` is a statement about some model.
-/
theorem not_valid_of_blake3 {equation : BlobEq} {left right : O256}
    (lhsDigest : equation.lhs = .blake3 left) (rhsDigest : equation.rhs = .blake3 right)
    (different : left ≠ right) : ¬ equation.Valid cas := by
  intro valid
  obtain ⟨model⟩ := standing
  have equal : equation.lhs.denote model = equation.rhs.denote model := valid model
  rw [lhsDigest, rhsDigest] at equal
  exact BlobExpr.denote_blake3_ne model different equal

/-- Distinct digests refute, on an equation given by its two sides. -/
theorem not_valid_of_digests {left right : O256} (different : left ≠ right) :
    ¬ (BlobEq.mk (.blake3 left) (.blake3 right)).Valid cas :=
  not_valid_of_blake3 rfl rfl different

/-- Two expressions that evaluate to *different* byte strings are not equal.
Evaluation therefore settles the question in both directions. -/
theorem not_valid_of_eval? {equation : BlobEq} {lhsValue rhsValue : Bytes}
    (lhsEval : equation.lhs.eval? = some lhsValue) (rhsEval : equation.rhs.eval? = some rhsValue)
    (differ : lhsValue ≠ rhsValue) : ¬ equation.Valid cas := by
  intro valid
  obtain ⟨model⟩ := standing
  have equal : equation.lhs.denote model = equation.rhs.denote model := valid model
  rw [BlobExpr.eval?_sound lhsEval model, BlobExpr.eval?_sound rhsEval model] at equal
  exact differ (Option.some.inj equal)

/--
Equality preserves length: two equal expressions whose lengths are both known
have the same length.

Note what is *not* claimed: an equality does not make `BlobExpr.length?` agree as
an `Option`, because two expressions undefined everywhere are equal while
neither has a known length.  An equality premise therefore has to be paired with
a computed length on one side anyway, at which point it is the ordinary
length-agreement premise, which is why "use an equality fact as the cancellation
precondition" is no shortcut.
-/
theorem length?_agree_of_valid {equation : BlobEq} (valid : equation.Valid cas)
    {lhsLength rhsLength : Nat} (lhsKnown : equation.lhs.length? = some lhsLength)
    (rhsKnown : equation.rhs.length? = some rhsLength) : lhsLength = rhsLength := by
  obtain ⟨model⟩ := standing
  obtain ⟨blob, denoted, measured⟩ := BlobExpr.length?_sound lhsKnown model
  have rhsDenoted : equation.rhs.denote model = some blob := (valid model).symm.trans denoted
  exact measured.symm.trans (BlobExpr.length_of_length? rhsKnown rhsDenoted)

/-- An equality never exhibits a strict length comparison: `BlobExpr.cmpLength?`
either agrees or declines to answer. -/
theorem cmpLength?_of_valid {equation : BlobEq} (valid : equation.Valid cas) :
    equation.lhs.cmpLength? equation.rhs = some .eq ∨
      equation.lhs.cmpLength? equation.rhs = none := by
  cases lhsKnown : equation.lhs.length? with
  | none => exact Or.inr (BlobExpr.cmpLength?_of_unknown_left _ lhsKnown)
  | some lhsLength =>
      cases rhsKnown : equation.rhs.length? with
      | none => exact Or.inr (BlobExpr.cmpLength?_of_unknown_right _ rhsKnown)
      | some rhsLength =>
          refine Or.inl ?_
          rw [BlobExpr.cmpLength?_of_length? lhsKnown rhsKnown,
            length?_agree_of_valid valid lhsKnown rhsKnown, Nat.compare_eq_eq.mpr rfl]

/--
RULE: length disagreement refutes an equality.

Sound only because `BlobExpr.length?` bounds-checks every slice, so `some n`
certifies that the expression is defined in every model *and* that its value is
`n` octets long.  A bare span width would not: two out-of-range slices of
differing widths are both undefined and are therefore equal.
-/
theorem not_valid_of_length_disagreement {equation : BlobEq} {lhsLength rhsLength : Nat}
    (lhsKnown : equation.lhs.length? = some lhsLength)
    (rhsKnown : equation.rhs.length? = some rhsLength) (differ : lhsLength ≠ rhsLength) :
    ¬ equation.Valid cas := fun valid ↦ differ (length?_agree_of_valid valid lhsKnown rhsKnown)

/-- The `BlobExpr.cmpLength?` phrasing of `not_valid_of_length_disagreement`,
matching the shape the decision procedure tests. -/
theorem not_valid_of_cmpLength? {equation : BlobEq}
    (differ : equation.lhs.cmpLength? equation.rhs ≠ some .eq)
    (known : equation.lhs.cmpLength? equation.rhs ≠ none) : ¬ equation.Valid cas := fun valid ↦
  (cmpLength?_of_valid valid).elim differ known

end Refutation

/--
Settle this equality where the rules settle it: `some true` when provable,
`some false` when refutable, and `none` when unknown.  It never guesses.

The four branches are reflexivity, digest separation, length disagreement and
evaluation, in increasing cost.  Digest separation is the branch the model
semantics licensed: `σ` is injective, so distinct addresses denote distinct
blobs in every model — and *equal* digests are caught by the reflexivity branch
above it, never by this one.  Length disagreement is sound only because
`BlobExpr.length?` bounds-checks.  Evaluation settles the question in both
directions, since `BlobExpr.eval?` answering `some v` pins the denotation.

One branch is deliberately absent.  There is no structural-mismatch branch:
`cat (bytes "ab") (bytes "c")` and `cat (bytes "a") (bytes "bc")` are equal, so
concluding `false` from unequal operands would be unsound.  Note also that the
`cmpLength?` match falls through on `none` as well as on `some .eq`, so two
unknown lengths never refute.
-/
def decide? (equation : BlobEq) : Option Bool :=
  if equation.lhs = equation.rhs then
    some true
  else if equation.lhs.isDigest = true ∧ equation.rhs.isDigest = true then
    some false
  else
    match equation.lhs.cmpLength? equation.rhs with
    | some .lt | some .gt => some false
    | _ =>
        equation.lhs.eval?.bind fun lhsValue ↦
          equation.rhs.eval?.map fun rhsValue ↦ decide (lhsValue = rhsValue)

@[simp] theorem decide?_self (expr : BlobExpr) : (BlobEq.mk expr expr).decide? = some true :=
  if_pos rfl

/-- Read the evaluation branch of `decide?` back into its two evaluations. -/
theorem eval?_bind_eq_some {lhs rhs : BlobExpr} {result : Bool}
    (evaluated : lhs.eval?.bind (fun lhsValue ↦ rhs.eval?.map fun rhsValue ↦
      decide (lhsValue = rhsValue)) = some result) :
    ∃ lhsValue rhsValue, lhs.eval? = some lhsValue ∧ rhs.eval? = some rhsValue ∧
      result = decide (lhsValue = rhsValue) := by
  cases lhsEval : lhs.eval? with
  | none => rw [lhsEval] at evaluated; simp at evaluated
  | some lhsValue =>
      cases rhsEval : rhs.eval? with
      | none => rw [lhsEval, rhsEval] at evaluated; simp at evaluated
      | some rhsValue =>
          rw [lhsEval, rhsEval] at evaluated
          simp only [Option.bind_some, Option.map_some] at evaluated
          exact ⟨lhsValue, rhsValue, rfl, rfl, (Option.some.inj evaluated).symm⟩

section Decision

variable [Name Bytes O256] {cas : Cas}

/-- `decide?` never claims an equality it cannot justify: `some true` is a
proof, and it needs no model to exist. -/
theorem valid_of_decide?_true {equation : BlobEq} (decided : equation.decide? = some true) :
    equation.Valid cas := by
  by_cases equal : equation.lhs = equation.rhs
  · intro model
    rw [equal]
  · rw [decide?, if_neg equal] at decided
    by_cases digests : equation.lhs.isDigest = true ∧ equation.rhs.isDigest = true
    · rw [if_pos digests] at decided
      simp at decided
    · rw [if_neg digests] at decided
      have fromEval : equation.lhs.eval?.bind (fun lhsValue ↦ equation.rhs.eval?.map fun rhsValue ↦
          decide (lhsValue = rhsValue)) = some true → equation.Valid cas := by
        intro evaluated
        obtain ⟨lhsValue, rhsValue, lhsEval, rhsEval, result⟩ := eval?_bind_eq_some evaluated
        have values : lhsValue = rhsValue := of_decide_eq_true result.symm
        subst values
        exact valid_of_eval? lhsEval rhsEval
      cases ordering : equation.lhs.cmpLength? equation.rhs with
      | none => rw [ordering] at decided; exact fromEval decided
      | some order =>
          cases order with
          | lt => rw [ordering] at decided; simp at decided
          | eq => rw [ordering] at decided; exact fromEval decided
          | gt => rw [ordering] at decided; simp at decided

variable [Nonempty (Model cas)]

/-- `decide?` never refutes an equality it cannot refute: `some false` is a
proof of disequality, under the standing assumption that a model exists. -/
theorem not_valid_of_decide?_false {equation : BlobEq} (decided : equation.decide? = some false) :
    ¬ equation.Valid cas := by
  by_cases equal : equation.lhs = equation.rhs
  · rw [decide?, if_pos equal] at decided
    simp at decided
  · rw [decide?, if_neg equal] at decided
    by_cases digests : equation.lhs.isDigest = true ∧ equation.rhs.isDigest = true
    · obtain ⟨leftHash, lhsDigest⟩ := BlobExpr.isDigest_iff.mp digests.1
      obtain ⟨rightHash, rhsDigest⟩ := BlobExpr.isDigest_iff.mp digests.2
      exact not_valid_of_blake3 lhsDigest rhsDigest
        (fun same ↦ equal (by rw [lhsDigest, rhsDigest, same]))
    · rw [if_neg digests] at decided
      have fromEval : equation.lhs.eval?.bind (fun lhsValue ↦ equation.rhs.eval?.map fun rhsValue ↦
          decide (lhsValue = rhsValue)) = some false → ¬ equation.Valid cas := by
        intro evaluated
        obtain ⟨lhsValue, rhsValue, lhsEval, rhsEval, result⟩ := eval?_bind_eq_some evaluated
        exact not_valid_of_eval? lhsEval rhsEval (of_decide_eq_false result.symm)
      cases ordering : equation.lhs.cmpLength? equation.rhs with
      | none => rw [ordering] at decided; exact fromEval decided
      | some order =>
          cases order with
          | lt => exact not_valid_of_cmpLength? (by rw [ordering]; simp) (by rw [ordering]; simp)
          | eq => rw [ordering] at decided; exact fromEval decided
          | gt => exact not_valid_of_cmpLength? (by rw [ordering]; simp) (by rw [ordering]; simp)

end Decision

end BlobEq

/--
A checked blob equality over a given store: the LCF wrapper.

The `valid` field is proof data, so the only way to obtain a fact is to discharge
`BlobEq.Valid` — either by deciding it with `check?` or by one of the rules
below, each of which is a theorem of this file applied to its premises.  A fact
belongs to the store it was checked against; there is no store-free equality.
-/
structure BlobEqFact [Name Bytes O256] (cas : Cas) where
  prop : BlobEq
  valid : prop.Valid cas

namespace BlobEqFact

variable [Name Bytes O256] {cas : Cas}

/-- RULE: evaluation.  The LCF elimination boundary for unchecked equations:
`BlobEq.decide?` answers `some true` only when the equation is provable, so that
answer *is* the proof. -/
def check? (cas : Cas) (equation : BlobEq) : Option (BlobEqFact cas) :=
  if decided : equation.decide? = some true then
    some ⟨equation, BlobEq.valid_of_decide?_true decided⟩
  else
    none

/-- RULE: reflexivity.  Total, and needing no definedness: it holds for an
out-of-range slice exactly as it holds for a literal. -/
def refl (cas : Cas) (expr : BlobExpr) : BlobEqFact cas :=
  ⟨BlobEq.mk expr expr, BlobEq.valid_refl expr⟩

/-- RULE: symmetry.  Total. -/
def symm (fact : BlobEqFact cas) : BlobEqFact cas :=
  ⟨BlobEq.mk fact.prop.rhs fact.prop.lhs, BlobEq.valid_symm fact.valid⟩

/-- RULE: transitivity.  Partial only in the syntactic middle-term check: the
proposition itself needs nothing beyond the shared expression, in particular no
collision-freedom. -/
def trans? (first second : BlobEqFact cas) : Option (BlobEqFact cas) :=
  if shared : first.prop.rhs = second.prop.lhs then
    some ⟨BlobEq.mk first.prop.lhs second.prop.rhs,
      BlobEq.valid_trans first.valid second.valid shared⟩
  else
    none

/-- RULE: congruence for concatenation.  Total, and equality only. -/
def cat (head tail : BlobEqFact cas) : BlobEqFact cas :=
  ⟨BlobEq.mk (.cat head.prop.lhs tail.prop.lhs) (.cat head.prop.rhs tail.prop.rhs),
    BlobEq.valid_cat head.valid tail.valid⟩

/-- RULE: congruence for slicing.  Total, and one span for both sides. -/
def slice (fact : BlobEqFact cas) (span : BlobSpan) : BlobEqFact cas :=
  ⟨BlobEq.mk (.slice fact.prop.lhs span) (.slice fact.prop.rhs span),
    BlobEq.valid_slice fact.valid span⟩

@[simp] theorem check?_isSome (cas : Cas) (equation : BlobEq) :
    (check? cas equation).isSome = decide (equation.decide? = some true) := by
  by_cases decided : equation.decide? = some true <;> simp [check?, decided]

end BlobEqFact

/--
The proposition a Rust `CasRangeFact` carries: *some* blob named `hash` has
`blob` at `span`.

This is a claim about `Nucleus.Name.name` alone, and it is deliberately the
*weaker* claim: it says a blob named `hash` exists with these octets there, not
that a model sends `hash` to that blob.
-/
def CasRange.Valid [Name Bytes O256] (hash : O256) (span : BlobSpan) (blob : Bytes) : Prop :=
  ∃ whole : Bytes, Name.name whole = hash ∧ whole.slice? span.start span.stop = some blob

/--
Read a *stored* range as a blob-expression equality.

This is the hypothesis-free form, and it is the one the Rust range facts should
use: what licenses the equation is that the store holds the pair, so every model
is pinned there by `Model.extendsCas`.  Nothing about the naming function is
needed beyond the check the pair already carries.
-/
theorem BlobEq.valid_ofCasRange_of_mem [Name Bytes O256] {cas : Cas} {pair : CasPair}
    (member : pair ∈ cas) {span : BlobSpan} {blob : Bytes}
    (sliced : pair.blob.slice? span.start span.stop = some blob) :
    (BlobEq.mk ((BlobExpr.blake3 pair.hash).sliceOf span) (.bytes blob)).Valid cas := by
  rw [valid_mk_iff]
  intro model
  rw [BlobExpr.denote_sliceOf, BlobExpr.denote_slice, BlobExpr.denote_blake3,
    model.extendsCas pair member, Option.bind_some, sliced, BlobExpr.denote_bytes]

/--
Read an *unstored* range as a blob-expression equality.

This is what the section property would buy, and the hypotheses say exactly why
it is not free.  `CasRange.Valid` witnesses only that *some* blob named `hash`
has these octets; `blake3 hash` denotes whatever the model sends `hash` to, and
for an address the store does not pin those are unrelated.  `sections` closes the
gap and injectivity of the naming function turns the two naming equations into
one blob.  See the header of `Nucleus.Blob.Expr` for why `Model` does not simply
demand the section property.
-/
theorem BlobEq.valid_ofCasRange [Name Bytes O256] {cas : Cas}
    (sections : ∀ model : Model cas, model.IsSection)
    (injective : Function.Injective (Name.name : Bytes → O256))
    {hash : O256} {span : BlobSpan} {blob : Bytes} (fact : CasRange.Valid hash span blob) :
    (BlobEq.mk ((BlobExpr.blake3 hash).sliceOf span) (.bytes blob)).Valid cas := by
  obtain ⟨whole, named, sliced⟩ := fact
  rw [valid_mk_iff]
  intro model
  have same : model.sigma hash = whole := injective ((sections model hash).trans named.symm)
  rw [BlobExpr.denote_sliceOf, BlobExpr.denote_slice, BlobExpr.denote_blake3, same,
    Option.bind_some, sliced, BlobExpr.denote_bytes]

/--
Recover a range fact from an equality of the shape a range fact has.

Under the fibre semantics this direction was free; under the model semantics it
is not, and the difference is instructive.  The equality pins `σ hash` and
nothing more, so producing a blob *named* `hash` needs one model that is a
section.  The asymmetry with `BlobEq.valid_ofCasRange_of_mem` is why the two
propositions are kept apart.
-/
theorem CasRange.of_valid [Name Bytes O256] {cas : Cas} {model : Model cas}
    (isSection : model.IsSection) {hash : O256} {span : BlobSpan} {blob : Bytes}
    (valid : (BlobEq.mk ((BlobExpr.blake3 hash).sliceOf span) (.bytes blob)).Valid cas) :
    CasRange.Valid hash span blob := by
  have denoted : ((BlobExpr.blake3 hash).sliceOf span).denote model
      = (BlobExpr.bytes blob).denote model := valid model
  rw [BlobExpr.denote_sliceOf, BlobExpr.denote_slice, BlobExpr.denote_blake3, Option.bind_some,
    BlobExpr.denote_bytes] at denoted
  exact ⟨model.sigma hash, isSection hash, denoted⟩

/-!
## Traps

Each statement below is a rule that looks plausible and is false, pinned as a
counterexample so that neither track can drift into implementing it.
-/

section Traps

variable [Name Bytes O256]

/--
COUNTEREXAMPLE: congruence for `cat` runs one way only.

`"ab" ++ "c"` and `"a" ++ "bc"` denote the same byte string while neither their
heads nor their tails do.  A concatenation does not remember where it was split,
so concluding *disequality* from unequal operands is unsound: this is why
`BlobEq.decide?` has no structural-mismatch branch and why `BlobEq.valid_cat`
has no converse.  The same trap applies to `BlobEq.valid_slice`.

Stated here on *syntactic* inequality, which is what a decision procedure can
test.  `exists_valid_cat_of_operands_not_valid` sharpens it to genuine semantic
inequality, at the cost of needing the standing assumption.
-/
theorem exists_valid_cat_of_operands_ne (cas : Cas) :
    ∃ lhsHead lhsTail rhsHead rhsTail : BlobExpr,
      (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas ∧
        lhsHead ≠ rhsHead ∧ lhsTail ≠ rhsTail := by
  have split : ((Bytes.empty.push 97).push 98).append (Bytes.empty.push 99) =
      (Bytes.empty.push 97).append ((Bytes.empty.push 98).push 99) := by
    ext
    simp
  refine ⟨.bytes ((Bytes.empty.push 97).push 98), .bytes (Bytes.empty.push 99),
    .bytes (Bytes.empty.push 97), .bytes ((Bytes.empty.push 98).push 99), ?_, ?_, ?_⟩
  · rw [BlobEq.valid_mk_iff]
    intro model
    rw [BlobExpr.denote_cat, BlobExpr.denote_cat]
    simp only [BlobExpr.denote_bytes, Option.bind_some, Option.map_some, split]
  · intro equal
    simp only [BlobExpr.bytes.injEq] at equal
    exact absurd equal (by decide)
  · intro equal
    simp only [BlobExpr.bytes.injEq] at equal
    exact absurd equal (by decide)

/--
Two out-of-range slices of *different* naive widths are equal, because both are
undefined in every model.

This is the trap that forces `BlobExpr.length?` to bounds-check a slice against
its subject: reporting the bare span width would make these two look like a
length disagreement and hence a disequality, which is false.
-/
theorem valid_voidSlice (cas : Cas) (left right : Nat) :
    (BlobEq.mk (.voidSlice left) (.voidSlice right)).Valid cas := by
  rw [BlobEq.valid_mk_iff]
  intro model
  rw [BlobExpr.denote_voidSlice, BlobExpr.denote_voidSlice]

/--
COUNTEREXAMPLE: an equality premise on its own yields no length agreement.

Two expressions undefined everywhere are equal while `BlobExpr.cmpLength?` still
declines to answer.  So "use an equality fact as the cancellation precondition"
is not a route to that precondition; pairing the equality with a computed length
on one side is, and that is the ordinary rule.
-/
theorem exists_valid_of_cmpLength?_eq_none (cas : Cas) :
    ∃ lhs rhs : BlobExpr, (BlobEq.mk lhs rhs).Valid cas ∧ lhs.cmpLength? rhs = none ∧ lhs ≠ rhs :=
  ⟨.voidSlice 4, .voidSlice 2, valid_voidSlice cas 4 2,
    BlobExpr.cmpLength?_of_unknown_left _ (BlobExpr.length?_voidSlice 4), by decide⟩

/-- Known and differing lengths do refute, with no evaluation and no
allocation. -/
example : (BlobEq.mk (.zero 3) (.bytes Bytes.empty)).decide? = some false := by
  decide

/-- `blake3 hash` is the blob *named* by `hash`, never the octets of `hash`
itself; nothing relates them, only one side is a digest, and the decision
procedure declines. -/
example (hash : O256) : (BlobEq.mk (.blake3 hash) (.bytes hash.encode)).decide? = none := by
  rw [BlobEq.decide?, if_neg (by simp), if_neg (by simp [BlobExpr.isDigest])]
  simp [BlobExpr.cmpLength?]

/-- Distinct digests now *refute*, where the fibre reading had to decline: this
is the branch the model semantics added. -/
example {left right : O256} (different : left ≠ right) :
    (BlobEq.mk (.blake3 left) (.blake3 right)).decide? = some false := by
  rw [BlobEq.decide?, if_neg (by simpa using different), if_pos ⟨rfl, rfl⟩]

end Traps

section RefutationTraps

variable [Name Bytes O256] {cas : Cas} [Nonempty (Model cas)]

/--
COUNTEREXAMPLE: head cancellation genuinely needs its definedness side
condition.

The two heads have the same *known* length and the two concatenations are equal,
yet the heads are not equal: both tails are undefined, so both concatenations are
undefined and the equality holds under the weak reading.  "Equal concatenations
with agreeing head lengths have equal heads" is therefore FALSE, and
`BlobEq.valid_cancel_heads_of_head_lengths` is the true rule — the tail length it
additionally demands is exactly what excludes this case.
-/
theorem exists_valid_cat_of_head_lengths_of_heads_not_valid :
    ∃ lhsHead lhsTail rhsHead rhsTail : BlobExpr,
      (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas ∧
        lhsHead.length? = some 1 ∧ rhsHead.length? = some 1 ∧
        ¬ (BlobEq.mk lhsHead rhsHead).Valid cas := by
  refine ⟨.bytes (Bytes.empty.push 0), .voidSlice 0, .bytes (Bytes.empty.push 1), .voidSlice 0,
    ?_, ?_, ?_, ?_⟩
  · refine BlobEq.valid_of_undefined ?_ ?_ <;> intro model <;>
      simp [BlobExpr.denote_cat]
  · simp
  · simp
  · intro valid
    have equal : (BlobExpr.bytes (Bytes.empty.push 0)).denote (Classical.arbitrary (Model cas))
        = (BlobExpr.bytes (Bytes.empty.push 1)).denote (Classical.arbitrary (Model cas)) :=
      valid (Classical.arbitrary (Model cas))
    rw [BlobExpr.denote_bytes, BlobExpr.denote_bytes] at equal
    exact absurd (Option.some.inj equal) (by decide)

/--
THE CAT TRAP, semantic form: the operands are not merely syntactically
distinct, they are genuinely *unequal*.

`"ab" ++ "c"` and `"a" ++ "bc"` are equal, while `"ab"` and `"a"` differ in
every model and so do `"c"` and `"bc"`.  So `BlobEq.valid_cat` has no converse
in the strongest available sense: a rule reading operand equality off a
concatenation equality would not merely overreach, it would derive an equation
that is false in every model.  Read contrapositively — which is how a decision
procedure meets it — the same witnesses say that unequal operands are no
evidence of unequal concatenations, which is why `BlobEq.decide?` has no
structural-mismatch branch.  `exists_valid_cat_of_operands_ne` is the same trap
stated on the syntactic inequality a decision procedure can actually test.
-/
theorem exists_valid_cat_of_operands_not_valid :
    ∃ lhsHead lhsTail rhsHead rhsTail : BlobExpr,
      (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas ∧
        ¬ (BlobEq.mk lhsHead rhsHead).Valid cas ∧
        ¬ (BlobEq.mk lhsTail rhsTail).Valid cas := by
  have split : ((Bytes.empty.push 97).push 98).append (Bytes.empty.push 99) =
      (Bytes.empty.push 97).append ((Bytes.empty.push 98).push 99) := by
    ext
    simp
  refine ⟨.bytes ((Bytes.empty.push 97).push 98), .bytes (Bytes.empty.push 99),
    .bytes (Bytes.empty.push 97), .bytes ((Bytes.empty.push 98).push 99), ?_, ?_, ?_⟩
  · rw [BlobEq.valid_mk_iff]
    intro model
    rw [BlobExpr.denote_cat, BlobExpr.denote_cat]
    simp only [BlobExpr.denote_bytes, Option.bind_some, Option.map_some, split]
  · intro valid
    have equal : (BlobExpr.bytes ((Bytes.empty.push 97).push 98)).denote
          (Classical.arbitrary (Model cas))
        = (BlobExpr.bytes (Bytes.empty.push 97)).denote (Classical.arbitrary (Model cas)) :=
      valid (Classical.arbitrary (Model cas))
    rw [BlobExpr.denote_bytes, BlobExpr.denote_bytes] at equal
    exact absurd (Option.some.inj equal) (by decide)
  · intro valid
    have equal : (BlobExpr.bytes (Bytes.empty.push 99)).denote (Classical.arbitrary (Model cas))
        = (BlobExpr.bytes ((Bytes.empty.push 98).push 99)).denote
          (Classical.arbitrary (Model cas)) :=
      valid (Classical.arbitrary (Model cas))
    rw [BlobExpr.denote_bytes, BlobExpr.denote_bytes] at equal
    exact absurd (Option.some.inj equal) (by decide)

/--
COUNTEREXAMPLE: tail cancellation genuinely needs its definedness side
condition, exactly mirroring the head case.

The two tails have the same *known* length and the two concatenations are equal,
yet the tails are not equal: both heads are undefined, so both concatenations
are undefined and the equality holds under the weak reading.  "Equal
concatenations with agreeing tail lengths have equal tails" is therefore FALSE.

Together with `exists_valid_cat_of_head_lengths_of_heads_not_valid` this pins
the shape of the general rule from both sides: one agreed length gives the
*opposite* component for free and the *same* component only with a definedness
witness.  A rule that claims both components from one agreed length is unsound.
-/
theorem exists_valid_cat_of_tail_lengths_of_tails_not_valid :
    ∃ lhsHead lhsTail rhsHead rhsTail : BlobExpr,
      (BlobEq.mk (.cat lhsHead lhsTail) (.cat rhsHead rhsTail)).Valid cas ∧
        lhsTail.length? = some 1 ∧ rhsTail.length? = some 1 ∧
        ¬ (BlobEq.mk lhsTail rhsTail).Valid cas := by
  refine ⟨.voidSlice 0, .bytes (Bytes.empty.push 0), .voidSlice 0, .bytes (Bytes.empty.push 1),
    ?_, ?_, ?_, ?_⟩
  · refine BlobEq.valid_of_undefined ?_ ?_ <;> intro model <;>
      simp [BlobExpr.denote_cat]
  · simp
  · simp
  · intro valid
    have equal : (BlobExpr.bytes (Bytes.empty.push 0)).denote (Classical.arbitrary (Model cas))
        = (BlobExpr.bytes (Bytes.empty.push 1)).denote (Classical.arbitrary (Model cas)) :=
      valid (Classical.arbitrary (Model cas))
    rw [BlobExpr.denote_bytes, BlobExpr.denote_bytes] at equal
    exact absurd (Option.some.inj equal) (by decide)

end RefutationTraps

/-!
## Non-vacuity

The refutation section is conditional on a model existing, so it is worth
pinning that the condition is *satisfiable*: the empty store is collision-free,
so it has a model, so digest disequality is genuinely derivable there rather
than derivable only because the hypothesis is unavailable.
-/

section NonVacuity

variable [Name Bytes O256]

/-- The empty store satisfies the standing assumption. -/
instance nonempty_model_empty : Nonempty (Model (Cas.empty : Cas)) :=
  Cas.nonempty_model_of_collisionFree Cas.collisionFree_empty

/-- Digest disequality is derivable, not vacuous: over the empty store the
standing assumption holds and distinct digests still refute. -/
theorem not_valid_of_digests_empty {left right : O256} (different : left ≠ right) :
    ¬ (BlobEq.mk (.blake3 left) (.blake3 right)).Valid Cas.empty :=
  BlobEq.not_valid_of_digests different

/-- And reflexivity stays total under the weak reading: an expression undefined
in every model is still equal to itself. -/
theorem valid_refl_voidSlice_empty (width : Nat) :
    (BlobEq.mk (.voidSlice width) (.voidSlice width)).Valid Cas.empty :=
  BlobEq.valid_refl _

end NonVacuity

end Nucleus
