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

## Range facts

The last third of the file leaves equalities for `Nucleus.CasRange.Valid`, the
weaker claim a Rust `CasRangeFact` carries: *some* blob named `hash` holds these
octets at this span.  Two questions are settled there.  Which equalities yield
one — `Nucleus.Cas.pins_of_valid_blake3` says a contentful equality forces the
store to pin the digest, which is the step the Rust `BlobFact::to_range_fact`
takes and which needs no section property.  And what may be done with one —
`Nucleus.CasRange.valid_slice`, `Nucleus.CasRange.valid_fuse` and
`Nucleus.CasRange.exists_length_of_valid_open` are the Rust `slice`, `fuse` and
`blob_len`, each with the side conditions the Rust enforces and a counterexample
for each condition that could plausibly be dropped.
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
Recover a range fact from an equality of the shape a range fact has, assuming a
model that is a section.

Under the fibre semantics this direction was free; under the model semantics it
is not, and the difference is instructive.  The equality pins `σ hash` and
nothing more, so producing a blob *named* `hash` needs one model that is a
section.  The asymmetry with `BlobEq.valid_ofCasRange_of_mem` is why the two
propositions are kept apart.

This is no longer the only route: `CasRange.of_valid_of_pins` and
`CasRange.of_valid_of_contentful` below reach the same conclusion with no
section property, by deriving the pin from the equality instead of assuming the
naming function is total on addresses.  They are kept side by side because the
section-free versions carry a side condition this one does not need — see
`CasRange.Contentful`.
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
## Slicing a slice

Four facts about `Nucleus.Bytes.slice?` that the pinning lemma and the range
rules below both need.  They are stated here rather than with `Bytes` because
they exist only to serve those rules: each one reads a successful slice back
into the arithmetic of absolute blob coordinates, which is the coordinate system
a `Nucleus.CasRange.Valid` claim is written in.
-/

namespace Bytes

/-- Only the resolved upper bound is observable: two spans that resolve to the
same offset select the same octets, defined or not.  This is what lets an open
span be traded for the closed one it happens to resolve to. -/
theorem slice?_congr {whole : Bytes} {start : Nat} {left right : Option Nat}
    (agree : left.getD whole.length = right.getD whole.length) :
    whole.slice? start left = whole.slice? start right := by
  unfold slice?
  rw [agree]

/-- A successful slice resolves its upper bound to `start + width`.  This is the
"known end" of a range claim, and it is why an open span still pins one. -/
theorem getD_of_slice? {whole part : Bytes} {start : Nat} {stop : Option Nat}
    (sliced : whole.slice? start stop = some part) :
    stop.getD whole.length = start + part.length := by
  obtain ⟨lower, _, _⟩ := slice?_eq_some_iff.mp sliced
  have measured := length_of_slice? sliced
  omega

/-- A successful slice ends inside its subject. -/
theorem le_length_of_slice? {whole part : Bytes} {start : Nat} {stop : Option Nat}
    (sliced : whole.slice? start stop = some part) : start + part.length ≤ whole.length := by
  obtain ⟨_, upper, _⟩ := slice?_eq_some_iff.mp sliced
  rw [← getD_of_slice? sliced]
  exact upper

/-- The octets a successful slice selects, in the list normal form, with the
span's own bounds already resolved away. -/
theorem toList_of_slice? {whole part : Bytes} {start : Nat} {stop : Option Nat}
    (sliced : whole.slice? start stop = some part) :
    part.toList = (whole.toList.drop start).take part.length := by
  obtain ⟨_, _, listed⟩ := slice?_eq_some_iff.mp sliced
  have unfolded := congrArg Bytes.toList listed
  rw [Bytes.toList_ofList, getD_of_slice? sliced] at unfolded
  rw [unfolded, show start + part.length - start = part.length by omega]

/--
Slicing a slice, in absolute coordinates.

The left side is the slice a range rule can actually compute — of the octets the
fact holds, at offsets relative to where they start — and the right side is the
slice of the whole blob it stands for.  Both are `some`, and they agree.
-/
theorem slice?_of_slice? {whole part : Bytes} {start : Nat} {stop : Option Nat}
    (outer : whole.slice? start stop = some part) {innerStart innerStop : Nat}
    (lower : start ≤ innerStart) (ordered : innerStart ≤ innerStop)
    (upper : innerStop ≤ start + part.length) :
    part.slice? (innerStart - start) (some (innerStop - start))
      = whole.slice? innerStart (some innerStop) := by
  obtain ⟨outerLower, outerUpper, listed⟩ := slice?_eq_some_iff.mp outer
  have known := getD_of_slice? outer
  have bounded : start + part.length ≤ whole.length := le_length_of_slice? outer
  rw [slice?_of_le (by simp; omega) (by simp; omega),
    slice?_of_le (by simp; omega) (by simp; omega)]
  congr 1
  rw [listed]
  simp only [toList_ofList, List.drop_take, List.drop_drop, List.take_take, Option.getD_some]
  rw [show start + (innerStart - start) = innerStart by omega,
    show min (innerStop - start - (innerStart - start))
      (stop.getD whole.length - start - (innerStart - start)) = innerStop - innerStart by omega]

end Bytes

/-!
## The pinning lemma

`Nucleus.CasRange.of_valid` above assumes `Model.IsSection`, which the design
deliberately does not adopt; this section is what replaces it, and it is what
the Rust `BlobFact::to_range_fact` rule actually leans on.

The argument is that an *unpinned* address is free, and freeness is refutable.
Suppose the store pins nothing at `hash`.  There are only finitely many
addresses, so a model reads only finitely many blobs — `Model.exists_length_bound`
— while `Bytes` is infinite, so some byte string is denoted by no address at
all.  Sending `hash` there is still a model, by `Model.update`, and the octets
it selects can be chosen to disagree with the literal on the right of the
equation.  Two models that disagree refute the equation.  So a valid equation
about `blake3 hash` forces the store to pin `hash`; and a pinned address is read
back to a checked pair, which already carries `name blob = hash`, so the naming
claim follows with no section property anywhere.

### The one shape this misses

Exactly one family of equations survives an unpinned address:
`slice (blake3 h) [k, k) = bytes ""`, an empty closed window over no octets.
Every byte string at least `k` octets long selects nothing there, so at `k = 0`
the equation is valid in *every* model of *every* store, while `CasRange.Valid`
still asks for a blob named `h` — which is a claim about the naming function
that nothing licenses.  `CasRange.Contentful` is the side condition that
excludes it, `exists_valid_not_casRange` is the counterexample that shows the
condition cannot be dropped, and `Nucleus.BlobEq.valid_emptyWindow` is the
equation itself.  The Rust rule accepts this shape and is unsound on it.
-/

/--
A byte string, longer than `bound`, whose `span` selects something other than
`blob`.

This is the whole construction behind the pinning lemma, and the case analysis
is the content.  An open span is refuted by length, since a long enough subject
has a long enough tail; a backwards closed span is refuted outright, since it
selects nothing whatever the subject; a closed span of the wrong width is
refuted by length again; and a closed span of the right *nonzero* width is
refuted by content, by filling the subject with an octet the first octet of
`blob` is not.  The excluded case — a closed span of width zero over the empty
byte string — is `CasRange.Contentful`, and it is genuinely not refutable.

The length bound is how freshness is bought: `Model.exists_length_bound` turns
it into "no address denotes this".
-/
theorem exists_fresh_slice?_ne (span : BlobSpan) (blob : Bytes) (bound : Nat)
    (contentful : span.stop ≠ some span.start ∨ blob ≠ Bytes.empty) :
    ∃ whole : Bytes, bound < whole.length ∧ whole.slice? span.start span.stop ≠ some blob := by
  classical
  cases stop : span.stop with
  | none =>
      refine ⟨Bytes.replicate (bound + span.start + blob.length + 1) 0,
        by simp only [Bytes.length_replicate]; omega, ?_⟩
      intro sliced
      have measured := Bytes.length_of_slice? sliced
      simp only [Option.getD_none, Bytes.length_replicate] at measured
      omega
  | some limit =>
      by_cases lower : span.start ≤ limit
      · by_cases width : blob.length = limit - span.start
        · have nonempty : blob.toList ≠ [] := by
            intro empty
            have zero : blob.length = 0 := by
              rw [Bytes.length_eq_toList_length, empty]
              rfl
            refine contentful.elim (fun different ↦ different ?_) fun different ↦ different ?_
            · rw [stop]
              congr 1
              omega
            · exact Bytes.ext (by rw [empty, Bytes.toList_empty])
          obtain ⟨head, rest, listed⟩ := List.exists_cons_of_ne_nil nonempty
          refine ⟨Bytes.replicate (bound + limit + 1) (if head = 0 then 1 else 0),
            by simp only [Bytes.length_replicate]; omega, ?_⟩
          intro sliced
          rw [Bytes.slice?_of_le (by simpa using lower)
            (by simp only [Option.getD_some, Bytes.length_replicate]; omega)] at sliced
          simp only [Option.getD_some, Bytes.toList_replicate, List.drop_replicate,
            List.take_replicate] at sliced
          have member : head ∈ List.replicate (min (limit - span.start)
              (bound + limit + 1 - span.start)) (if head = 0 then 1 else 0) := by
            rw [← Bytes.toList_ofList (List.replicate _ _), Option.some.inj sliced, listed]
            exact List.mem_cons_self
          have equal := List.eq_of_mem_replicate member
          split at equal <;> simp_all
        · refine ⟨Bytes.replicate (bound + limit + 1) 0,
            by simp only [Bytes.length_replicate]; omega, ?_⟩
          intro sliced
          have measured := Bytes.length_of_slice? sliced
          simp only [Option.getD_some] at measured
          exact width measured
      · refine ⟨Bytes.replicate (bound + 1) 0,
          by simp only [Bytes.length_replicate]; omega, ?_⟩
        rw [Bytes.slice?_eq_none (by simp only [Option.getD_some]; tauto)]
        simp

/--
A range claim says something about the naming function unless it is the empty
closed window over no octets.

`slice (blake3 h) [k, k) = bytes ""` is the sole shape a *free* address
satisfies, so it is the sole shape from which no pin — and hence no naming
claim — can be recovered.  Everything else, including every open span and every
window of nonzero width, is contentful.
-/
def CasRange.Contentful (span : BlobSpan) (blob : Bytes) : Prop :=
  span.stop ≠ some span.start ∨ blob ≠ Bytes.empty

/-- A range reaching the end of the blob is always contentful: it pins a length
even when it carries no octets. -/
theorem CasRange.contentful_of_open {span : BlobSpan} {blob : Bytes}
    (reaches : span.stop = none) : CasRange.Contentful span blob :=
  Or.inl (by rw [reaches]; simp)

/-- A range carrying octets is always contentful. -/
theorem CasRange.contentful_of_ne_empty {span : BlobSpan} {blob : Bytes}
    (carries : blob ≠ Bytes.empty) : CasRange.Contentful span blob :=
  Or.inr carries

section Pinning

variable [Name Bytes O256] {cas : Cas}

/-- Read an equality of range-fact shape as a statement about `sigma` in one
model.  Every proof below starts here, and the `sliceOf` normalisation is why
the whole-blob and sub-range shapes need no separate treatment. -/
theorem BlobEq.slice?_of_valid_blake3 {hash : O256} {span : BlobSpan} {blob : Bytes}
    (valid : (BlobEq.mk ((BlobExpr.blake3 hash).sliceOf span) (.bytes blob)).Valid cas)
    (model : Model cas) : (model.sigma hash).slice? span.start span.stop = some blob := by
  have denoted := valid model
  rw [BlobExpr.denote_sliceOf, BlobExpr.denote_slice, BlobExpr.denote_blake3, Option.bind_some,
    BlobExpr.denote_bytes] at denoted
  exact denoted

/--
THE PINNING LEMMA: a contentful equality about `blake3 hash` forces the store to
pin `hash`.

This is the step the Rust `BlobFact::to_range_fact` rule takes and the Lean
theory had no statement for.  It needs no section property: an unpinned address
is free, and `Model.update` spends that freedom on a byte string chosen by
`exists_fresh_slice?_ne` to select the wrong octets, which contradicts an
equality that holds in *every* model.  The standing assumption appears because
the argument needs a model to move.
-/
theorem Cas.pins_of_valid_blake3 [standing : Nonempty (Model cas)] {hash : O256}
    {span : BlobSpan} {blob : Bytes} (contentful : CasRange.Contentful span blob)
    (valid : (BlobEq.mk ((BlobExpr.blake3 hash).sliceOf span) (.bytes blob)).Valid cas) :
    cas.Pins hash := by
  by_contra unpinned
  obtain ⟨model⟩ := standing
  obtain ⟨bound, bounded⟩ := model.exists_length_bound
  obtain ⟨whole, long, different⟩ := exists_fresh_slice?_ne span blob bound contentful
  have fresh : whole ∉ Set.range model.sigma := by
    rintro ⟨address, denoted⟩
    have measured := bounded address
    rw [denoted] at measured
    omega
  have twisted := BlobEq.slice?_of_valid_blake3 valid (model.update whole unpinned fresh)
  rw [Model.update_sigma_self] at twisted
  exact different twisted

/--
RULE: recover a range fact from an equality, for a *pinned* address — with no
section property.

This is the sibling of `Nucleus.CasRange.of_valid` the design actually wants.
The pin does all the work: every model reads `hash` back to the checked pair's
blob, so the equality is a statement about *that* blob, and the pair already
carries `name blob = hash`.  A model is still needed, because the equality is
quantified over models and says nothing when there are none; that is the
standing assumption, not an extra premise of this rule.
-/
theorem CasRange.of_valid_of_pins (model : Model cas) {hash : O256} {span : BlobSpan}
    {blob : Bytes} (pinned : cas.Pins hash)
    (valid : (BlobEq.mk ((BlobExpr.blake3 hash).sliceOf span) (.bytes blob)).Valid cas) :
    CasRange.Valid hash span blob := by
  obtain ⟨pair, member, addressed⟩ := pinned
  refine ⟨pair.blob, pair.valid_hash.trans addressed, ?_⟩
  have sliced := BlobEq.slice?_of_valid_blake3 valid model
  rwa [← addressed, model.extendsCas pair member] at sliced

/--
RULE: recover a range fact from a contentful equality, with no section property
and no pin supplied — the pin is derived.

This is `Nucleus.CasRange.of_valid` with `Model.IsSection` traded for
`CasRange.Contentful`, and it is the theorem the Rust rule should cite.  The
trade is not free in one direction only: the section property would also cover
the empty closed window, which is false without it; see
`exists_valid_not_casRange`.
-/
theorem CasRange.of_valid_of_contentful [Nonempty (Model cas)] {hash : O256} {span : BlobSpan}
    {blob : Bytes} (contentful : CasRange.Contentful span blob)
    (valid : (BlobEq.mk ((BlobExpr.blake3 hash).sliceOf span) (.bytes blob)).Valid cas) :
    CasRange.Valid hash span blob :=
  CasRange.of_valid_of_pins (Classical.arbitrary (Model cas))
    (Cas.pins_of_valid_blake3 contentful valid) valid

/--
The empty closed window is valid at *every* address of *every* store.

Nothing is pinned, nothing is assumed, and nothing is learnt: every byte string
selects no octets on `[0, 0)`.  This is the equation that makes
`CasRange.Contentful` a genuine side condition rather than bookkeeping.
-/
theorem BlobEq.valid_emptyWindow (cas : Cas) (hash : O256) :
    (BlobEq.mk ((BlobExpr.blake3 hash).sliceOf ⟨0, some 0⟩) (.bytes Bytes.empty)).Valid cas := by
  rw [BlobEq.valid_mk_iff]
  intro model
  rw [BlobExpr.denote_sliceOf, BlobExpr.denote_slice, BlobExpr.denote_blake3, Option.bind_some,
    BlobExpr.denote_bytes, Bytes.slice?_of_le (by simp) (by simp)]
  rfl

end Pinning

/-!
## The range rules

`Nucleus.CasRange.Valid` is a claim about the naming function alone: *some* blob
named `hash` carries `blob` at `span`.  The three rules the Rust `CasRangeFact`
offers are stated over it here, each with the side conditions the Rust actually
enforces.

Two of them need a hypothesis the Rust crate carries as a standing assumption
rather than a premise, and it is worth being explicit about which.  `slice`
needs nothing: one witness serves the sub-range too.  `fuse` and the length rule
need `Name.name` to be *injective*, because `CasRange.Valid` only says that some
blob named `hash` exists, and two facts about one address could otherwise be
witnessed by two different blobs — see `exists_valid_fuse_not_valid`, which
fuses two true facts into a false one under a colliding naming function.  This
is the same hypothesis `Nucleus.BlobEq.valid_ofCasRange` already takes, and it is
collision-freedom in its idealised, store-independent form.
-/

section RangeRules

variable [Name Bytes O256]

/-- Under an injective naming function a range claim determines its octets: the
address determines the blob, and slicing is a function. -/
theorem CasRange.eq_of_valid (injective : Function.Injective (Name.name : Bytes → O256))
    {hash : O256} {span : BlobSpan} {left right : Bytes}
    (leftFact : CasRange.Valid hash span left) (rightFact : CasRange.Valid hash span right) :
    left = right := by
  obtain ⟨leftWhole, leftNamed, leftSliced⟩ := leftFact
  obtain ⟨rightWhole, rightNamed, rightSliced⟩ := rightFact
  have same : leftWhole = rightWhole := injective (leftNamed.trans rightNamed.symm)
  subst same
  exact Option.some.inj (leftSliced.symm.trans rightSliced)

/--
RULE: narrow a range fact to a sub-range, in absolute blob coordinates.

The four hypotheses are exactly the four refusals of the Rust `slice`.
`reaches` is the one that is easy to get wrong: an open upper bound asks where
the blob *ends*, and only a fact whose own upper bound is open knows that, so a
closed fact may not be widened into an open one — `exists_valid_slice_not_valid`
is the counterexample.  The remaining three are the containment of the request
in the octets the fact already holds, and they are what makes the local slice on
the left of the conclusion succeed.

The conclusion carries that local slice on purpose: it is the byte string the
Rust rule computes, so the theorem says both that the computation succeeds and
that its result is a fact.  No injectivity is needed, because the witness of the
premise witnesses the conclusion too.
-/
theorem CasRange.valid_slice {hash : O256} {span : BlobSpan} {blob : Bytes}
    (fact : CasRange.Valid hash span blob) {sub : BlobSpan}
    (reaches : sub.stop = none → span.stop = none)
    (lower : span.start ≤ sub.start)
    (ordered : sub.start ≤ sub.stop.getD (span.start + blob.length))
    (upper : sub.stop.getD (span.start + blob.length) ≤ span.start + blob.length) :
    ∃ part : Bytes,
      blob.slice? (sub.start - span.start)
          (some (sub.stop.getD (span.start + blob.length) - span.start)) = some part ∧
        CasRange.Valid hash sub part := by
  obtain ⟨whole, named, sliced⟩ := fact
  have known : span.stop.getD whole.length = span.start + blob.length := Bytes.getD_of_slice? sliced
  have bounded : span.start + blob.length ≤ whole.length := Bytes.le_length_of_slice? sliced
  have agree : sub.stop.getD whole.length = sub.stop.getD (span.start + blob.length) := by
    cases subStop : sub.stop with
    | none =>
        rw [reaches subStop] at known
        simp only [Option.getD_none] at known ⊢
        omega
    | some limit => simp
  have inner := Bytes.slice?_of_slice? sliced lower ordered upper
  have outer : whole.slice? sub.start sub.stop
      = whole.slice? sub.start (some (sub.stop.getD (span.start + blob.length))) :=
    Bytes.slice?_congr (by simpa using agree)
  have defined : whole.slice? sub.start (some (sub.stop.getD (span.start + blob.length)))
      = some (Bytes.ofList ((whole.toList.drop sub.start).take
        (sub.stop.getD (span.start + blob.length) - sub.start))) :=
    Bytes.slice?_of_le (by simpa using ordered) (by simp; omega)
  exact ⟨_, inner.trans defined, whole, named, outer.trans defined⟩

/-- `CasRange.valid_slice` on the shape a rule consumes: the narrowed octets are
supplied, rather than existentially produced. -/
theorem CasRange.valid_slice_of_slice? {hash : O256} {span : BlobSpan} {blob : Bytes}
    (fact : CasRange.Valid hash span blob) {sub : BlobSpan} {part : Bytes}
    (reaches : sub.stop = none → span.stop = none)
    (lower : span.start ≤ sub.start)
    (ordered : sub.start ≤ sub.stop.getD (span.start + blob.length))
    (upper : sub.stop.getD (span.start + blob.length) ≤ span.start + blob.length)
    (narrowed : blob.slice? (sub.start - span.start)
      (some (sub.stop.getD (span.start + blob.length) - span.start)) = some part) :
    CasRange.Valid hash sub part := by
  obtain ⟨other, sliced, valid⟩ := CasRange.valid_slice fact reaches lower ordered upper
  rwa [Option.some.inj (sliced.symm.trans narrowed)] at valid

/--
RULE: fuse two facts about one blob whose ranges overlap or touch.

`ordered` picks which operand starts first, which the Rust rule decides by
comparison; the statement is otherwise symmetric.  `touching` is the refusal of
a gap, and it is load-bearing rather than defensive: the fused octets are the
first fact's followed by whatever of the second's the first does not already
cover, and a gap would leave octets in the union that neither operand carries,
so the formula would name the wrong byte string.  `fusedStart` and `fusedStop`
are the Rust rule's output shape — the earlier start, the later end, and an open
upper bound exactly when either operand has one, which is what makes a prefix
fused with a suffix a whole-blob fact.  `spliced` is the Rust seam, clamped
exactly as the Rust clamps it, so that a contained second operand contributes
nothing and the one formula covers all three of the Rust's branches.

Injectivity is not decoration.  Without it the two premises may be witnessed by
two *different* blobs that merely share an address, and their union need not be
any blob at all: `exists_valid_fuse_not_valid` is that counterexample.
-/
theorem CasRange.valid_fuse (injective : Function.Injective (Name.name : Bytes → O256))
    {hash : O256} {leftSpan rightSpan fused : BlobSpan} {leftBlob rightBlob seam : Bytes}
    (leftFact : CasRange.Valid hash leftSpan leftBlob)
    (rightFact : CasRange.Valid hash rightSpan rightBlob)
    (ordered : leftSpan.start ≤ rightSpan.start)
    (touching : rightSpan.start ≤ leftSpan.start + leftBlob.length)
    (fusedStart : fused.start = min leftSpan.start rightSpan.start)
    (fusedStop : fused.stop =
      if leftSpan.stop = none ∨ rightSpan.stop = none then none
      else some (max (leftSpan.start + leftBlob.length) (rightSpan.start + rightBlob.length)))
    (spliced : rightBlob.slice?
        (min (leftSpan.start + leftBlob.length - rightSpan.start) rightBlob.length) none
      = some seam) :
    CasRange.Valid hash fused (leftBlob.append seam) := by
  obtain ⟨whole, leftNamed, leftSliced⟩ := leftFact
  obtain ⟨rightWhole, rightNamed, rightSliced⟩ := rightFact
  have same : rightWhole = whole := injective (rightNamed.trans leftNamed.symm)
  rw [same] at rightSliced
  rw [Nat.min_eq_left ordered] at fusedStart
  have leftKnown : leftSpan.stop.getD whole.length = leftSpan.start + leftBlob.length :=
    Bytes.getD_of_slice? leftSliced
  have rightKnown : rightSpan.stop.getD whole.length = rightSpan.start + rightBlob.length :=
    Bytes.getD_of_slice? rightSliced
  have leftBound : leftSpan.start + leftBlob.length ≤ whole.length :=
    Bytes.le_length_of_slice? leftSliced
  have rightBound : rightSpan.start + rightBlob.length ≤ whole.length :=
    Bytes.le_length_of_slice? rightSliced
  have fusedEnd : fused.stop.getD whole.length
      = max (leftSpan.start + leftBlob.length) (rightSpan.start + rightBlob.length) := by
    rw [fusedStop]
    split
    · rename_i openEnd
      simp only [Option.getD_none]
      rcases openEnd with reaches | reaches
      · have resolved : whole.length = leftSpan.start + leftBlob.length := by
          rw [reaches] at leftKnown
          exact leftKnown
        omega
      · have resolved : whole.length = rightSpan.start + rightBlob.length := by
          rw [reaches] at rightKnown
          exact rightKnown
        omega
    · simp
  have leftList := Bytes.toList_of_slice? leftSliced
  have rightList := Bytes.toList_of_slice? rightSliced
  have seamList : seam.toList
      = (whole.toList.drop (leftSpan.start + leftBlob.length)).take
        (max (leftSpan.start + leftBlob.length) (rightSpan.start + rightBlob.length)
          - (leftSpan.start + leftBlob.length)) := by
    have unfolded := Bytes.toList_of_slice? spliced
    have measured := Bytes.length_of_slice? spliced
    simp only [Option.getD_none] at measured
    rw [unfolded, rightList, measured, List.drop_take, List.take_take, List.drop_drop]
    rw [show min (rightBlob.length
          - min (leftSpan.start + leftBlob.length - rightSpan.start) rightBlob.length)
          (rightBlob.length
            - min (leftSpan.start + leftBlob.length - rightSpan.start) rightBlob.length)
        = max (leftSpan.start + leftBlob.length) (rightSpan.start + rightBlob.length)
          - (leftSpan.start + leftBlob.length) by omega]
    rcases Nat.le_total (leftSpan.start + leftBlob.length)
      (rightSpan.start + rightBlob.length) with growing | shrinking
    · rw [show rightSpan.start
        + min (leftSpan.start + leftBlob.length - rightSpan.start) rightBlob.length
        = leftSpan.start + leftBlob.length by omega]
    · rw [show max (leftSpan.start + leftBlob.length) (rightSpan.start + rightBlob.length)
        - (leftSpan.start + leftBlob.length) = 0 by omega]
      simp
  refine ⟨whole, leftNamed, ?_⟩
  rw [fusedStart, Bytes.slice?_of_le (by omega) (by omega)]
  apply congrArg
  apply Bytes.ext
  rw [Bytes.toList_ofList, Bytes.toList_append, leftList, seamList, fusedEnd,
    show max (leftSpan.start + leftBlob.length) (rightSpan.start + rightBlob.length)
        - leftSpan.start
      = leftBlob.length + (max (leftSpan.start + leftBlob.length)
        (rightSpan.start + rightBlob.length) - (leftSpan.start + leftBlob.length)) by omega,
    List.take_add, List.drop_drop]

/--
RULE: a range reaching the end of the blob pins the blob's length.

Only an open upper bound reaches it, which is the whole of the Rust
`blob_len` returning `None` otherwise: a closed range's own end is not the
blob's, and no witness of the fact is obliged to agree on the length —
`exists_valid_length_ne` exhibits two of different lengths.  The empty case is
the data-free length claim: a fact about `n..` carrying no octets says exactly
that the blob is `n` octets long.
-/
theorem CasRange.exists_length_of_valid_open {hash : O256} {span : BlobSpan} {blob : Bytes}
    (reaches : span.stop = none) (fact : CasRange.Valid hash span blob) :
    ∃ whole : Bytes, Name.name whole = hash ∧ whole.length = span.start + blob.length := by
  obtain ⟨whole, named, sliced⟩ := fact
  refine ⟨whole, named, ?_⟩
  have known := Bytes.getD_of_slice? sliced
  rw [reaches] at known
  exact known

/-- The length rule as a statement about *every* blob named `hash`, which is
what "the blob's length" means once the naming function is injective. -/
theorem CasRange.length_of_valid_open (injective : Function.Injective (Name.name : Bytes → O256))
    {hash : O256} {span : BlobSpan} {blob whole : Bytes} (reaches : span.stop = none)
    (fact : CasRange.Valid hash span blob) (named : Name.name whole = hash) :
    whole.length = span.start + blob.length := by
  obtain ⟨other, otherNamed, measured⟩ := CasRange.exists_length_of_valid_open reaches fact
  rw [← injective (otherNamed.trans named.symm)]
  exact measured

end RangeRules

/-!
## Range traps

One naming function serves every counterexample below: it answers `1` on the
byte strings beginning `ab` and `0` on all the others.  It is not injective, and
it is not surjective, and each range rule loses exactly one of its side
conditions to one of those two failures.
-/

section RangeTraps

/-- A naming function that separates only the byte strings beginning `ab`.  It
is deliberately neither injective nor surjective: `0` collides massively, and
no byte string is named `2` at all. -/
local instance prefixName : Name Bytes O256 where
  name blob := if blob.toList.take 2 = [97, 98] then 1 else 0

/-- Only a byte string beginning `ab` is named `1`. -/
theorem name_of_prefix {whole : Bytes} (named : Name.name whole = (1 : O256)) :
    whole.toList.take 2 = [97, 98] := by
  by_contra different
  rw [show Name.name whole = if whole.toList.take 2 = [97, 98] then (1 : O256) else 0 from rfl,
    if_neg different] at named
  exact absurd named (by decide)

/-- No byte string beginning `ab` is named `0`. -/
theorem name_of_not_prefix {whole : Bytes} (named : Name.name whole = (0 : O256)) :
    whole.toList.take 2 ≠ [97, 98] := by
  intro prefixed
  rw [show Name.name whole = if whole.toList.take 2 = [97, 98] then (1 : O256) else 0 from rfl,
    if_pos prefixed] at named
  exact absurd named (by decide)

/-- `ab` is named `1`. -/
theorem name_ab : Name.name (Bytes.ofList [97, 98]) = (1 : O256) := by
  change (if (Bytes.ofList [97, 98]).toList.take 2 = [97, 98] then (1 : O256) else 0) = 1
  simp

/-- `abc` is named `1` as well: the naming function reads two octets. -/
theorem name_abc : Name.name (Bytes.ofList [97, 98, 99]) = (1 : O256) := by
  change (if (Bytes.ofList [97, 98, 99]).toList.take 2 = [97, 98] then (1 : O256) else 0) = 1
  simp

/-- `aa` is named `0`. -/
theorem name_aa : Name.name (Bytes.ofList [97, 97]) = (0 : O256) := by
  change (if (Bytes.ofList [97, 97]).toList.take 2 = [97, 98] then (1 : O256) else 0) = 0
  simp

/-- `bb` is named `0`, colliding with `aa`. -/
theorem name_bb : Name.name (Bytes.ofList [98, 98]) = (0 : O256) := by
  change (if (Bytes.ofList [98, 98]).toList.take 2 = [97, 98] then (1 : O256) else 0) = 0
  simp

/-- No byte string is named `2`: this naming function is not surjective, which
is what makes an unpinned naming claim refutable. -/
theorem unnamed_two (whole : Bytes) : Name.name whole ≠ (2 : O256) := by
  change (if whole.toList.take 2 = [97, 98] then (1 : O256) else 0) ≠ 2
  split <;> decide

/--
COUNTEREXAMPLE: the empty closed window is valid at an unpinned address and yet
names nothing.

Every hypothesis of `Nucleus.CasRange.of_valid_of_contentful` except
`CasRange.Contentful` holds — the equality is valid over the empty store, which
is collision-free and so has a model — and the range claim is false, because no
byte string is named `2`.  So `CasRange.Contentful` cannot be dropped, and the
Rust `BlobFact::to_range_fact` is unsound on exactly this shape: it mints a
naming claim about an address that need name nothing.
-/
theorem exists_valid_not_casRange :
    Nonempty (Model (Cas.empty : Cas)) ∧
      (BlobEq.mk ((BlobExpr.blake3 2).sliceOf ⟨0, some 0⟩) (.bytes Bytes.empty)).Valid Cas.empty ∧
      ¬ Cas.empty.Pins (2 : O256) ∧
      ¬ CasRange.Valid (2 : O256) ⟨0, some 0⟩ Bytes.empty :=
  ⟨Cas.nonempty_model_of_collisionFree Cas.collisionFree_empty,
    BlobEq.valid_emptyWindow Cas.empty 2, Cas.not_pins_empty 2,
    fun ⟨whole, named, _⟩ ↦ unnamed_two whole named⟩

/--
COUNTEREXAMPLE: `slice` genuinely needs its open-upper-bound side condition.

A fact about `0..1` of a blob named `1` is true, and the same octets claimed for
`0..` are false: the open request asks where the blob ends, and this fact does
not know.  Dropping `reaches` from `Nucleus.CasRange.valid_slice` would derive
the second from the first.
-/
theorem exists_valid_slice_not_valid :
    CasRange.Valid (1 : O256) ⟨0, some 1⟩ (Bytes.ofList [97]) ∧
      ¬ CasRange.Valid (1 : O256) ⟨0, none⟩ (Bytes.ofList [97]) := by
  refine ⟨⟨Bytes.ofList [97, 98], name_ab, ?_⟩, ?_⟩
  · rw [Bytes.slice?_of_le (by simp) (by simp)]
    rfl
  · rintro ⟨whole, named, sliced⟩
    simp only [Bytes.slice?_zero_none] at sliced
    rw [Option.some.inj sliced] at named
    have prefixed := name_of_prefix named
    simp at prefixed

/--
COUNTEREXAMPLE: `fuse` genuinely needs injectivity of the naming function.

`a` at `0..1` and `b` at `1..2` are both true of the address `0`, witnessed by
`aa` and by `bb`; every other hypothesis of `Nucleus.CasRange.valid_fuse` holds,
with the ranges touching at `1` and the seam empty.  Their union, `ab` at
`0..2`, is false: a byte string beginning `ab` is named `1`, never `0`.  So two
facts about one address say nothing about each other once that address is shared
by two blobs, and fusing them is unsound under a collision.
-/
theorem exists_valid_fuse_not_valid :
    CasRange.Valid (0 : O256) ⟨0, some 1⟩ (Bytes.ofList [97]) ∧
      CasRange.Valid (0 : O256) ⟨1, some 2⟩ (Bytes.ofList [98]) ∧
      (Bytes.ofList [98]).slice? 0 none = some (Bytes.ofList [98]) ∧
      ¬ CasRange.Valid (0 : O256) ⟨0, some 2⟩ ((Bytes.ofList [97]).append (Bytes.ofList [98])) := by
  refine ⟨⟨Bytes.ofList [97, 97], name_aa, ?_⟩, ⟨Bytes.ofList [98, 98], name_bb, ?_⟩, by simp, ?_⟩
  · rw [Bytes.slice?_of_le (by simp) (by simp)]
    rfl
  · rw [Bytes.slice?_of_le (by simp) (by simp)]
    rfl
  · rintro ⟨whole, named, sliced⟩
    refine name_of_not_prefix named ?_
    obtain ⟨_, _, listed⟩ := Bytes.slice?_eq_some_iff.mp sliced
    have unfolded := congrArg Bytes.toList listed
    simp only [Bytes.toList_append, Bytes.toList_ofList, Option.getD_some, Nat.sub_zero,
      List.drop_zero, List.cons_append, List.nil_append] at unfolded
    exact unfolded.symm

/--
COUNTEREXAMPLE: a closed range does not pin the blob's length.

`ab` at `0..2` is a true fact about the address `1`, witnessed by `ab` and by
`abc`, whose lengths differ.  So the fact's own data settles no length, which is
why the Rust `blob_len` answers `None` for a closed range instead of mistaking
the range's end for the blob's.
-/
theorem exists_valid_length_ne :
    Name.name (Bytes.ofList [97, 98]) = (1 : O256) ∧
      (Bytes.ofList [97, 98]).slice? 0 (some 2) = some (Bytes.ofList [97, 98]) ∧
      Name.name (Bytes.ofList [97, 98, 99]) = (1 : O256) ∧
      (Bytes.ofList [97, 98, 99]).slice? 0 (some 2) = some (Bytes.ofList [97, 98]) ∧
      (Bytes.ofList [97, 98]).length ≠ (Bytes.ofList [97, 98, 99]).length := by
  refine ⟨name_ab, ?_, name_abc, ?_, by simp⟩
  · rw [Bytes.slice?_of_le (by simp) (by simp)]
    rfl
  · rw [Bytes.slice?_of_le (by simp) (by simp)]
    rfl

end RangeTraps

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
