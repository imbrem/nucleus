import Nucleus.Hol.Ethane.Arena.OneBased
import Mathlib.Logic.Relation

/-!
# Equality classes in one-based Ethane arenas

The optional `eq` member is a union-find parent, but its logical meaning is
just equality of its endpoints.  Consequently a parent cycle is harmless:
the undirected equivalence closure is still the represented equality class.

This file specifies the two Rust lookup APIs. `FindResult` is the immutable
query. `CompressionResult` is the mutable query: it may rewrite parents, but
must preserve every equality class and make the returned representative a
root.  The Rust implementation chooses the least member when it encounters a
cycle; `FindResult.canonical` records that choice without making acyclicity an
invariant.
-/

namespace Nucleus.Hol.Ethane.OneBased

set_option relaxedAutoImplicit true

/-- One directed equality-parent edge stored in an arena row. -/
def EqEdge (arena : Arena) (left right : Ref) : Prop :=
  arena.eq? left = some right

/-- The equality class represented by the parent graph. -/
def EqClass (arena : Arena) : Ref → Ref → Prop :=
  Relation.EqvGen (EqEdge arena)

namespace EqClass

theorem edge (edge : EqEdge arena left right) : EqClass arena left right :=
  .rel _ _ edge

@[refl] theorem refl (reference : Ref) : EqClass arena reference reference :=
  Relation.EqvGen.refl reference

@[symm] theorem symm (connected : EqClass arena left right) :
    EqClass arena right left :=
  Relation.EqvGen.symm _ _ connected

@[trans] theorem trans (leftMiddle : EqClass arena left middle)
    (middleRight : EqClass arena middle right) : EqClass arena left right :=
  Relation.EqvGen.trans _ _ _ leftMiddle middleRight

/-- Sound parent edges make their entire equivalence closure sound. -/
theorem sound {R : Ref → Ref → Prop}
    (edgeSound : ∀ {left right}, EqEdge arena left right → R left right)
    (refl : ∀ reference, R reference reference)
    (symm : ∀ {left right}, R left right → R right left)
    (trans : ∀ {left middle right}, R left middle → R middle right → R left right)
    (connected : EqClass arena left right) : R left right := by
  induction connected with
  | rel left right edge => exact edgeSound edge
  | refl reference => exact refl reference
  | symm left right _ ih => exact symm ih
  | trans left middle right _ _ leftRight middleRight =>
      exact trans leftRight middleRight

end EqClass

/-- Directed reachability along parent pointers, including zero steps. -/
abbrev ParentReach (arena : Arena) := Relation.ReflTransGen (EqEdge arena)

/-- A reference lies on a nonempty directed parent cycle. -/
def OnParentCycle (arena : Arena) (reference : Ref) : Prop :=
  Relation.TransGen (EqEdge arena) reference reference

/-- Postcondition of immutable `Kernel::find`.

An ordinary tree stops at a row without a parent. A cyclic parent component
stops at the least member of its cycle, matching Rust. -/
structure FindResult (arena : Arena) (start representative : Ref) : Prop where
  connected : EqClass arena start representative
  stopped : arena.eq? representative = none ∨ OnParentCycle arena representative
  canonical : OnParentCycle arena representative →
    ∀ member, ParentReach arena representative member →
      ParentReach arena member representative → representative ≤ member

namespace FindResult

theorem equality (result : FindResult arena start representative)
    {R : Ref → Ref → Prop}
    (edgeSound : ∀ {left right}, EqEdge arena left right → R left right)
    (refl : ∀ reference, R reference reference)
    (symm : ∀ {left right}, R left right → R right left)
    (trans : ∀ {left middle right}, R left middle → R middle right → R left right) :
    R start representative :=
  result.connected.sound edgeSound refl symm trans

end FindResult

/-- Postcondition of mutable `Kernel::find_mut`.

Path compression is permitted to discard redundant parent edges. Its exact
logical obligation is preservation of all equality classes, followed by an
acyclic root at the representative selected by the pre-compression lookup. -/
structure CompressionResult (before after : Arena) (start representative : Ref) : Prop where
  found : FindResult before start representative
  classes : ∀ left right, EqClass before left right ↔ EqClass after left right
  root : after.eq? representative = none

namespace CompressionResult

theorem connectedAfter (result : CompressionResult before after start representative) :
    EqClass after start representative :=
  (result.classes start representative).mp result.found.connected

/-- Compression preserves semantic equality whenever the original parent
edges were sound. -/
theorem equality {R : Ref → Ref → Prop}
    (result : CompressionResult before after start representative)
    (edgeSound : ∀ {left right}, EqEdge before left right → R left right)
    (refl : ∀ reference, R reference reference)
    (symm : ∀ {left right}, R left right → R right left)
    (trans : ∀ {left middle right}, R left middle → R middle right → R left right) :
    R start representative :=
  result.found.equality edgeSound refl symm trans

end CompressionResult

/-- Joining two classes is sound exactly when the new bridge is sound and no
previous class changes its meaning. This is the logical contract of every
Rust rule that writes an `eq` parent. -/
structure UnionResult (before after : Arena) (left right : Ref) where
  leftRepresentative : Ref
  rightRepresentative : Ref
  leftFind : FindResult before left leftRepresentative
  rightFind : FindResult before right rightRepresentative
  joined : EqClass after left right
  oldClasses : ∀ {a b}, EqClass before a b → EqClass after a b
  noOtherMerge : ∀ {a b}, EqClass after a b →
    EqClass before a b ∨
      (EqClass before a left ∧ EqClass before right b) ∨
      (EqClass before a right ∧ EqClass before left b)

end Nucleus.Hol.Ethane.OneBased
