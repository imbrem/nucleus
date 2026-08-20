import Nucleus.HolE.Named.Unsorted
import Mathlib.Data.List.OfFn

/-!
# Finite contexts for unsorted named HolE

A context is canonically a list: list order records presentation order while
membership supplies the logical assumptions.  `Indexed` and `OrderedMap` are
implementation-oriented views of the same finite data.
-/

namespace Nucleus.HolE.Named.Unsorted.Context

universe u v
set_option relaxedAutoImplicit true

abbrev ListCtx (Sig : Signature) := List (Expr Sig)

/-- A finite context addressed by dense indices. -/
structure Indexed (Sig : Signature) where
  size : Nat
  term : Fin size → Expr Sig

namespace Indexed

/-- Read an indexed context in index order. -/
def toList (context : Indexed Sig) : ListCtx Sig :=
  List.ofFn context.term

/-- Address a list by `Fin list.length`. -/
def ofList (context : ListCtx Sig) : Indexed Sig where
  size := context.length
  term := context.get

@[simp] theorem toList_ofList (context : ListCtx Sig) :
    (ofList context).toList = context := by
  simp [ofList, toList]

theorem ext {left right : Indexed Sig} (size : left.size = right.size)
    (terms : ∀ i, left.term i = right.term (size ▸ i)) : left = right := by
  cases left
  cases right
  cases size
  congr
  funext i
  exact terms i

end Indexed

/-- A finite partial map together with an explicit order of all its keys.

`support` says that `key` enumerates exactly the domain of `lookup`; `nodup`
makes that enumeration unique.  Values are obtained from `lookup`, so the map
and ordered views cannot disagree. -/
structure OrderedMap (Sig : Signature) (Name : Type v) where
  size : Nat
  key : Fin size → Name
  lookup : Name → Option (Expr Sig)
  nodup : Function.Injective key
  support : ∀ name, lookup name ≠ none ↔ ∃ i, key i = name

namespace OrderedMap

theorem lookup_key_ne_none (context : OrderedMap Sig Name) (i : Fin context.size) :
    context.lookup (context.key i) ≠ none :=
  (context.support (context.key i)).2 ⟨i, rfl⟩

/-- The term stored at one position in the declared key order. -/
def term (context : OrderedMap Sig Name) (i : Fin context.size) : Expr Sig :=
  match equality : context.lookup (context.key i) with
  | some value => value
  | none => False.elim ((lookup_key_ne_none context i) equality)

/-- Forget keys but retain their declared order. -/
noncomputable def toIndexed (context : OrderedMap Sig Name) : Indexed Sig where
  size := context.size
  term := context.term

/-- Read an ordered finite map as a list. -/
noncomputable def toList (context : OrderedMap Sig Name) : ListCtx Sig :=
  context.toIndexed.toList

/-- Give a dense context its canonical `Fin size` keys. -/
def ofIndexed (context : Indexed Sig) : OrderedMap Sig (Fin context.size) where
  size := context.size
  key := id
  lookup := fun i => some (context.term i)
  nodup := fun _ _ equality => equality
  support := fun name => by simp

/-- Give a list its canonical dense keys. -/
def ofList (context : ListCtx Sig) : OrderedMap Sig (Fin context.length) :=
  ofIndexed (Indexed.ofList context)

@[simp] theorem term_ofIndexed (context : Indexed Sig) (i : Fin context.size) :
    (ofIndexed context).term i = context.term i := by
  simp [term, ofIndexed]

@[simp] theorem toIndexed_ofIndexed (context : Indexed Sig) :
    (ofIndexed context).toIndexed = context := by
  cases context
  rfl

@[simp] theorem toList_ofList (context : ListCtx Sig) :
    (ofList context).toList = context := by
  change ((ofList context).toIndexed).toList = context
  rw [show (ofList context).toIndexed = Indexed.ofList context by
    exact toIndexed_ofIndexed (Indexed.ofList context)]
  exact Indexed.toList_ofList context

end OrderedMap

end Nucleus.HolE.Named.Unsorted.Context
