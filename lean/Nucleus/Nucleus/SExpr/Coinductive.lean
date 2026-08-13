import Nucleus.SExpr.Pointer
import Mathlib.Data.Countable.Basic

/-!
# Coinductive and rational binary S-expressions

An observation path uses `false` for car and `true` for cdr. A coherent tree
has the canonical nil observation below every nil or atom. Finite heaps denote
coherent trees without an acyclicity assumption. Quotienting finite rooted
heaps by equal denotation gives the regular (rational) trees.
-/

namespace Nucleus

universe u

namespace SExpr2

/-- One observable layer of a potentially infinite binary S-expression. -/
inductive Shape (Atom : Type u) where
  | nil
  | atom (value : Atom)
  | cons
  deriving DecidableEq, Repr

/-- Greatest-fixpoint binary S-expressions, represented by coherent finite-path
observations. Paths below a non-cons node canonically observe nil. -/
structure Coinductive (Atom : Type u) where
  observe : List Bool → Shape Atom
  below_noncons : ∀ path direction, observe path ≠ .cons →
    observe (path ++ [direction]) = .nil

namespace Coinductive

variable {Atom : Type u}

@[ext] theorem ext {left right : Coinductive Atom}
    (h : ∀ path, left.observe path = right.observe path) : left = right := by
  cases left
  cases right
  congr
  funext path
  exact h path

/-- Follow a path in a finite pointer heap. Cycles are harmless because every
individual observation uses only finitely many pointer steps. Invalid pointers
have the canonical nil denotation. -/
def observeHeap (heap : Heap Atom) : Nat → List Bool → Shape Atom
  | 0, _ => .nil
  | pointer, [] =>
      match heap.get? pointer with
      | some (.atom value) => .atom value
      | some (.cons ..) => .cons
      | none => .nil
  | pointer, direction :: path =>
      match heap.get? pointer with
      | some (.cons car cdr) => observeHeap heap (if direction then cdr else car) path
      | _ => .nil

private theorem observeHeap_below (heap : Heap Atom) :
    ∀ pointer path direction, observeHeap heap pointer path ≠ .cons →
      observeHeap heap pointer (path ++ [direction]) = .nil := by
  intro pointer path
  induction path generalizing pointer with
  | nil =>
      intro direction h
      cases pointer with
      | zero => rfl
      | succ pointer =>
          cases hg : heap.get? (pointer + 1) with
          | none => simp only [List.nil_append, observeHeap, hg]
          | some node =>
              cases node <;> simp_all [observeHeap]
  | cons head tail ih =>
      intro direction h
      cases pointer with
      | zero => rfl
      | succ pointer =>
          simp only [List.cons_append, observeHeap] at h ⊢
          cases hg : heap.get? (pointer + 1) with
          | none => rfl
          | some node =>
              cases node with
              | atom => rfl
              | cons car cdr =>
                  simp only [hg] at h
                  exact ih _ _ h

/-- Denotation of a finite heap in the greatest fixpoint. No acyclicity is
required. -/
def ofHeap (heap : Heap Atom) : Coinductive Atom where
  observe := observeHeap heap heap.root
  below_noncons := observeHeap_below heap heap.root

private def observeCellTable (table : CellTable ι Atom) : ι → List Bool → Shape Atom
  | index, [] => match table index with
      | .atom value => .atom value
      | .cons _ => .cons
  | index, direction :: path => match table index with
      | .atom _ => .nil
      | .cons cell => observeCellTable table (if direction then cell.cdr else cell.car) path

private theorem observeCellTable_below (table : CellTable ι Atom) :
    ∀ index path direction, observeCellTable table index path ≠ .cons →
      observeCellTable table index (path ++ [direction]) = .nil := by
  intro index path
  induction path generalizing index with
  | nil =>
      intro direction h
      cases hc : table index with
      | atom => simp [observeCellTable, hc]
      | cons => simp [observeCellTable, hc] at h
  | cons side path ih =>
      intro direction h
      cases hc : table index with
      | atom => simp [observeCellTable, hc]
      | cons cell =>
          simp only [List.cons_append, observeCellTable, hc] at h ⊢
          exact ih _ direction h

/-- Greatest-fixpoint denotation of an arbitrary total indexed table. Unlike
`CellTable.deref`, this is productive for cyclic and infinite tables. -/
def ofCellTable (table : CellTable ι Atom) (root : ι) : Coinductive Atom where
  observe := observeCellTable table root
  below_noncons := observeCellTable_below table root

/-- A finite S-expression embeds in the greatest fixpoint. -/
def ofSExpr2 : SExpr2 Atom → Coinductive Atom
  | .nil => ⟨fun _ => .nil, by simp⟩
  | .atom value => ⟨fun path => if path.isEmpty then .atom value else .nil, by
      intro path direction _
      simp⟩
  | .cons car cdr =>
      let left := ofSExpr2 car
      let right := ofSExpr2 cdr
      ⟨fun path => match path with
        | [] => .cons
        | false :: rest => left.observe rest
        | true :: rest => right.observe rest,
       by
        intro path direction h
        cases path with
        | nil => simp at h
        | cons side rest =>
            simp only [List.cons_append]
            cases side <;> simp only
            · exact left.below_noncons rest direction h
            · exact right.below_noncons rest direction h⟩

theorem ofSExpr2_injective : Function.Injective (ofSExpr2 : SExpr2 Atom → Coinductive Atom) := by
  intro left
  induction left with
  | nil =>
      intro right h
      cases right with
      | nil => rfl
      | atom value =>
          have hr := congrArg (fun tree => tree.observe []) h
          simp [ofSExpr2] at hr
      | cons car cdr =>
          have hr := congrArg (fun tree => tree.observe []) h
          simp [ofSExpr2] at hr
  | atom value =>
      intro right h
      cases right with
      | nil =>
          have hr := congrArg (fun tree => tree.observe []) h
          simp [ofSExpr2] at hr
      | atom value' =>
          have hr := congrArg (fun tree => tree.observe []) h
          change Shape.atom value = Shape.atom value' at hr
          exact congrArg SExpr2.atom (Shape.atom.inj hr)
      | cons car cdr =>
          have hr := congrArg (fun tree => tree.observe []) h
          simp [ofSExpr2] at hr
  | cons car cdr ihCar ihCdr =>
      intro right h
      cases right with
      | nil =>
          have hr := congrArg (fun tree => tree.observe []) h
          simp [ofSExpr2] at hr
      | atom value =>
          have hr := congrArg (fun tree => tree.observe []) h
          simp [ofSExpr2] at hr
      | cons car' cdr' =>
          congr
          · apply ihCar
            apply ext
            intro path
            have hp := congrArg (fun tree => tree.observe (false :: path)) h
            simpa [ofSExpr2] using hp
          · apply ihCdr
            apply ext
            intro path
            have hp := congrArg (fun tree => tree.observe (true :: path)) h
            simpa [ofSExpr2] using hp

private def streamObserve (stream : Nat → Bool) : List Bool → Shape Unit
  | [] => .cons
  | false :: [] => if stream 0 then .atom () else .nil
  | false :: _ :: _ => .nil
  | true :: rest => streamObserve (fun n => stream (n + 1)) rest

private theorem streamObserve_below (stream : Nat → Bool) :
    ∀ path direction, streamObserve stream path ≠ .cons →
      streamObserve stream (path ++ [direction]) = .nil := by
  intro path
  induction path generalizing stream with
  | nil => simp [streamObserve]
  | cons head tail ih =>
      cases head
      · cases tail <;> simp [streamObserve]
      · intro direction h
        simp only [List.cons_append, streamObserve]
        exact ih _ direction h

/-- Encode an arbitrary Boolean stream down an infinite cdr spine, using each
car to record the next bit. -/
def ofStream (stream : Nat → Bool) : Coinductive Unit where
  observe := streamObserve stream
  below_noncons := streamObserve_below stream

private theorem streamObserve_bit (stream : Nat → Bool) (n : Nat) :
    streamObserve stream (List.replicate n true ++ [false]) =
      if stream n then .atom () else .nil := by
  induction n generalizing stream with
  | zero => simp [streamObserve]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, streamObserve]
      simpa [Nat.add_comm] using ih (fun i => stream (i + 1))

theorem ofStream_injective : Function.Injective ofStream := by
  intro left right h
  funext n
  have hp := congrArg
    (fun tree => tree.observe (List.replicate n true ++ [false])) h
  simp only [ofStream, streamObserve_bit] at hp
  cases hl : left n <;> cases hr : right n <;> simp_all

/-- Number of cons layers on the all-cdr path of a finite expression. -/
def cdrDepth : SExpr2 Atom → Nat
  | .cons _ cdr => cdrDepth cdr + 1
  | _ => 0

private theorem finite_cdr_stops (value : SExpr2 Atom) :
    (ofSExpr2 value).observe (List.replicate (cdrDepth value + 1) true) ≠ .cons := by
  induction value with
  | nil => simp [cdrDepth, ofSExpr2]
  | atom => simp [cdrDepth, ofSExpr2]
  | cons car cdr ihCar ihCdr =>
      simpa [cdrDepth, ofSExpr2, List.replicate_succ] using ihCdr

/-- The one-cell cdr loop, whose car is nil and whose cdr is itself. -/
def cdrLoopHeap : Heap Unit := ⟨[.cons 0 1], 1⟩

private theorem cdrLoop_observe (n : Nat) :
    (ofHeap cdrLoopHeap).observe (List.replicate n true) = .cons := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [cdrLoopHeap, ofHeap, observeHeap, Heap.get?, List.replicate_succ] using ih

/-- Rational trees strictly contain the least fixpoint: the cdr loop is regular
but cannot be any finite `SExpr2`. -/
theorem cdrLoop_not_finite : ∀ value : SExpr2 Unit,
    ofHeap cdrLoopHeap ≠ ofSExpr2 value := by
  intro value h
  have hp := congrArg
    (fun tree => tree.observe (List.replicate (cdrDepth value + 1) true)) h
  rw [cdrLoop_observe] at hp
  exact finite_cdr_stops value hp.symm

/-- The greatest fixpoint is genuinely larger than the countable rational
fragment: already with one atom it contains an injective copy of Boolean
streams. -/
theorem not_countable : ¬Countable (Coinductive Unit) := by
  intro h
  letI : Countable (Coinductive Unit) := h
  haveI : Countable (Nat → Bool) := ofStream_injective.countable
  obtain ⟨enumerate, surjective⟩ := exists_surjective_nat (Nat → Bool)
  let diagonal : Nat → Bool := fun n => !(enumerate n n)
  obtain ⟨n, hn⟩ := surjective diagonal
  have := congrFun hn n
  simp [diagonal] at this

end Coinductive

/-- A finite presentation of a rational tree. -/
abbrev Presentation (Atom : Type u) := Heap Atom

/-- Two presentations are equivalent exactly when their observations agree. -/
def Presentation.setoid (Atom : Type u) : Setoid (Presentation Atom) where
  r left right := Coinductive.ofHeap left = Coinductive.ofHeap right
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Rational trees are finite pointer graphs quotiented by denotation, including
unreachable-table-tail differences. -/
def Rational (Atom : Type u) := Quotient (Presentation.setoid Atom)

namespace Rational

variable {Atom : Type u}

def ofHeap (heap : Heap Atom) : Rational Atom := Quotient.mk _ heap

/-- Rational trees embed into the greatest fixpoint by denotation. -/
def toCoinductive : Rational Atom → Coinductive Atom :=
  Quotient.lift Coinductive.ofHeap fun _ _ h => h

theorem toCoinductive_ofHeap (heap : Heap Atom) :
    toCoinductive (ofHeap heap) = Coinductive.ofHeap heap := rfl

theorem toCoinductive_injective :
    Function.Injective (toCoinductive : Rational Atom → Coinductive Atom) := by
  intro left right h
  induction left using Quotient.inductionOn with
  | _ left =>
      induction right using Quotient.inductionOn with
      | _ right => exact Quotient.sound h

/-- Rational trees remain countable whenever atoms are countable. -/
noncomputable instance [Countable Atom] : Countable (Rational Atom) :=
  Quotient.countable

/-- Rational trees over a countable atom type cannot exhaust the greatest
fixpoint, even in the one-atom case. -/
theorem not_surjective_unit :
    ¬Function.Surjective (toCoinductive : Rational Unit → Coinductive Unit) := by
  intro h
  have : Countable (Coinductive Unit) := h.countable
  exact Coinductive.not_countable this

end Rational
end SExpr2
end Nucleus
