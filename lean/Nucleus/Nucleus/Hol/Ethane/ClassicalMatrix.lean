import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Dedup

/-!
# Classical CNF-to-DNF matrix sequents

This module is the representation-independent specification of the reusable
classical theorem arena.  The left side is a conjunction of disjunctive
clauses (CNF), while the right side is a disjunction of conjunctive cubes
(DNF).  In particular, the two physically identical list-of-lists have
different polarity-aware types and meanings.

Empty rows and matrices have their standard meanings: an empty clause is
false, an empty CNF is true, an empty cube is true, and an empty DNF is false.
Normalization only sorts and removes duplicates; it performs no semantic
simplification.
-/

namespace Nucleus.Hol.Ethane.ClassicalMatrix

variable {Atom : Type}

/-- A literal carries an atom and a polarity bit. `false` is positive. -/
abbrev Lit (Atom : Type) := Atom × Bool

/-- Complement a literal without inspecting its atom. -/
def Lit.neg {Atom : Type} (literal : Lit Atom) : Lit Atom :=
  (literal.1, !literal.2)

@[simp] theorem Lit.neg_neg {Atom : Type} (literal : Lit Atom) :
    literal.neg.neg = literal := by
  simp [Lit.neg]

structure Clause (Atom : Type) where
  literals : List (Lit Atom)
  deriving DecidableEq

structure Cnf (Atom : Type) where
  clauses : List (Clause Atom)
  deriving DecidableEq

structure Cube (Atom : Type) where
  literals : List (Lit Atom)
  deriving DecidableEq

structure Dnf (Atom : Type) where
  cubes : List (Cube Atom)
  deriving DecidableEq

structure Sequent (Atom : Type) where
  left : Cnf Atom
  right : Dnf Atom
  deriving DecidableEq

/-- A valuation is deliberately over unsigned atoms. -/
abbrev Valuation (Atom : Type) := Atom → Prop

def Lit.Holds {Atom : Type} (valuation : Valuation Atom) (literal : Lit Atom) : Prop :=
  if literal.2 then ¬valuation literal.1 else valuation literal.1

@[simp] theorem Lit.holds_neg {Atom : Type} (valuation : Valuation Atom)
    (literal : Lit Atom) : literal.neg.Holds valuation ↔ ¬literal.Holds valuation := by
  cases literal with
  | mk atom polarity =>
      cases polarity <;> simp [Lit.neg, Lit.Holds]

def Clause.Holds {Atom : Type} (valuation : Valuation Atom) (clause : Clause Atom) : Prop :=
  ∃ literal ∈ clause.literals, literal.Holds valuation

def Cnf.Holds {Atom : Type} (valuation : Valuation Atom) (cnf : Cnf Atom) : Prop :=
  ∀ clause ∈ cnf.clauses, clause.Holds valuation

def Cube.Holds {Atom : Type} (valuation : Valuation Atom) (cube : Cube Atom) : Prop :=
  ∀ literal ∈ cube.literals, literal.Holds valuation

def Dnf.Holds {Atom : Type} (valuation : Valuation Atom) (dnf : Dnf Atom) : Prop :=
  ∃ cube ∈ dnf.cubes, cube.Holds valuation

def Sequent.Holds {Atom : Type} (valuation : Valuation Atom) (sequent : Sequent Atom) : Prop :=
  sequent.left.Holds valuation → sequent.right.Holds valuation

def Sequent.Sound {Atom : Type} (sequent : Sequent Atom) : Prop :=
  ∀ valuation, sequent.Holds valuation

@[simp] theorem empty_clause_false {Atom : Type} (valuation : Valuation Atom) :
    ¬(Clause.mk []).Holds valuation := by
  simp [Clause.Holds]

@[simp] theorem empty_cnf_true {Atom : Type} (valuation : Valuation Atom) :
    (Cnf.mk []).Holds valuation := by
  simp [Cnf.Holds]

@[simp] theorem empty_cube_true {Atom : Type} (valuation : Valuation Atom) :
    (Cube.mk []).Holds valuation := by
  simp [Cube.Holds]

@[simp] theorem empty_dnf_false {Atom : Type} (valuation : Valuation Atom) :
    ¬(Dnf.mk []).Holds valuation := by
  simp [Dnf.Holds]

/-- Pointwise complement turns a disjunctive clause into a conjunctive cube. -/
def Clause.neg {Atom : Type} (clause : Clause Atom) : Cube Atom :=
  ⟨clause.literals.map Lit.neg⟩

/-- Pointwise complement turns a conjunctive cube into a disjunctive clause. -/
def Cube.neg {Atom : Type} (cube : Cube Atom) : Clause Atom :=
  ⟨cube.literals.map Lit.neg⟩

@[simp] theorem Clause.neg_neg {Atom : Type} (clause : Clause Atom) :
    clause.neg.neg = clause := by
  cases clause
  simp [Clause.neg, Cube.neg, List.map_map, Function.comp_def]

@[simp] theorem Cube.neg_neg {Atom : Type} (cube : Cube Atom) :
    cube.neg.neg = cube := by
  cases cube
  simp [Clause.neg, Cube.neg, List.map_map, Function.comp_def]

theorem Clause.neg_holds {Atom : Type} (valuation : Valuation Atom) (clause : Clause Atom) :
    clause.neg.Holds valuation ↔ ¬clause.Holds valuation := by
  simp only [Clause.neg, Cube.Holds, Clause.Holds, List.mem_map]
  constructor
  · intro all ⟨literal, member, truth⟩
    exact (Lit.holds_neg valuation literal).mp (all literal.neg ⟨literal, member, rfl⟩) truth
  · intro notClause literal member
    obtain ⟨source, sourceMember, rfl⟩ := member
    rw [Lit.holds_neg]
    intro truth
    exact notClause ⟨source, sourceMember, truth⟩

theorem Cube.neg_holds {Atom : Type} (valuation : Valuation Atom) (cube : Cube Atom) :
    cube.neg.Holds valuation ↔ ¬cube.Holds valuation := by
  simp only [Cube.neg, Clause.Holds, Cube.Holds, List.mem_map]
  constructor
  · rintro ⟨literal, ⟨source, sourceMember, equal⟩, truth⟩ all
    subst literal
    exact ((Lit.holds_neg valuation source).mp truth) (all source sourceMember)
  · intro notCube
    by_contra noComplement
    push Not at noComplement
    apply notCube
    intro literal member
    by_contra false
    exact noComplement literal.neg ⟨literal, member, rfl⟩
      ((Lit.holds_neg valuation literal).mpr false)

/-! ## Backward-compatible singleton embedding -/

def embedLeft {Atom : Type} (premises : List (Lit Atom)) : Cnf Atom :=
  ⟨premises.map fun literal => Clause.mk [literal]⟩

def embedRight {Atom : Type} (conclusions : List (Lit Atom)) : Dnf Atom :=
  ⟨conclusions.map fun literal => Cube.mk [literal]⟩

@[simp] theorem embedLeft_holds {Atom : Type} (valuation : Valuation Atom)
    (premises : List (Lit Atom)) :
    (embedLeft premises).Holds valuation ↔
      ∀ literal ∈ premises, literal.Holds valuation := by
  constructor
  · intro all literal member
    have singleton := all (Clause.mk [literal]) (by simp [embedLeft, member])
    simpa [Clause.Holds] using singleton
  · intro all clause member
    obtain ⟨literal, literalMember, rfl⟩ := (List.mem_map.mp member)
    simpa [Clause.Holds] using all literal literalMember

@[simp] theorem embedRight_holds {Atom : Type} (valuation : Valuation Atom)
    (conclusions : List (Lit Atom)) :
    (embedRight conclusions).Holds valuation ↔
      ∃ literal ∈ conclusions, literal.Holds valuation := by
  constructor
  · rintro ⟨cube, member, truth⟩
    obtain ⟨literal, literalMember, rfl⟩ := List.mem_map.mp member
    exact ⟨literal, literalMember, by simpa [Cube.Holds] using truth⟩
  · rintro ⟨literal, member, truth⟩
    exact ⟨Cube.mk [literal], by simp [embedRight, member], by simpa [Cube.Holds]⟩

/-! ## Sort-and-deduplicate normalization -/

def canonical [LinearOrder α] (values : List α) : List α :=
  values.toFinset.sort (· ≤ ·)

@[simp] theorem mem_canonical [LinearOrder α] (value : α) (values : List α) :
    value ∈ canonical values ↔ value ∈ values := by
  simp [canonical]

def Clause.normalize [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (clause : Clause Atom) : Clause Atom :=
  ⟨canonical clause.literals⟩

def Cube.normalize [DecidableEq Atom] [LinearOrder (Lit Atom)] (cube : Cube Atom) : Cube Atom :=
  ⟨canonical cube.literals⟩

def Cnf.normalize [DecidableEq Atom] [LinearOrder (Lit Atom)] (cnf : Cnf Atom) : Cnf Atom :=
  ⟨(cnf.clauses.map Clause.normalize).dedup⟩

def Dnf.normalize [DecidableEq Atom] [LinearOrder (Lit Atom)] (dnf : Dnf Atom) : Dnf Atom :=
  ⟨(dnf.cubes.map Cube.normalize).dedup⟩

def Sequent.normalize [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (sequent : Sequent Atom) : Sequent Atom :=
  ⟨sequent.left.normalize, sequent.right.normalize⟩

@[simp] theorem Clause.normalize_holds [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (valuation : Valuation Atom)
    (clause : Clause Atom) : clause.normalize.Holds valuation ↔ clause.Holds valuation := by
  simp [Clause.normalize, Clause.Holds]

@[simp] theorem Cube.normalize_holds [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (valuation : Valuation Atom)
    (cube : Cube Atom) : cube.normalize.Holds valuation ↔ cube.Holds valuation := by
  simp [Cube.normalize, Cube.Holds]

@[simp] theorem Cnf.normalize_holds [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (valuation : Valuation Atom)
    (cnf : Cnf Atom) : cnf.normalize.Holds valuation ↔ cnf.Holds valuation := by
  simp [Cnf.normalize, Cnf.Holds]

@[simp] theorem Dnf.normalize_holds [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (valuation : Valuation Atom)
    (dnf : Dnf Atom) : dnf.normalize.Holds valuation ↔ dnf.Holds valuation := by
  simp [Dnf.normalize, Dnf.Holds]

@[simp] theorem Sequent.normalize_holds [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (valuation : Valuation Atom)
    (sequent : Sequent Atom) : sequent.normalize.Holds valuation ↔ sequent.Holds valuation := by
  simp [Sequent.normalize, Sequent.Holds]

theorem normalize_sound_iff [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (sequent : Sequent Atom) :
    sequent.normalize.Sound ↔ sequent.Sound := by
  simp [Sequent.Sound]

/-! ## Primitive matrix rules -/

theorem identity (literal : Lit Atom) :
    (Sequent.mk (Cnf.mk [Clause.mk [literal]]) (Dnf.mk [Cube.mk [literal]])).Sound := by
  intro valuation premise
  have clauseTruth := premise (Clause.mk [literal]) (by simp)
  obtain ⟨found, member, truth⟩ := clauseTruth
  have equal : found = literal := by simpa using member
  subst found
  exact ⟨Cube.mk [literal], by simp, by simpa [Cube.Holds]⟩

/-- Adding left clauses strengthens an antecedent; adding right cubes weakens
the consequent. -/
theorem weaken {sourceLeft extraLeft : List (Clause Atom)}
    {sourceRight extraRight : List (Cube Atom)}
    (sound : (Sequent.mk (Cnf.mk sourceLeft) (Dnf.mk sourceRight)).Sound) :
    (Sequent.mk (Cnf.mk (sourceLeft ++ extraLeft))
      (Dnf.mk (sourceRight ++ extraRight))).Sound := by
  intro valuation targetLeft
  obtain ⟨cube, member, truth⟩ := sound valuation (by
    intro clause member
    exact targetLeft clause (List.mem_append_left _ member))
  exact ⟨cube, List.mem_append_left _ member, truth⟩

/-- Indexed transfer: remove one left clause and insert its complemented cube
on the right. The list decomposition is the proof-level form of a checked row
index. -/
theorem transferClauseRight {before after : List (Clause Atom)} {right : List (Cube Atom)}
    (clause : Clause Atom)
    (sound : (Sequent.mk (Cnf.mk (before ++ clause :: after)) (Dnf.mk right)).Sound) :
    (Sequent.mk (Cnf.mk (before ++ after)) (Dnf.mk (clause.neg :: right))).Sound := by
  intro valuation left
  by_cases clauseTruth : clause.Holds valuation
  · obtain ⟨cube, member, truth⟩ := sound valuation (by
      intro candidate member
      rcases List.mem_append.mp member with member | member
      · exact left candidate (List.mem_append_left _ member)
      · simp only [List.mem_cons] at member
        rcases member with equal | member
        · simpa [equal] using clauseTruth
        · exact left candidate (List.mem_append_right _ member))
    exact ⟨cube, by simp [member], truth⟩
  · exact ⟨clause.neg, by simp, (Clause.neg_holds valuation clause).mpr clauseTruth⟩

/-- Indexed transfer: remove one right cube and insert its complemented clause
on the left. -/
theorem transferCubeLeft {left : List (Clause Atom)} {before after : List (Cube Atom)}
    (cube : Cube Atom)
    (sound : (Sequent.mk (Cnf.mk left) (Dnf.mk (before ++ cube :: after))).Sound) :
    (Sequent.mk (Cnf.mk (cube.neg :: left)) (Dnf.mk (before ++ after))).Sound := by
  intro valuation premises
  obtain ⟨candidate, member, truth⟩ := sound valuation (by
    intro clause member
    exact premises clause (by simp [member]))
  rcases List.mem_append.mp member with member | member
  · exact ⟨candidate, List.mem_append_left _ member, truth⟩
  · simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst candidate
      have notCube : ¬cube.Holds valuation := (Cube.neg_holds valuation cube).mp
        (premises cube.neg (by simp))
      exact (notCube truth).elim
    · exact ⟨candidate, List.mem_append_right _ member, truth⟩

/-- Singleton cut between a right cube and a left clause. -/
theorem cut (pivot : Lit Atom) {leftPrem rightPrem : List (Clause Atom)}
    {leftConc rightConc : List (Cube Atom)}
    (leftSound : (Sequent.mk (Cnf.mk leftPrem)
      (Dnf.mk (Cube.mk [pivot] :: leftConc))).Sound)
    (rightSound : (Sequent.mk (Cnf.mk (Clause.mk [pivot] :: rightPrem))
      (Dnf.mk rightConc)).Sound) :
    (Sequent.mk (Cnf.mk (leftPrem ++ rightPrem))
      (Dnf.mk (leftConc ++ rightConc))).Sound := by
  intro valuation premises
  obtain ⟨cube, member, truth⟩ := leftSound valuation (by
    intro clause member
    exact premises clause (List.mem_append_left _ member))
  simp only [List.mem_cons] at member
  rcases member with equal | member
  · subst cube
    have pivotTruth : pivot.Holds valuation := by
      simpa [Cube.Holds] using truth
    obtain ⟨cube, member, truth⟩ := rightSound valuation (by
      intro clause member
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst clause
        simpa [Clause.Holds] using pivotTruth
      · exact premises clause (List.mem_append_right _ member))
    exact ⟨cube, List.mem_append_right _ member, truth⟩
  · exact ⟨cube, List.mem_append_left _ member, truth⟩

/-- Resolution between complementary singleton cubes. -/
theorem resolution (pivot : Lit Atom) {leftPrem rightPrem : List (Clause Atom)}
    {leftConc rightConc : List (Cube Atom)}
    (leftSound : (Sequent.mk (Cnf.mk leftPrem)
      (Dnf.mk (Cube.mk [pivot] :: leftConc))).Sound)
    (rightSound : (Sequent.mk (Cnf.mk rightPrem)
      (Dnf.mk (Cube.mk [pivot.neg] :: rightConc))).Sound) :
    (Sequent.mk (Cnf.mk (leftPrem ++ rightPrem))
      (Dnf.mk (leftConc ++ rightConc))).Sound := by
  intro valuation premises
  by_cases truth : pivot.Holds valuation
  · obtain ⟨cube, member, cubeTruth⟩ := rightSound valuation (by
      intro clause member
      exact premises clause (List.mem_append_right _ member))
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst cube
      have complement : pivot.neg.Holds valuation := by simpa [Cube.Holds] using cubeTruth
      exact ((Lit.holds_neg valuation pivot).mp complement truth).elim
    · exact ⟨cube, List.mem_append_right _ member, cubeTruth⟩
  · obtain ⟨cube, member, cubeTruth⟩ := leftSound valuation (by
      intro clause member
      exact premises clause (List.mem_append_left _ member))
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst cube
      have pivotTruth : pivot.Holds valuation := by simpa [Cube.Holds] using cubeTruth
      exact (truth pivotTruth).elim
    · exact ⟨cube, List.mem_append_left _ member, cubeTruth⟩

/-! ## Theorem slots and free-list lifecycle -/

structure Store (Atom : Type) where
  slots : List (Option (Sequent Atom))
  free : List Nat

def Store.lookup (store : Store Atom) (id : Nat) : Option (Sequent Atom) :=
  store.slots[id]?.join

def Store.WellFormed (store : Store Atom) : Prop :=
  store.free.Nodup ∧ ∀ id ∈ store.free, id < store.slots.length ∧ store.lookup id = none

def Store.LiveSound (store : Store Atom) : Prop :=
  ∀ id fact, store.lookup id = some fact → fact.Sound

/-- Empty storage has no live logical claims. -/
def Store.empty : Store Atom := ⟨[], []⟩

/-- Append is the fresh-slot branch of theorem allocation. -/
def Store.append (store : Store Atom) (fact : Sequent Atom) : Nat × Store Atom :=
  (store.slots.length, { store with slots := store.slots ++ [some fact] })

/-- Remove exactly one live theorem and add its slot to the free list. -/
def Store.delete? (store : Store Atom) (id : Nat) : Option (Store Atom) :=
  match store.lookup id with
  | none => none
  | some _ => some { slots := store.slots.set id none, free := id :: store.free }

/-- Reuse the most recently removed slot. -/
def Store.reuse? (store : Store Atom) (fact : Sequent Atom) : Option (Nat × Store Atom) :=
  match store.free with
  | [] => none
  | id :: rest =>
      if id < store.slots.length ∧ store.lookup id = none then
        some (id, { slots := store.slots.set id (some fact), free := rest })
      else none

/-- Allocate from the free list when possible and append otherwise. -/
def Store.insert (store : Store Atom) (fact : Sequent Atom) : Nat × Store Atom :=
  match store.reuse? fact with
  | some result => result
  | none => store.append fact

/-- Persistent theorem copy: the source remains live and allocation follows
the same free-list policy as ordinary insertion. -/
def Store.copy? (store : Store Atom) (source : Nat) : Option (Nat × Store Atom) :=
  (store.lookup source).map store.insert

/-- Atomic checked replacement of one live theorem. -/
def Store.mutate? (store : Store Atom) (id : Nat) (replacement : Sequent Atom) :
    Option (Store Atom) :=
  match store.lookup id with
  | none => none
  | some _ => some { store with slots := store.slots.set id (some replacement) }

/-- Normalization is exposed as a semantics-preserving in-place mutation. -/
def Store.normalize? [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (store : Store Atom) (id : Nat) : Option (Store Atom) :=
  (store.lookup id).bind fun fact => store.mutate? id fact.normalize

/-- Storage reuse is logically sound whenever it inserts a checked theorem and
preserves all other live lookups. This isolates free-list allocation from the
calculus: dead slot contents and free-list order have no logical meaning. -/
theorem reuse_preserves_live_sound {before after : Store Atom} {reused : Nat}
    {replacement : Sequent Atom} (beforeSound : before.LiveSound)
    (replacementSound : replacement.Sound)
    (inserted : after.lookup reused = some replacement)
    (preserved : ∀ id, id ≠ reused → after.lookup id = before.lookup id) :
    after.LiveSound := by
  intro id fact live
  by_cases same : id = reused
  · subst id
    have equal := Option.some.inj (inserted.symm.trans live)
    subst fact
    exact replacementSound
  · exact beforeSound id fact ((preserved id same).symm.trans live)

/-- The logical contract shared by every checked in-place rule. -/
theorem mutation_preserves_live_sound {before after : Store Atom} {target : Nat}
    {replacement : Sequent Atom} (beforeSound : before.LiveSound)
    (replacementSound : replacement.Sound)
    (inserted : after.lookup target = some replacement)
    (preserved : ∀ id, id ≠ target → after.lookup id = before.lookup id) :
    after.LiveSound :=
  reuse_preserves_live_sound beforeSound replacementSound inserted preserved

/-- Sorting and duplicate removal supply the checked replacement required by
the generic mutation theorem. -/
theorem normalization_replacement_sound [DecidableEq Atom] [LinearOrder (Lit Atom)]
    {fact : Sequent Atom} (sound : fact.Sound) : fact.normalize.Sound :=
  (normalize_sound_iff fact).mpr sound

/-- Deleting one theorem is sound because it cannot create a live lookup. -/
theorem deletion_preserves_live_sound {before after : Store Atom}
    (beforeSound : before.LiveSound)
    (onlyRemoves : ∀ id fact, after.lookup id = some fact →
      before.lookup id = some fact) :
    after.LiveSound := by
  intro id fact live
  exact beforeSound id fact (onlyRemoves id fact live)

/-- Copying a theorem has exactly the same logical obligation as reuse: the
copied statement was already live and hence sound. -/
theorem copy_preserves_live_sound {before after : Store Atom} {source copied : Nat}
    {fact : Sequent Atom} (beforeSound : before.LiveSound)
    (sourceLive : before.lookup source = some fact)
    (copiedLive : after.lookup copied = some fact)
    (preserved : ∀ id, id ≠ copied → after.lookup id = before.lookup id) :
    after.LiveSound :=
  reuse_preserves_live_sound beforeSound (beforeSound source fact sourceLive)
    copiedLive preserved

/-! ## Why the right side is DNF, not CNF -/

/-- Interpreting both sides as CNF invalidates clause transfer. With `p = true`,
`true -> (p ∧ ¬p)` is false, while `(true ∧ p) -> p` is true. The latter is
what naive pointwise transfer of the `¬p` clause would produce. -/
theorem rhs_cnf_transfer_counterexample :
    let p : Lit Unit := ((), false)
    let notP : Lit Unit := p.neg
    let valuation : Valuation Unit := fun _ => True
    ¬((Cnf.mk []).Holds valuation →
        (Cnf.mk [Clause.mk [p], Clause.mk [notP]]).Holds valuation) ∧
      ((Cnf.mk [Clause.mk [p]]).Holds valuation →
        (Cnf.mk [Clause.mk [p]]).Holds valuation) := by
  simp [Cnf.Holds, Clause.Holds, Lit.Holds, Lit.neg]

/-! ## Representative shared vectors -/

/-- A compact representative row suitable for mirroring in Rust tests:
`(p ∨ ¬q) ∧ r ⊢ (p ∧ r) ∨ ¬q`. -/
def representative : Sequent Nat :=
  { left := Cnf.mk [
      Clause.mk [(1, false), (2, true)],
      Clause.mk [(3, false)]]
    right := Dnf.mk [
      Cube.mk [(1, false), (3, false)],
      Cube.mk [(2, true)]] }

example : representative.left.clauses.length = 2 := rfl
example : representative.right.cubes.length = 2 := rfl

end Nucleus.Hol.Ethane.ClassicalMatrix
