import Nucleus.Classical.Refutation
import Nucleus.Classical.Tagged.Runtime.Derive

/-!
# Canonical compatibility rules for classical matrices

The legacy matrix is the strict depth-two tagged shape
`AND(OR(literal...)) ⊢ OR(AND(literal...))`.  This module parses that shape,
constructs rule targets as decoded syntax, and proves them through the existing
representation-independent matrix semantics.  Packing and theorem sealing stay
in `Runtime.Kernel`.
-/

namespace Nucleus.Classical.Tagged.Runtime.Matrix

open Nucleus.Classical
open Nucleus.Classical.Tagged

abbrev LegacyLit := Nucleus.Hol.Ethane.ClassicalMatrix.Lit Nat
abbrev LegacyClause := Nucleus.Hol.Ethane.ClassicalMatrix.Clause Nat
abbrev LegacyCube := Nucleus.Hol.Ethane.ClassicalMatrix.Cube Nat
abbrev LegacySequent := Nucleus.Hol.Ethane.ClassicalMatrix.Sequent Nat

/-- The decoded, polarity-aware depth-two matrix. -/
structure Syntax where
  cnf : List (List (Classical.Literal Nat))
  dnf : List (List (Classical.Literal Nat))
  deriving DecidableEq, Repr

/-- Select which matrix of rows an operation addresses. -/
inductive Side where
  | cnf
  | dnf
  deriving DecidableEq, Repr

def toLegacyLiteral (literal : Classical.Literal Nat) : LegacyLit :=
  (literal.atom, literal.negative)

def ofLegacyLiteral (literal : LegacyLit) : Classical.Literal Nat :=
  ⟨literal.1, literal.2⟩

@[simp] theorem ofLegacyLiteral_toLegacyLiteral (literal : Classical.Literal Nat) :
    ofLegacyLiteral (toLegacyLiteral literal) = literal := by
  cases literal
  simp [ofLegacyLiteral, toLegacyLiteral]

@[simp] theorem toLegacyLiteral_ofLegacyLiteral (literal : LegacyLit) :
    toLegacyLiteral (ofLegacyLiteral literal) = literal := by
  cases literal
  rfl

@[simp] theorem refutationLiteral_toLegacyLiteral
    (literal : Classical.Literal Nat) :
    Refutation.Matrix.literal (toLegacyLiteral literal) = literal := by
  cases literal
  rfl

def legacyClause (row : List (Classical.Literal Nat)) : LegacyClause :=
  ⟨row.map toLegacyLiteral⟩

def legacyCube (row : List (Classical.Literal Nat)) : LegacyCube :=
  ⟨row.map toLegacyLiteral⟩

def Syntax.toLegacy (matrix : Syntax) : LegacySequent :=
  ⟨⟨matrix.cnf.map legacyClause⟩, ⟨matrix.dnf.map legacyCube⟩⟩

def literalFormula (literal : Classical.Literal Nat) : Tagged.Formula Nat :=
  .literal literal

def clauseFormula (row : List (Classical.Literal Nat)) : Tagged.Formula Nat :=
  .or false (row.map literalFormula)

def cubeFormula (row : List (Classical.Literal Nat)) : Tagged.Formula Nat :=
  .and false (row.map literalFormula)

def cnfFormula (rows : List (List (Classical.Literal Nat))) : Tagged.Formula Nat :=
  .and false (rows.map clauseFormula)

def dnfFormula (rows : List (List (Classical.Literal Nat))) : Tagged.Formula Nat :=
  .or false (rows.map cubeFormula)

/-- Encode a decoded matrix in the tagged runtime AST. -/
def encode (matrix : Syntax) : Tagged.Sequent Nat :=
  ⟨cnfFormula matrix.cnf, dnfFormula matrix.dnf⟩

private def traverse? (decode : α → Option β) : List α → Option (List β)
  | [] => some []
  | value :: values => do
      let head ← decode value
      let tail ← traverse? decode values
      some (head :: tail)

private def literal? : Tagged.Formula Nat → Option (Classical.Literal Nat)
  | .literal literal => some literal
  | _ => none

private def clause? : Tagged.Formula Nat → Option (List (Classical.Literal Nat))
  | .or false children => traverse? literal? children
  | _ => none

private def cube? : Tagged.Formula Nat → Option (List (Classical.Literal Nat))
  | .and false children => traverse? literal? children
  | _ => none

private def cnf? : Tagged.Formula Nat → Option (List (List (Classical.Literal Nat)))
  | .and false children => traverse? clause? children
  | _ => none

private def dnf? : Tagged.Formula Nat → Option (List (List (Classical.Literal Nat)))
  | .or false children => traverse? cube? children
  | _ => none

/-- Accept exactly a positive depth-two CNF-to-DNF matrix sequent. -/
def decode? (sequent : Tagged.Sequent Nat) : Option Syntax := do
  let cnf ← cnf? sequent.premise
  let dnf ← dnf? sequent.conclusion
  some ⟨cnf, dnf⟩

@[simp] private theorem traverse?_literals
    (values : List (Classical.Literal Nat)) :
    traverse? literal? (values.map literalFormula) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [traverse?, literal?, literalFormula, ih]

@[simp] private theorem traverse?_clauses
    (values : List (List (Classical.Literal Nat))) :
    traverse? clause? (values.map clauseFormula) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [traverse?, clause?, clauseFormula, ih]

@[simp] private theorem traverse?_cubes
    (values : List (List (Classical.Literal Nat))) :
    traverse? cube? (values.map cubeFormula) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [traverse?, cube?, cubeFormula, ih]

@[simp] theorem decode?_encode (matrix : Syntax) :
    decode? (encode matrix) = some matrix := by
  cases matrix with
  | mk cnf dnf =>
      simp [decode?, encode, cnfFormula, dnfFormula, cnf?, dnf?]

private theorem traverse?_result {decode : α → Option β} {encodeItem : β → α}
    (single : ∀ {source target}, decode source = some target →
      source = encodeItem target)
    {sources : List α} {targets : List β}
    (decoded : traverse? decode sources = some targets) :
    sources = targets.map encodeItem := by
  induction sources generalizing targets with
  | nil =>
      simp [traverse?] at decoded
      subst targets
      rfl
  | cons source sources ih =>
      cases head : decode source with
      | none => simp [traverse?, head] at decoded
      | some target =>
          cases tail : traverse? decode sources with
          | none => simp [traverse?, head, tail] at decoded
          | some targets' =>
              have equal : target :: targets' = targets := by
                simpa [traverse?, head, tail] using decoded
              subst targets
              simp only [List.map_cons, List.cons.injEq]
              exact ⟨single head, ih tail⟩

private theorem literal?_result {source : Tagged.Formula Nat}
    {target : Classical.Literal Nat} (decoded : literal? source = some target) :
    source = literalFormula target := by
  cases source <;> simp [literal?, literalFormula] at decoded ⊢
  simpa [literalFormula] using congrArg Tagged.Formula.literal decoded

private theorem clause?_result {source : Tagged.Formula Nat}
    {target : List (Classical.Literal Nat)} (decoded : clause? source = some target) :
    source = clauseFormula target := by
  cases source with
  | literal _ | and _ _ | sat _ _ => simp [clause?] at decoded
  | or negative children =>
      cases negative with
      | true => simp [clause?] at decoded
      | false =>
          simpa [clause?, clauseFormula] using congrArg (Tagged.Formula.or false)
            (traverse?_result literal?_result decoded)

private theorem cube?_result {source : Tagged.Formula Nat}
    {target : List (Classical.Literal Nat)} (decoded : cube? source = some target) :
    source = cubeFormula target := by
  cases source with
  | literal _ | or _ _ | sat _ _ => simp [cube?] at decoded
  | and negative children =>
      cases negative with
      | true => simp [cube?] at decoded
      | false =>
          simpa [cube?, cubeFormula] using congrArg (Tagged.Formula.and false)
            (traverse?_result literal?_result decoded)

private theorem cnf?_result {source : Tagged.Formula Nat}
    {target : List (List (Classical.Literal Nat))}
    (decoded : cnf? source = some target) : source = cnfFormula target := by
  cases source with
  | literal _ | or _ _ | sat _ _ => simp [cnf?] at decoded
  | and negative children =>
      cases negative with
      | true => simp [cnf?] at decoded
      | false =>
          simpa [cnf?, cnfFormula] using congrArg (Tagged.Formula.and false)
            (traverse?_result clause?_result decoded)

private theorem dnf?_result {source : Tagged.Formula Nat}
    {target : List (List (Classical.Literal Nat))}
    (decoded : dnf? source = some target) : source = dnfFormula target := by
  cases source with
  | literal _ | and _ _ | sat _ _ => simp [dnf?] at decoded
  | or negative children =>
      cases negative with
      | true => simp [dnf?] at decoded
      | false =>
          simpa [dnf?, dnfFormula] using congrArg (Tagged.Formula.or false)
            (traverse?_result cube?_result decoded)

theorem decode?_result {sequent : Tagged.Sequent Nat} {matrix : Syntax}
    (decoded : decode? sequent = some matrix) : sequent = encode matrix := by
  unfold decode? at decoded
  cases premiseDecoded : cnf? sequent.premise with
  | none => simp [premiseDecoded] at decoded
  | some cnf =>
      rw [premiseDecoded] at decoded
      cases conclusionDecoded : dnf? sequent.conclusion with
      | none => simp [conclusionDecoded] at decoded
      | some dnf =>
          rw [conclusionDecoded] at decoded
          have equal : Syntax.mk cnf dnf = matrix := Option.some.inj decoded
          subst matrix
          cases sequent
          simp only [encode, Tagged.Sequent.mk.injEq]
          exact ⟨cnf?_result premiseDecoded, dnf?_result conclusionDecoded⟩

private theorem clauseFormula_eq_legacy
    (row : List (Classical.Literal Nat)) :
    clauseFormula row = Refutation.Tagged.clause
      ⟨row.map toLegacyLiteral⟩ := by
  unfold clauseFormula Refutation.Tagged.clause Tagged.Formula.disjunction
  apply congrArg (Tagged.Formula.or false)
  rw [List.map_map]
  apply List.map_congr_left
  intro literal _
  simp [literalFormula]

private theorem cubeFormula_eq_legacy
    (row : List (Classical.Literal Nat)) :
    cubeFormula row = Refutation.Tagged.cube
      ⟨row.map toLegacyLiteral⟩ := by
  unfold cubeFormula Refutation.Tagged.cube Tagged.Formula.conjunction
  apply congrArg (Tagged.Formula.and false)
  rw [List.map_map]
  apply List.map_congr_left
  intro literal _
  simp [literalFormula]

theorem encode_eq_matrixSequent (matrix : Syntax) :
    encode matrix = Refutation.Tagged.matrixSequent matrix.toLegacy := by
  cases matrix with
  | mk cnf dnf =>
      simp only [encode, cnfFormula, dnfFormula, Syntax.toLegacy,
        Refutation.Tagged.matrixSequent, Refutation.Tagged.cnf,
        Refutation.Tagged.dnf, Tagged.Formula.conjunction,
        Tagged.Formula.disjunction, List.map_map, Function.comp_def]
      congr 2
      · exact List.map_congr_left fun row _ => clauseFormula_eq_legacy row
      · exact List.map_congr_left fun row _ => cubeFormula_eq_legacy row

theorem encode_entailsAt_iff_sound (matrix : Syntax) :
    (encode matrix).EntailsAt Classical.bottom ↔ matrix.toLegacy.Sound := by
  rw [encode_eq_matrixSequent]
  exact Refutation.Tagged.matrixSequent_syllogism_iff matrix.toLegacy

private theorem legacySound_of_perms
    {sourceLeft targetLeft : List LegacyClause}
    {sourceRight targetRight : List LegacyCube}
    (left : sourceLeft.Perm targetLeft) (right : sourceRight.Perm targetRight)
    (sound : (Nucleus.Hol.Ethane.ClassicalMatrix.Sequent.mk
      ⟨sourceLeft⟩ ⟨sourceRight⟩).Sound) :
    (Nucleus.Hol.Ethane.ClassicalMatrix.Sequent.mk
      ⟨targetLeft⟩ ⟨targetRight⟩).Sound := by
  intro valuation targetPremise
  have sourcePremise :
      (Nucleus.Hol.Ethane.ClassicalMatrix.Cnf.mk sourceLeft).Holds valuation := by
    intro clause member
    exact targetPremise clause (left.mem_iff.mp member)
  obtain ⟨cube, member, truth⟩ := sound valuation sourcePremise
  exact ⟨cube, right.mem_iff.mp member, truth⟩

private structure Selection (α : Type) where
  before : List α
  value : α
  after : List α

private def select? : Nat → List α → Option (Selection α)
  | _, [] => none
  | 0, value :: values => some ⟨[], value, values⟩
  | index + 1, value :: values => do
      let selected ← select? index values
      some ⟨value :: selected.before, selected.value, selected.after⟩

private theorem select?_result {index : Nat} {values : List α}
    {selected : Selection α} (found : select? index values = some selected) :
    values = selected.before ++ selected.value :: selected.after := by
  induction index generalizing values selected with
  | zero =>
      cases values with
      | nil => simp [select?] at found
      | cons value values =>
          have equal : Selection.mk [] value values = selected := by
            simpa [select?] using Option.some.inj found
          subst selected
          rfl
  | succ index ih =>
      cases values with
      | nil => simp [select?] at found
      | cons value values =>
          cases recursive : select? index values with
          | none => simp [select?, recursive] at found
          | some tail =>
              rw [select?, recursive] at found
              have equal : Selection.mk (value :: tail.before) tail.value tail.after =
                  selected := by
                exact Option.some.inj found
              subst selected
              have tailResult : values = tail.before ++ tail.value :: tail.after :=
                ih (selected := tail) recursive
              rw [tailResult]
              rfl

def negateRow (row : List (Classical.Literal Nat)) :
    List (Classical.Literal Nat) := row.map Classical.Literal.neg

@[simp] theorem toLegacyLiteral_neg (literal : Classical.Literal Nat) :
    toLegacyLiteral literal.neg =
      Nucleus.Hol.Ethane.ClassicalMatrix.Lit.neg (toLegacyLiteral literal) := by
  cases literal with
  | mk atom negative => cases negative <;> rfl

/-- Remove matching singleton rows and perform legacy matrix cut. -/
def unitCutTarget? (pivot : Classical.Literal Nat)
    (left right : Tagged.Sequent Nat) : Option (Tagged.Sequent Nat) := do
  let leftMatrix ← decode? left
  let rightMatrix ← decode? right
  let leftRest ← Derive.eraseFirst? [pivot] leftMatrix.dnf
  let rightRest ← Derive.eraseFirst? [pivot] rightMatrix.cnf
  some (encode ⟨leftMatrix.cnf ++ rightRest, leftRest ++ rightMatrix.dnf⟩)

/-- Remove complementary singleton DNF rows and perform matrix resolution. -/
def unitResolveTarget? (pivot : Classical.Literal Nat)
    (left right : Tagged.Sequent Nat) : Option (Tagged.Sequent Nat) := do
  let leftMatrix ← decode? left
  let rightMatrix ← decode? right
  let leftRest ← Derive.eraseFirst? [pivot] leftMatrix.dnf
  let rightRest ← Derive.eraseFirst? [pivot.neg] rightMatrix.dnf
  some (encode ⟨leftMatrix.cnf ++ rightMatrix.cnf, leftRest ++ rightRest⟩)

/-- Move an indexed CNF row to the DNF after pointwise complementation. -/
def crossCnfRowTarget? (source : Tagged.Sequent Nat) (rowIndex : Nat) :
    Option (Tagged.Sequent Nat) := do
  let matrix ← decode? source
  let selected ← select? rowIndex matrix.cnf
  some (encode ⟨selected.before ++ selected.after,
    matrix.dnf ++ [negateRow selected.value]⟩)

/-- Move an indexed DNF row to the CNF after pointwise complementation. -/
def crossDnfRowTarget? (source : Tagged.Sequent Nat) (rowIndex : Nat) :
    Option (Tagged.Sequent Nat) := do
  let matrix ← decode? source
  let selected ← select? rowIndex matrix.dnf
  some (encode ⟨matrix.cnf ++ [negateRow selected.value],
    selected.before ++ selected.after⟩)

theorem unitCutTarget?_entailsAt {pivot : Classical.Literal Nat}
    {left right result : Tagged.Sequent Nat}
    (derived : unitCutTarget? pivot left right = some result)
    (leftSound : left.EntailsAt Classical.bottom)
    (rightSound : right.EntailsAt Classical.bottom) :
    result.EntailsAt Classical.bottom := by
  unfold unitCutTarget? at derived
  cases leftDecoded : decode? left with
  | none => simp [leftDecoded] at derived
  | some leftMatrix =>
      rw [leftDecoded] at derived
      cases rightDecoded : decode? right with
      | none => simp [rightDecoded] at derived
      | some rightMatrix =>
          rw [rightDecoded] at derived
          change (do
            let leftRest ← Derive.eraseFirst? [pivot] leftMatrix.dnf
            let rightRest ← Derive.eraseFirst? [pivot] rightMatrix.cnf
            some (encode ⟨leftMatrix.cnf ++ rightRest,
              leftRest ++ rightMatrix.dnf⟩)) = some result at derived
          cases leftErased : Derive.eraseFirst? [pivot] leftMatrix.dnf with
          | none => simp [leftErased] at derived
          | some leftRest =>
              rw [leftErased] at derived
              cases rightErased : Derive.eraseFirst? [pivot] rightMatrix.cnf with
              | none => simp [rightErased] at derived
              | some rightRest =>
                  rw [rightErased] at derived
                  have resultEqual : result = encode
                      ⟨leftMatrix.cnf ++ rightRest,
                        leftRest ++ rightMatrix.dnf⟩ :=
                    (Option.some.inj derived).symm
                  subst result
                  have leftEqual := decode?_result leftDecoded
                  have rightEqual := decode?_result rightDecoded
                  subst left
                  subst right
                  have leftRows : (leftMatrix.toLegacy.right.cubes).Perm
                      (legacyCube [pivot] :: leftRest.map legacyCube) := by
                    simpa [Syntax.toLegacy] using
                      (Derive.eraseFirst?_perm_front leftErased).map legacyCube
                  have rightRows : (rightMatrix.toLegacy.left.clauses).Perm
                      (legacyClause [pivot] :: rightRest.map legacyClause) := by
                    simpa [Syntax.toLegacy] using
                      (Derive.eraseFirst?_perm_front rightErased).map legacyClause
                  have leftReordered := legacySound_of_perms
                    (List.Perm.refl leftMatrix.toLegacy.left.clauses) leftRows
                    ((encode_entailsAt_iff_sound leftMatrix).mp leftSound)
                  have rightReordered := legacySound_of_perms rightRows
                    (List.Perm.refl rightMatrix.toLegacy.right.cubes)
                    ((encode_entailsAt_iff_sound rightMatrix).mp rightSound)
                  apply (encode_entailsAt_iff_sound _).mpr
                  simpa [Syntax.toLegacy, legacyClause, legacyCube,
                    List.map_append] using
                    Nucleus.Hol.Ethane.ClassicalMatrix.cut
                      (toLegacyLiteral pivot) leftReordered rightReordered

theorem unitResolveTarget?_entailsAt {pivot : Classical.Literal Nat}
    {left right result : Tagged.Sequent Nat}
    (derived : unitResolveTarget? pivot left right = some result)
    (leftSound : left.EntailsAt Classical.bottom)
    (rightSound : right.EntailsAt Classical.bottom) :
    result.EntailsAt Classical.bottom := by
  unfold unitResolveTarget? at derived
  cases leftDecoded : decode? left with
  | none => simp [leftDecoded] at derived
  | some leftMatrix =>
      rw [leftDecoded] at derived
      cases rightDecoded : decode? right with
      | none => simp [rightDecoded] at derived
      | some rightMatrix =>
          rw [rightDecoded] at derived
          change (do
            let leftRest ← Derive.eraseFirst? [pivot] leftMatrix.dnf
            let rightRest ← Derive.eraseFirst? [pivot.neg] rightMatrix.dnf
            some (encode ⟨leftMatrix.cnf ++ rightMatrix.cnf,
              leftRest ++ rightRest⟩)) = some result at derived
          cases leftErased : Derive.eraseFirst? [pivot] leftMatrix.dnf with
          | none => simp [leftErased] at derived
          | some leftRest =>
              rw [leftErased] at derived
              cases rightErased : Derive.eraseFirst? [pivot.neg] rightMatrix.dnf with
              | none => simp [rightErased] at derived
              | some rightRest =>
                  rw [rightErased] at derived
                  have resultEqual : result = encode
                      ⟨leftMatrix.cnf ++ rightMatrix.cnf,
                        leftRest ++ rightRest⟩ :=
                    (Option.some.inj derived).symm
                  subst result
                  have leftEqual := decode?_result leftDecoded
                  have rightEqual := decode?_result rightDecoded
                  subst left
                  subst right
                  have leftRows : (leftMatrix.toLegacy.right.cubes).Perm
                      (legacyCube [pivot] :: leftRest.map legacyCube) := by
                    simpa [Syntax.toLegacy] using
                      (Derive.eraseFirst?_perm_front leftErased).map legacyCube
                  have rightRows : (rightMatrix.toLegacy.right.cubes).Perm
                      (legacyCube [pivot.neg] :: rightRest.map legacyCube) := by
                    simpa [Syntax.toLegacy] using
                      (Derive.eraseFirst?_perm_front rightErased).map legacyCube
                  have leftReordered := legacySound_of_perms
                    (List.Perm.refl leftMatrix.toLegacy.left.clauses) leftRows
                    ((encode_entailsAt_iff_sound leftMatrix).mp leftSound)
                  have rightReordered := legacySound_of_perms
                    (List.Perm.refl rightMatrix.toLegacy.left.clauses) rightRows
                    ((encode_entailsAt_iff_sound rightMatrix).mp rightSound)
                  apply (encode_entailsAt_iff_sound _).mpr
                  simpa [Syntax.toLegacy, legacyClause, legacyCube,
                    List.map_append, toLegacyLiteral_neg] using
                    Nucleus.Hol.Ethane.ClassicalMatrix.resolution
                      (toLegacyLiteral pivot) leftReordered rightReordered

@[simp] theorem legacyCube_negateRow
    (row : List (Classical.Literal Nat)) :
    legacyCube (negateRow row) =
      Nucleus.Hol.Ethane.ClassicalMatrix.Clause.neg (legacyClause row) := by
  simp [legacyCube, legacyClause, negateRow,
    Nucleus.Hol.Ethane.ClassicalMatrix.Clause.neg, List.map_map,
    Function.comp_def]

@[simp] theorem legacyClause_negateRow
    (row : List (Classical.Literal Nat)) :
    legacyClause (negateRow row) =
      Nucleus.Hol.Ethane.ClassicalMatrix.Cube.neg (legacyCube row) := by
  simp [legacyCube, legacyClause, negateRow,
    Nucleus.Hol.Ethane.ClassicalMatrix.Cube.neg, List.map_map,
    Function.comp_def]

theorem crossCnfRowTarget?_entailsAt {source result : Tagged.Sequent Nat}
    {rowIndex : Nat}
    (derived : crossCnfRowTarget? source rowIndex = some result)
    (sourceSound : source.EntailsAt Classical.bottom) :
    result.EntailsAt Classical.bottom := by
  unfold crossCnfRowTarget? at derived
  cases decoded : decode? source with
  | none => simp [decoded] at derived
  | some matrix =>
      rw [decoded] at derived
      change (do
        let selected ← select? rowIndex matrix.cnf
        some (encode ⟨selected.before ++ selected.after,
          matrix.dnf ++ [negateRow selected.value]⟩)) = some result at derived
      cases found : select? rowIndex matrix.cnf with
      | none => simp [found] at derived
      | some selected =>
          rw [found] at derived
          have resultEqual : result = encode
              ⟨selected.before ++ selected.after,
                matrix.dnf ++ [negateRow selected.value]⟩ :=
            (Option.some.inj derived).symm
          subst result
          have sourceEqual := decode?_result decoded
          subst source
          have decomposition := select?_result found
          have sourceLegacy := (encode_entailsAt_iff_sound matrix).mp sourceSound
          simp only [Syntax.toLegacy] at sourceLegacy
          rw [decomposition] at sourceLegacy
          have transferred :=
            Nucleus.Hol.Ethane.ClassicalMatrix.transferClauseRight
              (legacyClause selected.value) (by
                simpa [Syntax.toLegacy, List.map_append] using sourceLegacy)
          have reordered := legacySound_of_perms
            (List.Perm.refl
              ((selected.before.map legacyClause) ++ selected.after.map legacyClause))
            (List.perm_append_comm :
              ([Nucleus.Hol.Ethane.ClassicalMatrix.Clause.neg
                  (legacyClause selected.value)] ++ matrix.dnf.map legacyCube).Perm
                (matrix.dnf.map legacyCube ++
                  [Nucleus.Hol.Ethane.ClassicalMatrix.Clause.neg
                    (legacyClause selected.value)])) transferred
          apply (encode_entailsAt_iff_sound _).mpr
          simpa [Syntax.toLegacy, List.map_append] using reordered

theorem crossDnfRowTarget?_entailsAt {source result : Tagged.Sequent Nat}
    {rowIndex : Nat}
    (derived : crossDnfRowTarget? source rowIndex = some result)
    (sourceSound : source.EntailsAt Classical.bottom) :
    result.EntailsAt Classical.bottom := by
  unfold crossDnfRowTarget? at derived
  cases decoded : decode? source with
  | none => simp [decoded] at derived
  | some matrix =>
      rw [decoded] at derived
      change (do
        let selected ← select? rowIndex matrix.dnf
        some (encode ⟨matrix.cnf ++ [negateRow selected.value],
          selected.before ++ selected.after⟩)) = some result at derived
      cases found : select? rowIndex matrix.dnf with
      | none => simp [found] at derived
      | some selected =>
          rw [found] at derived
          have resultEqual : result = encode
              ⟨matrix.cnf ++ [negateRow selected.value],
                selected.before ++ selected.after⟩ :=
            (Option.some.inj derived).symm
          subst result
          have sourceEqual := decode?_result decoded
          subst source
          have decomposition := select?_result found
          have sourceLegacy := (encode_entailsAt_iff_sound matrix).mp sourceSound
          simp only [Syntax.toLegacy] at sourceLegacy
          rw [decomposition] at sourceLegacy
          have transferred :=
            Nucleus.Hol.Ethane.ClassicalMatrix.transferCubeLeft
              (legacyCube selected.value) (by
                simpa [Syntax.toLegacy, List.map_append] using sourceLegacy)
          have reordered := legacySound_of_perms
            (List.perm_append_comm :
              ([Nucleus.Hol.Ethane.ClassicalMatrix.Cube.neg
                  (legacyCube selected.value)] ++ matrix.cnf.map legacyClause).Perm
                (matrix.cnf.map legacyClause ++
                  [Nucleus.Hol.Ethane.ClassicalMatrix.Cube.neg
                    (legacyCube selected.value)]))
            (List.Perm.refl
              (selected.before.map legacyCube ++ selected.after.map legacyCube))
            transferred
          apply (encode_entailsAt_iff_sound _).mpr
          simpa [Syntax.toLegacy, List.map_append] using reordered

private theorem legacyClause_holds_iff_of_mem
    {left right : List (Classical.Literal Nat)}
    (same : ∀ literal, literal ∈ left ↔ literal ∈ right)
    (valuation : Nucleus.Hol.Ethane.ClassicalMatrix.Valuation Nat) :
    (legacyClause left).Holds valuation ↔ (legacyClause right).Holds valuation := by
  constructor
  · rintro ⟨literal, member, truth⟩
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact ⟨toLegacyLiteral source,
      List.mem_map.mpr ⟨source, (same source).mp sourceMember, rfl⟩, truth⟩
  · rintro ⟨literal, member, truth⟩
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact ⟨toLegacyLiteral source,
      List.mem_map.mpr ⟨source, (same source).mpr sourceMember, rfl⟩, truth⟩

private theorem legacyCube_holds_iff_of_mem
    {left right : List (Classical.Literal Nat)}
    (same : ∀ literal, literal ∈ left ↔ literal ∈ right)
    (valuation : Nucleus.Hol.Ethane.ClassicalMatrix.Valuation Nat) :
    (legacyCube left).Holds valuation ↔ (legacyCube right).Holds valuation := by
  constructor
  · intro leftHolds literal member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact leftHolds (toLegacyLiteral source)
      (List.mem_map.mpr ⟨source, (same source).mpr sourceMember, rfl⟩)
  · intro rightHolds literal member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact rightHolds (toLegacyLiteral source)
      (List.mem_map.mpr ⟨source, (same source).mp sourceMember, rfl⟩)

private theorem replaceClause_sound
    {before after : List LegacyClause} {right : List LegacyCube}
    {source target : List (Classical.Literal Nat)}
    (same : ∀ literal, literal ∈ source ↔ literal ∈ target)
    (sound : (Nucleus.Hol.Ethane.ClassicalMatrix.Sequent.mk
      ⟨before ++ legacyClause source :: after⟩ ⟨right⟩).Sound) :
    (Nucleus.Hol.Ethane.ClassicalMatrix.Sequent.mk
      ⟨before ++ legacyClause target :: after⟩ ⟨right⟩).Sound := by
  intro valuation targetPremise
  apply sound valuation
  intro clause member
  rcases List.mem_append.mp member with member | member
  · exact targetPremise clause (List.mem_append_left _ member)
  · rcases List.mem_cons.mp member with equal | member
    · subst clause
      exact (legacyClause_holds_iff_of_mem same valuation).mpr
        (targetPremise (legacyClause target) (by simp))
    · exact targetPremise clause (List.mem_append_right _ (by simp [member]))

private theorem replaceCube_sound
    {left : List LegacyClause} {before after : List LegacyCube}
    {source target : List (Classical.Literal Nat)}
    (same : ∀ literal, literal ∈ source ↔ literal ∈ target)
    (sound : (Nucleus.Hol.Ethane.ClassicalMatrix.Sequent.mk ⟨left⟩
      ⟨before ++ legacyCube source :: after⟩).Sound) :
    (Nucleus.Hol.Ethane.ClassicalMatrix.Sequent.mk ⟨left⟩
      ⟨before ++ legacyCube target :: after⟩).Sound := by
  intro valuation premise
  obtain ⟨cube, member, truth⟩ := sound valuation premise
  rcases List.mem_append.mp member with member | member
  · exact ⟨cube, List.mem_append_left _ member, truth⟩
  · rcases List.mem_cons.mp member with equal | member
    · subst cube
      exact ⟨legacyCube target, by simp,
        (legacyCube_holds_iff_of_mem same valuation).mp truth⟩
    · exact ⟨cube, List.mem_append_right _ (by simp [member]), truth⟩

/-- Replace one row by a caller-supplied literal permutation. -/
def permuteRowTarget? (source : Tagged.Sequent Nat) (side : Side)
    (rowIndex : Nat) (candidate : List (Classical.Literal Nat)) :
    Option (Tagged.Sequent Nat) := do
  let matrix ← decode? source
  match side with
  | .cnf =>
      let selected ← select? rowIndex matrix.cnf
      if candidate.Perm selected.value then
        some (encode ⟨selected.before ++ candidate :: selected.after, matrix.dnf⟩)
      else none
  | .dnf =>
      let selected ← select? rowIndex matrix.dnf
      if candidate.Perm selected.value then
        some (encode ⟨matrix.cnf, selected.before ++ candidate :: selected.after⟩)
      else none

/-- Deduplicate literals in one selected row, preserving first occurrences. -/
def dedupeRowTarget? (source : Tagged.Sequent Nat) (side : Side)
    (rowIndex : Nat) : Option (Tagged.Sequent Nat) := do
  let matrix ← decode? source
  match side with
  | .cnf =>
      let selected ← select? rowIndex matrix.cnf
      some (encode ⟨selected.before ++ selected.value.eraseDups :: selected.after,
        matrix.dnf⟩)
  | .dnf =>
      let selected ← select? rowIndex matrix.dnf
      some (encode ⟨matrix.cnf,
        selected.before ++ selected.value.eraseDups :: selected.after⟩)

theorem permuteRowTarget?_entailsAt {source result : Tagged.Sequent Nat}
    {side : Side} {rowIndex : Nat}
    {candidate : List (Classical.Literal Nat)}
    (derived : permuteRowTarget? source side rowIndex candidate = some result)
    (sourceSound : source.EntailsAt Classical.bottom) :
    result.EntailsAt Classical.bottom := by
  unfold permuteRowTarget? at derived
  cases decoded : decode? source with
  | none => simp [decoded] at derived
  | some matrix =>
      rw [decoded] at derived
      cases side with
      | cnf =>
          change (do
            let selected ← select? rowIndex matrix.cnf
            if candidate.Perm selected.value then
              some (encode ⟨selected.before ++ candidate :: selected.after,
                matrix.dnf⟩)
            else none) = some result at derived
          cases found : select? rowIndex matrix.cnf with
          | none => simp [found] at derived
          | some selected =>
              rw [found] at derived
              change (if candidate.Perm selected.value then
                some (encode ⟨selected.before ++ candidate :: selected.after,
                  matrix.dnf⟩) else none) = some result at derived
              split at derived
              next permutation =>
                have resultEqual : result = encode
                    ⟨selected.before ++ candidate :: selected.after,
                      matrix.dnf⟩ := (Option.some.inj derived).symm
                subst result
                have sourceEqual := decode?_result decoded
                subst source
                have decomposition := select?_result found
                have sourceLegacy :=
                  (encode_entailsAt_iff_sound matrix).mp sourceSound
                simp only [Syntax.toLegacy] at sourceLegacy
                rw [decomposition] at sourceLegacy
                apply (encode_entailsAt_iff_sound _).mpr
                simpa [Syntax.toLegacy, List.map_append] using
                  replaceClause_sound
                    (source := selected.value) (target := candidate)
                    (same := fun literal => (permutation.mem_iff).symm)
                    (by simpa only [List.map_append, List.map_cons] using sourceLegacy)
              next => contradiction
      | dnf =>
          change (do
            let selected ← select? rowIndex matrix.dnf
            if candidate.Perm selected.value then
              some (encode ⟨matrix.cnf,
                selected.before ++ candidate :: selected.after⟩)
            else none) = some result at derived
          cases found : select? rowIndex matrix.dnf with
          | none => simp [found] at derived
          | some selected =>
              rw [found] at derived
              change (if candidate.Perm selected.value then
                some (encode ⟨matrix.cnf,
                  selected.before ++ candidate :: selected.after⟩)
                else none) = some result at derived
              split at derived
              next permutation =>
                have resultEqual : result = encode
                    ⟨matrix.cnf,
                      selected.before ++ candidate :: selected.after⟩ :=
                  (Option.some.inj derived).symm
                subst result
                have sourceEqual := decode?_result decoded
                subst source
                have decomposition := select?_result found
                have sourceLegacy :=
                  (encode_entailsAt_iff_sound matrix).mp sourceSound
                simp only [Syntax.toLegacy] at sourceLegacy
                rw [decomposition] at sourceLegacy
                apply (encode_entailsAt_iff_sound _).mpr
                simpa [Syntax.toLegacy, List.map_append] using
                  replaceCube_sound
                    (source := selected.value) (target := candidate)
                    (same := fun literal => (permutation.mem_iff).symm)
                    (by simpa only [List.map_append, List.map_cons] using sourceLegacy)
              next => contradiction

theorem dedupeRowTarget?_entailsAt {source result : Tagged.Sequent Nat}
    {side : Side} {rowIndex : Nat}
    (derived : dedupeRowTarget? source side rowIndex = some result)
    (sourceSound : source.EntailsAt Classical.bottom) :
    result.EntailsAt Classical.bottom := by
  unfold dedupeRowTarget? at derived
  cases decoded : decode? source with
  | none => simp [decoded] at derived
  | some matrix =>
      rw [decoded] at derived
      cases side with
      | cnf =>
          change (do
            let selected ← select? rowIndex matrix.cnf
            some (encode ⟨selected.before ++ selected.value.eraseDups :: selected.after,
              matrix.dnf⟩)) = some result at derived
          cases found : select? rowIndex matrix.cnf with
          | none => simp [found] at derived
          | some selected =>
              rw [found] at derived
              have resultEqual : result = encode
                  ⟨selected.before ++ selected.value.eraseDups :: selected.after,
                    matrix.dnf⟩ := (Option.some.inj derived).symm
              subst result
              have sourceEqual := decode?_result decoded
              subst source
              have decomposition := select?_result found
              have sourceLegacy :=
                (encode_entailsAt_iff_sound matrix).mp sourceSound
              simp only [Syntax.toLegacy] at sourceLegacy
              rw [decomposition] at sourceLegacy
              apply (encode_entailsAt_iff_sound _).mpr
              simpa [Syntax.toLegacy, List.map_append] using
                replaceClause_sound (source := selected.value)
                  (target := selected.value.eraseDups)
                  (same := by intro literal; simp)
                  (by simpa only [List.map_append, List.map_cons] using sourceLegacy)
      | dnf =>
          change (do
            let selected ← select? rowIndex matrix.dnf
            some (encode ⟨matrix.cnf,
              selected.before ++ selected.value.eraseDups :: selected.after⟩)) =
                some result at derived
          cases found : select? rowIndex matrix.dnf with
          | none => simp [found] at derived
          | some selected =>
              rw [found] at derived
              have resultEqual : result = encode
                  ⟨matrix.cnf,
                    selected.before ++ selected.value.eraseDups :: selected.after⟩ :=
                (Option.some.inj derived).symm
              subst result
              have sourceEqual := decode?_result decoded
              subst source
              have decomposition := select?_result found
              have sourceLegacy :=
                (encode_entailsAt_iff_sound matrix).mp sourceSound
              simp only [Syntax.toLegacy] at sourceLegacy
              rw [decomposition] at sourceLegacy
              apply (encode_entailsAt_iff_sound _).mpr
              simpa [Syntax.toLegacy, List.map_append] using
                replaceCube_sound (source := selected.value)
                  (target := selected.value.eraseDups)
                  (same := by intro literal; simp)
                  (by simpa only [List.map_append, List.map_cons] using sourceLegacy)

/-! ## Executable correspondence fixture -/

private def fixtureP : Classical.Literal Nat := ⟨1, false⟩
private def fixtureQ : Classical.Literal Nat := ⟨2, false⟩

set_option linter.style.nativeDecide false in
/-- Rust and Lean both retain the first occurrence during row deduplication. -/
example : dedupeRowTarget? (encode ⟨[[fixtureP, fixtureQ, fixtureP]], []⟩)
    .cnf 0 = some (encode ⟨[[fixtureP, fixtureQ]], []⟩) := by
  native_decide

/-- The exact singleton matrix identity used by the legacy runtime. -/
def identity (pivot : Classical.Literal Nat) : Tagged.Sequent Nat :=
  encode ⟨[[pivot]], [[pivot]]⟩

theorem identity_entailsAt (pivot : Classical.Literal Nat) :
    (identity pivot).EntailsAt Classical.bottom := by
  apply (encode_entailsAt_iff_sound _).mpr
  simpa [identity, Syntax.toLegacy, legacyClause, legacyCube] using
    Nucleus.Hol.Ethane.ClassicalMatrix.identity (toLegacyLiteral pivot)

/-- Append one CNF row to a strict matrix sequent. -/
def weakenCnfRowTarget? (source : Tagged.Sequent Nat)
    (row : List (Classical.Literal Nat)) : Option (Tagged.Sequent Nat) := do
  let matrix ← decode? source
  some (encode { matrix with cnf := matrix.cnf ++ [row] })

/-- Append one DNF row to a strict matrix sequent. -/
def weakenDnfRowTarget? (source : Tagged.Sequent Nat)
    (row : List (Classical.Literal Nat)) : Option (Tagged.Sequent Nat) := do
  let matrix ← decode? source
  some (encode { matrix with dnf := matrix.dnf ++ [row] })

theorem weakenCnfRowTarget?_entailsAt {source result : Tagged.Sequent Nat}
    {row : List (Classical.Literal Nat)}
    (derived : weakenCnfRowTarget? source row = some result)
    (sourceSound : source.EntailsAt Classical.bottom) :
    result.EntailsAt Classical.bottom := by
  unfold weakenCnfRowTarget? at derived
  cases decoded : decode? source with
  | none => simp [decoded] at derived
  | some matrix =>
      rw [decoded] at derived
      have resultEqual : result = encode { matrix with cnf := matrix.cnf ++ [row] } :=
        (Option.some.inj derived).symm
      subst result
      have sourceEqual := decode?_result decoded
      subst source
      apply (encode_entailsAt_iff_sound _).mpr
      simpa [Syntax.toLegacy, legacyClause] using
        Nucleus.Hol.Ethane.ClassicalMatrix.weaken
          (extraLeft := [⟨row.map toLegacyLiteral⟩])
          (extraRight := []) ((encode_entailsAt_iff_sound matrix).mp sourceSound)

theorem weakenDnfRowTarget?_entailsAt {source result : Tagged.Sequent Nat}
    {row : List (Classical.Literal Nat)}
    (derived : weakenDnfRowTarget? source row = some result)
    (sourceSound : source.EntailsAt Classical.bottom) :
    result.EntailsAt Classical.bottom := by
  unfold weakenDnfRowTarget? at derived
  cases decoded : decode? source with
  | none => simp [decoded] at derived
  | some matrix =>
      rw [decoded] at derived
      have resultEqual : result = encode { matrix with dnf := matrix.dnf ++ [row] } :=
        (Option.some.inj derived).symm
      subst result
      have sourceEqual := decode?_result decoded
      subst source
      apply (encode_entailsAt_iff_sound _).mpr
      simpa [Syntax.toLegacy, legacyCube] using
        Nucleus.Hol.Ethane.ClassicalMatrix.weaken
          (extraLeft := []) (extraRight := [⟨row.map toLegacyLiteral⟩])
          ((encode_entailsAt_iff_sound matrix).mp sourceSound)

end Nucleus.Classical.Tagged.Runtime.Matrix
