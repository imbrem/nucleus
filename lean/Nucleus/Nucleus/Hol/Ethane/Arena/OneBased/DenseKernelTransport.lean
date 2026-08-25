import Nucleus.Hol.Ethane.Arena.OneBased.Layout
import Nucleus.Hol.Ethane.Arena.OneBased.FusedUnionProofs

/-!
# Transporting the HOL kernel across dense classifier changes

Changing the fused conversion column may replace the reference advertising a
row's classifier.  Resolution is consequently not literally invariant: a term
can resolve at a convertible, syntactically distinct type.  This module states
the exact semantic transport boundary and lifts it through sorting, recursive
resolution clients, and the complete legacy `CoreKernelValid` invariant.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true

namespace Columns.Dense

/-- Every directed classifier route in a checked fused column moves strictly
backward from its source all the way to its classifier. -/
theorem ClassifierRoute.classifier_lt_value
    (route : ClassifierRoute dense classifier value length)
    (decreases : dense.conv.Decreases) : classifier < value := by
  induction route with
  | terminal edge => exact decreases edge.1
  | step edge tail ih => exact ih.trans (decreases edge.1)

/-- A successful classifier lookup in a checked kernel always names an
earlier allocation.  This is the well-founded recursive edge missing from the
raw defensive decoder model. -/
theorem FusedChecked.classifier_lt (checked : FusedChecked dense)
    (resident : dense.expr? value ≠ none)
    (found : dense.classifier? value = some classifier) : classifier < value := by
  have classified := dense.classifier?_sound value classifier checked.toChecked
    resident found
  obtain ⟨length, _, route⟩ := HasClassifier.route checked resident classified
  exact route.classifier_lt_value checked.convDecreases

end Columns.Dense

open Columns

/-- A classifier traversal cannot start from a missing syntax row.  Raw dense
columns may contain dangling cells, but a missing source has no category and
therefore cannot yield a classifier. -/
theorem Dense.classifierAt?_none_of_tagSort?_none
    {dense : Dense} {reference : Ref} {fuel : Nat}
    (missing : dense.tagSort? reference = none) :
    dense.classifierAt? fuel reference = none := by
  induction fuel generalizing reference with
  | zero => rfl
  | succ fuel ih =>
      simp only [Dense.classifierAt?]
      cases link : dense.conv.get? reference with
      | none => rfl
      | some target =>
          rw [missing]
          by_cases targetMissing : dense.tagSort? target = none
          · simp [targetMissing, ih targetMissing]
          · have reverse : (none : Option TagSort) ≠ dense.tagSort? target :=
              Ne.symm targetMissing
            simp [reverse, Dense.classifierSort?]

theorem Dense.classifier?_source_resident
    {dense : Dense} {reference classifier : Ref}
    (found : dense.classifier? reference = some classifier) :
    dense.expr? reference ≠ none := by
  intro missing
  have noCategory : dense.tagSort? reference = none := by
    simp [Dense.tagSort?, missing]
  have noClassifier := dense.classifierAt?_none_of_tagSort?_none
    (fuel := dense.defs.length + 1) noCategory
  unfold Dense.classifier? at found
  rw [noClassifier] at found
  contradiction

/-- Retrieve the allocation bound attached to a structurally valid row. -/
theorem RowsValid.rowValidAt (valid : RowsValid allocated rows)
    (found : rows[position]? = some row) : RowValid (allocated + position) row := by
  induction rows generalizing allocated position with
  | nil => simp at found
  | cons head tail ih =>
      cases position with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst row
          simpa [RowsValid] using valid.1
      | succ position =>
          simp only [List.getElem?_cons_succ] at found
          have tailValid := valid.2
          have result := ih tailValid found
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- Ordinary syntax children of a resident row are strictly earlier than the
row itself. -/
theorem Arena.StructurallyValid.exprChild_lt
    (arena : Arena) (reference child : Ref) (row : detail.Expr)
    (valid : Arena.StructurallyValid arena)
    (found : arena.row? reference = some row)
    (member : child ∈ row.children) : child < reference := by
  have exprFound : arena.dense.expr? reference = some row := by
    simpa [Arena.row?, Dense.row?] using found
  let rawRow : detail.Row := { expr := row }
  have rowValid : RowValid (reference.value.toNat - 1) rawRow := by
    have lookup : arena.syntaxRows[(reference.value.toNat - 1)]? = some rawRow := by
      simpa [Arena.syntaxRows, rawRow, Dense.expr?] using exprFound
    simpa using valid.rowValidAt lookup
  have bound := rowValid child (by simpa [detail.Row.children] using member)
  change child.value.toNat < reference.value.toNat
  have positive : 0 < reference.value.toNat := by
    apply Nat.pos_of_ne_zero
    intro zero
    change reference.1.toNat = 0 at zero
    exact reference.property.1 (UInt64.toNat_inj.mp zero)
  omega

namespace Value

set_option linter.unusedSimpArgs false

/-- The precise effect of dense classifier re-advertising: syntax is stable,
while a term may acquire a convertible advertised type. Equality's operand
type is now an immutable expression child, so it follows this same rule. -/
inductive SamePayload : Value → Value → Prop where
  | kind (kind : Kind) : SamePayload (.kind kind) (.kind kind)
  | family (kind : Kind) (expression : EmptyExpr (.kind kind)) :
      SamePayload (.family kind expression) (.family kind expression)
  | term (oldType newType : EmptyTy) (expression : EmptyTm)
      (conversion : Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) oldType.toHolE newType.toHolE)) :
      SamePayload (.term oldType expression) (.term newType expression)

/-- Reflexive payload transport is available for logically well-formed
values.  The premise matters for terms: a named advertised type need not
lower in the empty scope unless the resolved value is well formed. -/
theorem SamePayload.refl (wellFormed : value.WellFormed) :
    SamePayload value value := by
  cases value with
  | kind kind => exact .kind kind
  | family kind expression => exact .family kind expression
  | term type expression =>
      cases equal_self wellFormed with
      | term _ _ classifierConversion _ =>
          exact .term type type expression classifierConversion

theorem SamePayload.equal (same : SamePayload oldValue newValue)
    (oldWellFormed : oldValue.WellFormed)
    (newWellFormed : newValue.WellFormed) : Equal oldValue newValue := by
  cases same with
  | kind kind => exact .kind kind
  | family kind expression => exact equal_self oldWellFormed
  | term oldType newType expression classifierConversion =>
      have self := equal_self oldWellFormed
      cases self with
      | term _ _ _ termConversion =>
          exact .term oldWellFormed newWellFormed classifierConversion termConversion

theorem SamePayload.tagSort_eq (same : SamePayload oldValue newValue) :
    oldValue.tagSort = newValue.tagSort := by
  cases same <;> rfl

theorem Equal.family_from_star
    (equal : Equal (.family .star oldType) value) :
    ∃ newType, value = .family .star newType ∧
      Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) oldType.toHolE newType.toHolE) := by
  cases equal with
  | family conversion => exact ⟨_, rfl, conversion⟩

/-- Pointwise simulation restricted to the children of one expression.

This is the induction-friendly form: recursive resolution only has to
transport references that the current row actually consults. -/
def LookupSameOn (references : List Ref)
    (oldLookup newLookup : Ref → Option Value) : Prop :=
  ∀ reference, reference ∈ references → ∀ oldValue,
    oldLookup reference = some oldValue →
      ∃ newValue, newLookup reference = some newValue ∧
        SamePayload oldValue newValue

theorem LookupSameOn.kind
    (same : LookupSameOn references oldLookup newLookup)
    (member : reference ∈ references)
    (found : oldLookup reference = some (.kind kindValue)) :
    newLookup reference = some (.kind kindValue) := by
  obtain ⟨newValue, newFound, payload⟩ :=
    same reference member (.kind kindValue) found
  cases payload
  exact newFound

theorem LookupSameOn.family
    (same : LookupSameOn references oldLookup newLookup)
    (member : reference ∈ references)
    (found : oldLookup reference = some (.family kindValue expression)) :
    newLookup reference = some (.family kindValue expression) := by
  obtain ⟨newValue, newFound, payload⟩ :=
    same reference member (.family kindValue expression) found
  cases payload
  exact newFound

theorem LookupSameOn.term
    (same : LookupSameOn references oldLookup newLookup)
    (member : reference ∈ references)
    (found : oldLookup reference = some (.term type expression)) :
    ∃ newType, newLookup reference = some (.term newType expression) ∧
      Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) type.toHolE newType.toHolE) := by
  obtain ⟨newValue, newFound, payload⟩ :=
    same reference member (.term type expression) found
  cases payload with
  | term _ newType _ conversion => exact ⟨newType, newFound, conversion⟩

/-- Transport supplied for the row's possibly changed declared classifier. -/
def DeclaredSame (oldLookup newLookup : Ref → Option Value)
    (oldDeclared newDeclared : Option Ref) : Prop :=
  ∀ oldSort, oldDeclared = some oldSort →
    ∃ newSort, newDeclared = some newSort ∧
      ∀ oldType, oldLookup oldSort = some (.family .star oldType) →
        ∃ newType, newLookup newSort = some (.family .star newType) ∧
          Nonempty (Nucleus.HolE.Named.FamEq
            (.nil : TyScope []) oldType.toHolE newType.toHolE)

theorem DeclaredSame.family (same : DeclaredSame oldLookup newLookup
    oldDeclared newDeclared) (declared : oldDeclared = some oldSort)
    (found : oldLookup oldSort = some (.family .star oldType)) :
    ∃ newSort newType, newDeclared = some newSort ∧
      newLookup newSort = some (.family .star newType) ∧
      Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) oldType.toHolE newType.toHolE) := by
  obtain ⟨newSort, newDeclaredEq, transport⟩ := same oldSort declared
  obtain ⟨newType, newFound, conversion⟩ := transport oldType found
  exact ⟨newSort, newType, newDeclaredEq, newFound, conversion⟩

private theorem elaborateExpr_samePayload_app
    (lookups : LookupSameOn [function, argument] oldLocal newLocal)
    (declared : DeclaredSame oldLocal newLocal oldDeclared newDeclared)
    (found : elaborateExpr oldLocal oldForeign oldDeclared
      (.app function argument) = some oldValue) :
    ∃ newValue, elaborateExpr newLocal oldForeign newDeclared
        (.app function argument) = some newValue ∧
      SamePayload oldValue newValue := by
  cases functionFound : oldLocal function with
  | none => simp [elaborateExpr, functionFound] at found
  | some functionValue =>
    cases functionValue with
    | kind kind => simp [elaborateExpr, functionFound] at found
    | family kind expression => simp [elaborateExpr, functionFound] at found
    | term functionType functionExpression =>
      cases argumentFound : oldLocal argument with
      | none => simp [elaborateExpr, functionFound, argumentFound] at found
      | some argumentValue =>
        cases argumentValue with
        | kind kind => simp [elaborateExpr, functionFound, argumentFound] at found
        | family kind expression =>
            simp [elaborateExpr, functionFound, argumentFound] at found
        | term argumentType argumentExpression =>
          cases declaredFound : oldDeclared with
          | none =>
              simp [elaborateExpr, functionFound, argumentFound,
                declaredFound] at found
          | some oldSort =>
            cases sortFound : oldLocal oldSort with
            | none =>
                simp [elaborateExpr, functionFound, argumentFound,
                  declaredFound, sortFound] at found
            | some sortValue =>
              cases sortValue with
              | kind kind =>
                  simp [elaborateExpr, functionFound, argumentFound,
                    declaredFound, sortFound] at found
              | term type expression =>
                  simp [elaborateExpr, functionFound, argumentFound,
                    declaredFound, sortFound] at found
              | family kind oldAdvertised =>
                cases kind with
                | arr domain codomain =>
                    simp [elaborateExpr, functionFound, argumentFound,
                      declaredFound, sortFound] at found
                | star =>
                  obtain ⟨_newFunctionType, newFunctionFound, _⟩ :=
                    lookups.term (by simp) functionFound
                  obtain ⟨_newArgumentType, newArgumentFound, _⟩ :=
                    lookups.term (by simp) argumentFound
                  obtain ⟨_newSort, newAdvertised, newDeclaredFound,
                    newSortFound, conversion⟩ :=
                      declared.family declaredFound sortFound
                  have oldValueEq : oldValue = .term oldAdvertised
                      (.app functionExpression argumentExpression) := by
                    simpa [elaborateExpr, functionFound, argumentFound,
                      declaredFound, sortFound] using found.symm
                  refine ⟨.term newAdvertised
                    (.app functionExpression argumentExpression), ?_, ?_⟩
                  · simp [elaborateExpr, newFunctionFound, newArgumentFound,
                      newDeclaredFound, newSortFound]
                  · rw [oldValueEq]
                    exact .term oldAdvertised newAdvertised _ conversion

private theorem elaborateExpr_samePayload_lam
    (lookups : LookupSameOn [binder, body] oldLocal newLocal)
    (declared : DeclaredSame oldLocal newLocal oldDeclared newDeclared)
    (found : elaborateExpr oldLocal oldForeign oldDeclared (.lam binder body) =
      some oldValue) :
    ∃ newValue, elaborateExpr newLocal oldForeign newDeclared (.lam binder body) =
        some newValue ∧ SamePayload oldValue newValue := by
  cases binderFound : oldLocal binder with
  | none => simp [elaborateExpr, binderFound] at found
  | some binderValue =>
    cases binderValue with
    | kind kind => simp [elaborateExpr, binderFound] at found
    | family kind expression => simp [elaborateExpr, binderFound] at found
    | term binderType binderExpression =>
      cases binderDataFound : tmFvData? binderExpression with
      | none => simp [elaborateExpr, binderFound, binderDataFound] at found
      | some binderData =>
        rcases binderData with ⟨name, syntacticDomain⟩
        cases bodyFound : oldLocal body with
        | none =>
            simp [elaborateExpr, binderFound, binderDataFound, bodyFound] at found
        | some bodyValue =>
          cases bodyValue with
          | kind kind =>
              simp [elaborateExpr, binderFound, binderDataFound, bodyFound] at found
          | family kind expression =>
              simp [elaborateExpr, binderFound, binderDataFound, bodyFound] at found
          | term bodyType bodyExpression =>
            cases declaredFound : oldDeclared with
            | none =>
                simp [elaborateExpr, binderFound, binderDataFound, bodyFound,
                  declaredFound] at found
            | some oldSort =>
              cases sortFound : oldLocal oldSort with
              | none =>
                  simp [elaborateExpr, binderFound, binderDataFound, bodyFound,
                    declaredFound, sortFound] at found
              | some sortValue =>
                cases sortValue with
                | kind kind =>
                    simp [elaborateExpr, binderFound, binderDataFound, bodyFound,
                      declaredFound, sortFound] at found
                | term type expression =>
                    simp [elaborateExpr, binderFound, binderDataFound, bodyFound,
                      declaredFound, sortFound] at found
                | family kind oldAdvertised =>
                  cases kind with
                  | arr domain codomain =>
                      simp [elaborateExpr, binderFound, binderDataFound,
                        bodyFound, declaredFound, sortFound] at found
                  | star =>
                    obtain ⟨_newBinderType, newBinderFound, _⟩ :=
                      lookups.term (by simp) binderFound
                    obtain ⟨_newBodyType, newBodyFound, _⟩ :=
                      lookups.term (by simp) bodyFound
                    obtain ⟨_newSort, newAdvertised, newDeclaredFound,
                      newSortFound, conversion⟩ :=
                        declared.family declaredFound sortFound
                    have oldValueEq : oldValue = .term oldAdvertised
                        (.lam name syntacticDomain bodyExpression) := by
                      simpa [elaborateExpr, binderFound, binderDataFound,
                        bodyFound, declaredFound, sortFound] using found.symm
                    refine ⟨.term newAdvertised
                      (.lam name syntacticDomain bodyExpression), ?_, ?_⟩
                    · simp [elaborateExpr, newBinderFound, binderDataFound,
                        newBodyFound, newDeclaredFound, newSortFound]
                    · rw [oldValueEq]
                      exact .term oldAdvertised newAdvertised _ conversion

private theorem elaborateExpr_samePayload_eps
    (lookups : LookupSameOn [typeRef, predicate] oldLocal newLocal)
    (declared : DeclaredSame oldLocal newLocal oldDeclared newDeclared)
    (found : elaborateExpr oldLocal oldForeign oldDeclared
      (.eps typeRef predicate) = some oldValue) :
    ∃ newValue, elaborateExpr newLocal oldForeign newDeclared
        (.eps typeRef predicate) = some newValue ∧ SamePayload oldValue newValue := by
  cases typeFound : oldLocal typeRef with
  | none => simp [elaborateExpr, typeFound] at found
  | some typeValue =>
    cases typeValue with
    | kind kind => simp [elaborateExpr, typeFound] at found
    | term type expression => simp [elaborateExpr, typeFound] at found
    | family kind syntacticType =>
      cases kind with
      | arr domain codomain => simp [elaborateExpr, typeFound] at found
      | star =>
        cases predicateFound : oldLocal predicate with
        | none => simp [elaborateExpr, typeFound, predicateFound] at found
        | some predicateValue =>
          cases predicateValue with
          | kind kind => simp [elaborateExpr, typeFound, predicateFound] at found
          | family kind expression =>
              simp [elaborateExpr, typeFound, predicateFound] at found
          | term predicateType predicateExpression =>
            cases declaredFound : oldDeclared with
            | none =>
                simp [elaborateExpr, typeFound, predicateFound,
                  declaredFound] at found
            | some oldSort =>
              cases sortFound : oldLocal oldSort with
              | none =>
                  simp [elaborateExpr, typeFound, predicateFound,
                    declaredFound, sortFound] at found
              | some sortValue =>
                cases sortValue with
                | kind kind =>
                    simp [elaborateExpr, typeFound, predicateFound,
                      declaredFound, sortFound] at found
                | term type expression =>
                    simp [elaborateExpr, typeFound, predicateFound,
                      declaredFound, sortFound] at found
                | family kind oldAdvertised =>
                  cases kind with
                  | arr domain codomain =>
                      simp [elaborateExpr, typeFound, predicateFound,
                        declaredFound, sortFound] at found
                  | star =>
                    have newType := lookups.family (by simp) typeFound
                    obtain ⟨_newPredicateType, newPredicateFound, _⟩ :=
                      lookups.term (by simp) predicateFound
                    obtain ⟨_newSort, newAdvertised, newDeclaredFound,
                      newSortFound, conversion⟩ :=
                        declared.family declaredFound sortFound
                    have oldValueEq : oldValue = .term oldAdvertised
                        (.eps syntacticType predicateExpression) := by
                      simpa [elaborateExpr, typeFound, predicateFound,
                        declaredFound, sortFound] using found.symm
                    refine ⟨.term newAdvertised
                      (.eps syntacticType predicateExpression), ?_, ?_⟩
                    · simp [elaborateExpr, newType, newPredicateFound,
                        newDeclaredFound, newSortFound]
                    · rw [oldValueEq]
                      exact .term oldAdvertised newAdvertised _ conversion

private theorem elaborateExpr_samePayload_op2
    (lookups : LookupSameOn [left, right] oldLocal newLocal)
    (declared : DeclaredSame oldLocal newLocal oldDeclared newDeclared)
    (found : elaborateExpr oldLocal oldForeign oldDeclared (.op2 op left right) =
      some oldValue) :
    ∃ newValue, elaborateExpr newLocal oldForeign newDeclared
        (.op2 op left right) = some newValue ∧ SamePayload oldValue newValue := by
  cases leftFound : oldLocal left with
  | none => simp [elaborateExpr, leftFound] at found
  | some leftValue =>
    cases leftValue with
    | kind kind => simp [elaborateExpr, leftFound] at found
    | family kind family => simp [elaborateExpr, leftFound] at found
    | term leftType leftExpression =>
      cases rightFound : oldLocal right with
      | none => simp [elaborateExpr, leftFound, rightFound] at found
      | some rightValue =>
        cases rightValue with
        | kind kind => simp [elaborateExpr, leftFound, rightFound] at found
        | family kind family =>
            simp [elaborateExpr, leftFound, rightFound] at found
        | term rightType rightExpression =>
          cases declaredFound : oldDeclared with
          | none =>
              simp [elaborateExpr, leftFound, rightFound, declaredFound] at found
          | some oldSort =>
            cases sortFound : oldLocal oldSort with
            | none =>
                simp [elaborateExpr, leftFound, rightFound, declaredFound,
                  sortFound] at found
            | some sortValue =>
              cases sortValue with
              | kind kind =>
                  simp [elaborateExpr, leftFound, rightFound, declaredFound,
                    sortFound] at found
              | term type expression =>
                  simp [elaborateExpr, leftFound, rightFound, declaredFound,
                    sortFound] at found
              | family kind oldAdvertised =>
                cases kind with
                | arr domain codomain =>
                    simp [elaborateExpr, leftFound, rightFound, declaredFound,
                      sortFound] at found
                | star =>
                  obtain ⟨_newLeftType, newLeftFound, _⟩ :=
                    lookups.term (by simp) leftFound
                  obtain ⟨_newRightType, newRightFound, _⟩ :=
                    lookups.term (by simp) rightFound
                  obtain ⟨_newSort, newAdvertised, newDeclaredFound,
                    newSortFound, conversion⟩ :=
                      declared.family declaredFound sortFound
                  have oldValueEq : oldValue = .term oldAdvertised
                      (op.lower leftExpression rightExpression) := by
                    simpa [elaborateExpr, leftFound, rightFound, declaredFound,
                      sortFound] using found.symm
                  refine ⟨.term newAdvertised
                    (op.lower leftExpression rightExpression), ?_, ?_⟩
                  · simp [elaborateExpr, newLeftFound, newRightFound,
                      newDeclaredFound, newSortFound]
                  · rw [oldValueEq]
                    exact .term oldAdvertised newAdvertised _ conversion

private theorem elaborateExpr_samePayload_tyApp
    (lookups : LookupSameOn [function, argument] oldLocal newLocal)
    (found : elaborateExpr oldLocal oldForeign oldDeclared
      (.tyApp function argument) = some oldValue) :
    ∃ newValue, elaborateExpr newLocal oldForeign newDeclared
        (.tyApp function argument) = some newValue ∧ SamePayload oldValue newValue := by
  cases functionFound : oldLocal function with
  | none => simp [elaborateExpr, functionFound] at found
  | some functionValue =>
    cases functionValue with
    | kind kind => simp [elaborateExpr, functionFound] at found
    | term type expression => simp [elaborateExpr, functionFound] at found
    | family functionKind functionExpression =>
      cases functionKind with
      | star => simp [elaborateExpr, functionFound] at found
      | arr domain codomain =>
        cases argumentFound : oldLocal argument with
        | none => simp [elaborateExpr, functionFound, argumentFound] at found
        | some argumentValue =>
          cases argumentValue with
          | kind kind =>
              simp [elaborateExpr, functionFound, argumentFound] at found
          | term type expression =>
              simp [elaborateExpr, functionFound, argumentFound] at found
          | family actual argumentExpression =>
            by_cases actualDomain : actual = domain
            · have newFunction := lookups.family (by simp) functionFound
              have newArgument := lookups.family (by simp) argumentFound
              have oldValueEq : oldValue = .family codomain
                  (.tyApp functionExpression (actualDomain ▸ argumentExpression)) := by
                simpa [elaborateExpr, functionFound, argumentFound,
                  actualDomain] using found.symm
              refine ⟨.family codomain
                (.tyApp functionExpression (actualDomain ▸ argumentExpression)), ?_, ?_⟩
              · simp [elaborateExpr, newFunction, newArgument, actualDomain]
              · rw [oldValueEq]
                exact .family _ _
            · simp [elaborateExpr, functionFound, argumentFound,
                actualDomain] at found

private theorem elaborateExpr_samePayload_tyLam
    (lookups : LookupSameOn [binder, body] oldLocal newLocal)
    (found : elaborateExpr oldLocal oldForeign oldDeclared (.tyLam binder body) =
      some oldValue) :
    ∃ newValue, elaborateExpr newLocal oldForeign newDeclared (.tyLam binder body) =
        some newValue ∧ SamePayload oldValue newValue := by
  cases binderFound : oldLocal binder with
  | none => simp [elaborateExpr, binderFound] at found
  | some binderValue =>
    cases binderValue with
    | kind kind => simp [elaborateExpr, binderFound] at found
    | term type expression => simp [elaborateExpr, binderFound] at found
    | family domain binderExpression =>
      cases nameFound : tyFvName? binderExpression with
      | none => simp [elaborateExpr, binderFound, nameFound] at found
      | some name =>
        cases bodyFound : oldLocal body with
        | none => simp [elaborateExpr, binderFound, nameFound, bodyFound] at found
        | some bodyValue =>
          cases bodyValue with
          | kind kind =>
              simp [elaborateExpr, binderFound, nameFound, bodyFound] at found
          | term type expression =>
              simp [elaborateExpr, binderFound, nameFound, bodyFound] at found
          | family codomain bodyExpression =>
            have newBinder := lookups.family (by simp) binderFound
            have newBody := lookups.family (by simp) bodyFound
            have oldValueEq : oldValue = .family (.arr domain codomain)
                (.tyLam name bodyExpression) := by
              simpa [elaborateExpr, binderFound, nameFound, bodyFound]
                using found.symm
            refine ⟨.family (.arr domain codomain) (.tyLam name bodyExpression),
              ?_, ?_⟩
            · simp [elaborateExpr, newBinder, nameFound, newBody]
            · rw [oldValueEq]
              exact .family _ _

private theorem elaborateExpr_samePayload_eq
    (lookups : LookupSameOn [typeRef, left, right] oldLocal newLocal)
    (declared : DeclaredSame oldLocal newLocal oldDeclared newDeclared)
    (found : elaborateExpr oldLocal oldForeign oldDeclared
      (.eq typeRef left right) = some oldValue) :
    ∃ newValue, elaborateExpr newLocal oldForeign newDeclared
        (.eq typeRef left right) = some newValue ∧ SamePayload oldValue newValue := by
  cases typeFound : oldLocal typeRef with
  | none => simp [elaborateExpr, typeFound] at found
  | some typeValue =>
    cases typeValue with
    | kind kind => simp [elaborateExpr, typeFound] at found
    | term type expression => simp [elaborateExpr, typeFound] at found
    | family kind syntacticType =>
      cases kind with
      | arr domain codomain => simp [elaborateExpr, typeFound] at found
      | star =>
        cases leftFound : oldLocal left with
        | none => simp [elaborateExpr, typeFound, leftFound] at found
        | some leftValue =>
          cases leftValue with
          | kind kind => simp [elaborateExpr, typeFound, leftFound] at found
          | family kind expression =>
              simp [elaborateExpr, typeFound, leftFound] at found
          | term leftType leftExpression =>
            cases rightFound : oldLocal right with
            | none =>
                simp [elaborateExpr, typeFound, leftFound, rightFound] at found
            | some rightValue =>
              cases rightValue with
              | kind kind =>
                  simp [elaborateExpr, typeFound, leftFound, rightFound] at found
              | family kind expression =>
                  simp [elaborateExpr, typeFound, leftFound, rightFound] at found
              | term rightType rightExpression =>
                cases declaredFound : oldDeclared with
                | none =>
                    simp [elaborateExpr, typeFound, leftFound, rightFound,
                      declaredFound] at found
                | some oldSort =>
                  cases sortFound : oldLocal oldSort with
                  | none =>
                      simp [elaborateExpr, typeFound, leftFound, rightFound,
                        declaredFound, sortFound] at found
                  | some sortValue =>
                    cases sortValue with
                    | kind kind =>
                        simp [elaborateExpr, typeFound, leftFound, rightFound,
                          declaredFound, sortFound] at found
                    | term type expression =>
                        simp [elaborateExpr, typeFound, leftFound, rightFound,
                          declaredFound, sortFound] at found
                    | family kind oldAdvertised =>
                      cases kind with
                      | arr domain codomain =>
                          simp [elaborateExpr, typeFound, leftFound, rightFound,
                            declaredFound, sortFound] at found
                      | star =>
                        have newType := lookups.family (by simp) typeFound
                        obtain ⟨_newLeftType, newLeftFound, _⟩ :=
                          lookups.term (by simp) leftFound
                        obtain ⟨_newRightType, newRightFound, _⟩ :=
                          lookups.term (by simp) rightFound
                        obtain ⟨_newSort, newAdvertised, newDeclaredFound,
                          newSortFound, conversion⟩ :=
                            declared.family declaredFound sortFound
                        have oldValueEq : oldValue = .term oldAdvertised
                            (.eq syntacticType leftExpression rightExpression) := by
                          simpa [elaborateExpr, typeFound, leftFound, rightFound,
                            declaredFound, sortFound] using found.symm
                        refine ⟨.term newAdvertised
                          (.eq syntacticType leftExpression rightExpression), ?_, ?_⟩
                        · simp [elaborateExpr, newType, newLeftFound,
                            newRightFound, newDeclaredFound, newSortFound]
                        · rw [oldValueEq]
                          exact .term oldAdvertised newAdvertised _ conversion

/-- Elaboration congruence requiring simulations only for actual children. -/
theorem elaborateExpr_samePayload_on
    (lookups : LookupSameOn expression.children oldLocal newLocal)
    (foreign : oldForeign = newForeign)
    (declared : DeclaredSame oldLocal newLocal oldDeclared newDeclared)
    (found : elaborateExpr oldLocal oldForeign oldDeclared expression =
      some oldValue) (oldWellFormed : oldValue.WellFormed) :
    ∃ newValue,
      elaborateExpr newLocal newForeign newDeclared expression = some newValue ∧
      SamePayload oldValue newValue := by
  subst newForeign
  cases expression
  case kindStar =>
    refine ⟨.kind .star, rfl, ?_⟩
    have oldValueEq : oldValue = .kind .star := by
      simpa [elaborateExpr] using found.symm
    rw [oldValueEq]
    exact .kind .star
  case boolTy =>
    refine ⟨.family .star .boolTy, rfl, ?_⟩
    have oldValueEq : oldValue = .family .star .boolTy := by
      simpa [elaborateExpr] using found.symm
    rw [oldValueEq]
    exact .family .star .boolTy
  case tmRef => exact ⟨oldValue, found, SamePayload.refl oldWellFormed⟩
  case tyRef => exact ⟨oldValue, found, SamePayload.refl oldWellFormed⟩
  case kindRef => exact ⟨oldValue, found, SamePayload.refl oldWellFormed⟩
  case kindArr domain codomain =>
    simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found ⊢
    rcases found with ⟨domainValue, domainFound, rest⟩
    cases domainValue with
    | kind domainKind =>
      have newDomain := lookups.kind (by simp [detail.Expr.children]) domainFound
      rw [Option.bind_eq_some_iff] at rest
      rcases rest with ⟨codomainValue, codomainFound, output⟩
      cases codomainValue with
      | kind codomainKind =>
        have newCodomain :=
          lookups.kind (by simp [detail.Expr.children]) codomainFound
        have outputEq : oldValue = .kind (.arr domainKind codomainKind) := by
          simpa using output.symm
        refine ⟨.kind (.arr domainKind codomainKind), ?_, ?_⟩
        · simp [newDomain, newCodomain]
        · rw [outputEq]
          exact .kind _
      | family kind expression => simp at output
      | term type expression => simp at output
    | family kind expression => simp at rest
    | term type expression => simp at rest
  case tyArr domain codomain =>
    simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found ⊢
    rcases found with ⟨domainValue, domainFound, rest⟩
    cases domainValue with
    | kind domainKind => simp at rest
    | term type expression => simp at rest
    | family domainKind domainExpression =>
      cases domainKind with
      | arr first second => simp at rest
      | star =>
        have newDomain :=
          lookups.family (by simp [detail.Expr.children]) domainFound
        rw [Option.bind_eq_some_iff] at rest
        rcases rest with ⟨codomainValue, codomainFound, output⟩
        cases codomainValue with
        | kind codomainKind => simp at output
        | term type expression => simp at output
        | family codomainKind codomainExpression =>
          cases codomainKind with
          | arr first second => simp at output
          | star =>
            have newCodomain :=
              lookups.family (by simp [detail.Expr.children]) codomainFound
            have outputEq : oldValue = .family .star
                (.arr domainExpression codomainExpression) := by
              simpa using output.symm
            refine ⟨.family .star (.arr domainExpression codomainExpression), ?_, ?_⟩
            · simp [newDomain, newCodomain]
            · rw [outputEq]
              exact .family _ _
  case tyFv name kindRef =>
    cases kindFound : oldLocal kindRef with
    | none => simp [elaborateExpr, kindFound] at found
    | some kindValue =>
      cases kindValue with
      | family kind expression => simp [elaborateExpr, kindFound] at found
      | term type expression => simp [elaborateExpr, kindFound] at found
      | kind kind =>
        have newKind := lookups.kind (by simp [detail.Expr.children]) kindFound
        have oldValueEq : oldValue = .family kind (.tyFv name.toNat kind) := by
          simpa [elaborateExpr, kindFound] using found.symm
        refine ⟨.family kind (.tyFv name.toNat kind), ?_, ?_⟩
        · simp [elaborateExpr, newKind]
        · rw [oldValueEq]
          exact .family _ _
  case model name predicate =>
    cases predicateFound : oldLocal predicate with
    | none => simp [elaborateExpr, predicateFound] at found
    | some predicateValue =>
      cases predicateValue with
      | kind kind => simp [elaborateExpr, predicateFound] at found
      | family kind expression => simp [elaborateExpr, predicateFound] at found
      | term predicateType predicateExpression =>
        obtain ⟨newPredicateType, newPredicateFound, _⟩ :=
          lookups.term (by simp [detail.Expr.children]) predicateFound
        have oldValueEq : oldValue =
            .family .star (.model name.toNat predicateExpression) := by
          simpa [elaborateExpr, predicateFound] using found.symm
        refine ⟨.family .star (.model name.toNat predicateExpression), ?_, ?_⟩
        · simp [elaborateExpr, newPredicateFound]
        · rw [oldValueEq]
          exact .family _ _
  case bool value =>
    cases declaredFound : oldDeclared with
    | none => simp [elaborateExpr, declaredFound] at found
    | some oldSort =>
      cases sortFound : oldLocal oldSort with
      | none => simp [elaborateExpr, declaredFound, sortFound] at found
      | some sortValue =>
        cases sortValue with
        | kind kind => simp [elaborateExpr, declaredFound, sortFound] at found
        | term type expression =>
            simp [elaborateExpr, declaredFound, sortFound] at found
        | family kind oldAdvertised =>
          cases kind with
          | arr domain codomain =>
              simp [elaborateExpr, declaredFound, sortFound] at found
          | star =>
            obtain ⟨newSort, newAdvertised, newDeclaredFound, newSortFound,
              conversion⟩ := declared.family declaredFound sortFound
            have oldValueEq : oldValue = .term oldAdvertised (.bool value) := by
              simpa [elaborateExpr, declaredFound, sortFound] using found.symm
            refine ⟨.term newAdvertised (.bool value), ?_, ?_⟩
            · simp [elaborateExpr, newDeclaredFound, newSortFound]
            · rw [oldValueEq]
              exact .term oldAdvertised newAdvertised _ conversion
  case op1 op operand =>
    cases operandFound : oldLocal operand with
    | none => simp [elaborateExpr, operandFound] at found
    | some operandValue =>
      cases operandValue with
      | kind kind => simp [elaborateExpr, operandFound] at found
      | family kind expression => simp [elaborateExpr, operandFound] at found
      | term operandType operandExpression =>
        cases declaredFound : oldDeclared with
        | none => simp [elaborateExpr, operandFound, declaredFound] at found
        | some oldSort =>
          cases sortFound : oldLocal oldSort with
          | none =>
              simp [elaborateExpr, operandFound, declaredFound, sortFound] at found
          | some sortValue =>
            cases sortValue with
            | kind kind =>
                simp [elaborateExpr, operandFound, declaredFound, sortFound] at found
            | term type expression =>
                simp [elaborateExpr, operandFound, declaredFound, sortFound] at found
            | family kind oldAdvertised =>
              cases kind with
              | arr domain codomain =>
                  simp [elaborateExpr, operandFound, declaredFound,
                    sortFound] at found
              | star =>
                obtain ⟨newOperandType, newOperandFound, _⟩ :=
                  lookups.term (by simp [detail.Expr.children]) operandFound
                obtain ⟨newSort, newAdvertised, newDeclaredFound, newSortFound,
                  conversion⟩ := declared.family declaredFound sortFound
                have oldValueEq : oldValue =
                    .term oldAdvertised (op.lower operandExpression) := by
                  simpa [elaborateExpr, operandFound, declaredFound, sortFound]
                    using found.symm
                refine ⟨.term newAdvertised (op.lower operandExpression), ?_, ?_⟩
                · simp [elaborateExpr, newOperandFound, newDeclaredFound,
                    newSortFound]
                · rw [oldValueEq]
                  exact .term oldAdvertised newAdvertised _ conversion
  case app function argument =>
    exact elaborateExpr_samePayload_app lookups declared found
  case tmFv name syntacticTypeRef =>
    cases typeFound : oldLocal syntacticTypeRef with
    | none => simp [elaborateExpr, typeFound] at found
    | some typeValue =>
      cases typeValue with
      | kind kind => simp [elaborateExpr, typeFound] at found
      | term type expression => simp [elaborateExpr, typeFound] at found
      | family kind syntacticType =>
        cases kind with
        | arr domain codomain => simp [elaborateExpr, typeFound] at found
        | star =>
          cases declaredFound : oldDeclared with
          | none => simp [elaborateExpr, typeFound, declaredFound] at found
          | some oldSort =>
            cases sortFound : oldLocal oldSort with
            | none =>
                simp [elaborateExpr, typeFound, declaredFound, sortFound] at found
            | some sortValue =>
              cases sortValue with
              | kind kind =>
                  simp [elaborateExpr, typeFound, declaredFound, sortFound] at found
              | term type expression =>
                  simp [elaborateExpr, typeFound, declaredFound, sortFound] at found
              | family kind oldAdvertised =>
                cases kind with
                | arr domain codomain =>
                    simp [elaborateExpr, typeFound, declaredFound, sortFound] at found
                | star =>
                  have newType :=
                    lookups.family (by simp [detail.Expr.children]) typeFound
                  obtain ⟨newSort, newAdvertised, newDeclaredFound,
                    newSortFound, conversion⟩ :=
                      declared.family declaredFound sortFound
                  have oldValueEq : oldValue = .term oldAdvertised
                      (.tmFv name.toNat syntacticType) := by
                    simpa [elaborateExpr, typeFound, declaredFound, sortFound]
                      using found.symm
                  refine ⟨.term newAdvertised
                    (.tmFv name.toNat syntacticType), ?_, ?_⟩
                  · simp [elaborateExpr, newType, newDeclaredFound,
                      newSortFound]
                  · rw [oldValueEq]
                    exact .term oldAdvertised newAdvertised _ conversion
  case tyExists name predicate =>
    cases predicateFound : oldLocal predicate with
    | none => simp [elaborateExpr, predicateFound] at found
    | some predicateValue =>
      cases predicateValue with
      | kind kind => simp [elaborateExpr, predicateFound] at found
      | family kind expression => simp [elaborateExpr, predicateFound] at found
      | term predicateType predicateExpression =>
        cases declaredFound : oldDeclared with
        | none => simp [elaborateExpr, predicateFound, declaredFound] at found
        | some oldSort =>
          cases sortFound : oldLocal oldSort with
          | none =>
              simp [elaborateExpr, predicateFound, declaredFound, sortFound] at found
          | some sortValue =>
            cases sortValue with
            | kind kind =>
                simp [elaborateExpr, predicateFound, declaredFound, sortFound] at found
            | term type expression =>
                simp [elaborateExpr, predicateFound, declaredFound, sortFound] at found
            | family kind oldAdvertised =>
              cases kind with
              | arr domain codomain =>
                  simp [elaborateExpr, predicateFound, declaredFound,
                    sortFound] at found
              | star =>
                obtain ⟨newPredicateType, newPredicateFound, _⟩ :=
                  lookups.term (by simp [detail.Expr.children]) predicateFound
                obtain ⟨newSort, newAdvertised, newDeclaredFound, newSortFound,
                  conversion⟩ := declared.family declaredFound sortFound
                have oldValueEq : oldValue = .term oldAdvertised
                    (.tyExists name.toNat predicateExpression) := by
                  simpa [elaborateExpr, predicateFound, declaredFound, sortFound]
                    using found.symm
                refine ⟨.term newAdvertised
                  (.tyExists name.toNat predicateExpression), ?_, ?_⟩
                · simp [elaborateExpr, newPredicateFound, newDeclaredFound,
                    newSortFound]
                · rw [oldValueEq]
                  exact .term oldAdvertised newAdvertised _ conversion
  case tyApp function argument =>
    exact elaborateExpr_samePayload_tyApp lookups found
  case tyLam binder body =>
    exact elaborateExpr_samePayload_tyLam lookups found
  case lam binder body =>
    exact elaborateExpr_samePayload_lam lookups declared found
  case eps typeRef predicate =>
    exact elaborateExpr_samePayload_eps lookups declared found
  case op2 op left right =>
    exact elaborateExpr_samePayload_op2 lookups declared found
  case eq typeRef left right =>
    exact elaborateExpr_samePayload_eq lookups declared found

private theorem elaborateExpr_eq_without_declared_not_term
    (found : elaborateExpr localLookup foreignLookup none (.eq type left right) =
      some (.term advertised expression)) : False := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
  obtain ⟨typeValue, _, rest⟩ := found
  cases typeValue with
  | kind kind => simp at rest
  | term type expression => simp at rest
  | family kind syntacticType =>
      cases kind with
      | arr domain codomain => simp at rest
      | star =>
          rw [Option.bind_eq_some_iff] at rest
          obtain ⟨leftValue, _, rest⟩ := rest
          cases leftValue with
          | kind kind => simp at rest
          | family kind expression => simp at rest
          | term type left =>
              rw [Option.bind_eq_some_iff] at rest
              obtain ⟨rightValue, _, rest⟩ := rest
              cases rightValue with
              | kind kind => simp at rest
              | family kind expression => simp at rest
              | term type right => simp [elaborateTerm] at rest

private def IsForeignRef : detail.Expr → Prop
  | .tmRef _ _ | .tyRef _ _ | .kindRef _ _ => True
  | _ => False

private theorem finalTermClassifier
    {localLookup : Ref → Option Value} {sort : Ref}
    {makeTerm : EmptyTm} {advertised : EmptyTy}
    {termExpression : EmptyTm}
    (found : elaborateTerm localLookup (some sort) makeTerm =
      some (.term advertised termExpression)) :
    localLookup sort = some (Value.family .star advertised) := by
  unfold elaborateTerm at found
  cases lookup : localLookup sort with
  | none => simp [lookup] at found
  | some value =>
      cases value with
      | kind kind => simp [lookup] at found
      | term type expression => simp [lookup] at found
      | family kind expression =>
          cases kind with
          | arr domain codomain => simp [lookup] at found
          | star =>
              simp only [lookup, Option.bind_some, Option.some.injEq] at found
              cases found
              rfl

private theorem elaborateExpr_tyExists_classifier
    (found : elaborateExpr localLookup foreignLookup (some sort)
      (.tyExists name predicate) = some (.term advertised termExpression)) :
    localLookup sort = some (.family .star advertised) := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
  obtain ⟨predicateValue, _, rest⟩ := found
  cases predicateValue with
  | kind kind => simp at rest
  | family kind expression => simp at rest
  | term type expression => exact finalTermClassifier rest

private theorem elaborateExpr_tmFv_classifier
    (found : elaborateExpr localLookup foreignLookup (some sort)
      (.tmFv name type) = some (.term advertised termExpression)) :
    localLookup sort = some (.family .star advertised) := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
  obtain ⟨typeValue, _, rest⟩ := found
  cases typeValue with
  | kind kind => simp at rest
  | term type expression => simp at rest
  | family kind expression =>
      cases kind with
      | arr domain codomain => simp at rest
      | star => exact finalTermClassifier rest

private theorem elaborateExpr_app_classifier
    (found : elaborateExpr localLookup foreignLookup (some sort)
      (.app function argument) = some (.term advertised termExpression)) :
    localLookup sort = some (.family .star advertised) := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
  obtain ⟨functionValue, _, rest⟩ := found
  cases functionValue with
  | kind kind => simp at rest
  | family kind expression => simp at rest
  | term type function =>
      rw [Option.bind_eq_some_iff] at rest
      obtain ⟨argumentValue, _, rest⟩ := rest
      cases argumentValue with
      | kind kind => simp at rest
      | family kind expression => simp at rest
      | term type argument => exact finalTermClassifier rest

private theorem elaborateExpr_lam_classifier
    (found : elaborateExpr localLookup foreignLookup (some sort)
      (.lam binder body) = some (.term advertised termExpression)) :
    localLookup sort = some (.family .star advertised) := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
  obtain ⟨binderValue, _, rest⟩ := found
  cases binderValue with
  | kind kind => simp at rest
  | family kind expression => simp at rest
  | term type binder =>
      cases binderData : tmFvData? binder with
      | none => simp [binderData] at rest
      | some data =>
          obtain ⟨name, syntacticDomain⟩ := data
          simp only [binderData] at rest
          rw [Option.bind_eq_some_iff] at rest
          obtain ⟨bodyValue, _, rest⟩ := rest
          cases bodyValue with
          | kind kind => simp at rest
          | family kind expression => simp at rest
          | term type body => exact finalTermClassifier rest

private theorem elaborateExpr_bool_classifier
    (found : elaborateExpr localLookup foreignLookup (some sort)
      (.bool value) = some (.term advertised termExpression)) :
    localLookup sort = some (.family .star advertised) := by
  exact finalTermClassifier (by simpa only [elaborateExpr] using found)

private theorem elaborateExpr_op1_classifier
    (found : elaborateExpr localLookup foreignLookup (some sort)
      (.op1 op operand) = some (.term advertised termExpression)) :
    localLookup sort = some (.family .star advertised) := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
  obtain ⟨operandValue, _, rest⟩ := found
  cases operandValue with
  | kind kind => simp at rest
  | family kind expression => simp at rest
  | term type operand => exact finalTermClassifier rest

private theorem elaborateExpr_op2_classifier
    (found : elaborateExpr localLookup foreignLookup (some sort)
      (.op2 op left right) = some (.term advertised termExpression)) :
    localLookup sort = some (.family .star advertised) := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
  obtain ⟨leftValue, _, rest⟩ := found
  cases leftValue with
  | kind kind => simp at rest
  | family kind expression => simp at rest
  | term type left =>
      rw [Option.bind_eq_some_iff] at rest
      obtain ⟨rightValue, _, rest⟩ := rest
      cases rightValue with
      | kind kind => simp at rest
      | family kind expression => simp at rest
      | term type right => exact finalTermClassifier rest

private theorem elaborateExpr_eq_classifier
    (found : elaborateExpr localLookup foreignLookup (some sort)
      (.eq type left right) = some (.term advertised termExpression)) :
    localLookup sort = some (.family .star advertised) := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
  obtain ⟨typeValue, _, rest⟩ := found
  cases typeValue with
  | kind kind => simp at rest
  | term type expression => simp at rest
  | family kind syntacticType =>
      cases kind with
      | arr domain codomain => simp at rest
      | star =>
          rw [Option.bind_eq_some_iff] at rest
          obtain ⟨leftValue, _, rest⟩ := rest
          cases leftValue with
          | kind kind => simp at rest
          | family kind expression => simp at rest
          | term type left =>
              rw [Option.bind_eq_some_iff] at rest
              obtain ⟨rightValue, _, rest⟩ := rest
              cases rightValue with
              | kind kind => simp at rest
              | family kind expression => simp at rest
              | term type right => exact finalTermClassifier rest

private theorem elaborateExpr_eps_classifier
    (found : elaborateExpr localLookup foreignLookup (some sort)
      (.eps type predicate) = some (.term advertised termExpression)) :
    localLookup sort = some (.family .star advertised) := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
  obtain ⟨typeValue, _, rest⟩ := found
  cases typeValue with
  | kind kind => simp at rest
  | term type expression => simp at rest
  | family kind syntacticType =>
      cases kind with
      | arr domain codomain => simp at rest
      | star =>
          rw [Option.bind_eq_some_iff] at rest
          obtain ⟨predicateValue, _, rest⟩ := rest
          cases predicateValue with
          | kind kind => simp at rest
          | family kind expression => simp at rest
          | term type predicate => exact finalTermClassifier rest

private theorem elaborateExpr_term_classifier_of_not_ref
    (notRef : ¬ IsForeignRef expression)
  (found : elaborateExpr localLookup foreignLookup (some sort) expression =
      some (.term advertised termExpression)) :
    localLookup sort = some (.family .star advertised) := by
  cases expression with
  | tyExists => exact elaborateExpr_tyExists_classifier found
  | tmFv => exact elaborateExpr_tmFv_classifier found
  | app => exact elaborateExpr_app_classifier found
  | lam => exact elaborateExpr_lam_classifier found
  | bool => exact elaborateExpr_bool_classifier found
  | op1 => exact elaborateExpr_op1_classifier found
  | op2 => exact elaborateExpr_op2_classifier found
  | eq => exact elaborateExpr_eq_classifier found
  | eps => exact elaborateExpr_eps_classifier found
  | tmRef => simp [IsForeignRef] at notRef
  | tyRef => simp [IsForeignRef] at notRef
  | kindRef => simp [IsForeignRef] at notRef
  | kindStar => simp [elaborateExpr] at found
  | boolTy => simp [elaborateExpr] at found
  | kindArr =>
      simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
      obtain ⟨domainValue, _, rest⟩ := found
      cases domainValue with
      | family kind expression => simp at rest
      | term type expression => simp at rest
      | kind domain =>
          rw [Option.bind_eq_some_iff] at rest
          obtain ⟨codomainValue, _, rest⟩ := rest
          cases codomainValue <;> simp at rest
  | tyArr =>
      simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
      obtain ⟨domainValue, _, rest⟩ := found
      cases domainValue with
      | kind kind => simp at rest
      | term type expression => simp at rest
      | family kind domain =>
          cases kind with
          | arr left right => simp at rest
          | star =>
              rw [Option.bind_eq_some_iff] at rest
              obtain ⟨codomainValue, _, rest⟩ := rest
              cases codomainValue with
              | kind kind => simp at rest
              | term type expression => simp at rest
              | family kind expression => cases kind <;> simp at rest
  | tyApp =>
      simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
      obtain ⟨functionValue, _, rest⟩ := found
      cases functionValue with
      | kind kind => simp at rest
      | term type expression => simp at rest
      | family kind function =>
          cases kind with
          | star => simp at rest
          | arr domain codomain =>
              rw [Option.bind_eq_some_iff] at rest
              obtain ⟨argumentValue, _, rest⟩ := rest
              cases argumentValue with
              | kind kind => simp at rest
              | term type expression => simp at rest
              | family actual argument =>
                  split at rest <;> simp_all
  | tyLam =>
      simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found
      obtain ⟨binderValue, _, rest⟩ := found
      cases binderValue with
      | kind kind => simp at rest
      | term type expression => simp at rest
      | family domain binder =>
          cases binderName : tyFvName? binder with
          | none => simp [binderName] at rest
          | some name =>
              simp only [binderName] at rest
              rw [Option.bind_eq_some_iff] at rest
              obtain ⟨bodyValue, _, rest⟩ := rest
              cases bodyValue <;> simp at rest
  | tyFv => simp [elaborateExpr, Option.bind_eq_some_iff] at found; aesop
  | model => simp [elaborateExpr, Option.bind_eq_some_iff] at found; aesop

set_option linter.flexible false in
/-- With no declared classifier, successful elaboration can only construct a
kind/family payload or return an imported value verbatim.  Child
reclassification therefore cannot invalidate an already well-formed result. -/
theorem elaborateExpr_wellFormed_without_declared
    (lookups : LookupSameOn expression.children oldLocal newLocal)
    (foreign : oldForeign = newForeign)
    (oldFound : elaborateExpr oldLocal oldForeign none expression =
      some oldValue)
    (newFound : elaborateExpr newLocal newForeign none expression =
      some newValue) (wellFormed : oldValue.WellFormed) :
    newValue.WellFormed := by
  subst newForeign
  cases expression
  case tmRef =>
    have equal := Option.some.inj (oldFound.symm.trans newFound)
    rwa [← equal]
  case tyRef =>
    have equal := Option.some.inj (oldFound.symm.trans newFound)
    rwa [← equal]
  case kindRef =>
    have equal := Option.some.inj (oldFound.symm.trans newFound)
    rwa [← equal]
  case eq type left right =>
    obtain ⟨transported, transportedFound, same⟩ :=
      elaborateExpr_samePayload_on lookups rfl
        (by simp [DeclaredSame]) oldFound wellFormed
    have transportedEq := Option.some.inj (transportedFound.symm.trans newFound)
    subst transported
    cases same with
    | kind kind => trivial
    | family kind expression => exact wellFormed
    | term oldType newType expression conversion =>
        exact False.elim (elaborateExpr_eq_without_declared_not_term oldFound)
  all_goals
    obtain ⟨transported, transportedFound, same⟩ :=
      elaborateExpr_samePayload_on lookups rfl
        (by simp [DeclaredSame]) oldFound wellFormed
    have transportedEq := Option.some.inj (transportedFound.symm.trans newFound)
    subst transported
    cases same with
    | kind kind => trivial
    | family kind expression => exact wellFormed
    | term oldType newType expression conversion =>
        exfalso
        simp only [elaborateExpr] at oldFound
        simp [Option.bind_eq_some_iff, elaborateTerm] at oldFound
        all_goals
          obtain ⟨value, _valueFound, oldFound⟩ := oldFound
          cases value <;> try simp_all [Option.bind_eq_some_iff, elaborateTerm]
        all_goals try cases_type Kind <;>
          simp_all [Option.bind_eq_some_iff, elaborateTerm]
        all_goals repeat' split at oldFound <;>
          simp_all [Option.bind_eq_some_iff, elaborateTerm]
        all_goals
          obtain ⟨value, _valueFound, oldFound⟩ := oldFound
          cases value <;> try simp_all [Option.bind_eq_some_iff, elaborateTerm]
        all_goals
          cases_type Kind <;>
            simp_all [Option.bind_eq_some_iff, elaborateTerm]

private theorem option_bind_of_extension
    (optionExt : ∀ element, oldOption = some element →
      newOption = some element)
    (functionExt : ∀ element result, oldFunction element = some result →
      newFunction element = some result)
    (found : oldOption.bind oldFunction = some result) :
    newOption.bind newFunction = some result := by
  rw [Option.bind_eq_some_iff] at found ⊢
  obtain ⟨element, optionFound, functionFound⟩ := found
  exact ⟨element, optionExt element optionFound,
    functionExt element result functionFound⟩

private theorem option_bind_same_of_extension
    (optionExt : ∀ element, oldOption = some element →
      newOption = some element)
    (found : oldOption.bind function = some result) :
    newOption.bind function = some result :=
  option_bind_of_extension optionExt (fun _ _ found => found) found

private theorem elaborateExpr_of_lookup_extension_kindArr
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.kindArr domain codomain) =
      some value) :
    elaborateExpr newLocal newForeign declared (.kindArr domain codomain) =
      some value := by
  simp [elaborateExpr, Option.bind_eq_some_iff] at found ⊢
  aesop (add safe forward [localExt]) (add unsafe apply [option_bind_same_of_extension])

private theorem elaborateExpr_of_lookup_extension_tyArr
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.tyArr domain codomain) =
      some value) :
    elaborateExpr newLocal newForeign declared (.tyArr domain codomain) =
      some value := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found ⊢
  aesop (add safe forward [localExt]) (add unsafe apply [option_bind_same_of_extension])

private theorem elaborateExpr_of_lookup_extension_tyApp
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.tyApp function argument) =
      some value) :
    elaborateExpr newLocal newForeign declared (.tyApp function argument) =
      some value := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found ⊢
  aesop (add safe forward [localExt]) (add unsafe apply [option_bind_same_of_extension])

private theorem elaborateExpr_of_lookup_extension_tyLam
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.tyLam binder body) =
      some value) :
    elaborateExpr newLocal newForeign declared (.tyLam binder body) =
      some value := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found ⊢
  aesop (add safe forward [localExt]) (add unsafe apply [option_bind_same_of_extension])

private theorem elaborateExpr_of_lookup_extension_tyFv
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.tyFv name kindRef) = some value) :
    elaborateExpr newLocal newForeign declared (.tyFv name kindRef) = some value := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found ⊢
  aesop (add safe forward [localExt]) (add unsafe apply [option_bind_same_of_extension])

private theorem elaborateExpr_of_lookup_extension_tyExists
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.tyExists name predicate) =
      some value) :
    elaborateExpr newLocal newForeign declared (.tyExists name predicate) =
      some value := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found ⊢
  aesop (add safe forward [localExt]) (add unsafe apply [option_bind_same_of_extension])

private theorem elaborateExpr_of_lookup_extension_model
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.model name predicate) =
      some value) :
    elaborateExpr newLocal newForeign declared (.model name predicate) = some value := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found ⊢
  aesop (add safe forward [localExt]) (add unsafe apply [option_bind_same_of_extension])

private theorem elaborateExpr_of_lookup_extension_tmFv
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.tmFv name type) = some value) :
    elaborateExpr newLocal newForeign declared (.tmFv name type) = some value := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found ⊢
  aesop (add safe forward [localExt]) (add unsafe apply [option_bind_same_of_extension])

private theorem elaborateExpr_of_lookup_extension_app
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.app function argument) =
      some value) :
    elaborateExpr newLocal newForeign declared (.app function argument) = some value := by
  cases functionFound : oldLocal function with
  | none => simp [elaborateExpr, functionFound] at found
  | some functionValue =>
    have newFunctionFound := localExt function functionValue functionFound
    cases functionValue with
    | kind kind => simp [elaborateExpr, functionFound] at found
    | family kind expression => simp [elaborateExpr, functionFound] at found
    | term functionType functionExpression =>
      cases argumentFound : oldLocal argument with
      | none => simp [elaborateExpr, functionFound, argumentFound] at found
      | some argumentValue =>
        have newArgumentFound := localExt argument argumentValue argumentFound
        cases argumentValue with
        | kind kind => simp [elaborateExpr, functionFound, argumentFound] at found
        | family kind expression =>
            simp [elaborateExpr, functionFound, argumentFound] at found
        | term argumentType argumentExpression =>
          cases declaredFound : declared with
          | none => simp [elaborateExpr, functionFound, argumentFound,
              declaredFound] at found
          | some sort =>
            cases sortFound : oldLocal sort with
            | none => simp [elaborateExpr, functionFound, argumentFound,
                declaredFound, sortFound] at found
            | some sortValue =>
              have newSortFound := localExt sort sortValue sortFound
              cases sortValue <;>
                simp_all [elaborateExpr, functionFound, newFunctionFound,
                  argumentFound, newArgumentFound, declaredFound, sortFound,
                  newSortFound]

private theorem elaborateExpr_of_lookup_extension_lam
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.lam binder body) = some value) :
    elaborateExpr newLocal newForeign declared (.lam binder body) = some value := by
  cases binderFound : oldLocal binder with
  | none => simp [elaborateExpr, binderFound] at found
  | some binderValue =>
    have newBinderFound := localExt binder binderValue binderFound
    cases binderValue with
    | kind kind => simp [elaborateExpr, binderFound] at found
    | family kind expression => simp [elaborateExpr, binderFound] at found
    | term binderType binderExpression =>
      cases binderData : tmFvData? binderExpression with
      | none => simp [elaborateExpr, binderFound, binderData] at found
      | some data =>
        rcases data with ⟨name, syntacticDomain⟩
        cases bodyFound : oldLocal body with
        | none => simp [elaborateExpr, binderFound, binderData, bodyFound] at found
        | some bodyValue =>
          have newBodyFound := localExt body bodyValue bodyFound
          cases bodyValue with
          | kind kind => simp [elaborateExpr, binderFound, binderData,
              bodyFound] at found
          | family kind expression => simp [elaborateExpr, binderFound,
              binderData, bodyFound] at found
          | term bodyType bodyExpression =>
            cases declaredFound : declared with
            | none => simp [elaborateExpr, binderFound, binderData, bodyFound,
                declaredFound] at found
            | some sort =>
              cases sortFound : oldLocal sort with
              | none => simp [elaborateExpr, binderFound, binderData, bodyFound,
                  declaredFound, sortFound] at found
              | some sortValue =>
                have newSortFound := localExt sort sortValue sortFound
                cases sortValue <;>
                  simp_all [elaborateExpr, binderFound, newBinderFound,
                    binderData, bodyFound, newBodyFound, declaredFound,
                    sortFound, newSortFound]

private theorem elaborateExpr_of_lookup_extension_op1
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.op1 op operand) = some value) :
    elaborateExpr newLocal newForeign declared (.op1 op operand) = some value := by
  simp only [elaborateExpr, Bind.bind, Option.bind_eq_some_iff] at found ⊢
  aesop (add safe forward [localExt]) (add unsafe apply [option_bind_same_of_extension])

private theorem elaborateExpr_of_lookup_extension_bool
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.bool boolean) = some value) :
    elaborateExpr newLocal newForeign declared (.bool boolean) = some value := by
  cases declaredFound : declared with
  | none => simp [elaborateExpr, declaredFound] at found
  | some sort =>
    simp only [elaborateExpr, declaredFound] at found ⊢
    exact option_bind_same_of_extension
      (fun element elementFound => localExt sort element elementFound) found

private theorem elaborateExpr_of_lookup_extension_op2
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.op2 op left right) = some value) :
    elaborateExpr newLocal newForeign declared (.op2 op left right) = some value := by
  cases leftFound : oldLocal left with
  | none => simp [elaborateExpr, leftFound] at found
  | some leftValue =>
    have newLeftFound := localExt left leftValue leftFound
    cases leftValue with
    | kind kind => simp [elaborateExpr, leftFound] at found
    | family kind expression => simp [elaborateExpr, leftFound] at found
    | term leftType leftExpression =>
      cases rightFound : oldLocal right with
      | none => simp [elaborateExpr, leftFound, rightFound] at found
      | some rightValue =>
        have newRightFound := localExt right rightValue rightFound
        cases rightValue with
        | kind kind => simp [elaborateExpr, leftFound, rightFound] at found
        | family kind expression => simp [elaborateExpr, leftFound,
            rightFound] at found
        | term rightType rightExpression =>
          cases declaredFound : declared with
          | none => simp [elaborateExpr, leftFound, rightFound,
              declaredFound] at found
          | some sort =>
            cases sortFound : oldLocal sort with
            | none => simp [elaborateExpr, leftFound, rightFound,
                declaredFound, sortFound] at found
            | some sortValue =>
              have newSortFound := localExt sort sortValue sortFound
              cases sortValue <;>
                simp_all [elaborateExpr, leftFound, newLeftFound, rightFound,
                  newRightFound, declaredFound, sortFound, newSortFound]

private theorem elaborateExpr_of_lookup_extension_eq
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.eq type left right) = some value) :
    elaborateExpr newLocal newForeign declared (.eq type left right) = some value := by
  cases typeFound : oldLocal type with
  | none => simp [elaborateExpr, typeFound] at found
  | some typeValue =>
    have newTypeFound := localExt type typeValue typeFound
    cases typeValue with
    | kind kind => simp [elaborateExpr, typeFound] at found
    | term type expression => simp [elaborateExpr, typeFound] at found
    | family kind syntacticType =>
      cases kind with
      | arr domain codomain => simp [elaborateExpr, typeFound] at found
      | star =>
        cases leftFound : oldLocal left with
        | none => simp [elaborateExpr, typeFound, leftFound] at found
        | some leftValue =>
          have newLeftFound := localExt left leftValue leftFound
          cases leftValue with
          | kind kind => simp [elaborateExpr, typeFound, leftFound] at found
          | family kind expression => simp [elaborateExpr, typeFound,
              leftFound] at found
          | term leftType leftExpression =>
            cases rightFound : oldLocal right with
            | none => simp [elaborateExpr, typeFound, leftFound,
                rightFound] at found
            | some rightValue =>
              have newRightFound := localExt right rightValue rightFound
              cases rightValue with
              | kind kind => simp [elaborateExpr, typeFound, leftFound,
                  rightFound] at found
              | family kind expression => simp [elaborateExpr, typeFound,
                  leftFound, rightFound] at found
              | term rightType rightExpression =>
                cases declaredFound : declared with
                | none => simp [elaborateExpr, typeFound, leftFound, rightFound,
                    declaredFound] at found
                | some sort =>
                  cases sortFound : oldLocal sort with
                  | none => simp [elaborateExpr, typeFound, leftFound, rightFound,
                      declaredFound, sortFound] at found
                  | some sortValue =>
                    have newSortFound := localExt sort sortValue sortFound
                    cases sortValue <;>
                      simp_all [elaborateExpr, typeFound, newTypeFound,
                        leftFound, newLeftFound, rightFound, newRightFound,
                        declaredFound, sortFound, newSortFound]

private theorem elaborateExpr_of_lookup_extension_eps
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared (.eps type predicate) = some value) :
    elaborateExpr newLocal newForeign declared (.eps type predicate) = some value := by
  cases typeFound : oldLocal type with
  | none => simp [elaborateExpr, typeFound] at found
  | some typeValue =>
    have newTypeFound := localExt type typeValue typeFound
    cases typeValue with
    | kind kind => simp [elaborateExpr, typeFound] at found
    | term type expression => simp [elaborateExpr, typeFound] at found
    | family kind syntacticType =>
      cases kind with
      | arr domain codomain => simp [elaborateExpr, typeFound] at found
      | star =>
        cases predicateFound : oldLocal predicate with
        | none => simp [elaborateExpr, typeFound, predicateFound] at found
        | some predicateValue =>
          have newPredicateFound := localExt predicate predicateValue predicateFound
          cases predicateValue with
          | kind kind => simp [elaborateExpr, typeFound, predicateFound] at found
          | family kind expression => simp [elaborateExpr, typeFound,
              predicateFound] at found
          | term predicateType predicateExpression =>
            cases declaredFound : declared with
            | none => simp [elaborateExpr, typeFound, predicateFound,
                declaredFound] at found
            | some sort =>
              cases sortFound : oldLocal sort with
              | none => simp [elaborateExpr, typeFound, predicateFound,
                  declaredFound, sortFound] at found
              | some sortValue =>
                have newSortFound := localExt sort sortValue sortFound
                cases sortValue <;>
                  simp_all [elaborateExpr, typeFound, newTypeFound,
                    predicateFound, newPredicateFound, declaredFound,
                    sortFound, newSortFound]

/-- Increasing recursive lookup availability cannot change an elaboration
which already succeeded when the row and its declared classifier are fixed. -/
theorem elaborateExpr_of_lookup_extension
    (localExt : ∀ reference value, oldLocal reference = some value →
      newLocal reference = some value)
    (foreign : ∀ source reference value,
      oldForeign source reference = some value →
      newForeign source reference = some value)
    (found : elaborateExpr oldLocal oldForeign declared expression = some value) :
    elaborateExpr newLocal newForeign declared expression = some value := by
  cases expression <;> first
    | exact found
    | exact elaborateExpr_of_lookup_extension_kindArr localExt found
    | exact elaborateExpr_of_lookup_extension_tyArr localExt found
    | exact elaborateExpr_of_lookup_extension_tyApp localExt found
    | exact elaborateExpr_of_lookup_extension_tyLam localExt found
    | exact elaborateExpr_of_lookup_extension_tyFv localExt found
    | exact elaborateExpr_of_lookup_extension_tyExists localExt found
    | exact elaborateExpr_of_lookup_extension_model localExt found
    | exact elaborateExpr_of_lookup_extension_tmFv localExt found
    | exact elaborateExpr_of_lookup_extension_app localExt found
    | exact elaborateExpr_of_lookup_extension_lam localExt found
    | exact elaborateExpr_of_lookup_extension_op1 localExt found
    | exact elaborateExpr_of_lookup_extension_bool localExt found
    | exact elaborateExpr_of_lookup_extension_op2 localExt found
    | exact elaborateExpr_of_lookup_extension_eq localExt found
    | exact elaborateExpr_of_lookup_extension_eps localExt found
    | (simp only [elaborateExpr] at found ⊢
       first
       | exact option_bind_same_of_extension localExt found
       | exact option_bind_same_of_extension
           (fun element elementFound => foreign _ _ element elementFound) found)

/-- Once fuel-bounded resolution succeeds, one additional unit of fuel
preserves the exact reconstructed value. -/
theorem resolveAt?_succ_of_some
    (found : resolveAt? fuel resolve arena reference = some value) :
    resolveAt? (fuel + 1) resolve arena reference = some value := by
  induction fuel generalizing arena reference value with
  | zero => simp [resolveAt?] at found
  | succ fuel ih =>
      simp only [resolveAt?] at found
      cases rowFound : arena.row? reference with
      | none => simp [rowFound] at found
      | some row =>
          rw [rowFound] at found
          simp only at found
          change (match arena.row? reference with
            | none => none
            | some row => elaborateExpr
                (resolveAt? (fuel + 1) resolve arena)
                (resolveForeignUsing? (resolveAt? (fuel + 1) resolve)
                  resolve arena) (arena.sort? reference) row) = some value
          rw [rowFound]
          apply elaborateExpr_of_lookup_extension
            (fun child childValue childFound => ih childFound) ?_ found
          intro source foreignReference foreignValue foreignFound
          unfold resolveForeignUsing? at foreignFound ⊢
          cases importFound : arena.import? source with
          | none => simp [importFound] at foreignFound
          | some entry =>
              simp only [importFound] at foreignFound ⊢
              cases resolved : resolveImport? resolve entry with
              | none => simp [resolved] at foreignFound
              | some imported =>
                  simp only [resolved, importFound] at foreignFound ⊢
                  exact ih foreignFound

theorem resolveAt?_of_le (le : firstFuel ≤ secondFuel)
    (found : resolveAt? firstFuel resolve arena reference = some value) :
    resolveAt? secondFuel resolve arena reference = some value := by
  induction secondFuel, le using Nat.le_induction with
  | base => exact found
  | succ secondFuel _ ih =>
      simpa [Nat.add_comm] using resolveAt?_succ_of_some ih

/-- Successful resolution is deterministic even when witnessed at different
fuel bounds. -/
theorem Resolves.value_unique
    (left : Resolves resolve arena reference leftValue)
    (right : Resolves resolve arena reference rightValue) :
    leftValue = rightValue := by
  rcases left with ⟨leftFuel, leftFound⟩
  rcases right with ⟨rightFuel, rightFound⟩
  let common := max leftFuel rightFuel
  have leftAtCommon : resolveAt? common resolve arena reference = some leftValue :=
    resolveAt?_of_le (secondFuel := common) (Nat.le_max_left _ _) leftFound
  have rightAtCommon : resolveAt? common resolve arena reference = some rightValue :=
    resolveAt?_of_le (secondFuel := common) (Nat.le_max_right _ _) rightFound
  exact Option.some.inj (leftAtCommon.symm.trans rightAtCommon)

/-- Pointwise transport of the finitely many children of a row can be
observed through one target lookup function. -/
theorem LookupSameOn.of_resolves
    (transport : ∀ reference, reference ∈ references → ∀ oldValue,
      oldLookup reference = some oldValue →
        ∃ newValue, Resolves resolve arena reference newValue ∧
          SamePayload oldValue newValue) :
    ∃ fuel, LookupSameOn references oldLookup
      (resolveAt? fuel resolve arena) := by
  induction references with
  | nil => exact ⟨0, by simp [LookupSameOn]⟩
  | cons head tail ih =>
      have tailTransport : ∀ reference, reference ∈ tail → ∀ oldValue,
          oldLookup reference = some oldValue →
            ∃ newValue, Resolves resolve arena reference newValue ∧
              SamePayload oldValue newValue := by
        intro reference member
        exact transport reference (by simp [member])
      obtain ⟨tailFuel, tailSame⟩ := ih tailTransport
      cases headFound : oldLookup head with
      | none =>
          exact ⟨tailFuel, by
            intro reference member oldValue found
            rcases List.mem_cons.mp member with rfl | member
            · simp [headFound] at found
            · exact tailSame reference member oldValue found⟩
      | some headValue =>
          obtain ⟨newHead, ⟨headFuel, headAtFuel⟩, headSame⟩ :=
            transport head (by simp) headValue headFound
          let fuel := max headFuel tailFuel
          refine ⟨fuel, ?_⟩
          intro reference member oldValue found
          rcases List.mem_cons.mp member with rfl | member
          · have oldEq : oldValue = headValue :=
              Option.some.inj (found.symm.trans headFound)
            subst oldValue
            exact ⟨newHead,
              resolveAt?_of_le (Nat.le_max_left _ _) headAtFuel, headSame⟩
          · obtain ⟨newValue, newFound, same⟩ :=
              tailSame reference member oldValue found
            exact ⟨newValue,
              resolveAt?_of_le (Nat.le_max_right _ _) newFound, same⟩

/-- Replacing a well-formed value by an equal value preserves its sorting by
the same classifier.  Together with `HasSort.replaceClassifier`, this is the
two-sided reclassification law needed after recursive resolution changes both
a row value and the value of its classifier. -/
theorem HasSort.replaceValue {oldValue newValue classifier : Value}
    (sorted : oldValue.HasSort classifier)
    (oldWellFormed : oldValue.WellFormed)
    (newWellFormed : newValue.WellFormed)
    (equal : Equal oldValue newValue) :
    newValue.HasSort classifier := by
  cases equal with
  | kind kind => exact sorted
  | @family kind left right conversion =>
      cases classifier with
      | kind actual => exact sorted
      | family actual expression => exact False.elim sorted
      | term type expression => exact False.elim sorted
  | @term oldType newType oldTerm newTerm oldTermWellFormed
      newTermWellFormed classifierConversion termConversion =>
      cases classifier with
      | kind kind => simp [HasSort] at sorted
      | family kind expression =>
          cases kind with
          | arr domain codomain => simp [HasSort] at sorted
          | star =>
              rcases sorted with ⟨sorted⟩
              rcases classifierConversion with ⟨classifierConversion⟩
              rcases oldWellFormed with
                ⟨_loweredTerm, loweredType, _termLowering,
                  typeLowering, typing⟩
              have typeLowering' := typeLowering
              change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) oldType.toHolE =
                some loweredType at typeLowering'
              rw [classifierConversion.leftLowering] at typeLowering'
              have same := Option.some.inj typeLowering'
              subst loweredType
              exact ⟨classifierConversion.symm.trans typing.typeKinded sorted⟩
      | term type expression => simp [HasSort] at sorted

end Value

set_option linter.unusedSimpArgs true

namespace ContextClaim

/-- Regression theorem for the fused representation: a proposition remains a
valid context member when the same term syntax is advertised at a distinct
convertible Boolean type. -/
theorem readvertise {resolve : Resolver} {arena : Arena} {reference : Ref}
    {oldType newType : EmptyTy} {expression : EmptyTm}
    (resolved : Resolves resolve arena reference (.term newType expression))
    (oldWellFormed : Value.WellFormed (.term oldType expression))
    (newTypeWellFormed : Value.WellFormed (.family .star newType))
    (conversion : Nucleus.HolE.Named.FamEq
      (.nil : TyScope []) oldType.toHolE newType.toHolE)
    (boolean : Nucleus.HolE.Named.FamEq
      (.nil : TyScope []) oldType.toHolE
        (Nucleus.Hol.Ethane.Expr.boolTy : EmptyTy).toHolE) :
    ContextClaim resolve arena reference := by
  have newWellFormed := oldWellFormed.reclassifyTerm newTypeWellFormed conversion
  rcases oldWellFormed with
    ⟨_loweredTerm, loweredType, _termLowering, typeLowering, typing⟩
  have typeLowering' := typeLowering
  change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) oldType.toHolE =
    some loweredType at typeLowering'
  rw [conversion.leftLowering] at typeLowering'
  have same := Option.some.inj typeLowering'
  subst loweredType
  exact ⟨newType, expression, resolved, newWellFormed,
    ⟨conversion.symm.trans typing.typeKinded boolean⟩⟩

end ContextClaim

/-- Replace only the physical dense definition/column storage of the legacy
HOL proof core.  Imports, theorem caches, context, and capabilities remain
byte-for-byte unchanged. -/
def Arena.withDense (arena : Arena) (dense : Dense) : Arena :=
  match arena with
  | .mk imports axs _ synFacts synFree ctx assume assert =>
      .mk imports axs dense synFacts synFree ctx assume assert

@[simp] theorem Arena.withDense_dense (arena : Arena) (dense : Dense) :
    (arena.withDense dense).dense = dense := by cases arena; rfl

@[simp] theorem Arena.withDense_imports (arena : Arena) (dense : Dense) :
    (arena.withDense dense).imports = arena.imports := by cases arena; rfl

@[simp] theorem Arena.withDense_axs (arena : Arena) (dense : Dense) :
    (arena.withDense dense).axs = arena.axs := by cases arena; rfl

@[simp] theorem Arena.withDense_ctx (arena : Arena) (dense : Dense) :
    (arena.withDense dense).ctx = arena.ctx := by cases arena; rfl

@[simp] theorem Arena.withDense_assume (arena : Arena) (dense : Dense) :
    (arena.withDense dense).assume = arena.assume := by cases arena; rfl

@[simp] theorem Arena.withDense_assert (arena : Arena) (dense : Dense) :
    (arena.withDense dense).assert = arena.assert := by cases arena; rfl

@[simp] theorem Arena.withDense_row? (arena : Arena) (dense : Dense)
    (reference : Ref) :
    (arena.withDense dense).row? reference = dense.row? reference := by
  cases arena
  rfl

@[simp] theorem Arena.withDense_eq? (arena : Arena) (dense : Dense)
    (reference : Ref) :
    (arena.withDense dense).eq? reference = dense.eq.get? reference := by
  cases arena
  rfl

@[simp] theorem Arena.withDense_sort? (arena : Arena) (dense : Dense)
    (reference : Ref) :
    (arena.withDense dense).sort? reference = dense.classifier? reference := by
  cases arena
  rfl

/-- Concrete footprint of a sound dense-column rewrite.

Syntax is unchanged. Classifier and equality observations are stated directly
on their columns; they are never projected through definition rows. -/
structure CoreDenseChange (resolve : Resolver) (before after : Arena) : Prop where
  structural : after.StructurallyValid
  imports : after.imports = before.imports
  defsLength : after.defs.length = before.defs.length
  rows : ∀ reference, after.row? reference = before.row? reference
  classifier : ∀ reference,
    (before.sort? reference = none ∧ after.sort? reference = none) ∨
      ∃ oldSort newSort,
        before.sort? reference = some oldSort ∧
        after.sort? reference = some newSort ∧
        oldSort < reference ∧ newSort < reference ∧
        before.row? oldSort ≠ none ∧ before.row? newSort ≠ none ∧
        ReferenceEqual resolve before oldSort newSort
  eq : ∀ reference right, after.eq? reference = some right →
    ReferenceEqual resolve before reference right
  classes : ∀ left right,
    before.row? left ≠ none → before.row? right ≠ none →
      EqClass after left right → ReferenceEqual resolve before left right
  ctx : after.ctx = before.ctx
  axs : after.axs = before.axs
  conclusions : Conclusions resolve before → Conclusions resolve after

namespace SynFact.Valid

/-- A checked direct cache fact supplies exactly the representation-level
endpoint conditions consumed by `unionSynFactExact`. These conditions follow
from resolution and are not extra trusted inputs to the kernel operation. -/
theorem denseEndpoints
    (valid : SynFact.Valid resolve arena fact) :
    arena.dense.expr? fact.input ≠ none ∧
    arena.dense.expr? fact.output ≠ none ∧
    Columns.SameCategory arena.dense fact.input fact.output := by
  rcases valid with ⟨input, output, inputResolved, outputResolved,
    _inputWellFormed, _outputWellFormed, compatible, _meaning⟩
  have inputFull : Resolves resolve arena fact.input input :=
    (resolves_withoutSyn_iff resolve arena fact.input input).mp inputResolved
  have outputFull : Resolves resolve arena fact.output output :=
    (resolves_withoutSyn_iff resolve arena fact.output output).mp outputResolved
  refine ⟨inputFull.resident, outputFull.resident, ?_⟩
  refine ⟨input.tagSort, inputFull.tagSort?, ?_⟩
  rw [compatible.tagSort_eq]
  exact outputFull.tagSort?

end SynFact.Valid

namespace CoreDenseChange

theorem sourceWellFormed (valid : before.CoreKernelValid resolve)
    (resolved : Resolves resolve before reference value) : value.WellFormed := by
  rcases resolved with ⟨fuel, found⟩
  cases fuel with
  | zero => simp [resolveAt?] at found
  | succ fuel =>
      simp only [resolveAt?] at found
      cases rowFound : before.row? reference with
      | none => simp [rowFound] at found
      | some row =>
          rw [rowFound] at found
          obtain ⟨canonical, canonicalResolved, canonicalWellFormed⟩ :=
            valid.definitions reference row rowFound
          have same : canonical = value :=
            Value.Resolves.value_unique canonicalResolved
              ⟨fuel + 1, by
                simp only [resolveAt?, rowFound]
                exact found⟩
          simpa [same] using canonicalWellFormed

/-- Semantic reference equality is reflexive on every resident definition of
a valid source kernel. -/
theorem referenceEqual_refl (valid : arena.CoreKernelValid resolve)
    (resident : arena.row? reference ≠ none) :
    ReferenceEqual resolve arena reference reference := by
  cases found : arena.row? reference with
  | none => exact (resident found).elim
  | some row =>
      obtain ⟨value, resolved, wellFormed⟩ :=
        valid.definitions reference row found
      exact ⟨value, value, resolved, resolved, wellFormed, wellFormed,
        Value.equal_self wellFormed⟩

/-- Semantic reference equality is symmetric. -/
theorem referenceEqual_symm
    (equal : ReferenceEqual resolve arena left right) :
    ReferenceEqual resolve arena right left := by
  rcases equal with ⟨leftValue, rightValue, leftResolved, rightResolved,
    leftWellFormed, rightWellFormed, valueEqual⟩
  exact ⟨rightValue, leftValue, rightResolved, leftResolved,
    rightWellFormed, leftWellFormed, valueEqual.symm⟩

/-- Semantic reference equality is transitive; deterministic resolution
identifies the two witnesses selected for the middle reference. -/
theorem referenceEqual_trans
    (leftMiddle : ReferenceEqual resolve arena left middle)
    (middleRight : ReferenceEqual resolve arena middle right) :
    ReferenceEqual resolve arena left right := by
  rcases leftMiddle with ⟨leftValue, firstMiddle, leftResolved,
    firstMiddleResolved, leftWellFormed, firstMiddleWellFormed, leftEqual⟩
  rcases middleRight with ⟨secondMiddle, rightValue, secondMiddleResolved,
    rightResolved, secondMiddleWellFormed, rightWellFormed, rightEqual⟩
  have middleEq : firstMiddle = secondMiddle :=
    Value.Resolves.value_unique firstMiddleResolved secondMiddleResolved
  subst secondMiddle
  exact ⟨leftValue, rightValue, leftResolved, rightResolved,
    leftWellFormed, rightWellFormed,
    leftEqual.trans firstMiddleWellFormed rightEqual⟩

/-- A checked semantic equality class preserves row residency in both
directions.  Reflexive classes may name anything; the equivalence formulation
is what makes that case harmless. -/
theorem semanticClass_resident_iff (checked : FusedChecked dense)
    (connected : Class dense .semantic left right) :
    (dense.expr? left ≠ none) ↔ dense.expr? right ≠ none := by
  induction connected with
  | rel left right edge =>
      have targets := checked.eqTargets left right edge
      exact ⟨fun _ => targets.2, fun _ => targets.1⟩
  | refl reference => exact Iff.rfl
  | symm left right _ ih => exact ih.symm
  | trans left middle right _ _ leftMiddle middleRight =>
      exact leftMiddle.trans middleRight

/-- Eliminate a post-union semantic class into HOL equality.  The auxiliary
relation carries residency equivalence so transitivity can recover the middle
row required by `CoreKernelValid.classes`. -/
theorem EqualitySequence.referenceEqual
    (sequence : EqualitySequence equivalent beforeDense left right relation
      afterDense outcome)
    (checked : FusedChecked beforeDense)
    (valid : beforeArena.CoreKernelValid resolve)
    (denseEq : beforeArena.dense = beforeDense)
    (leftResident : beforeDense.expr? left ≠ none)
    (rightResident : beforeDense.expr? right ≠ none)
    (endpoint : ReferenceEqual resolve beforeArena left right)
    (connected : Class afterDense .semantic a b)
    (aResident : beforeDense.expr? a ≠ none) :
    ReferenceEqual resolve beforeArena a b := by
  subst beforeDense
  let R : Ref → Ref → Prop := fun x y =>
    ((beforeArena.dense.expr? x ≠ none) ↔
      (beforeArena.dense.expr? y ≠ none)) ∧
      (beforeArena.dense.expr? x ≠ none → ReferenceEqual resolve beforeArena x y)
  have oldSound : ∀ {x y}, Class beforeArena.dense .semantic x y → R x y := by
    intro x y related
    have residentIff := semanticClass_resident_iff checked related
    refine ⟨residentIff, ?_⟩
    intro xResident
    have yResident := residentIff.mp xResident
    apply valid.classes
    · change beforeArena.dense.expr? x ≠ none
      exact xResident
    · change beforeArena.dense.expr? y ≠ none
      exact yResident
    · change Columns.Class beforeArena.dense .semantic x y
      exact related
  have endpointR : R left right := by
    exact ⟨⟨fun _ => rightResident, fun _ => leftResident⟩,
      fun _ => endpoint⟩
  have symmR : ∀ {x y}, R x y → R y x := by
    intro x y related
    refine ⟨related.1.symm, ?_⟩
    intro yResident
    exact referenceEqual_symm (related.2 (related.1.mpr yResident))
  have transR : ∀ {x y z}, R x y → R y z → R x z := by
    intro x y z leftMiddle middleRight
    refine ⟨leftMiddle.1.trans middleRight.1, ?_⟩
    intro xResident
    have yResident := leftMiddle.1.mp xResident
    exact referenceEqual_trans (leftMiddle.2 xResident)
      (middleRight.2 yResident)
  exact (sequence.semanticSound oldSound endpointR symmR transR connected).2 aResident

/-- The exact Rust equality-cache sequence induces a sound mutation of the
legacy HOL core.  Definition rows remain syntax-only; every changed
classifier or semantic parent is justified directly from the dense columns.

Legacy assertion records can mention locally resolved classifiers, so the
current normalized layout's empty assertion list is an explicit premise. -/
theorem EqualitySequence.coreDenseChange
    (sequence : EqualitySequence equivalent before.dense left right relation
      afterDense outcome)
    (checked : FusedChecked before.dense)
    (valid : before.CoreKernelValid resolve)
    (endpoint : ReferenceEqual resolve before left right)
    (noAssert : before.assert = []) :
    CoreDenseChange resolve before (before.withDense afterDense) := by
  have pre : DirectFactPreconditions before.dense equivalent left right relation := by
    cases sequence <;> assumption
  have afterChecked := sequence.checked checked
  have defs := sequence.defs
  have oldClassEqual : ∀ {a b}, Class before.dense .semantic a b →
      before.dense.expr? a ≠ none → ReferenceEqual resolve before a b := by
    intro a b connected aResident
    have bResident := (semanticClass_resident_iff checked connected).mp aResident
    apply valid.classes
    · change before.dense.expr? a ≠ none
      exact aResident
    · change before.dense.expr? b ≠ none
      exact bResident
    · change Class before.dense .semantic a b
      exact connected
  refine ({
    structural := ?_
    imports := Arena.withDense_imports before afterDense
    defsLength := ?_
    rows := ?_
    classifier := ?_
    eq := ?_
    classes := ?_
    ctx := Arena.withDense_ctx before afterDense
    axs := Arena.withDense_axs before afterDense
    conclusions := ?_
  } : CoreDenseChange resolve before (before.withDense afterDense))
  · have sourceStructural := valid.structural
    unfold Arena.StructurallyValid Arena.syntaxRows at sourceStructural ⊢
    simp only [Arena.withDense_dense]
    rw [defs]
    exact sourceStructural
  · simp only [Arena.defs, Arena.withDense_dense, Dense.rows_length]
    rw [defs]
  · intro reference
    rw [Arena.withDense_row?]
    simp only [Arena.row?, Dense.row?, Dense.expr?]
    rw [defs]
  · intro reference
    rw [Arena.withDense_sort?]
    by_cases resident : before.dense.expr? reference = none
    · left
      have oldNone : before.sort? reference = none := by
        apply Dense.classifierAt?_none_of_tagSort?_none
        simp [Dense.tagSort?, resident]
      refine ⟨oldNone, ?_⟩
      apply Dense.classifierAt?_none_of_tagSort?_none
      have afterMissing : afterDense.expr? reference = none := by
        change afterDense.defs[(reference.value.toNat - 1)]? = none
        change before.dense.defs[(reference.value.toNat - 1)]? = none at resident
        rw [defs]
        exact resident
      simp [Dense.tagSort?, afterMissing]
    · have afterResident : afterDense.expr? reference ≠ none := by
        change afterDense.defs[(reference.value.toNat - 1)]? ≠ none
        change before.dense.defs[(reference.value.toNat - 1)]? ≠ none at resident
        rw [defs]
        exact resident
      cases oldFound : before.sort? reference with
      | none =>
          left
          refine ⟨rfl, ?_⟩
          cases newFound : afterDense.classifier? reference with
          | none => simpa using newFound
          | some newSort =>
              have newClassified :=
                (afterChecked.classifierLookup afterResident).mp newFound
              have oldExists :=
                (sequence.classifierOptionality checked resident).mp
                  ⟨newSort, newClassified⟩
              rcases oldExists with ⟨oldSort, oldClassified⟩
              have contradiction := checked.classifierComplete resident oldClassified
              have contradictionArena : before.sort? reference = some oldSort := by
                simpa [Arena.sort?] using contradiction
              rw [oldFound] at contradictionArena
              contradiction
      | some oldSort =>
          have oldClassified := (checked.classifierLookup resident).mp oldFound
          have newExists :=
            (sequence.classifierOptionality checked resident).mpr
              ⟨oldSort, oldClassified⟩
          rcases newExists with ⟨newSort, newClassified⟩
          have newFound := afterChecked.classifierComplete afterResident newClassified
          have oldTargetResident : before.dense.expr? oldSort ≠ none := by
            rcases oldClassified with ⟨root, _connected, edge⟩
            exact (checked.convTargets root oldSort edge.1).2
          have newTargetAfter : afterDense.expr? newSort ≠ none := by
            rcases newClassified with ⟨root, _connected, edge⟩
            exact (afterChecked.convTargets root newSort edge.1).2
          have newTargetBefore : before.dense.expr? newSort ≠ none := by
            change before.dense.defs[(newSort.value.toNat - 1)]? ≠ none
            change afterDense.defs[(newSort.value.toNat - 1)]? ≠ none at newTargetAfter
            rw [defs] at newTargetAfter
            exact newTargetAfter
          right
          refine ⟨oldSort, newSort, rfl, (by simpa using newFound),
            Columns.Dense.FusedChecked.classifier_lt checked resident oldFound,
            Columns.Dense.FusedChecked.classifier_lt afterChecked afterResident newFound,
            ?_, ?_, ?_⟩
          · simpa [Arena.row?, Dense.row?] using oldTargetResident
          · simpa [Arena.row?, Dense.row?] using newTargetBefore
          · have joined := sequence.classifierCases checked resident oldFound newFound
            rcases joined with old | ⟨oldSide, newSide⟩
            · exact oldClassEqual old oldTargetResident
            · have oldToEndpoint :
                  ReferenceEqual resolve before oldSort left ∨
                    ReferenceEqual resolve before oldSort right := by
                rcases oldSide with toLeft | toRight
                · exact Or.inl (oldClassEqual toLeft oldTargetResident)
                · exact Or.inr (oldClassEqual toRight oldTargetResident)
              have newToEndpoint :
                  ReferenceEqual resolve before newSort left ∨
                    ReferenceEqual resolve before newSort right := by
                rcases newSide with toLeft | toRight
                · exact Or.inl (oldClassEqual toLeft newTargetBefore)
                · exact Or.inr (oldClassEqual toRight newTargetBefore)
              rcases oldToEndpoint with oldLeft | oldRight <;>
                rcases newToEndpoint with newLeft | newRight
              · exact referenceEqual_trans oldLeft (referenceEqual_symm newLeft)
              · exact referenceEqual_trans
                  (referenceEqual_trans oldLeft endpoint)
                  (referenceEqual_symm newRight)
              · exact referenceEqual_trans
                  (referenceEqual_trans oldRight (referenceEqual_symm endpoint))
                  (referenceEqual_symm newLeft)
              · exact referenceEqual_trans oldRight (referenceEqual_symm newRight)
  · intro reference right found
    have targets := afterChecked.eqTargets reference right (by
      simpa [Arena.withDense_eq?] using found)
    have referenceResident : before.dense.expr? reference ≠ none := by
      have targetSourceAfter := targets.1
      change before.dense.defs[(reference.value.toNat - 1)]? ≠ none
      change afterDense.defs[(reference.value.toNat - 1)]? ≠ none at targetSourceAfter
      rw [defs] at targetSourceAfter
      exact targetSourceAfter
    have edge : Edge afterDense .semantic reference right := by
      change afterDense.eq.get? reference = some right
      simpa [Arena.withDense_eq?] using found
    have connected : Class afterDense .semantic reference right :=
      Relation.EqvGen.rel _ _ edge
    exact _root_.Nucleus.Hol.Ethane.OneBased.CoreDenseChange.EqualitySequence.referenceEqual
      sequence checked valid rfl pre.leftResident
      pre.rightResident endpoint connected referenceResident
  · intro a b aResident _bResident connected
    have aDenseResident : before.dense.expr? a ≠ none := by
      simpa [Arena.row?, Dense.row?] using aResident
    have connectedDense : Class afterDense .semantic a b := by
      apply connected.mono
      intro x y edge
      change afterDense.eq.get? x = some y
      simpa [EqEdge, Arena.eq?, Arena.withDense_eq?] using edge
    exact _root_.Nucleus.Hol.Ethane.OneBased.CoreDenseChange.EqualitySequence.referenceEqual
      sequence checked valid rfl pre.leftResident
      pre.rightResident endpoint connectedDense aDenseResident
  · intro _source
    simp [Conclusions, noAssert]

/-- Imported lookup is unaffected because classifier rewrites do not mutate
the import table. -/
theorem foreign_eq (change : CoreDenseChange resolve before after)
    (fuel : Nat) :
    resolveForeignUsing? (resolveAt? fuel resolve) resolve before =
      resolveForeignUsing? (resolveAt? fuel resolve) resolve after := by
  funext source foreignReference
  unfold resolveForeignUsing?
  have importEq : before.import? source = after.import? source := by
    simp only [Arena.import?]
    rw [change.imports]
  rw [importEq]

theorem foreign_of_le (le : firstFuel ≤ secondFuel)
    (found : resolveForeignUsing? (resolveAt? firstFuel resolve) resolve arena
      source reference = some value) :
    resolveForeignUsing? (resolveAt? secondFuel resolve) resolve arena
      source reference = some value := by
  unfold resolveForeignUsing? at found ⊢
  cases importFound : arena.import? source with
  | none => simp [importFound] at found
  | some entry =>
    simp only [importFound] at found ⊢
    cases resolved : resolveImport? resolve entry with
    | none => simp [resolved] at found
    | some imported =>
      simp only [resolved] at found ⊢
      exact Value.resolveAt?_of_le le found

/-- Resolution transport is well-founded on references: both ordinary syntax
children and the old/new advertised classifiers are strictly earlier than the
row being reconstructed. -/
theorem resolves (change : CoreDenseChange resolve before after)
    (valid : before.CoreKernelValid resolve) (reference : Ref)
    (oldValue : Value) (resolved : Resolves resolve before reference oldValue) :
    ∃ newValue, Resolves resolve after reference newValue ∧
      Value.SamePayload oldValue newValue ∧ newValue.WellFormed := by
  induction hn : reference.value.toNat using Nat.strong_induction_on
      generalizing reference oldValue with
  | h number ih =>
      rcases resolved with ⟨oldFuelSucc, oldFound⟩
      cases oldFuelSucc with
      | zero => simp [resolveAt?] at oldFound
      | succ oldFuel =>
          simp only [resolveAt?] at oldFound
          cases oldRowFound : before.row? reference with
          | none => simp [oldRowFound] at oldFound
          | some oldRow =>
              rw [oldRowFound] at oldFound
              simp only at oldFound
              obtain ⟨canonicalValue, canonicalResolved, canonicalWellFormed⟩ :=
                valid.definitions reference oldRow oldRowFound
              have canonicalEq : canonicalValue = oldValue :=
                Value.Resolves.value_unique canonicalResolved
                  ⟨oldFuel + 1, by
                    simp only [resolveAt?, oldRowFound]
                    exact oldFound⟩
              subst canonicalValue
              have newRowFound : after.row? reference = some oldRow := by
                rw [change.rows, oldRowFound]
              have sortCase := change.classifier (resolve := resolve) reference
              have childTransport : ∀ child, child ∈ oldRow.children →
                  ∀ childValue,
                    resolveAt? oldFuel resolve before child = some childValue →
                      ∃ newValue, Resolves resolve after child newValue ∧
                        Value.SamePayload childValue newValue := by
                intro child member childValue childFound
                have childLt := valid.structural.exprChild_lt before reference child
                  oldRow oldRowFound member
                change child.value.toNat < reference.value.toNat at childLt
                rw [hn] at childLt
                obtain ⟨newValue, newResolved, same, _newWellFormed⟩ :=
                  ih child.value.toNat childLt
                    child childValue ⟨oldFuel, childFound⟩ rfl
                exact ⟨newValue, newResolved, same⟩
              obtain ⟨childFuel, childrenSame⟩ :=
                Value.LookupSameOn.of_resolves childTransport
              rcases sortCase with noSort | changedSort
              · rcases noSort with ⟨oldSortNone, newSortNone⟩
                let fuel := max oldFuel childFuel
                have childrenAtFuel : Value.LookupSameOn oldRow.children
                    (resolveAt? oldFuel resolve before)
                    (resolveAt? fuel resolve after) := by
                  intro child member childValue childFound
                  obtain ⟨newValue, newFound, same⟩ :=
                    childrenSame child member childValue childFound
                  exact ⟨newValue,
                    Value.resolveAt?_of_le (Nat.le_max_right _ _) newFound, same⟩
                obtain ⟨newValue, intermediateFound, same⟩ :=
                  Value.elaborateExpr_samePayload_on childrenAtFuel
                    (change.foreign_eq (resolve := resolve) oldFuel)
                    (by simp [Value.DeclaredSame, oldSortNone]) oldFound
                    canonicalWellFormed
                have newFound : elaborateExpr
                    (resolveAt? fuel resolve after)
                    (resolveForeignUsing? (resolveAt? fuel resolve) resolve after)
                    (after.sort? reference) oldRow = some newValue :=
                  Value.elaborateExpr_of_lookup_extension
                  (fun _ _ found => found)
                  (fun source foreignReference foreignValue found =>
                    foreign_of_le (resolve := resolve) (arena := after)
                      (firstFuel := oldFuel) (secondFuel := fuel)
                      (Nat.le_max_left _ _) found) intermediateFound
                have newWellFormed :=
                  Value.elaborateExpr_wellFormed_without_declared childrenAtFuel
                    (change.foreign_eq (resolve := resolve) oldFuel)
                    (by simpa [oldSortNone] using oldFound)
                    (by simpa [newSortNone] using intermediateFound)
                    canonicalWellFormed
                refine ⟨newValue, ⟨fuel + 1, ?_⟩, same, newWellFormed⟩
                simp only [resolveAt?, newRowFound]
                simpa [newSortNone] using newFound
              · obtain ⟨oldSort, newSort, oldDeclared, newDeclared,
                    oldSortLt, newSortLt, oldResident, newResident, related⟩ :=
                  changedSort
                have nonTermTransport (notTerm : oldValue.tagSort ≠ .tm) :
                    ∃ newValue, Resolves resolve after reference newValue ∧
                      Value.SamePayload oldValue newValue ∧
                      newValue.WellFormed := by
                  obtain ⟨leftValue, rightValue, leftResolved, rightResolved,
                      leftWellFormed, rightWellFormed, equal⟩ := related
                  obtain ⟨newClassifier, newClassifierResolved, classifierSame,
                      newClassifierWellFormed⟩ :=
                    ih newSort.value.toNat (by
                      have newSortNat := newSortLt
                      change newSort.value.toNat < reference.value.toNat at newSortNat
                      rw [hn] at newSortNat
                      exact newSortNat)
                      newSort rightValue rightResolved rfl
                  rcases newClassifierResolved with
                    ⟨classifierFuel, classifierAtFuel⟩
                  let fuel := max classifierFuel (max oldFuel childFuel)
                  have childrenAtFuel : Value.LookupSameOn oldRow.children
                      (resolveAt? oldFuel resolve before)
                      (resolveAt? fuel resolve after) := by
                    intro child member childValue childFound
                    obtain ⟨targetValue, targetFound, same⟩ :=
                      childrenSame child member childValue childFound
                    exact ⟨targetValue,
                      Value.resolveAt?_of_le
                        (le_trans (Nat.le_max_right _ _)
                          (Nat.le_max_right _ _)) targetFound, same⟩
                  have classifierAtCommon :
                      resolveAt? fuel resolve after newSort = some newClassifier :=
                    Value.resolveAt?_of_le (Nat.le_max_left _ _)
                      classifierAtFuel
                  have declaredSame : Value.DeclaredSame
                      (resolveAt? oldFuel resolve before)
                      (resolveAt? fuel resolve after)
                      (before.sort? reference) (after.sort? reference) := by
                    intro selected selectedEq
                    have selectedOld : selected = oldSort := by
                      rw [oldDeclared] at selectedEq
                      exact Option.some.inj selectedEq.symm
                    subst selected
                    refine ⟨newSort, newDeclared, ?_⟩
                    intro oldType selectedFound
                    have leftEq : leftValue = .family .star oldType :=
                      Value.Resolves.value_unique leftResolved
                        ⟨oldFuel, selectedFound⟩
                    subst leftValue
                    obtain ⟨newTypeBefore, rightValueEq, typeConversion⟩ :=
                      equal.family_from_star
                    subst rightValue
                    cases classifierSame with
                    | family _ _ =>
                      exact ⟨newTypeBefore, classifierAtCommon, typeConversion⟩
                  obtain ⟨newValue, intermediateFound, same⟩ :=
                    Value.elaborateExpr_samePayload_on childrenAtFuel
                      (change.foreign_eq (resolve := resolve) oldFuel)
                      declaredSame oldFound
                      canonicalWellFormed
                  have newFound : elaborateExpr
                      (resolveAt? fuel resolve after)
                      (resolveForeignUsing? (resolveAt? fuel resolve) resolve after)
                      (after.sort? reference) oldRow = some newValue :=
                    Value.elaborateExpr_of_lookup_extension
                    (fun _ _ found => found)
                    (fun _ _ _ found => foreign_of_le
                      (resolve := resolve) (arena := after)
                      (firstFuel := oldFuel) (secondFuel := fuel)
                      (Nat.le_trans (Nat.le_max_left _ _)
                        (Nat.le_max_right _ _)) found) intermediateFound
                  have newWellFormed : newValue.WellFormed := by
                    cases same with
                    | kind kind => trivial
                    | family kind expression => exact canonicalWellFormed
                    | term oldType newType expression conversion =>
                      exact False.elim (notTerm rfl)
                  refine ⟨newValue, ⟨fuel + 1, ?_⟩, same, newWellFormed⟩
                  simp only [resolveAt?, newRowFound]
                  exact newFound
                by_cases refCase : Value.IsForeignRef oldRow
                · cases expressionCase : oldRow <;>
                    simp [Value.IsForeignRef, expressionCase] at refCase
                  all_goals
                    let refFuel := max oldFuel childFuel
                    have oldFoundAfter := oldFound
                    rw [change.foreign_eq (resolve := resolve) oldFuel] at oldFoundAfter
                    have finalFound : elaborateExpr
                        (resolveAt? oldFuel resolve before)
                        (resolveForeignUsing? (resolveAt? refFuel resolve) resolve after)
                        (before.sort? reference) oldRow = some oldValue :=
                      Value.elaborateExpr_of_lookup_extension
                      (fun _ _ found => found)
                      (fun source foreignReference foreignValue found =>
                        foreign_of_le (resolve := resolve) (arena := after)
                          (firstFuel := oldFuel) (secondFuel := refFuel)
                          (Nat.le_max_left _ _) found) oldFoundAfter
                    refine ⟨oldValue, ⟨refFuel + 1, ?_⟩,
                      Value.SamePayload.refl canonicalWellFormed,
                      canonicalWellFormed⟩
                    simp only [resolveAt?, newRowFound]
                    simpa [expressionCase, elaborateExpr] using finalFound
                · cases oldValue with
                  | kind kind => exact nonTermTransport (by simp [Value.tagSort])
                  | family kind expression =>
                      exact nonTermTransport (by simp [Value.tagSort])
                  | term advertised expression =>
                    have oldClassifierFound : ∃ oldType,
                        resolveAt? oldFuel resolve before oldSort =
                          some (.family .star oldType) := by
                      exact ⟨advertised,
                        Value.elaborateExpr_term_classifier_of_not_ref refCase
                          (by simpa [oldDeclared] using oldFound)⟩
                    obtain ⟨oldType, oldClassifierAtFuel⟩ := oldClassifierFound
                    obtain ⟨leftValue, rightValue, leftResolved, rightResolved,
                        leftWellFormed, rightWellFormed, equal⟩ := related
                    have leftEq : leftValue = .family .star oldType :=
                      Value.Resolves.value_unique leftResolved
                        ⟨oldFuel, oldClassifierAtFuel⟩
                    subst leftValue
                    obtain ⟨newTypeBefore, rightValueEq, typeConversion⟩ :=
                      equal.family_from_star
                    subst rightValue
                    obtain ⟨newClassifier, newClassifierResolved, classifierSame,
                        newClassifierWellFormed⟩ :=
                      ih newSort.value.toNat (by
                        have newSortNat := newSortLt
                        change newSort.value.toNat < reference.value.toNat at newSortNat
                        rw [hn] at newSortNat
                        exact newSortNat)
                        newSort (.family .star newTypeBefore) rightResolved rfl
                    cases classifierSame with
                    | family _ _ =>
                        rcases newClassifierResolved with
                          ⟨classifierFuel, classifierAtFuel⟩
                        let fuel := max classifierFuel (max oldFuel childFuel)
                        have childrenAtFuel : Value.LookupSameOn oldRow.children
                            (resolveAt? oldFuel resolve before)
                            (resolveAt? fuel resolve after) := by
                          intro child member childValue childFound
                          obtain ⟨targetValue, targetFound, same⟩ :=
                            childrenSame child member childValue childFound
                          exact ⟨targetValue,
                            Value.resolveAt?_of_le
                              (le_trans (Nat.le_max_right _ _)
                                (Nat.le_max_right _ _)) targetFound, same⟩
                        have classifierAtCommon :
                            resolveAt? fuel resolve after newSort =
                              some (.family .star newTypeBefore) :=
                          Value.resolveAt?_of_le (Nat.le_max_left _ _)
                            classifierAtFuel
                        have declaredSame : Value.DeclaredSame
                            (resolveAt? oldFuel resolve before)
                            (resolveAt? fuel resolve after)
                            (before.sort? reference) (after.sort? reference) := by
                          intro selected selectedEq
                          have selectedOld : selected = oldSort := by
                            rw [oldDeclared] at selectedEq
                            exact Option.some.inj selectedEq.symm
                          subst selected
                          refine ⟨newSort, newDeclared, ?_⟩
                          intro selectedType selectedFound
                          have selectedValueEq :
                              Value.family .star selectedType =
                                Value.family .star oldType :=
                            Option.some.inj
                              (selectedFound.symm.trans oldClassifierAtFuel)
                          cases selectedValueEq
                          exact ⟨newTypeBefore, classifierAtCommon, typeConversion⟩
                        obtain ⟨newValue, intermediateFound, same⟩ :=
                          Value.elaborateExpr_samePayload_on childrenAtFuel
                            (change.foreign_eq (resolve := resolve) oldFuel)
                            declaredSame oldFound
                            canonicalWellFormed
                        have newFound : elaborateExpr
                            (resolveAt? fuel resolve after)
                            (resolveForeignUsing? (resolveAt? fuel resolve) resolve after)
                            (after.sort? reference) oldRow = some newValue :=
                          Value.elaborateExpr_of_lookup_extension
                          (fun _ _ found => found)
                          (fun _ _ _ found => foreign_of_le
                            (resolve := resolve) (arena := after)
                            (firstFuel := oldFuel) (secondFuel := fuel)
                            (le_trans (Nat.le_max_left _ _)
                              (Nat.le_max_right _ _)) found) intermediateFound
                        cases same with
                        | term oldAdvertised newAdvertised expression conversion =>
                          rcases conversion with ⟨conversion⟩
                          have advertisedAtFuel :
                              resolveAt? fuel resolve after newSort =
                                some (.family .star newAdvertised) :=
                            Value.elaborateExpr_term_classifier_of_not_ref refCase
                              (by simpa [newDeclared] using newFound)
                          have advertisedValueEq :
                              Value.family .star newAdvertised =
                                Value.family .star newTypeBefore :=
                            Option.some.inj
                              (advertisedAtFuel.symm.trans classifierAtCommon)
                          cases advertisedValueEq
                          have newWellFormed := canonicalWellFormed.reclassifyTerm
                            newClassifierWellFormed conversion
                          refine ⟨.term newTypeBefore expression, ⟨fuel + 1, ?_⟩,
                            .term advertised newTypeBefore expression ⟨conversion⟩,
                            newWellFormed⟩
                          simp only [resolveAt?, newRowFound]
                          exact newFound

end CoreDenseChange

namespace SynFact.Valid

/-- Exact end-to-end certificate for Rust's state-aware direct-fact cache
union. Successful and partially failed executions alike mutate only through a
`CoreDenseChange`; all endpoint premises come from the checked fact itself. -/
theorem unionSynFactExact_coreDenseChange
    (factValid : SynFact.Valid resolve arena fact) (direct : fact.Direct)
    (checked : Columns.FusedChecked arena.dense)
    (refines : Columns.Refines arena.dense)
    (coreValid : arena.CoreKernelValid resolve) (noAssert : arena.assert = [])
    (result : Columns.UnionSynResult)
    (found : Columns.Dense.unionSynFactExact arena.dense fact.input fact.output
      fact.rel = result) :
    match result with
    | .success after =>
        CoreDenseChange resolve arena (arena.withDense after)
    | .failure after _ =>
        CoreDenseChange resolve arena (arena.withDense after) := by
  obtain ⟨inputResident, outputResident, sameCategory⟩ :=
    factValid.denseEndpoints
  obtain ⟨_equivalent, sequence⟩ :=
    Columns.unionSynFactExact_result_sequence inputResident outputResident
      sameCategory refines result found
  have endpoint := factValid.direct_referenceEqual direct
  cases result with
  | success after =>
      exact CoreDenseChange.EqualitySequence.coreDenseChange sequence checked
        coreValid endpoint noAssert
  | failure after error =>
      exact CoreDenseChange.EqualitySequence.coreDenseChange sequence checked
        coreValid endpoint noAssert

end SynFact.Valid

/-- One-way semantic simulation induced by a sound dense-column mutation.

The target may resolve a syntactically different `Value`, but it must be
well-formed and equal in the proved HOL semantics.  Classifier references may
also change, so their transport is stated separately.  The remaining fields
are the exact observations of `CoreKernelValid` that do not depend on row
classification. -/
structure CoreReclassification (resolve : Resolver) (before after : Arena) : Prop where
  structural : after.StructurallyValid
  defsLength : after.defs.length = before.defs.length
  rowBackward : ∀ reference row, after.row? reference = some row →
    before.row? reference ≠ none
  resolves : ∀ reference oldValue,
    Resolves resolve before reference oldValue →
      ∃ newValue, oldValue.WellFormed ∧
        Resolves resolve after reference newValue ∧ newValue.WellFormed ∧
        Value.Equal oldValue newValue
  classifier : ∀ reference newSort,
    after.sort? reference = some newSort →
      ∃ oldSort, before.sort? reference = some oldSort ∧
        ∀ oldClassifier,
          Resolves resolve before oldSort oldClassifier →
            ∃ newClassifier, oldClassifier.WellFormed ∧
              Resolves resolve after newSort newClassifier ∧
              newClassifier.WellFormed ∧ Value.Equal oldClassifier newClassifier
  eq : ∀ reference right, after.eq? reference = some right →
    ReferenceEqual resolve before reference right
  classes : ∀ left right,
    before.row? left ≠ none → before.row? right ≠ none →
      EqClass after left right → ReferenceEqual resolve before left right
  ctx : after.ctx = before.ctx
  axs : after.axs = before.axs
  conclusions : Conclusions resolve before → Conclusions resolve after

namespace CoreDenseChange

/-- The concrete dense-column footprint realizes the abstract semantic
reclassification interface. -/
theorem reclassification (change : CoreDenseChange resolve before after)
    (valid : before.CoreKernelValid resolve) :
    CoreReclassification resolve before after where
  structural := change.structural
  defsLength := change.defsLength
  rowBackward reference row found := by
    rw [change.rows] at found
    simp [found]
  resolves reference oldValue oldResolved := by
    obtain ⟨newValue, newResolved, same, newWellFormed⟩ :=
      change.resolves valid reference oldValue oldResolved
    have oldWellFormed := sourceWellFormed valid oldResolved
    exact ⟨newValue, oldWellFormed, newResolved, newWellFormed,
      same.equal oldWellFormed newWellFormed⟩
  classifier reference newSort newSortFound := by
    rcases change.classifier reference with unchanged | changed
    · exact False.elim (by rw [unchanged.2] at newSortFound; contradiction)
    · obtain ⟨oldSort, actualNewSort, oldDeclared, newDeclared,
          _oldLt, _newLt, _oldResident, _newResident, related⟩ := changed
      have sameSort : actualNewSort = newSort :=
        Option.some.inj (newDeclared.symm.trans newSortFound)
      subst actualNewSort
      refine ⟨oldSort, oldDeclared, ?_⟩
      intro oldClassifier oldClassifierResolved
      obtain ⟨leftValue, rightValue, leftResolved, rightResolved,
          leftWellFormed, rightWellFormed, oldEqual⟩ := related
      have leftEq : leftValue = oldClassifier :=
        Value.Resolves.value_unique leftResolved oldClassifierResolved
      subst leftValue
      obtain ⟨newClassifier, newResolved, same, newWellFormed⟩ :=
        change.resolves valid newSort rightValue rightResolved
      have rightToNew := same.equal rightWellFormed newWellFormed
      have oldToNew := oldEqual.trans rightWellFormed rightToNew
      exact ⟨newClassifier,
        sourceWellFormed valid oldClassifierResolved,
        newResolved, newWellFormed, oldToNew⟩
  eq := change.eq
  classes := change.classes
  ctx := change.ctx
  axs := change.axs
  conclusions := change.conclusions

end CoreDenseChange

namespace CoreReclassification

/-- Every source row that resolves well has a well-formed target denotation.
This is the precise existential content needed by `FullyResolves`. -/
theorem resolvesWellFormed (transport : CoreReclassification resolve before after)
    (resolved : Resolves resolve before reference oldValue) :
    ∃ newValue, Resolves resolve after reference newValue ∧ newValue.WellFormed := by
  rcases transport.resolves reference oldValue resolved with
    ⟨newValue, _oldWellFormed, newResolved, newWellFormed, _⟩
  exact ⟨newValue, newResolved, newWellFormed⟩

/-- Every target denotation reflects to an equal well-formed source
denotation.  This is derived, rather than assumed: target resolution proves
row residency, `rowBackward` finds the unchanged source syntax, source kernel
validity supplies its canonical value, and forward transport plus resolution
uniqueness identifies the requested target value. -/
theorem reflects (transport : CoreReclassification resolve before after)
    (valid : before.CoreKernelValid resolve)
    (resolved : Resolves resolve after reference newValue) :
    ∃ oldValue, Resolves resolve before reference oldValue ∧
      oldValue.WellFormed ∧ newValue.WellFormed ∧
      Value.Equal oldValue newValue := by
  have afterPresent : after.row? reference ≠ none := by
    rcases resolved with ⟨fuel, found⟩
    cases fuel with
    | zero => simp [resolveAt?] at found
    | succ fuel =>
        simp only [resolveAt?] at found
        cases rowFound : after.row? reference with
        | none => simp [rowFound] at found
        | some row => simp
  cases afterFound : after.row? reference with
  | none => exact False.elim (afterPresent afterFound)
  | some row =>
      have beforePresent := transport.rowBackward reference row afterFound
      cases beforeFound : before.row? reference with
      | none => exact False.elim (beforePresent beforeFound)
      | some beforeRow =>
          obtain ⟨oldValue, oldResolved, oldWellFormed⟩ :=
            valid.definitions reference beforeRow beforeFound
          obtain ⟨transported, _oldWellFormed, transportedResolved,
              transportedWellFormed, equal⟩ :=
            transport.resolves reference oldValue oldResolved
          have same : transported = newValue :=
            Value.Resolves.value_unique transportedResolved resolved
          subst transported
          exact ⟨oldValue, oldResolved, oldWellFormed,
            transportedWellFormed, equal⟩

/-- Recursive availability transports even though the classified values need
not be syntactically identical. -/
theorem fullyResolves (transport : CoreReclassification resolve before after)
    (fully : FullyResolves resolve before) : FullyResolves resolve after := by
  intro reference inBounds
  have beforeBounds : reference.value.toNat ≤ before.defs.length := by
    rw [← transport.defsLength]
    exact inBounds
  rcases fully reference beforeBounds with ⟨oldValue, oldResolved⟩
  rcases transport.resolvesWellFormed oldResolved with
    ⟨newValue, newResolved, _⟩
  exact ⟨newValue, newResolved⟩

/-- Semantic reference equality is stable when both denotations are replaced
by proved-equal well-formed values. -/
theorem referenceEqual (transport : CoreReclassification resolve before after)
    (equal : ReferenceEqual resolve before left right) :
    ReferenceEqual resolve after left right := by
  rcases equal with ⟨oldLeft, oldRight, oldLeftResolved, oldRightResolved,
    oldLeftWellFormed, oldRightWellFormed, oldEqual⟩
  rcases transport.resolves left oldLeft oldLeftResolved with
    ⟨newLeft, _, newLeftResolved, newLeftWellFormed, leftEqual⟩
  rcases transport.resolves right oldRight oldRightResolved with
    ⟨newRight, _, newRightResolved, newRightWellFormed, rightEqual⟩
  have newOldRight := leftEqual.symm.trans oldLeftWellFormed oldEqual
  have newEqual := newOldRight.trans oldRightWellFormed rightEqual
  exact ⟨newLeft, newRight, newLeftResolved, newRightResolved,
    newLeftWellFormed, newRightWellFormed, newEqual⟩

/-- Boolean context membership is invariant under re-advertising a term at a
convertible type. -/
theorem contextClaim (transport : CoreReclassification resolve before after)
    (claim : ContextClaim resolve before reference) :
    ContextClaim resolve after reference := by
  rcases claim with ⟨oldType, oldExpression, oldResolved,
    oldWellFormed, oldBoolean⟩
  rcases transport.resolves reference (.term oldType oldExpression) oldResolved with
    ⟨newValue, _, newResolved, newWellFormed, equal⟩
  cases equal with
  | term leftWellFormed rightWellFormed classifierConversion termConversion =>
      rcases classifierConversion with ⟨classifierConversion⟩
      rcases oldBoolean with ⟨oldBoolean⟩
      rcases oldWellFormed with
        ⟨_loweredTerm, loweredType, _termLowering, typeLowering, typing⟩
      have typeLowering' := typeLowering
      change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) oldType.toHolE =
        some loweredType at typeLowering'
      rw [classifierConversion.leftLowering] at typeLowering'
      have same := Option.some.inj typeLowering'
      subst loweredType
      exact ⟨_, _, newResolved, newWellFormed,
        ⟨classifierConversion.symm.trans typing.typeKinded oldBoolean⟩⟩

/-- A sorting witness survives simultaneous reclassification of the row and
its classifier. -/
theorem sorting (transport : CoreReclassification resolve before after)
    (claim : SortingMemberClaim resolve before reference) :
    SortingMemberClaim resolve after reference := by
  unfold SortingMemberClaim at claim ⊢
  cases newSortEq : after.sort? reference with
  | none => trivial
  | some newSort =>
      rcases transport.classifier reference newSort newSortEq with
        ⟨oldSort, oldSortEq, classifierTransport⟩
      rw [oldSortEq] at claim
      rcases claim with ⟨claimedSort, oldValue, oldClassifier,
        claimedSortEq, oldResolved, oldClassifierResolved, oldSorted⟩
      have sortSame : oldSort = claimedSort :=
        Option.some.inj (oldSortEq.symm.trans claimedSortEq)
      subst claimedSort
      rcases transport.resolves reference oldValue oldResolved with
        ⟨newValue, oldValueWellFormed, newResolved, newValueWellFormed, valueEqual⟩
      rcases classifierTransport oldClassifier oldClassifierResolved with
        ⟨newClassifier, oldClassifierWellFormed, newClassifierResolved,
          newClassifierWellFormed, classifierEqual⟩
      have oldAtNew := oldSorted.replaceClassifier oldClassifierWellFormed classifierEqual
      have newSorted := oldAtNew.replaceValue oldValueWellFormed
        newValueWellFormed valueEqual
      exact ⟨newSort, newValue, newClassifier, newSortEq, newResolved,
        newClassifierResolved, newSorted⟩

/-- The complete legacy HOL invariant survives a sound recursive
reclassification.  No theorem, context, or equality fact is discarded; all
denotations are transported through `Value.Equal`. -/
theorem coreKernelValid (transport : CoreReclassification resolve before after)
    (valid : before.CoreKernelValid resolve) : after.CoreKernelValid resolve := by
  constructor
  · exact transport.structural
  · intro reference row rowLookup
    have beforePresent := transport.rowBackward reference row rowLookup
    cases beforeLookup : before.row? reference with
    | none => exact False.elim (beforePresent beforeLookup)
    | some beforeRow =>
        rcases valid.definitions reference beforeRow beforeLookup with
          ⟨oldValue, oldResolved, oldWellFormed⟩
        exact transport.resolvesWellFormed oldResolved
  · intro reference
    exact transport.sorting (valid.sorts reference)
  · intro reference
    unfold EqualityClaim
    cases afterEq : after.eq? reference with
    | none => trivial
    | some right =>
        exact transport.referenceEqual (transport.eq reference right afterEq)
  · intro left right leftPresent rightPresent connected
    have leftBefore : before.row? left ≠ none := by
      cases found : after.row? left with
      | none => exact False.elim (leftPresent found)
      | some row => exact transport.rowBackward left row found
    have rightBefore : before.row? right ≠ none := by
      cases found : after.row? right with
      | none => exact False.elim (rightPresent found)
      | some row => exact transport.rowBackward right row found
    exact transport.referenceEqual <|
      transport.classes left right leftBefore rightBefore connected
  · intro reference member
    apply transport.contextClaim
    apply valid.context reference
    rw [← transport.ctx]
    exact member
  · intro name member
    apply valid.axioms name
    rw [← transport.axs]
    exact member
  · exact transport.conclusions valid.conclusions

end CoreReclassification

namespace CoreDenseChange

/-- A checked dense classifier rewrite preserves the complete HOL kernel
invariant. -/
theorem coreKernelValid (change : CoreDenseChange resolve before after)
    (valid : before.CoreKernelValid resolve) :
    after.CoreKernelValid resolve :=
  (change.reclassification valid).coreKernelValid valid

end CoreDenseChange

end Nucleus.Hol.Ethane.OneBased
