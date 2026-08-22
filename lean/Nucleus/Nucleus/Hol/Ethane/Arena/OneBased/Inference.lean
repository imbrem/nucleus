import Nucleus.Hol.Ethane.Arena.OneBased.Resolve
import Nucleus.HolE.Semantics
import Nucleus.HolE.Substitution

/-!
# Syntax-directed checking for resolved Ethane values

Resolution reconstructs omitted annotations, but it deliberately does not
claim that open type variables are bound or that terms are well typed.  This
file supplies the second, logical pass over the locally nameless image.  The
checker uses strict syntactic type equality; conversion is introduced only by
an explicit checked equality operation.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true

namespace Value

/-- Logical well-formedness of a resolved value in the empty binder scopes.
Kinds are already intrinsically formed; families and terms carry the existing
Ethane kinding or typing certificate. -/
def WellFormed : Value → Prop
  | .kind _ => True
  | .family _ expression =>
      Nucleus.Hol.Ethane.Kinded (.nil : TyScope []) expression
  | .term type expression =>
      Nucleus.Hol.Ethane.HasType (.nil : TyScope [])
        (.nil : TmScope ArenaSig 0) Nucleus.HolE.emptyBound expression type

end Value

noncomputable section

noncomputable local instance (priority := low) {α : Type _} : DecidableEq α :=
  Classical.decEq α

mutual

/-- Check kinding of a locally nameless family in the empty signature. -/
def checkFam : Nucleus.HolE.Fam ArenaSig types kind → Bool
  | .boolTy => true
  | .arr domain codomain => checkFam domain && checkFam codomain
  | .tyApp function argument => checkFam function && checkFam argument
  | .tyLam body => checkFam body
  | .tyBv _ => true
  | .sub _ _ => false
  | .model predicate =>
      if inferTm Nucleus.HolE.emptyBound predicate = some .boolTy then true else false
  | .primFam symbol => nomatch symbol

/-- Infer the strict syntactic type of a locally nameless term.  Subtype-only
constructors are rejected because they cannot occur in Ethane. -/
def inferTm (Γ : Nucleus.HolE.BoundCtx ArenaSig types depth) :
    Nucleus.HolE.Tm ArenaSig types depth → Option (Nucleus.HolE.Ty ArenaSig types)
  | .tyExists predicate =>
      if inferTm Nucleus.HolE.emptyBound predicate = some .boolTy then
        some .boolTy
      else none
  | .primTm symbol => nomatch symbol
  | .bv index => some (Γ index)
  | .fv _ type => if checkFam type then some type else none
  | .app function argument =>
      match inferTm Γ function with
      | some (.arr domain codomain) =>
          if inferTm Γ argument = some domain then some codomain else none
      | _ => none
  | .lam domain body =>
      if checkFam domain then
        match inferTm (Nucleus.HolE.extendBound domain Γ) body with
        | some codomain => some (.arr domain codomain)
        | none => none
      else none
  | .bool _ => some .boolTy
  | .eq type left right =>
      if checkFam type = true ∧ inferTm Γ left = some type ∧
          inferTm Γ right = some type then
        some .boolTy
      else none
  | .eps type predicate =>
      if checkFam type = true ∧
          inferTm Γ predicate = some (.arr type .boolTy) then
        some type
      else none
  | .abs _ _ _ | .rep _ _ _ => none

end

/-- Constructor count shared by the mutually recursive family and term
checker proofs.  Unlike the generated `SizeOf` instance, it counts children
whose syntactic indices differ from their parent. -/
def nodeCount : Nucleus.HolE.Expr ArenaSig types sort depth → Nat
  | .boolTy => 1
  | .arr domain codomain => nodeCount domain + nodeCount codomain + 1
  | .tyApp function argument => nodeCount function + nodeCount argument + 1
  | .tyLam body => nodeCount body + 1
  | .tyBv _ => 1
  | .sub carrier predicate => nodeCount carrier + nodeCount predicate + 1
  | .tyExists predicate => nodeCount predicate + 1
  | .model predicate => nodeCount predicate + 1
  | .primFam _ | .primTm _ | .bv _ | .bool _ => 1
  | .fv _ type => nodeCount type + 1
  | .app function argument => nodeCount function + nodeCount argument + 1
  | .lam domain body => nodeCount domain + nodeCount body + 1
  | .eq type left right => nodeCount type + nodeCount left + nodeCount right + 1
  | .eps type predicate => nodeCount type + nodeCount predicate + 1
  | .abs carrier predicate value | .rep carrier predicate value =>
      nodeCount carrier + nodeCount predicate + nodeCount value + 1

/-- Soundness of family checking below a common syntax-size bound. -/
def FamSoundBelow (fuel : Nat) : Prop :=
  ∀ {types kind} (family : Nucleus.HolE.Fam ArenaSig types kind),
    nodeCount family < fuel → checkFam family = true → Nucleus.HolE.Kinded family

/-- Soundness of term inference below a common syntax-size bound. -/
def TmSoundBelow (fuel : Nat) : Prop :=
  ∀ {types depth} {Γ : Nucleus.HolE.BoundCtx ArenaSig types depth},
    Nucleus.HolE.TypedCtx Γ →
    ∀ (term : Nucleus.HolE.Tm ArenaSig types depth)
      (type : Nucleus.HolE.Ty ArenaSig types),
      nodeCount term < fuel → inferTm Γ term = some type →
        Nucleus.HolE.HasType Γ term type

/-- The two syntax-directed passes are simultaneously sound. -/
theorem checker_sound_below (fuel : Nat) :
    FamSoundBelow fuel ∧ TmSoundBelow fuel := by
  induction fuel with
  | zero => simp [FamSoundBelow, TmSoundBelow]
  | succ fuel ih =>
      constructor
      · intro types kind family smaller accepted
        cases family with
        | boolTy => exact .boolTy
        | arr domain codomain =>
            simp only [checkFam, Bool.and_eq_true] at accepted
            exact .arr
              (ih.1 domain (by
                have decrease : nodeCount domain <
                    nodeCount (Nucleus.HolE.Expr.arr domain codomain) := by
                  simp [nodeCount]
                omega) accepted.1)
              (ih.1 codomain (by
                have decrease : nodeCount codomain <
                    nodeCount (Nucleus.HolE.Expr.arr domain codomain) := by
                  simp [nodeCount]
                omega) accepted.2)
        | tyApp function argument =>
            simp only [checkFam, Bool.and_eq_true] at accepted
            exact .tyApp
              (ih.1 function (by
                have decrease : nodeCount function <
                    nodeCount (Nucleus.HolE.Expr.tyApp function argument) := by
                  simp [nodeCount]
                omega) accepted.1)
              (ih.1 argument (by
                have decrease : nodeCount argument <
                    nodeCount (Nucleus.HolE.Expr.tyApp function argument) := by
                  simp [nodeCount]
                omega) accepted.2)
        | tyLam body =>
            exact .tyLam (ih.1 body (by
              have decrease : nodeCount body <
                  nodeCount (Nucleus.HolE.Expr.tyLam body) := by
                simp [nodeCount]
              omega)
              (by simpa only [checkFam] using accepted))
        | tyBv v => exact .tyBv v
        | sub carrier predicate => simp [checkFam] at accepted
        | model predicate =>
            simp only [checkFam] at accepted
            split at accepted
            next inferred =>
              exact .model (ih.2 (fun index => Fin.elim0 index) predicate .boolTy
                (by
                  have decrease : nodeCount predicate <
                      nodeCount (Nucleus.HolE.Expr.model predicate) := by
                    simp [nodeCount]
                  omega) inferred)
            next => contradiction
        | primFam symbol => exact nomatch symbol
      · intro types depth Γ typedContext term type smaller accepted
        cases term with
        | tyExists predicate =>
            simp only [inferTm] at accepted
            split at accepted
            next inferred =>
              cases Option.some.inj accepted
              exact .tyExists (ih.2 (fun index => Fin.elim0 index) predicate .boolTy
                (by
                  have decrease : nodeCount predicate <
                      nodeCount (Nucleus.HolE.Expr.tyExists (depth := depth) predicate) := by
                    simp [nodeCount]
                  omega) inferred)
            next => contradiction
        | primTm symbol => exact nomatch symbol
        | bv index =>
            simp only [inferTm] at accepted
            cases Option.some.inj accepted
            exact .bv (typedContext index) rfl
        | fv name type =>
            simp only [inferTm] at accepted
            split at accepted
            next checked =>
              cases Option.some.inj accepted
              exact .fv name (ih.1 type (by
                have decrease : nodeCount type <
                    nodeCount (Nucleus.HolE.Expr.fv (depth := depth) name type) := by
                  simp [nodeCount]
                omega)
                (by simpa using checked))
            next => contradiction
        | app function argument =>
            simp only [inferTm] at accepted
            split at accepted <;> try contradiction
            rename_i domain codomain functionType
            split at accepted
            next argumentType =>
              cases Option.some.inj accepted
              exact .app
                (ih.2 typedContext function (.arr domain type)
                  (by
                    have decrease : nodeCount function <
                        nodeCount (Nucleus.HolE.Expr.app function argument) := by
                      simp [nodeCount]
                    omega) functionType)
                (ih.2 typedContext argument domain
                  (by
                    have decrease : nodeCount argument <
                        nodeCount (Nucleus.HolE.Expr.app function argument) := by
                      simp [nodeCount]
                    omega) argumentType)
            next => contradiction
        | lam domain body =>
            simp only [inferTm] at accepted
            split at accepted
            next domainChecked =>
              split at accepted <;> try contradiction
              rename_i codomain bodyType
              cases Option.some.inj accepted
              let domainKinded := ih.1 domain (by
                have decrease : nodeCount domain <
                    nodeCount (Nucleus.HolE.Expr.lam domain body) := by
                  simp [nodeCount]
                omega)
                (by simpa using domainChecked)
              exact .lam body domainKinded
                (ih.2 (Fin.cases domainKinded typedContext) body codomain
                  (by
                    have decrease : nodeCount body <
                        nodeCount (Nucleus.HolE.Expr.lam domain body) := by
                      simp [nodeCount]
                    omega) bodyType)
            next => contradiction
        | bool value =>
            simp only [inferTm] at accepted
            cases Option.some.inj accepted
            exact .bool value
        | eq family left right =>
            simp only [inferTm] at accepted
            split at accepted
            next checks =>
              cases Option.some.inj accepted
              exact .eq
                (ih.1 family (by
                  have decrease : nodeCount family <
                      nodeCount (Nucleus.HolE.Expr.eq family left right) := by
                    simp only [nodeCount]
                    omega
                  omega) checks.1)
                (ih.2 typedContext left family
                  (by
                    have decrease : nodeCount left <
                        nodeCount (Nucleus.HolE.Expr.eq family left right) := by
                      simp only [nodeCount]
                      omega
                    omega) checks.2.1)
                (ih.2 typedContext right family
                  (by
                    have decrease : nodeCount right <
                        nodeCount (Nucleus.HolE.Expr.eq family left right) := by
                      simp only [nodeCount]
                      omega
                    omega) checks.2.2)
            next => contradiction
        | eps type predicate =>
            simp only [inferTm] at accepted
            split at accepted
            next checks =>
              cases Option.some.inj accepted
              exact .eps
                (ih.1 type (by
                  have decrease : nodeCount type <
                      nodeCount (Nucleus.HolE.Expr.eps type predicate) := by
                    simp [nodeCount]
                  omega) checks.1)
                (ih.2 typedContext predicate (.arr type .boolTy)
                  (by
                    have decrease : nodeCount predicate <
                        nodeCount (Nucleus.HolE.Expr.eps type predicate) := by
                      simp [nodeCount]
                    omega) checks.2)
            next => contradiction
        | abs => simp [inferTm] at accepted
        | rep => simp [inferTm] at accepted

/-- Successful family checking produces the trusted kinding judgment. -/
theorem checkFam_sound {family : Nucleus.HolE.Fam ArenaSig types kind}
    (accepted : checkFam family = true) : Nucleus.HolE.Kinded family :=
  (checker_sound_below (nodeCount family + 1)).1 family (by omega) accepted

/-- Successful term inference produces the trusted typing judgment. -/
theorem inferTm_sound {Γ : Nucleus.HolE.BoundCtx ArenaSig types depth}
    (typedContext : Nucleus.HolE.TypedCtx Γ)
    {term : Nucleus.HolE.Tm ArenaSig types depth}
    {type : Nucleus.HolE.Ty ArenaSig types}
    (accepted : inferTm Γ term = some type) : Nucleus.HolE.HasType Γ term type :=
  (checker_sound_below (nodeCount term + 1)).2 typedContext term type (by omega) accepted

/-- A resolved value passes the logical checker in the empty binder scopes. -/
def Value.check : Value → Bool
  | .kind _ => true
  | .family _familyKind expression =>
      match expression.lower (.nil : TyScope []) (.nil : TmScope ArenaSig 0) with
      | some lowered => checkFam lowered
      | none => false
  | .term type expression =>
      match type.lowerTy (.nil : TyScope []),
          expression.lowerTm (.nil : TyScope []) (.nil : TmScope ArenaSig 0) with
      | some loweredType, some loweredTerm =>
          if inferTm Nucleus.HolE.emptyBound loweredTerm = some loweredType then
            true
          else false
      | _, _ => false

/-- The executable logical pass is sound for the existing Ethane judgments. -/
theorem Value.check_sound {value : Value} (accepted : value.check = true) :
    value.WellFormed := by
  cases value with
  | kind value => trivial
  | family familyKind expression =>
      simp only [Value.check] at accepted
      split at accepted <;> try contradiction
      rename_i lowered lowering
      exact Nucleus.Hol.Ethane.Checks.complete lowering rfl
        (checkFam_sound accepted)
  | term type expression =>
      simp only [Value.check] at accepted
      split at accepted <;> try contradiction
      rename_i loweredType loweredTerm typeLowering termLowering
      split at accepted
      next inferred =>
        refine Nucleus.Hol.Ethane.Checks.complete termLowering ?_
          (inferTm_sound (fun index => Fin.elim0 index) inferred)
        change (do
          let lowered ← type.lowerTy (.nil : TyScope [])
          pure (Nucleus.HolE.Classification.tm lowered)) =
            some (Nucleus.HolE.Classification.tm loweredType)
        rw [typeLowering]
        rfl
      next => contradiction

end

end Nucleus.Hol.Ethane.OneBased
