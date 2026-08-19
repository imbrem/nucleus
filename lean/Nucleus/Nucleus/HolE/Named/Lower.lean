import Nucleus.HolE.Named.FV

/-!
# Lowering named HolE to locally nameless HolE

Lowering is indexed by separate type and term scopes.  A variable is captured
only by an exact match of its name and syntactic sort.  Failure to resolve a
type variable is reported because locally nameless HolE has no free type
variable constructor.
-/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

noncomputable local instance (priority := low) {α : Type _} : DecidableEq α :=
  Classical.decEq α

abbrev TyScope := List TyDecl
abbrev TmScope (Sig : Signature) := List (TmDecl Sig)

def TyScope.kinds : TyScope → List Kind := List.map Decl.sort

private def lookupTy (wanted : TyDecl) :
    (scope : TyScope) → Option (Nucleus.HolE.TyVar scope.kinds wanted.sort)
  | [] => none
  | current :: rest =>
      if _names : wanted.name = current.name then
        if sorts : wanted.sort = current.sort then
          some (sorts ▸ Nucleus.HolE.TyVar.zero)
        else
          (lookupTy wanted rest).map Nucleus.HolE.TyVar.succ
      else
        (lookupTy wanted rest).map Nucleus.HolE.TyVar.succ

private noncomputable def lookupTm (wanted : TmDecl Sig) :
    (scope : TmScope Sig) → Option (Fin scope.length)
  | [] => none
  | current :: rest =>
      if wanted = current then
        some 0
      else
        (lookupTm wanted rest).map Fin.succ

def scopeDepth (sort : HolSort) (depth : Nat) : Nat :=
  match sort with
  | .kind _ => 0
  | .tm => depth

/-- Environment-indexed lowering. -/
noncomputable def lower (typeScope : TyScope) (termScope : TmScope Sig) :
    (expression : Expr Sig sort) →
      Option (Nucleus.HolE.Expr Sig typeScope.kinds sort
        (scopeDepth sort termScope.length))
  | .boolTy => some .boolTy
  | .arr A B => do return .arr (← lower typeScope [] A) (← lower typeScope [] B)
  | .tyApp F A => do return .tyApp (← lower typeScope [] F) (← lower typeScope [] A)
  | @Expr.tyLam _ domain _ _ name body => do
      return .tyLam (← lower (⟨name, domain⟩ :: typeScope) [] body)
  | .tyFv name kind => do return .tyBv (← lookupTy ⟨name, kind⟩ typeScope)
  | .sub A name predicate => do
      let loweredA ← lower typeScope [] A
      let loweredPredicate ← lower typeScope [⟨name, A⟩] predicate
      return .sub loweredA loweredPredicate
  | .tyExists name predicate => do
      return .tyExists (← lower (⟨name, .star⟩ :: typeScope) [] predicate)
  | .model name predicate => do
      return .model (← lower (⟨name, .star⟩ :: typeScope) [] predicate)
  | .primFam symbol => some (.primFam symbol)
  | .primTm symbol => some (.primTm symbol)
  | .tmFv name A =>
      match lookupTm ⟨name, A⟩ termScope with
      | some index => some (.bv index)
      | none => do return .fv name (← lower typeScope [] A)
  | .app function argument => do
      return .app (← lower typeScope termScope function)
        (← lower typeScope termScope argument)
  | .lam name A body => do
      return .lam (← lower typeScope [] A)
        (← lower typeScope (⟨name, A⟩ :: termScope) body)
  | .bool value => some (.bool value)
  | .eq A left right => do
      return .eq (← lower typeScope [] A) (← lower typeScope termScope left)
        (← lower typeScope termScope right)
  | .eps A predicate => do
      return .eps (← lower typeScope [] A) (← lower typeScope termScope predicate)
  | .abs A name predicate value => do
      return .abs (← lower typeScope [] A)
        (← lower typeScope [⟨name, A⟩] predicate)
        (← lower typeScope termScope value)
  | .rep A name predicate value => do
      return .rep (← lower typeScope [] A)
        (← lower typeScope [⟨name, A⟩] predicate)
        (← lower typeScope termScope value)

noncomputable def lowerFam (typeScope : TyScope) (family : Fam Sig kind) :
    Option (Nucleus.HolE.Fam Sig typeScope.kinds kind) :=
  lower typeScope [] family

noncomputable def lowerTy (typeScope : TyScope) (type : Ty Sig) :
    Option (Nucleus.HolE.Ty Sig typeScope.kinds) :=
  lower typeScope [] type

noncomputable def lowerTm (typeScope : TyScope) (termScope : TmScope Sig)
    (term : Tm Sig) :
    Option (Nucleus.HolE.Tm Sig typeScope.kinds termScope.length) :=
  lower typeScope termScope term

@[simp] theorem lower_letTm (typeScope : TyScope) (termScope : TmScope Sig)
    (name : Nat) (A : Ty Sig) (value body : Tm Sig) :
    lowerTm typeScope termScope (letTm name A value body) = (do
      let loweredFunction ← (do
        let loweredA ← lowerTy typeScope A
        let loweredBody ← lowerTm typeScope (⟨name, A⟩ :: termScope) body
        pure (.lam loweredA loweredBody))
      let loweredValue ← lowerTm typeScope termScope value
      pure (.app loweredFunction loweredValue)) := by
  simp only [lowerTm, lowerTy, letTm, lower]
  generalize typeEquation : lower typeScope [] A = loweredType
  generalize bodyEquation :
    lower typeScope (⟨name, A⟩ :: termScope) body = loweredBody
  cases loweredType <;> cases loweredBody <;> simp [Option.bind] <;> rfl

end Nucleus.HolE.Named
