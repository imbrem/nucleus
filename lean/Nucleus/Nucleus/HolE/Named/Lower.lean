import Nucleus.HolE.Named.FV

/-!
# Lowering named HolE to locally nameless HolE

The type and term scopes are intrinsically indexed by their locally nameless
contexts.  A binder captures only an exact syntactic `(name, sort)` match.
-/

namespace Nucleus.HolE.Named

universe u
set_option relaxedAutoImplicit true

noncomputable local instance (priority := low) {α : Type _} : DecidableEq α :=
  Classical.decEq α

inductive TyScope : List Kind → Type where
  | nil : TyScope []
  | cons (name : Nat) (rest : TyScope types) : TyScope (kind :: types)

inductive TmScope (Sig : Signature.{u}) : Nat → Type (max u 1) where
  | nil : TmScope Sig 0
  | cons (declaration : TmDecl Sig) (rest : TmScope Sig depth) :
      TmScope Sig (depth + 1)

def lookupTy (wanted : TyDecl) :
    (scope : TyScope types) → Option (Nucleus.HolE.TyVar types wanted.sort)
  | .nil => none
  | @TyScope.cons _ currentKind current rest =>
      if _names : wanted.name = current then
        if sorts : wanted.sort = currentKind then
          some (sorts ▸ Nucleus.HolE.TyVar.zero)
        else
          (lookupTy wanted rest).map Nucleus.HolE.TyVar.succ
      else
        (lookupTy wanted rest).map Nucleus.HolE.TyVar.succ

noncomputable def lookupTm (wanted : TmDecl Sig) :
    (scope : TmScope Sig depth) → Option (Fin depth)
  | .nil => none
  | .cons current rest =>
      if wanted = current then some 0 else (lookupTm wanted rest).map Fin.succ

mutual
/-- Lower a named type family in a type-variable scope. -/
noncomputable def lowerFam (typeScope : TyScope types) :
    Fam Sig kind → Option (Nucleus.HolE.Fam Sig types kind)
    | .boolTy => some .boolTy
    | .arr A B => return .arr (← lowerFam typeScope A) (← lowerFam typeScope B)
    | .tyApp F A => return .tyApp (← lowerFam typeScope F) (← lowerFam typeScope A)
    | @Expr.tyLam _ domain _ _ name body =>
        return .tyLam (← lowerFam (.cons (kind := domain) name typeScope) body)
    | .tyFv name kind => return .tyBv (← lookupTy ⟨name, kind⟩ typeScope)
    | .sub A name predicate => do
        let loweredA ← lowerFam typeScope A
        let loweredPredicate ← lowerTm typeScope (.cons ⟨name, A⟩ .nil) predicate
        return .sub loweredA loweredPredicate
    | .model name predicate =>
        return .model (← lowerTm (.cons (kind := .star) name typeScope) .nil predicate)
    | .primFam symbol => some (.primFam symbol)

/-- Lower a named term in independent type and term scopes. -/
noncomputable def lowerTm (typeScope : TyScope types) (termScope : TmScope Sig depth) :
    Tm Sig → Option (Nucleus.HolE.Tm Sig types depth)
    | .tyExists name predicate =>
        return .tyExists (← lowerTm (.cons (kind := .star) name typeScope) .nil predicate)
    | .primTm symbol => some (.primTm symbol)
    | .tmFv name A =>
        match lookupTm ⟨name, A⟩ termScope with
        | some index => some (.bv index)
        | none => return .fv name (← lowerFam typeScope A)
    | .app function argument =>
        return .app (← lowerTm typeScope termScope function)
          (← lowerTm typeScope termScope argument)
    | .lam name A body =>
        return .lam (← lowerFam typeScope A)
          (← lowerTm typeScope (.cons ⟨name, A⟩ termScope) body)
    | .bool value => some (.bool value)
    | .eq A left right =>
        return .eq (← lowerFam typeScope A) (← lowerTm typeScope termScope left)
          (← lowerTm typeScope termScope right)
    | .eps A predicate =>
        return .eps (← lowerFam typeScope A) (← lowerTm typeScope termScope predicate)
    | .abs A name predicate value =>
        return .abs (← lowerFam typeScope A)
          (← lowerTm typeScope (.cons ⟨name, A⟩ .nil) predicate)
          (← lowerTm typeScope termScope value)
    | .rep A name predicate value =>
        return .rep (← lowerFam typeScope A)
          (← lowerTm typeScope (.cons ⟨name, A⟩ .nil) predicate)
          (← lowerTm typeScope termScope value)
end

noncomputable def lowerTy (typeScope : TyScope types) (type : Ty Sig) :=
  lowerFam typeScope type

def scopeDepth (sort : HolSort) (depth : Nat) : Nat :=
  match sort with
  | .kind _ => 0
  | .tm => depth

/-- Sort-polymorphic lowering used by alpha equivalence and unified checking. -/
noncomputable def lower (typeScope : TyScope types) (termScope : TmScope Sig depth) :
    (expression : Expr Sig sort) →
      Option (Nucleus.HolE.Expr Sig types sort (scopeDepth sort depth)) :=
  match sort with
  | .kind _ => lowerFam typeScope
  | .tm => lowerTm typeScope termScope

@[simp] theorem lower_letTm (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (name : Nat) (A : Ty Sig) (value body : Tm Sig) :
    lowerTm typeScope termScope (letTm name A value body) = (do
      let loweredFunction ← (do
        let loweredA ← lowerFam typeScope A
        let loweredBody ← lowerTm typeScope (.cons ⟨name, A⟩ termScope) body
        pure (.lam loweredA loweredBody))
      let loweredValue ← lowerTm typeScope termScope value
      pure (.app loweredFunction loweredValue)) := by
  simp only [letTm, lowerTm]

end Nucleus.HolE.Named
