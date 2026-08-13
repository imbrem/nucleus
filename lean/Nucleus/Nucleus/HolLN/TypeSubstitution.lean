import Nucleus.HolLN.Typing

/-!
# Substitution for monomorphic base types

A type substitution maps every atomic `Base` type to an arbitrary well-kinded
HOL type. Because subtype types contain term predicates, substitution is one
dependent traversal over `Hol`: it covers types, term annotations, and subtype
predicates together. This module proves identity, composition, compatibility
with term binding operations, and preservation of kinding and typing.
-/

namespace Nucleus.HolLN

universe u v w

abbrev TypeSub (Base : Type u) (Target : Type v) := Base -> Ty Target

def substHol {Base : Type u} {Target : Type v} (σ : TypeSub Base Target) :
    {sort : HolSort} -> {depth : Nat} -> Hol Base sort depth -> Hol Target sort depth
  | _, _, .base name => σ name
  | _, _, .boolTy => .boolTy
  | _, _, .natTy => .natTy
  | _, _, .arr A B => .arr (substHol σ A) (substHol σ B)
  | _, _, .sub A p => .sub (substHol σ A) (substHol σ p)
  | _, _, .bound i => .bound i
  | _, _, .free name A => .free name (substHol σ A)
  | _, _, .app f x => .app (substHol σ f) (substHol σ x)
  | _, _, .lam A body => .lam (substHol σ A) (substHol σ body)
  | _, _, .bool value => .bool value
  | _, _, .zero => .zero
  | _, _, .succ value => .succ (substHol σ value)
  | _, _, .eq A x y => .eq (substHol σ A) (substHol σ x) (substHol σ y)
  | _, _, .eps A p => .eps (substHol σ A) (substHol σ p)
  | _, _, .abs A p x => .abs (substHol σ A) (substHol σ p) (substHol σ x)
  | _, _, .rep A p x => .rep (substHol σ A) (substHol σ p) (substHol σ x)

abbrev substTy {Base : Type u} {Target : Type v} (σ : TypeSub Base Target)
    (A : Ty Base) : Ty Target := substHol σ A

abbrev substTm {Base : Type u} {Target : Type v} (σ : TypeSub Base Target)
    {depth : Nat} (term : Tm Base depth) : Tm Target depth := substHol σ term

def substBoundCtx {Base : Type u} {Target : Type v} (σ : TypeSub Base Target)
    {depth : Nat} (Γ : BoundCtx Base depth) : BoundCtx Target depth :=
  fun i => substTy σ (Γ i)

def substHyps {Base : Type u} {Target : Type v} (σ : TypeSub Base Target)
    {depth : Nat} (H : List (Tm Base depth)) : List (Tm Target depth) :=
  H.map (substTm σ)

theorem substHol_identity {Base : Type u} : {sort : HolSort} -> {depth : Nat} ->
    (expression : Hol Base sort depth) -> substHol (fun name => .base name) expression = expression
  | _, _, .base name => rfl
  | _, _, .boolTy => rfl
  | _, _, .natTy => rfl
  | _, _, .arr A B => by simp [substHol, substHol_identity A, substHol_identity B]
  | _, _, .sub A p => by simp [substHol, substHol_identity A, substHol_identity p]
  | _, _, .bound i => rfl
  | _, _, .free name A => by
      simp [substHol, substHol_identity A]
  | _, _, .app f x => by simp [substHol, substHol_identity f, substHol_identity x]
  | _, _, .lam A body => by simp [substHol, substHol_identity A, substHol_identity body]
  | _, _, .bool value => rfl
  | _, _, .zero => rfl
  | _, _, .succ value => by simp [substHol, substHol_identity value]
  | _, _, .eq A x y => by
      simp [substHol, substHol_identity A, substHol_identity x, substHol_identity y]
  | _, _, .eps A p => by simp [substHol, substHol_identity A, substHol_identity p]
  | _, _, .abs A p x => by
      simp [substHol, substHol_identity A, substHol_identity p, substHol_identity x]
  | _, _, .rep A p x => by
      simp [substHol, substHol_identity A, substHol_identity p, substHol_identity x]

theorem substHol_comp {Base : Type u} {Middle : Type v} {Target : Type w}
    (σ : TypeSub Base Middle) (τ : TypeSub Middle Target) :
    {sort : HolSort} -> {depth : Nat} -> (expression : Hol Base sort depth) ->
      substHol τ (substHol σ expression) =
        substHol (fun name => substTy τ (σ name)) expression
  | _, _, .base name => rfl
  | _, _, .boolTy => rfl
  | _, _, .natTy => rfl
  | _, _, .arr A B => by simp [substHol, substHol_comp σ τ A, substHol_comp σ τ B]
  | _, _, .sub A p => by simp [substHol, substHol_comp σ τ A, substHol_comp σ τ p]
  | _, _, .bound i => rfl
  | _, _, .free name A => by
      simp [substHol, substHol_comp σ τ A]
  | _, _, .app f x => by simp [substHol, substHol_comp σ τ f, substHol_comp σ τ x]
  | _, _, .lam A body => by
      simp [substHol, substHol_comp σ τ A, substHol_comp σ τ body]
  | _, _, .bool value => rfl
  | _, _, .zero => rfl
  | _, _, .succ value => by simp [substHol, substHol_comp σ τ value]
  | _, _, .eq A x y => by
      simp [substHol, substHol_comp σ τ A, substHol_comp σ τ x, substHol_comp σ τ y]
  | _, _, .eps A p => by simp [substHol, substHol_comp σ τ A, substHol_comp σ τ p]
  | _, _, .abs A p x => by
      simp [substHol, substHol_comp σ τ A, substHol_comp σ τ p, substHol_comp σ τ x]
  | _, _, .rep A p x => by
      simp [substHol, substHol_comp σ τ A, substHol_comp σ τ p, substHol_comp σ τ x]

theorem substHol_fresh {Base : Type u} {Target : Type v} (σ : TypeSub Base Target)
    (name : Nat) (baseFresh : ∀ base, Fresh name (σ base)) :
    {sort : HolSort} -> {depth : Nat} -> (expression : Hol Base sort depth) ->
      Fresh name expression -> Fresh name (substHol σ expression)
  | _, _, .base base, _ => baseFresh base
  | _, _, .boolTy, _ => by simp [Fresh, FreeIn, substHol]
  | _, _, .natTy, _ => by simp [Fresh, FreeIn, substHol]
  | _, _, .arr A B, fresh => by
      simp only [Fresh, substHol, FreeIn, not_or] at fresh ⊢
      exact ⟨substHol_fresh σ name baseFresh A fresh.1,
        substHol_fresh σ name baseFresh B fresh.2⟩
  | _, _, .sub A p, fresh => by
      simp only [Fresh, substHol, FreeIn, not_or] at fresh ⊢
      exact ⟨substHol_fresh σ name baseFresh A fresh.1,
        substHol_fresh σ name baseFresh p fresh.2⟩
  | _, _, .bound i, _ => by simp [Fresh, FreeIn, substHol]
  | _, _, .free other A, fresh => by
      simp only [Fresh, substHol, FreeIn, not_or] at fresh ⊢
      exact ⟨fresh.1, substHol_fresh σ name baseFresh A fresh.2⟩
  | _, _, .app f x, fresh => by
      simp only [Fresh, substHol, FreeIn, not_or] at fresh ⊢
      exact ⟨substHol_fresh σ name baseFresh f fresh.1,
        substHol_fresh σ name baseFresh x fresh.2⟩
  | _, _, .lam A body, fresh => by
      simp only [Fresh, substHol, FreeIn, not_or] at fresh ⊢
      exact ⟨substHol_fresh σ name baseFresh A fresh.1,
        substHol_fresh σ name baseFresh body fresh.2⟩
  | _, _, .bool value, _ => by simp [Fresh, FreeIn, substHol]
  | _, _, .zero, _ => by simp [Fresh, FreeIn, substHol]
  | _, _, .succ value, fresh => by
      simpa [Fresh, substHol, FreeIn] using substHol_fresh σ name baseFresh value fresh
  | _, _, .eq A x y, fresh => by
      simp only [Fresh, substHol, FreeIn, not_or] at fresh ⊢
      exact ⟨substHol_fresh σ name baseFresh A fresh.1,
        substHol_fresh σ name baseFresh x fresh.2.1,
        substHol_fresh σ name baseFresh y fresh.2.2⟩
  | _, _, .eps A p, fresh => by
      simp only [Fresh, substHol, FreeIn, not_or] at fresh ⊢
      exact ⟨substHol_fresh σ name baseFresh A fresh.1,
        substHol_fresh σ name baseFresh p fresh.2⟩
  | _, _, .abs A p x, fresh => by
      simp only [Fresh, substHol, FreeIn, not_or] at fresh ⊢
      exact ⟨substHol_fresh σ name baseFresh A fresh.1,
        substHol_fresh σ name baseFresh p fresh.2.1,
        substHol_fresh σ name baseFresh x fresh.2.2⟩
  | _, _, .rep A p x, fresh => by
      simp only [Fresh, substHol, FreeIn, not_or] at fresh ⊢
      exact ⟨substHol_fresh σ name baseFresh A fresh.1,
        substHol_fresh σ name baseFresh p fresh.2.1,
        substHol_fresh σ name baseFresh x fresh.2.2⟩

theorem substTm_rename {Base : Type u} {Target : Type v} (σ : TypeSub Base Target)
    {m n : Nat} (ρ : Fin m -> Fin n) : (term : Tm Base m) ->
      substTm σ (rename ρ term) = rename ρ (substTm σ term)
  | .bound i => by simp [rename, substTm, substHol]
  | .free name A => by simp [rename, substTm, substHol]
  | .app f x => by simp [rename, substHol, substTm_rename σ ρ f, substTm_rename σ ρ x]
  | .lam A body => by
      simp [rename, substHol, substTm_rename σ (liftRen ρ) body]
  | .bool value => by simp [rename, substTm, substHol]
  | .zero => by simp [rename, substTm, substHol]
  | .succ value => by simp [rename, substHol, substTm_rename σ ρ value]
  | .eq A x y => by simp [rename, substHol, substTm_rename σ ρ x, substTm_rename σ ρ y]
  | .eps A p => by simp [rename, substHol, substTm_rename σ ρ p]
  | .abs A p x => by simp [rename, substHol, substTm_rename σ ρ x]
  | .rep A p x => by simp [rename, substHol, substTm_rename σ ρ x]

theorem substTm_weaken {Base : Type u} {Target : Type v} (σ : TypeSub Base Target)
    {depth : Nat} (term : Tm Base depth) :
    substTm σ (weaken term) = weaken (substTm σ term) :=
  substTm_rename σ Fin.succ term

theorem substTm_instantiate {Base : Type u} {Target : Type v}
    (typeSub : TypeSub Base Target) {m n : Nat} (termSub : Fin m -> Tm Base n) :
    (term : Tm Base m) ->
      substTm typeSub (instantiate termSub term) =
        instantiate (fun i => substTm typeSub (termSub i)) (substTm typeSub term)
  | .bound i => by simp [instantiate, substTm, substHol]
  | .free name A => by simp [instantiate, substTm, substHol]
  | .app f x => by
      simp [instantiate, substHol, substTm_instantiate typeSub termSub f,
        substTm_instantiate typeSub termSub x]
  | .lam A body => by
      simp only [instantiate, substHol]
      congr 2
      change substTm typeSub (instantiate (liftSub termSub) body) = _
      rw [substTm_instantiate typeSub (liftSub termSub) body]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp [liftSub, substTm_weaken]
  | .bool value => by simp [instantiate, substTm, substHol]
  | .zero => by simp [instantiate, substTm, substHol]
  | .succ value => by
      simp [instantiate, substHol, substTm_instantiate typeSub termSub value]
  | .eq A x y => by
      simp [instantiate, substHol, substTm_instantiate typeSub termSub x,
        substTm_instantiate typeSub termSub y]
  | .eps A p => by
      simp [instantiate, substHol, substTm_instantiate typeSub termSub p]
  | .abs A p x => by
      simp [instantiate, substHol, substTm_instantiate typeSub termSub x]
  | .rep A p x => by
      simp [instantiate, substHol, substTm_instantiate typeSub termSub x]

theorem substTm_openBound {Base : Type u} {Target : Type v}
    (σ : TypeSub Base Target) {depth : Nat} (body : Tm Base (depth + 1))
    (replacement : Tm Base depth) :
    substTm σ (openBound body replacement) =
      openBound (substTm σ body) (substTm σ replacement) := by
  simp only [openBound]
  rw [substTm_instantiate σ (Fin.cases replacement .bound) body]
  congr 1
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

theorem substTm_instantiateOne {Base : Type u} {Target : Type v}
    (σ : TypeSub Base Target) {depth : Nat} (predicate : Tm Base 1)
    (replacement : Tm Base depth) :
    substTm σ (instantiateOne predicate replacement) =
      instantiateOne (substTm σ predicate) (substTm σ replacement) := by
  exact substTm_instantiate σ (fun _ => replacement) predicate

theorem substBoundCtx_empty {Base : Type u} {Target : Type v} (σ : TypeSub Base Target) :
    substBoundCtx σ (emptyBound : BoundCtx Base 0) = emptyBound := by
  funext i
  exact Fin.elim0 i

theorem substBoundCtx_extend {Base : Type u} {Target : Type v}
    (σ : TypeSub Base Target) {depth : Nat} (Γ : BoundCtx Base depth) (A : Ty Base) :
    substBoundCtx σ (extendBound A Γ) =
      extendBound (substTy σ A) (substBoundCtx σ Γ) := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

def WellKindedTypeSub {Base : Type u} {Target : Type v}
    (σ : TypeSub Base Target) : Prop :=
  ∀ name, Kinded (σ name)

structure AdmissibleTypeSub {Base : Type u} {Target : Type v}
    (σ : TypeSub Base Target) : Prop where
  wellKinded : WellKindedTypeSub σ
  closed : ∀ base name, Fresh name (σ base)

mutual
  theorem Kinded.substTy {Base : Type u} {Target : Type v}
      {σ : TypeSub Base Target} (wellKinded : WellKindedTypeSub σ) :
      {A : Ty Base} -> Kinded A -> Kinded (Nucleus.HolLN.substTy σ A)
    | _, .base name => wellKinded name
    | _, .bool => .bool
    | _, .nat => .nat
    | _, .arr hA hB => .arr (Kinded.substTy wellKinded hA) (Kinded.substTy wellKinded hB)
    | _, .sub hA hp => by
        apply Kinded.sub (Kinded.substTy wellKinded hA)
        simpa [substTy, substTm, substHol, substBoundCtx_extend,
          substBoundCtx_empty] using
          HasType.substTy wellKinded hp

  theorem HasType.substTy {Base : Type u} {Target : Type v}
      {σ : TypeSub Base Target} (wellKinded : WellKindedTypeSub σ) :
      {depth : Nat} -> {Γ : BoundCtx Base depth} ->
      {term : Tm Base depth} -> {A : Ty Base} -> HasType Γ term A ->
        HasType (substBoundCtx σ Γ)
          (substTm σ term) (Nucleus.HolLN.substTy σ A)
    | _, _, _, _, .bound hA lookup => by
        apply HasType.bound (Kinded.substTy wellKinded hA)
        simp [substBoundCtx, lookup]
    | _, _, _, _, .free name hA =>
        HasType.free name (Kinded.substTy wellKinded hA)
    | _, _, _, _, .app hf hx =>
        .app (HasType.substTy wellKinded hf) (HasType.substTy wellKinded hx)
    | _, Γ, _, _, .lam body hA ht => by
        apply HasType.lam _ (Kinded.substTy wellKinded hA)
        simpa [substBoundCtx_extend] using HasType.substTy wellKinded ht
    | _, _, _, _, .bool value => .bool value
    | _, _, _, _, .zero => .zero
    | _, _, _, _, .succ ht => .succ (HasType.substTy wellKinded ht)
    | _, _, _, _, .eq hA hx hy =>
        .eq (Kinded.substTy wellKinded hA)
          (HasType.substTy wellKinded hx) (HasType.substTy wellKinded hy)
    | _, _, _, _, .eps hA hp =>
        .eps (Kinded.substTy wellKinded hA) (HasType.substTy wellKinded hp)
    | _, _, _, _, .abs hA hp hx => by
        apply HasType.abs (Kinded.substTy wellKinded hA) _ (HasType.substTy wellKinded hx)
        simpa [substTy, substTm, substHol, substBoundCtx_extend,
          substBoundCtx_empty] using
          HasType.substTy wellKinded hp
    | _, _, _, _, .rep hA hp hx => by
        apply HasType.rep (Kinded.substTy wellKinded hA) _ (HasType.substTy wellKinded hx)
        simpa [substTy, substTm, substHol, substBoundCtx_extend,
          substBoundCtx_empty] using
          HasType.substTy wellKinded hp
end

end Nucleus.HolLN
