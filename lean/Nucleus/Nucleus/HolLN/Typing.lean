import Nucleus.HolLN.Substitution

/-!
# Syntax-directed typing

Raw typing evidence lives in `Prop`; checked terms retain that proof behind a
small façade.  The term constructors are bound variable, free variable,
application, lambda, Boolean literal, zero, successor, equality, choice,
subtype abstraction, and subtype representation. Type formation covers base,
Boolean, individual/natural, arrow, and the fixed-context subtype predicate.
-/

namespace Nucleus.HolLN

universe u

abbrev BoundCtx (Base : Type u) (depth : Nat) := Fin depth -> Ty Base

def emptyBound {Base : Type u} : BoundCtx Base 0 := Fin.elim0

def extendBound {Base : Type u} {depth : Nat} (A : Ty Base)
    (Γ : BoundCtx Base depth) : BoundCtx Base (depth + 1) :=
  Fin.cases A Γ

/-- What a syntax node is classified by: type-family expressions have kinds
and terms have ordinary HOL types. -/
inductive Classification (Base : Type u) : HolSort -> Type u where
  | kind {indexed : Kind} : Classification Base (.kind indexed)
  | tm (value : Ty Base) : Classification Base .tm

/-- The single syntax-directed classification judgment. Its kind fragment
also validates predicates embedded in subtype types. -/
inductive Checks {Base : Type u} : {sort : HolSort} -> {depth : Nat} ->
    BoundCtx Base depth -> (expression : Hol Base sort depth) ->
    Classification Base sort -> Prop where
  | kindBase {kind : Kind} (name : Base) :
      Checks emptyBound (.base (kind := kind) name) (.kind)
  | kindBool : Checks emptyBound .boolTy (.kind)
  | kindNat : Checks emptyBound .natTy (.kind)
  | kindArr : Checks emptyBound A (.kind) -> Checks emptyBound B (.kind) ->
      Checks emptyBound (.arr A B) (.kind)
  | kindApp : Checks emptyBound F (.kind) ->
      Checks emptyBound A (.kind) -> Checks emptyBound (.tyApp F A) (.kind)
  | kindSub : Checks emptyBound A (.kind) ->
      Checks (extendBound A emptyBound) p (.tm .boolTy) ->
      Checks emptyBound (.sub A p) (.kind)
  | tmBv (hA : Checks emptyBound A (.kind)) (lookup : Γ i = A) :
      Checks Γ (.bv i) (.tm A)
  | tmFv (name : Nat) (hA : Checks emptyBound A (.kind)) :
      Checks Γ (.fv name A) (.tm A)
  | tmApp : Checks Γ f (.tm (.arr A B)) -> Checks Γ x (.tm A) ->
      Checks Γ (.app f x) (.tm B)
  | tmLam {depth : Nat} {Γ : BoundCtx Base depth}
      (body : Tm Base (depth + 1)) (hA : Checks emptyBound A (.kind)) :
      Checks (extendBound A Γ) body (.tm B) ->
      Checks Γ (.lam A body) (.tm (.arr A B))
  | tmBool (value : Bool) : Checks Γ (.bool value) (.tm .boolTy)
  | tmZero : Checks Γ .zero (.tm .natTy)
  | tmSucc : Checks Γ x (.tm .natTy) -> Checks Γ (.succ x) (.tm .natTy)
  | tmEq (hA : Checks emptyBound A (.kind)) :
      Checks Γ x (.tm A) -> Checks Γ y (.tm A) -> Checks Γ (.eq A x y) (.tm .boolTy)
  | tmEps (hA : Checks emptyBound A (.kind)) :
      Checks Γ p (.tm (.arr A .boolTy)) -> Checks Γ (.eps A p) (.tm A)
  | tmAbs (hA : Checks emptyBound A (.kind))
      (hp : Checks (extendBound A emptyBound) p (.tm .boolTy)) :
      Checks Γ x (.tm A) -> Checks Γ (.abs A p x) (.tm (.sub A p))
  | tmRep (hA : Checks emptyBound A (.kind))
      (hp : Checks (extendBound A emptyBound) p (.tm .boolTy)) :
      Checks Γ x (.tm (.sub A p)) -> Checks Γ (.rep A p x) (.tm A)

abbrev Kinded {Base : Type u} {kind : Kind} (A : Fam Base kind) : Prop :=
  Checks emptyBound A (.kind)

abbrev HasType {Base : Type u} {depth : Nat} (Γ : BoundCtx Base depth)
    (tm : Tm Base depth) (A : Ty Base) : Prop := Checks Γ tm (.tm A)

structure Checked {Base : Type u} {depth : Nat} (Γ : BoundCtx Base depth) (A : Ty Base) where
  tm : Tm Base depth
  typing : HasType Γ tm A

theorem HasType.regularity {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base} :
    HasType Γ t A -> Kinded A
  | .tmBv hA _ => hA
  | .tmFv _ hA => hA
  | .tmApp hf _ => by
      cases HasType.regularity hf with
      | kindArr _ hB => exact hB
  | .tmLam _ hA bodyTyping => .kindArr hA (HasType.regularity bodyTyping)
  | .tmBool _ => .kindBool
  | .tmZero => .kindNat
  | .tmSucc _ => .kindNat
  | .tmEq _ _ _ => .kindBool
  | .tmEps hA _ => hA
  | .tmAbs hA hp _ => .kindSub hA hp
  | .tmRep hA _ _ => hA

theorem Checked.scoped {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {A : Ty Base} (checked : Checked Γ A) :
    ScopedAt depth checked.tm :=
  scopedAt_index checked.tm

theorem Checked.locallyClosed {Base : Type u} {A : Ty Base}
    (checked : Checked (emptyBound : BoundCtx Base 0) A) :
    RequiredDepth checked.tm = 0 := by
  exact Nat.eq_zero_of_le_zero checked.scoped

/-- Syntax annotations make the synthesized type unique. -/
theorem HasType.unique {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A B : Ty Base}
    (first : HasType Γ t A) : HasType Γ t B -> A = B := by
  intro second
  cases first with
  | tmBv hA lookup =>
      cases second with
      | tmBv _ lookup' => exact lookup.symm.trans lookup'
  | tmFv name hA =>
      cases second with
      | tmFv _ _ => rfl
  | tmApp hf hx =>
      cases second with
      | tmApp hf' hx' =>
          have h := HasType.unique hf hf'
          exact Hol.arr.inj h |>.2
  | tmLam body hA bodyTyping =>
      cases second with
      | tmLam _ _ bodyTyping' =>
          exact congrArg (Hol.arr _) (HasType.unique bodyTyping bodyTyping')
  | tmBool value => cases second; rfl
  | tmZero => cases second; rfl
  | tmSucc valueTyping => cases second; rfl
  | tmEq hA hx hy => cases second; rfl
  | tmEps hA hp => cases second; rfl
  | tmAbs hA hp hx => cases second; rfl
  | tmRep hA hp hx => cases second; rfl

def ContextRenaming {Base : Type u} {m n : Nat} (Γ : BoundCtx Base m)
    (Γ' : BoundCtx Base n) (ρ : Fin m -> Fin n) : Prop :=
  ∀ i, Γ' (ρ i) = Γ i

theorem liftRen_context {Base : Type u} {m n : Nat} {Γ : BoundCtx Base m}
    {Γ' : BoundCtx Base n} {ρ : Fin m -> Fin n} (relation : ContextRenaming Γ Γ' ρ)
    (A : Ty Base) :
    ContextRenaming (extendBound A Γ) (extendBound A Γ') (liftRen ρ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact relation j

theorem HasType.renameBound {Base : Type u} {m n : Nat}
    {Γ : BoundCtx Base m} {Γ' : BoundCtx Base n} {ρ : Fin m -> Fin n}
    (relation : ContextRenaming Γ Γ' ρ) {t : Tm Base m} {A : Ty Base} :
    HasType Γ t A -> HasType Γ' (rename ρ t) A
  | .tmBv hA lookup => by
      simpa [rename] using Checks.tmBv hA ((relation _).trans lookup)
  | .tmFv name hA => by
      simpa [rename] using Checks.tmFv (Γ := Γ') name hA
  | .tmApp hf hx => by
      simpa [rename] using Checks.tmApp
        (HasType.renameBound relation hf) (HasType.renameBound relation hx)
  | .tmLam body hA ht =>
      by
        simpa [rename] using Checks.tmLam (Γ := Γ') (rename (liftRen ρ) body) hA
          (HasType.renameBound (liftRen_context relation _) ht)
  | .tmBool value => by simpa [rename] using Checks.tmBool (Γ := Γ') value
  | .tmZero => by simpa [rename] using Checks.tmZero (Γ := Γ')
  | .tmSucc valueTyping => by
      simpa [rename] using Checks.tmSucc (HasType.renameBound relation valueTyping)
  | .tmEq hA hx hy => by
      simpa [rename] using Checks.tmEq hA
        (HasType.renameBound relation hx) (HasType.renameBound relation hy)
  | .tmEps hA hp => by simpa [rename] using Checks.tmEps hA (HasType.renameBound relation hp)
  | .tmAbs hA hp hx => by simpa [rename] using Checks.tmAbs hA hp (HasType.renameBound relation hx)
  | .tmRep hA hp hx => by simpa [rename] using Checks.tmRep hA hp (HasType.renameBound relation hx)

theorem HasType.weakenBound {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A B : Ty Base}
    (typing : HasType Γ t A) :
    HasType (extendBound B Γ) (weaken t) A :=
  HasType.renameBound (ρ := Fin.succ) (Γ' := extendBound B Γ) (fun _ => rfl) typing

def TypedSubstitution {Base : Type u} {m n : Nat}
    (source : BoundCtx Base m) (target : BoundCtx Base n)
    (σ : Fin m -> Tm Base n) : Prop :=
  ∀ i, HasType target (σ i) (source i)

theorem liftSub_typed {Base : Type u} {m n : Nat}
    {source : BoundCtx Base m} {target : BoundCtx Base n}
    {σ : Fin m -> Tm Base n} (typed : TypedSubstitution source target σ)
    (A : Ty Base) (hA : Kinded A) :
    TypedSubstitution (extendBound A source) (extendBound A target) (liftSub σ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .tmBv hA rfl
  · exact HasType.weakenBound (typed j)

theorem HasType.instantiate {Base : Type u} {m n : Nat}
    {source : BoundCtx Base m} {target : BoundCtx Base n}
    {σ : Fin m -> Tm Base n} (typed : TypedSubstitution source target σ)
    {t : Tm Base m} {A : Ty Base} :
    HasType source t A -> HasType target (Nucleus.HolLN.instantiate σ t) A
  | .tmBv _ lookup => by
      rename_i i hA
      have hi := typed i
      rw [lookup] at hi
      simpa [Nucleus.HolLN.instantiate] using hi
  | .tmFv name hA => by
      simpa [Nucleus.HolLN.instantiate] using Checks.tmFv (Γ := target) name hA
  | .tmApp hf hx => by
      simpa [Nucleus.HolLN.instantiate] using Checks.tmApp
        (HasType.instantiate typed hf) (HasType.instantiate typed hx)
  | .tmLam body hA ht => by
      simpa [Nucleus.HolLN.instantiate] using
        Checks.tmLam (Γ := target) (Nucleus.HolLN.instantiate (liftSub σ) body) hA
          (HasType.instantiate (liftSub_typed typed _ hA) ht)
  | .tmBool value => by simpa [Nucleus.HolLN.instantiate] using Checks.tmBool (Γ := target) value
  | .tmZero => by simpa [Nucleus.HolLN.instantiate] using Checks.tmZero (Γ := target)
  | .tmSucc valueTyping => by
      simpa [Nucleus.HolLN.instantiate] using Checks.tmSucc (HasType.instantiate typed valueTyping)
  | .tmEq hA hx hy => by
      simpa [Nucleus.HolLN.instantiate] using Checks.tmEq hA
        (HasType.instantiate typed hx) (HasType.instantiate typed hy)
  | .tmEps hA hp => by simpa [Nucleus.HolLN.instantiate] using Checks.tmEps hA (HasType.instantiate typed hp)
  | .tmAbs hA hp hx => by simpa [Nucleus.HolLN.instantiate] using Checks.tmAbs hA hp (HasType.instantiate typed hx)
  | .tmRep hA hp hx => by simpa [Nucleus.HolLN.instantiate] using Checks.tmRep hA hp (HasType.instantiate typed hx)

theorem HasType.openBound {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {A B : Ty Base} {body : Tm Base (depth + 1)}
    {x : Tm Base depth} (bodyTyping : HasType (extendBound A Γ) body B)
    (argumentTyping : HasType Γ x A) (wellFormed : ∀ i, Kinded (Γ i)) :
    HasType Γ (Nucleus.HolLN.openBound body x) B := by
  apply bodyTyping.instantiate
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact argumentTyping
  · exact .tmBv (wellFormed j) rfl

theorem HasType.openFree {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {A B : Ty Base} {body : Tm Base (depth + 1)}
    {name : Nat} (bodyTyping : HasType (extendBound A Γ) body B)
    (hA : Kinded A)
    (wellFormed : ∀ i, Kinded (Γ i)) :
    HasType Γ (Nucleus.HolLN.openFree body name A) B := by
  apply bodyTyping.openBound (.tmFv name hA) wellFormed

end Nucleus.HolLN
