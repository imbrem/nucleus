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

mutual
  inductive Kinded {Base : Type u} : Ty Base -> Prop where
    | base (name : Base) : Kinded (.base name)
    | bool : Kinded .boolTy
    | nat : Kinded .natTy
    | arr : Kinded A -> Kinded B -> Kinded (.arr A B)
    | sub : Kinded A -> HasType (extendBound A emptyBound) p .boolTy ->
        Kinded (.sub A p)

  inductive HasType {Base : Type u} : {depth : Nat} ->
      BoundCtx Base depth -> Tm Base depth -> Ty Base -> Prop where
    | bound (hA : Kinded A) (lookup : Γ i = A) : HasType Γ (.bound i) A
    | free (name : Nat) (hA : Kinded A) : HasType Γ (.free name A) A
    | app : HasType Γ f (.arr A B) -> HasType Γ x A -> HasType Γ (.app f x) B
    | lam {depth : Nat} {Γ : BoundCtx Base depth}
        (body : Tm Base (depth + 1)) (hA : Kinded A) :
        HasType (extendBound A Γ) body B ->
        HasType Γ (.lam A body) (.arr A B)
    | bool (value : Bool) : HasType Γ (.bool value) .boolTy
    | zero : HasType Γ .zero .natTy
    | succ : HasType Γ x .natTy -> HasType Γ (.succ x) .natTy
    | eq (hA : Kinded A) : HasType Γ x A -> HasType Γ y A ->
        HasType Γ (.eq A x y) .boolTy
    | eps (hA : Kinded A) : HasType Γ p (.arr A .boolTy) ->
        HasType Γ (.eps A p) A
    | abs (hA : Kinded A)
        (hp : HasType (extendBound A emptyBound) p .boolTy) :
        HasType Γ x A -> HasType Γ (.abs A p x) (.sub A p)
    | rep (hA : Kinded A)
        (hp : HasType (extendBound A emptyBound) p .boolTy) :
        HasType Γ x (.sub A p) -> HasType Γ (.rep A p x) A
end

structure Checked {Base : Type u} {depth : Nat} (Γ : BoundCtx Base depth) (A : Ty Base) where
  term : Tm Base depth
  typing : HasType Γ term A

theorem HasType.regularity {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base} :
    HasType Γ t A -> Kinded A
  | .bound hA _ => hA
  | .free _ hA => hA
  | .app hf _ => by
      cases hf.regularity with
      | arr _ hB => exact hB
  | .lam _ hA bodyTyping => .arr hA bodyTyping.regularity
  | .bool _ => .bool
  | .zero => .nat
  | .succ _ => .nat
  | .eq _ _ _ => .bool
  | .eps hA _ => hA
  | .abs hA hp _ => .sub hA hp
  | .rep hA _ _ => hA

theorem Checked.scoped {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {A : Ty Base} (checked : Checked Γ A) :
    ScopedAt depth checked.term :=
  scopedAt_index checked.term

theorem Checked.locallyClosed {Base : Type u} {A : Ty Base}
    (checked : Checked (emptyBound : BoundCtx Base 0) A) :
    RequiredDepth checked.term = 0 := by
  exact Nat.eq_zero_of_le_zero checked.scoped

/-- Syntax annotations make the synthesized type unique. -/
theorem HasType.unique {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A B : Ty Base}
    (first : HasType Γ t A) : HasType Γ t B -> A = B := by
  intro second
  cases first with
  | bound hA lookup =>
      cases second with
      | bound _ lookup' => exact lookup.symm.trans lookup'
  | free name hA =>
      cases second with
      | free _ _ => rfl
  | app hf hx =>
      cases second with
      | app hf' hx' =>
          have h := hf.unique hf'
          exact Hol.arr.inj h |>.2
  | lam body hA bodyTyping =>
      cases second with
      | lam _ _ bodyTyping' =>
          exact congrArg (Hol.arr _) (bodyTyping.unique bodyTyping')
  | bool value => cases second; rfl
  | zero => cases second; rfl
  | succ valueTyping => cases second; rfl
  | eq hA hx hy => cases second; rfl
  | eps hA hp => cases second; rfl
  | abs hA hp hx => cases second; rfl
  | rep hA hp hx => cases second; rfl

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
  | .bound hA lookup => by
      simpa [rename] using HasType.bound hA ((relation _).trans lookup)
  | .free name hA => by
      simpa [rename] using HasType.free (Γ := Γ') name hA
  | .app hf hx => by simpa [rename] using .app (hf.renameBound relation) (hx.renameBound relation)
  | .lam body hA ht =>
      by
        simpa [rename] using HasType.lam (Γ := Γ') (rename (liftRen ρ) body) hA
          (ht.renameBound (liftRen_context relation _))
  | .bool value => by simpa [rename] using HasType.bool (Γ := Γ') value
  | .zero => by simpa [rename] using HasType.zero (Γ := Γ')
  | .succ valueTyping => by
      simpa [rename] using HasType.succ (valueTyping.renameBound relation)
  | .eq hA hx hy => by simpa [rename] using .eq hA (hx.renameBound relation) (hy.renameBound relation)
  | .eps hA hp => by simpa [rename] using .eps hA (hp.renameBound relation)
  | .abs hA hp hx => by simpa [rename] using .abs hA hp (hx.renameBound relation)
  | .rep hA hp hx => by simpa [rename] using .rep hA hp (hx.renameBound relation)

theorem HasType.weakenBound {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A B : Ty Base}
    (typing : HasType Γ t A) :
    HasType (extendBound B Γ) (weaken t) A :=
  typing.renameBound (ρ := Fin.succ) (Γ' := extendBound B Γ) (fun _ => rfl)

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
  · exact .bound hA rfl
  · exact (typed j).weakenBound

theorem HasType.instantiate {Base : Type u} {m n : Nat}
    {source : BoundCtx Base m} {target : BoundCtx Base n}
    {σ : Fin m -> Tm Base n} (typed : TypedSubstitution source target σ)
    {t : Tm Base m} {A : Ty Base} :
    HasType source t A -> HasType target (Nucleus.HolLN.instantiate σ t) A
  | .bound _ lookup => by
      rename_i i hA
      have hi := typed i
      rw [lookup] at hi
      simpa [Nucleus.HolLN.instantiate] using hi
  | .free name hA => by
      simpa [Nucleus.HolLN.instantiate] using HasType.free (Γ := target) name hA
  | .app hf hx => by simpa [Nucleus.HolLN.instantiate] using .app (hf.instantiate typed) (hx.instantiate typed)
  | .lam body hA ht => by
      simpa [Nucleus.HolLN.instantiate] using
        HasType.lam (Γ := target) (Nucleus.HolLN.instantiate (liftSub σ) body) hA
          (ht.instantiate (liftSub_typed typed _ hA))
  | .bool value => by simpa [Nucleus.HolLN.instantiate] using HasType.bool (Γ := target) value
  | .zero => by simpa [Nucleus.HolLN.instantiate] using HasType.zero (Γ := target)
  | .succ valueTyping => by
      simpa [Nucleus.HolLN.instantiate] using HasType.succ (valueTyping.instantiate typed)
  | .eq hA hx hy => by simpa [Nucleus.HolLN.instantiate] using .eq hA (hx.instantiate typed) (hy.instantiate typed)
  | .eps hA hp => by simpa [Nucleus.HolLN.instantiate] using .eps hA (hp.instantiate typed)
  | .abs hA hp hx => by simpa [Nucleus.HolLN.instantiate] using .abs hA hp (hx.instantiate typed)
  | .rep hA hp hx => by simpa [Nucleus.HolLN.instantiate] using .rep hA hp (hx.instantiate typed)

theorem HasType.openBound {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {A B : Ty Base} {body : Tm Base (depth + 1)}
    {x : Tm Base depth} (bodyTyping : HasType (extendBound A Γ) body B)
    (argumentTyping : HasType Γ x A) (wellFormed : ∀ i, Kinded (Γ i)) :
    HasType Γ (Nucleus.HolLN.openBound body x) B := by
  apply bodyTyping.instantiate
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact argumentTyping
  · exact .bound (wellFormed j) rfl

theorem HasType.openFree {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {A B : Ty Base} {body : Tm Base (depth + 1)}
    {name : Nat} (bodyTyping : HasType (extendBound A Γ) body B)
    (hA : Kinded A)
    (wellFormed : ∀ i, Kinded (Γ i)) :
    HasType Γ (Nucleus.HolLN.openFree body name A) B := by
  apply bodyTyping.openBound (.free name hA) wellFormed

end Nucleus.HolLN
