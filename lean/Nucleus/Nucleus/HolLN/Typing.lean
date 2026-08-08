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

abbrev FreeCtx (Base : Type u) := Nat -> Option (Ty Base)
abbrev BoundCtx (Base : Type u) (depth : Nat) := Fin depth -> Ty Base

def emptyContext {Base : Type u} : FreeCtx Base := fun _ => none
def emptyBound {Base : Type u} : BoundCtx Base 0 := Fin.elim0

def extendFree {Base : Type u} (Δ : FreeCtx Base) (name : Nat) (A : Ty Base) :
    FreeCtx Base :=
  fun other => if other = name then some A else Δ other

def removeFree {Base : Type u} (Δ : FreeCtx Base) (name : Nat) : FreeCtx Base :=
  fun other => if other = name then none else Δ other

def extendBound {Base : Type u} {depth : Nat} (A : Ty Base)
    (Γ : BoundCtx Base depth) : BoundCtx Base (depth + 1) :=
  Fin.cases A Γ

mutual
  inductive Kinded {Base : Type u} : Ty Base -> Prop where
    | base (name : Base) : Kinded (.base name)
    | bool : Kinded .boolTy
    | nat : Kinded .natTy
    | arr : Kinded A -> Kinded B -> Kinded (.arr A B)
    | sub : Kinded A -> HasType emptyContext (extendBound A emptyBound) p .boolTy ->
        Kinded (.sub A p)

  inductive HasType {Base : Type u} :
      (Δ : FreeCtx Base) -> {depth : Nat} ->
      BoundCtx Base depth -> Tm Base depth -> Ty Base -> Prop where
    | bound (hA : Kinded A) (lookup : Γ i = A) : HasType Δ Γ (.bound i) A
    | free (name : Nat) (hA : Kinded A) (lookup : Δ name = some A) :
        HasType Δ Γ (.free name) A
    | app : HasType Δ Γ f (.arr A B) -> HasType Δ Γ x A -> HasType Δ Γ (.app f x) B
    | lam {depth : Nat} {Γ : BoundCtx Base depth}
        (body : Tm Base (depth + 1)) (hA : Kinded A) :
        HasType Δ (extendBound A Γ) body B ->
        HasType Δ Γ (.lam A body) (.arr A B)
    | bool (value : Bool) : HasType Δ Γ (.bool value) .boolTy
    | zero : HasType Δ Γ .zero .natTy
    | succ : HasType Δ Γ x .natTy -> HasType Δ Γ (.succ x) .natTy
    | eq (hA : Kinded A) : HasType Δ Γ x A -> HasType Δ Γ y A ->
        HasType Δ Γ (.eq A x y) .boolTy
    | eps (hA : Kinded A) : HasType Δ Γ p (.arr A .boolTy) ->
        HasType Δ Γ (.eps A p) A
    | abs (hA : Kinded A)
        (hp : HasType emptyContext (extendBound A emptyBound) p .boolTy) :
        HasType Δ Γ x A -> HasType Δ Γ (.abs A p x) (.sub A p)
    | rep (hA : Kinded A)
        (hp : HasType emptyContext (extendBound A emptyBound) p .boolTy) :
        HasType Δ Γ x (.sub A p) -> HasType Δ Γ (.rep A p x) A
end

structure Checked {Base : Type u} (Δ : FreeCtx Base) {depth : Nat}
    (Γ : BoundCtx Base depth) (A : Ty Base) where
  term : Tm Base depth
  typing : HasType Δ Γ term A

theorem HasType.regularity {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base} :
    HasType Δ Γ t A -> Kinded A
  | .bound hA _ => hA
  | .free _ hA _ => hA
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

theorem Checked.scoped {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A : Ty Base} (checked : Checked Δ Γ A) :
    ScopedAt depth checked.term :=
  scopedAt_index checked.term

theorem Checked.locallyClosed {Base : Type u} {Δ : FreeCtx Base} {A : Ty Base}
    (checked : Checked Δ (emptyBound : BoundCtx Base 0) A) :
    RequiredDepth checked.term = 0 := by
  exact Nat.eq_zero_of_le_zero checked.scoped

/-- Syntax annotations make the synthesized type unique. -/
theorem HasType.unique {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A B : Ty Base}
    (first : HasType Δ Γ t A) : HasType Δ Γ t B -> A = B := by
  intro second
  cases first with
  | bound hA lookup =>
      cases second with
      | bound _ lookup' => exact lookup.symm.trans lookup'
  | free name hA lookup =>
      cases second with
      | free _ _ lookup' => exact Option.some.inj (lookup.symm.trans lookup')
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

/-- Free-context weakening, stated as preservation of every existing lookup. -/
theorem HasType.weakenFree {Base : Type u} {Δ Δ' : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base}
    (preserves : ∀ (name : Nat) (B : Ty Base), Δ name = some B -> Δ' name = some B) :
    HasType Δ Γ t A -> HasType Δ' Γ t A
  | .bound hA lookup => .bound hA lookup
  | .free name hA lookup => .free name hA (preserves name _ lookup)
  | .app hf hx => .app (hf.weakenFree preserves) (hx.weakenFree preserves)
  | .lam body hA ht => .lam body hA (ht.weakenFree preserves)
  | .bool value => .bool value
  | .zero => .zero
  | .succ valueTyping => .succ (valueTyping.weakenFree preserves)
  | .eq hA hx hy => .eq hA (hx.weakenFree preserves) (hy.weakenFree preserves)
  | .eps hA hp => .eps hA (hp.weakenFree preserves)
  | .abs hA hp hx => .abs hA hp (hx.weakenFree preserves)
  | .rep hA hp hx => .rep hA hp (hx.weakenFree preserves)

/-- A free assumption unused by the term can be removed from its context. -/
theorem HasType.strengthenFree {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base} (name : Nat) :
    HasType Δ Γ t A -> Fresh name t -> HasType (removeFree Δ name) Γ t A
  | .bound hA lookup, _ => .bound hA lookup
  | .free other hA lookup, freshness => by
      have different : other ≠ name := by simpa [Fresh, FreeIn] using freshness
      exact .free other hA (by simpa [removeFree, different] using lookup)
  | .app hf hx, freshness =>
      .app (hf.strengthenFree name (fun found => freshness (Or.inl found)))
        (hx.strengthenFree name (fun found => freshness (Or.inr found)))
  | .lam body hA ht, freshness =>
      .lam body hA
        (ht.strengthenFree name (fun found => freshness (Or.inr found)))
  | .bool value, _ => .bool value
  | .zero, _ => .zero
  | .succ valueTyping, freshness => .succ (valueTyping.strengthenFree name freshness)
  | .eq hA hx hy, freshness =>
      .eq hA
        (hx.strengthenFree name (fun found => freshness (Or.inr (Or.inl found))))
        (hy.strengthenFree name (fun found => freshness (Or.inr (Or.inr found))))
  | .eps hA hp, freshness =>
      .eps hA (hp.strengthenFree name (fun found => freshness (Or.inr found)))
  | .abs hA hp hx, freshness =>
      .abs hA hp
        (hx.strengthenFree name (fun found => freshness (Or.inr (Or.inr found))))
  | .rep hA hp hx, freshness =>
      .rep hA hp
        (hx.strengthenFree name (fun found => freshness (Or.inr (Or.inr found))))

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

theorem HasType.renameBound {Base : Type u} {Δ : FreeCtx Base} {m n : Nat}
    {Γ : BoundCtx Base m} {Γ' : BoundCtx Base n} {ρ : Fin m -> Fin n}
    (relation : ContextRenaming Γ Γ' ρ) {t : Tm Base m} {A : Ty Base} :
    HasType Δ Γ t A -> HasType Δ Γ' (rename ρ t) A
  | .bound hA lookup => by
      simpa [rename] using HasType.bound (Δ := Δ) hA ((relation _).trans lookup)
  | .free name hA lookup => by
      simpa [rename] using HasType.free (Γ := Γ') name hA lookup
  | .app hf hx => by simpa [rename] using .app (hf.renameBound relation) (hx.renameBound relation)
  | .lam body hA ht =>
      by
        simpa [rename] using HasType.lam (Γ := Γ') (rename (liftRen ρ) body) hA
          (ht.renameBound (liftRen_context relation _))
  | .bool value => by simpa [rename] using HasType.bool (Δ := Δ) (Γ := Γ') value
  | .zero => by simpa [rename] using HasType.zero (Δ := Δ) (Γ := Γ')
  | .succ valueTyping => by
      simpa [rename] using HasType.succ (valueTyping.renameBound relation)
  | .eq hA hx hy => by simpa [rename] using .eq hA (hx.renameBound relation) (hy.renameBound relation)
  | .eps hA hp => by simpa [rename] using .eps hA (hp.renameBound relation)
  | .abs hA hp hx => by simpa [rename] using .abs hA hp (hx.renameBound relation)
  | .rep hA hp hx => by simpa [rename] using .rep hA hp (hx.renameBound relation)

theorem HasType.weakenBound {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A B : Ty Base}
    (typing : HasType Δ Γ t A) :
    HasType Δ (extendBound B Γ) (weaken t) A :=
  typing.renameBound (ρ := Fin.succ) (Γ' := extendBound B Γ) (fun _ => rfl)

/-- Capture-avoiding substitution preserves typing. -/
theorem HasType.substFree {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t replacement : Tm Base depth} {A B : Ty Base}
    {name : Nat} (replacementTyping : HasType Δ Γ replacement B)
    : HasType (extendFree Δ name B) Γ t A ->
    HasType Δ Γ (Nucleus.HolLN.substFree name replacement t) A
  | .bound hA lookup => by
      simpa [Nucleus.HolLN.substFree] using HasType.bound (Δ := Δ) hA lookup
  | .free other hA lookup => by
      by_cases same : other = name
      · subst other
        have typeEquality : B = A := Option.some.inj (by simpa [extendFree] using lookup)
        simpa [Nucleus.HolLN.substFree] using typeEquality ▸ replacementTyping
      · have originalLookup : Δ other = some A := by
          simpa [extendFree, same] using lookup
        simpa [Nucleus.HolLN.substFree, same] using
          HasType.free (Γ := Γ) other hA originalLookup
  | .app hf hx => by
      simpa [Nucleus.HolLN.substFree] using HasType.app
        (HasType.substFree replacementTyping hf)
        (HasType.substFree replacementTyping hx)
  | .lam body hA ht => by
      simpa [Nucleus.HolLN.substFree] using
        HasType.lam (Γ := Γ) _ hA (HasType.substFree replacementTyping.weakenBound ht)
  | .bool value => by
      simpa [Nucleus.HolLN.substFree] using HasType.bool (Δ := Δ) (Γ := Γ) value
  | .zero => by
      simpa [Nucleus.HolLN.substFree] using HasType.zero (Δ := Δ) (Γ := Γ)
  | .succ valueTyping => by
      simpa [Nucleus.HolLN.substFree] using
        HasType.succ (HasType.substFree replacementTyping valueTyping)
  | .eq hA hx hy => by
      simpa [Nucleus.HolLN.substFree] using HasType.eq hA
        (HasType.substFree replacementTyping hx)
        (HasType.substFree replacementTyping hy)
  | .eps hA hp => by
      simpa [Nucleus.HolLN.substFree] using
        HasType.eps hA (HasType.substFree replacementTyping hp)
  | .abs hA hp hx => by
      simpa [Nucleus.HolLN.substFree] using
        HasType.abs hA hp (HasType.substFree replacementTyping hx)
  | .rep hA hp hx => by
      simpa [Nucleus.HolLN.substFree] using
        HasType.rep hA hp (HasType.substFree replacementTyping hx)

def TypedSubstitution {Base : Type u} {Δ : FreeCtx Base} {m n : Nat}
    (source : BoundCtx Base m) (target : BoundCtx Base n)
    (σ : Fin m -> Tm Base n) : Prop :=
  ∀ i, HasType Δ target (σ i) (source i)

theorem liftSub_typed {Base : Type u} {Δ : FreeCtx Base} {m n : Nat}
    {source : BoundCtx Base m} {target : BoundCtx Base n}
    {σ : Fin m -> Tm Base n} (typed : TypedSubstitution (Δ := Δ) source target σ)
    (A : Ty Base) (hA : Kinded A) :
    TypedSubstitution (Δ := Δ) (extendBound A source) (extendBound A target) (liftSub σ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .bound hA rfl
  · exact (typed j).weakenBound

theorem HasType.instantiate {Base : Type u} {Δ : FreeCtx Base} {m n : Nat}
    {source : BoundCtx Base m} {target : BoundCtx Base n}
    {σ : Fin m -> Tm Base n} (typed : TypedSubstitution (Δ := Δ) source target σ)
    {t : Tm Base m} {A : Ty Base} :
    HasType Δ source t A -> HasType Δ target (Nucleus.HolLN.instantiate σ t) A
  | .bound _ lookup => by
      rename_i i hA
      have hi := typed i
      rw [lookup] at hi
      simpa [Nucleus.HolLN.instantiate] using hi
  | .free name hA lookup => by
      simpa [Nucleus.HolLN.instantiate] using HasType.free (Γ := target) name hA lookup
  | .app hf hx => by simpa [Nucleus.HolLN.instantiate] using .app (hf.instantiate typed) (hx.instantiate typed)
  | .lam body hA ht => by
      simpa [Nucleus.HolLN.instantiate] using
        HasType.lam (Γ := target) (Nucleus.HolLN.instantiate (liftSub σ) body) hA
          (ht.instantiate (liftSub_typed typed _ hA))
  | .bool value => by simpa [Nucleus.HolLN.instantiate] using HasType.bool (Δ := Δ) (Γ := target) value
  | .zero => by simpa [Nucleus.HolLN.instantiate] using HasType.zero (Δ := Δ) (Γ := target)
  | .succ valueTyping => by
      simpa [Nucleus.HolLN.instantiate] using HasType.succ (valueTyping.instantiate typed)
  | .eq hA hx hy => by simpa [Nucleus.HolLN.instantiate] using .eq hA (hx.instantiate typed) (hy.instantiate typed)
  | .eps hA hp => by simpa [Nucleus.HolLN.instantiate] using .eps hA (hp.instantiate typed)
  | .abs hA hp hx => by simpa [Nucleus.HolLN.instantiate] using .abs hA hp (hx.instantiate typed)
  | .rep hA hp hx => by simpa [Nucleus.HolLN.instantiate] using .rep hA hp (hx.instantiate typed)

theorem HasType.openBound {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A B : Ty Base} {body : Tm Base (depth + 1)}
    {x : Tm Base depth} (bodyTyping : HasType Δ (extendBound A Γ) body B)
    (argumentTyping : HasType Δ Γ x A) (wellFormed : ∀ i, Kinded (Γ i)) :
    HasType Δ Γ (Nucleus.HolLN.openBound body x) B := by
  apply bodyTyping.instantiate
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact argumentTyping
  · exact .bound (wellFormed j) rfl

theorem HasType.openFree {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A B : Ty Base} {body : Tm Base (depth + 1)}
    {name : Nat} (bodyTyping : HasType Δ (extendBound A Γ) body B)
    (hA : Kinded A) (lookup : Δ name = some A)
    (wellFormed : ∀ i, Kinded (Γ i)) :
    HasType Δ Γ (Nucleus.HolLN.openFree body name) B := by
  apply bodyTyping.openBound (.free name hA lookup) wellFormed

end Nucleus.HolLN
