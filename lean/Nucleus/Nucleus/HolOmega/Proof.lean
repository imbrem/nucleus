import Nucleus.HolOmega.Typing

/-!
# Raw HOL-omega proof certificates

This file gives the raw-tree counterparts of every equality and theorem rule
implemented by `Kernel.EqTm` and `Kernel.Derives`.  The relations deliberately
carry `Kinded` / `HasType` evidence: a certificate is not a licence to form an
equation or theorem from ill-typed trees.

There is one necessary difference from the shallow semantic kernel.  Its
`Derives.repAbs` constructor accepts the semantic premise

```
forall rho gamma, P rho (x rho gamma)
```

for a meta-level predicate `P`.  Such a premise has no satisfactory raw
syntactic counterpart, and importing it into the raw calculus would amount to
postulating semantic truth.  Here a subtype predicate is the raw term `p`, so
`repAbs` instead requires an explicit raw proof of `p.inst x`.  Soundness will
later turn that certificate into precisely the semantic premise needed by the
kernel rule.
-/

universe u

namespace Nucleus.HolOmega

/-- Typed equality certificates for raw terms.

The final type index is explicit.  Besides ruling out malformed equations,
this retains the typing derivations needed by the eventual semantic soundness
proof without relying on uniqueness of raw typing.

The `hinst` / `heta` arguments on the four beta/eta rules are checker-side
*regularity certificates*, not additional logical premises.  They are
currently explicit because raw term substitution, type substitution, term
weakening, and type weakening have not yet been proved to preserve `HasType`.
Once those four regularity theorems exist, these arguments must be derived
inside smart constructors (and then removed from the public rule interface),
so that the final specification has exactly the kernel rules. -/
inductive EqTm {Base : Type u} :
    (Δ : KindCtx) → (Γ : TmCtx Base) → Tm Base → Tm Base → Ty Base → Prop
  | refl (ht : HasType Δ Γ t A) : EqTm Δ Γ t t A
  | symm : EqTm Δ Γ t u A → EqTm Δ Γ u t A
  | trans : EqTm Δ Γ t u A → EqTm Δ Γ u v A → EqTm Δ Γ t v A
  | app :
      EqTm Δ Γ f g (.tyArr A B) →
      EqTm Δ Γ x y A →
      EqTm Δ Γ (.tmApp f x) (.tmApp g y) B
  | lam (hA : Kinded Δ A ⟨.star, r⟩) :
      EqTm Δ (A :: Γ) t u B →
      EqTm Δ Γ (.tmLam A t) (.tmLam A u) (.tyArr A B)
  | tyApp {RK : RKind} (hX : Kinded Δ X RK) :
      EqTm Δ Γ f g (.tyAll RK A) →
      EqTm Δ Γ (.tmTyApp f X) (.tmTyApp g X) (A.instTy X)
  | tyLam {RK : RKind} :
      EqTm (RK :: Δ) Γ.liftTy t u A →
      EqTm Δ Γ (.tmTyLam RK t) (.tmTyLam RK u) (.tyAll RK A)
  | beta
      (hA : Kinded Δ A ⟨.star, r⟩)
      (hfun : HasType Δ (A :: Γ) t B)
      (hx : HasType Δ Γ x A)
      (hinst : HasType Δ Γ (t.inst x) B) :
      EqTm Δ Γ (.tmApp (.tmLam A t) x) (t.inst x) B
  | eta
      (hf : HasType Δ Γ f (.tyArr A B))
      (heta : HasType Δ Γ (.tmLam A (.tmApp (f.rename Nat.succ) (.tmVar 0)))
        (.tyArr A B)) :
      EqTm Δ Γ (.tmLam A (.tmApp (f.rename Nat.succ) (.tmVar 0))) f (.tyArr A B)
  | tyBeta {RK : RKind}
      (hbody : HasType (RK :: Δ) Γ.liftTy t A)
      (hX : Kinded Δ X RK)
      (hinst : HasType Δ Γ (t.instTy X) (A.instTy X)) :
      EqTm Δ Γ (.tmTyApp (.tmTyLam RK t) X) (t.instTy X) (A.instTy X)
  | tyEta {RK : RKind}
      (hf : HasType Δ Γ f (.tyAll RK A))
      (heta : HasType Δ Γ
        (.tmTyLam RK (.tmTyApp f.liftTy (.tyVar 0))) (.tyAll RK A)) :
      EqTm Δ Γ (.tmTyLam RK (.tmTyApp f.liftTy (.tyVar 0))) f (.tyAll RK A)

/-- A raw hypothesis list is well typed when every member is Boolean in the
same kind and term contexts. -/
def TypedHyps {Base : Type u} (Δ : KindCtx) (Γ : TmCtx Base)
    (H : Hyps Base) : Prop :=
  ∀ p ∈ H, HasType Δ Γ p .tyBool

/-- Typed theorem certificates for every rule of `Kernel.Derives`.

Every constructor carries `TypedHyps`, so even unused entries cannot make a
purported sequent malformed. -/
inductive Proves {Base : Type u} (Δ : KindCtx) (Γ : TmCtx Base) :
    Hyps Base → Tm Base → Prop
  | hyp (hH : TypedHyps Δ Γ H) (hp : p ∈ H) : Proves Δ Γ H p
  | truth (hH : TypedHyps Δ Γ H) : Proves Δ Γ H (.tmBool true)
  | eqRefl (hH : TypedHyps Δ Γ H) (hx : HasType Δ Γ x A)
      (hA : Kinded Δ A ⟨.star, r⟩) :
      Proves Δ Γ H (.tmEq A x x)
  | eqMp (hH : TypedHyps Δ Γ H)
      (hp : HasType Δ Γ p (.tyArr A .tyBool))
      (hx : HasType Δ Γ x A) (hy : HasType Δ Γ y A)
      (hA : Kinded Δ A ⟨.star, r⟩) :
      Proves Δ Γ H (.tmEq A x y) →
      Proves Δ Γ H (.tmApp p x) →
      Proves Δ Γ H (.tmApp p y)
  | choice (hH : TypedHyps Δ Γ H)
      (hp : HasType Δ Γ p (.tyArr A .tyBool))
      (hx : HasType Δ Γ x A) (hA : Kinded Δ A ⟨.star, r⟩) :
      Proves Δ Γ H (.tmApp p x) →
      Proves Δ Γ H (.tmApp p (.tmEps A p))
  | convert (hH : TypedHyps Δ Γ H) :
      EqTm Δ Γ p q .tyBool → Proves Δ Γ H p → Proves Δ Γ H q
  | eqOfEqTm (hH : TypedHyps Δ Γ H) (hA : Kinded Δ A ⟨.star, r⟩) :
      EqTm Δ Γ x y A → Proves Δ Γ H (.tmEq A x y)
  | antisymm
      (hH : TypedHyps Δ Γ H)
      (hp : HasType Δ Γ p .tyBool) (hq : HasType Δ Γ q .tyBool)
      (hpH : TypedHyps Δ Γ (p :: H)) (hqH : TypedHyps Δ Γ (q :: H)) :
      Proves Δ Γ (p :: H) q →
      Proves Δ Γ (q :: H) p →
      Proves Δ Γ H (.tmEq .tyBool p q)
  | absRep
      (hH : TypedHyps Δ Γ H) (hA : Kinded Δ A ⟨.star, r⟩)
      (hp : HasType Δ [A] p .tyBool)
      (hx : HasType Δ Γ x (.tySub A p)) :
      Proves Δ Γ H
        (.tmEq (.tySub A p) (.tmAbs A p (.tmRep A p x)) x)
  | repAbs
      (hH : TypedHyps Δ Γ H) (hA : Kinded Δ A ⟨.star, r⟩)
      (hp : HasType Δ [A] p .tyBool) (hx : HasType Δ Γ x A)
      (hpx : HasType Δ Γ (p.inst x) .tyBool) :
      Proves Δ Γ H (p.inst x) →
      Proves Δ Γ H
        (.tmEq A (.tmRep A p (.tmAbs A p x)) x)

end Nucleus.HolOmega
