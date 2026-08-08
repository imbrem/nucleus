import Nucleus.HolOmega.Substitution

/-!
# Formation and typing

Type formation and term typing as a **single** inductive relation indexed by
`JudgementIndex`, for the same reason the syntax is a single family: one
ordinary induction principle, so `induction` works and proofs are not forced
through a hand-written recursor with one motive per judgement.

The rules are syntax-directed. Each constructor checks only its immediate
children and the indicated context lookup, so there is no global
well-formedness pass hidden anywhere, and a derivation can be checked — later,
addressed — a node at a time.

`Kinded` and `HasType` survive as abbreviations, so the two judgements still
read as separate notions where that is clearer.

## The formation judgement carries a rank

`Kinded` concludes an `RKind`, not a `Kind`: a rank bound comes with the kind.
`tyAll` is the reason. Quantifying over *all* types of a kind has no set model,
so the quantifier ranges over the types below a rank, and the rank of the
result has to be tracked to know which quantifiers may later range over it.
The bounds mirror `Kernel.Universe` exactly:

* `tyArr` keeps the rank (`rank_arr`),
* `tySub` keeps the rank (`rank_subCode`),
* `tyBool` and `base` are rank `0`, so any bound holds,
* `tyAll` over rank `RK.rank` with body bounded by `s` lands at
  `max RK.rank s + 2` (`rank_allCode`).

`subsume` raises a rank, and only at kind `⋆`. That is not squeamishness: at
kind `⋆` a value is a code, and a code of rank `r` is literally a code of rank
`s ≥ r` with `El` unchanged. At kind `K ⇒ L` a value is a *function from*
rank-`r` values, so raising the rank enlarges the domain and there is nothing
to lift. `tyApp` therefore demands one rank for both operands, and `tyLam`
gives the binder and the body the same rank, matching `Kernel.Ty.lam`.

`HasType` records no rank. A term's type is a code; how far up the tower it
sits is the formation judgement's business, and soundness quantifies over the
denotations of the type rather than fixing one.
-/

universe u

namespace Nucleus.HolOmega

/-- Model-independent certificates for definitional conversion of raw types.
New conversion principles belong here only when accompanied by a
universe-polymorphic semantic soundness theorem. -/
inductive TyConv {Base : Type u} (Δ : KindCtx) : Ty Base → Ty Base → Prop
  | alpha (h : A = B) : TyConv Δ A B
  | trans : TyConv Δ A B → TyConv Δ B C → TyConv Δ A C
  | tyBeta (RK : RKind) (A X : Ty Base) :
      TyConv Δ (.tyApp (.tyLam RK A) X) (A.instTy X)

/-- A common index for the formation and typing judgements. -/
inductive JudgementIndex (Base : Type u) : Type u
  | kinded (Δ : KindCtx) (A : Ty Base) (RK : RKind)
  | hasType (Δ : KindCtx) (Γ : TmCtx Base) (t : Tm Base) (A : Ty Base)

/-- `Δ ⊢ A : K@r` and `Δ; Γ ⊢ t : A`, as one relation. -/
inductive Judgement {Base : Type u} : JudgementIndex Base → Prop
  | base {Δ : KindCtx} {c : Base} {r : Nat} :
      Judgement (.kinded Δ (.base c) ⟨.star, r⟩)
  | tyVar {Δ : KindCtx} {n : Nat} {RK : RKind} :
      Δ[n]? = some RK → Judgement (.kinded Δ (.tyVar n) RK)
  | tyLam {Δ : KindCtx} {RK : RKind} {A : Ty Base} {L : Kind} :
      Judgement (.kinded (RK :: Δ) A ⟨L, RK.rank⟩) →
      Judgement (.kinded Δ (.tyLam RK A) ⟨.arr RK.kind L, RK.rank⟩)
  | tyApp {Δ : KindCtx} {F X : Ty Base} {K L : Kind} {r : Nat} :
      Judgement (.kinded Δ F ⟨.arr K L, r⟩) →
      Judgement (.kinded Δ X ⟨K, r⟩) →
      Judgement (.kinded Δ (.tyApp F X) ⟨L, r⟩)
  | tyAll {Δ : KindCtx} {RK : RKind} {A : Ty Base} {s : Nat} :
      Judgement (.kinded (RK :: Δ) A ⟨.star, s⟩) →
      Judgement (.kinded Δ (.tyAll RK A) ⟨.star, max RK.rank s + 2⟩)
  | tyEx {Δ : KindCtx} {RK : RKind} {A : Ty Base} {s : Nat} :
      Judgement (.kinded (RK :: Δ) A ⟨.star, s⟩) →
      Judgement (.kinded Δ (.tyEx RK A) ⟨.star, max RK.rank s + 2⟩)
  | tyBool {Δ : KindCtx} {r : Nat} : Judgement (.kinded Δ .tyBool ⟨.star, r⟩)
  | tyArr {Δ : KindCtx} {A B : Ty Base} {r : Nat} :
      Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.kinded Δ B ⟨.star, r⟩) →
      Judgement (.kinded Δ (.tyArr A B) ⟨.star, r⟩)
  | tySub {Δ : KindCtx} {A : Ty Base} {p : Tm Base} {r : Nat} :
      Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.hasType Δ [A] p .tyBool) →
      Judgement (.kinded Δ (.tySub A p) ⟨.star, r⟩)
  | subsume {Δ : KindCtx} {A : Ty Base} {r s : Nat} :
      Judgement (.kinded Δ A ⟨.star, r⟩) → r ≤ s →
      Judgement (.kinded Δ A ⟨.star, s⟩)
  | conv {Δ : KindCtx} {Γ : TmCtx Base} {t : Tm Base} {A B : Ty Base} :
      Judgement (.hasType Δ Γ t A) → TyConv Δ A B →
      Judgement (.hasType Δ Γ t B)
  | tmVar {Δ : KindCtx} {Γ : TmCtx Base} {n : Nat} {A : Ty Base} :
      Γ[n]? = some A → Judgement (.hasType Δ Γ (.tmVar n) A)
  | tmApp {Δ : KindCtx} {Γ : TmCtx Base} {f x : Tm Base} {A B : Ty Base} :
      Judgement (.hasType Δ Γ f (.tyArr A B)) →
      Judgement (.hasType Δ Γ x A) →
      Judgement (.hasType Δ Γ (.tmApp f x) B)
  | tmLam {Δ : KindCtx} {Γ : TmCtx Base} {t : Tm Base} {A B : Ty Base}
      {r : Nat} :
      Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.hasType Δ (A :: Γ) t B) →
      Judgement (.hasType Δ Γ (.tmLam A t) (.tyArr A B))
  | tmTyApp {Δ : KindCtx} {Γ : TmCtx Base} {f : Tm Base} {RK : RKind}
      {B X : Ty Base} :
      Judgement (.hasType Δ Γ f (.tyAll RK B)) →
      Judgement (.kinded Δ X RK) →
      Judgement (.hasType Δ Γ (.tmTyApp f X) (B.instTy X))
  | tmTyLam {Δ : KindCtx} {Γ : TmCtx Base} {RK : RKind} {t : Tm Base}
      {A : Ty Base} :
      Judgement (.hasType (RK :: Δ) Γ.liftTy t A) →
      Judgement (.hasType Δ Γ (.tmTyLam RK t) (.tyAll RK A))
  | tmPack {Δ : KindCtx} {Γ : TmCtx Base} {RK : RKind} {A X : Ty Base}
      {t : Tm Base} {s : Nat} :
      Judgement (.kinded (RK :: Δ) A ⟨.star, s⟩) →
      Judgement (.kinded Δ X RK) →
      Judgement (.hasType Δ Γ t (A.instTy X)) →
      Judgement (.hasType Δ Γ (.tmPack RK A X t) (.tyEx RK A))
  | tmUnpack {Δ : KindCtx} {Γ : TmCtx Base} {RK : RKind} {A B : Ty Base}
      {k p : Tm Base} {s q : Nat} :
      Judgement (.kinded (RK :: Δ) A ⟨.star, s⟩) →
      Judgement (.kinded Δ B ⟨.star, q⟩) →
      Judgement (.hasType (RK :: Δ) (A :: Γ.liftTy) k B.liftTy) →
      Judgement (.hasType Δ Γ p (.tyEx RK A)) →
      Judgement (.hasType Δ Γ (.tmUnpack RK A B k p) B)
  | tmBool {Δ : KindCtx} {Γ : TmCtx Base} {b : Bool} :
      Judgement (.hasType Δ Γ (.tmBool b) .tyBool)
  | tmEq {Δ : KindCtx} {Γ : TmCtx Base} {x y : Tm Base} {A : Ty Base}
      {r : Nat} :
      Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.hasType Δ Γ x A) →
      Judgement (.hasType Δ Γ y A) →
      Judgement (.hasType Δ Γ (.tmEq A x y) .tyBool)
  | tmEps {Δ : KindCtx} {Γ : TmCtx Base} {p : Tm Base} {A : Ty Base}
      {r : Nat} :
      Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.hasType Δ Γ p (.tyArr A .tyBool)) →
      Judgement (.hasType Δ Γ (.tmEps A p) A)
  | tmAbs {Δ : KindCtx} {Γ : TmCtx Base} {p x : Tm Base} {A : Ty Base}
      {r : Nat} :
      Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.hasType Δ [A] p .tyBool) →
      Judgement (.hasType Δ Γ x A) →
      Judgement (.hasType Δ Γ (.tmAbs A p x) (.tySub A p))
  | tmRep {Δ : KindCtx} {Γ : TmCtx Base} {p x : Tm Base} {A : Ty Base}
      {r : Nat} :
      Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.hasType Δ [A] p .tyBool) →
      Judgement (.hasType Δ Γ x (.tySub A p)) →
      Judgement (.hasType Δ Γ (.tmRep A p x) A)

/-- `Δ ⊢ A : RK.kind` at rank `RK.rank`. -/
abbrev Kinded {Base : Type u} (Δ : KindCtx) (A : Ty Base) (RK : RKind) : Prop :=
  Judgement (.kinded Δ A RK)

/-- `Δ; Γ ⊢ t : A`. -/
abbrev HasType {Base : Type u} (Δ : KindCtx) (Γ : TmCtx Base) (t : Tm Base)
    (A : Ty Base) : Prop :=
  Judgement (.hasType Δ Γ t A)

end Nucleus.HolOmega
