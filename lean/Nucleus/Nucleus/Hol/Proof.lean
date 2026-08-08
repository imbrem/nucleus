import Nucleus.Hol.Substitution
import Nucleus.Hol.Typing
import Nucleus.HolOmega.Proof

/-!
# Raw proof certificates for monomorphic HOL

This is the extrinsic, tree-syntax counterpart of `Hol.Kernel.EqTm` and
`Hol.Kernel.Derives`.  Every rule carries enough formation evidence to rule
out malformed certificates.  The final section proves that the inclusion of
HOL into HOL-omega preserves every certificate.
-/

universe u

namespace Nucleus.Hol

variable {Base : Type u}

@[simp] theorem Expr.toOmega_tyBool :
    (Expr.tyBool : Ty Base).toOmega = .tyBool := rfl
@[simp] theorem Expr.toOmega_tyArr (A B : Ty Base) :
    (Expr.tyArr A B).toOmega = .tyArr A.toOmega B.toOmega := rfl
@[simp] theorem Expr.toOmega_tySub (A : Ty Base) (p : Tm Base) :
    (Expr.tySub A p).toOmega = .tySub A.toOmega p.toOmega := rfl

@[simp] theorem Expr.toOmega_tmVar (n : Nat) :
    (Expr.tmVar n : Tm Base).toOmega = .tmVar n := rfl
@[simp] theorem Expr.toOmega_tmApp (f x : Tm Base) :
    (Expr.tmApp f x).toOmega = .tmApp f.toOmega x.toOmega := rfl
@[simp] theorem Expr.toOmega_tmLam (A : Ty Base) (t : Tm Base) :
    (Expr.tmLam A t).toOmega = .tmLam A.toOmega t.toOmega := rfl
@[simp] theorem Expr.toOmega_tmBool (b : Bool) :
    (Expr.tmBool b : Tm Base).toOmega = .tmBool b := rfl
@[simp] theorem Expr.toOmega_tmEq (A : Ty Base) (x y : Tm Base) :
    (Expr.tmEq A x y).toOmega = .tmEq A.toOmega x.toOmega y.toOmega := rfl
@[simp] theorem Expr.toOmega_tmEps (A : Ty Base) (p : Tm Base) :
    (Expr.tmEps A p).toOmega = .tmEps A.toOmega p.toOmega := rfl
@[simp] theorem Expr.toOmega_tmAbs (A : Ty Base) (p x : Tm Base) :
    (Expr.tmAbs A p x).toOmega = .tmAbs A.toOmega p.toOmega x.toOmega := rfl
@[simp] theorem Expr.toOmega_tmRep (A : Ty Base) (p x : Tm Base) :
    (Expr.tmRep A p x).toOmega = .tmRep A.toOmega p.toOmega x.toOmega := rfl

theorem Expr.toOmega_rename : (t : Tm Base) -> (rho : Nat -> Nat) ->
    (t.rename rho).toOmega = t.toOmega.rename rho
  | .tmVar n, rho => by
      simp only [Expr.rename, Expr.toOmega_tmVar, HolOmega.Expr.rename]
  | .tmApp f x, rho => by
      simp only [Expr.rename, Expr.toOmega_tmApp, HolOmega.Expr.rename,
        toOmega_rename f rho, toOmega_rename x rho]
  | .tmLam A t, rho => by
      simp only [Expr.rename, Expr.toOmega_tmLam, HolOmega.Expr.rename,
        toOmega_rename t (liftRen rho)]
      congr 2
  | .tmBool b, rho => by
      simp only [Expr.rename, Expr.toOmega_tmBool, HolOmega.Expr.rename]
  | .tmEq A x y, rho => by
      simp only [Expr.rename, Expr.toOmega_tmEq, HolOmega.Expr.rename,
        toOmega_rename x rho, toOmega_rename y rho]
  | .tmEps A p, rho => by
      simp only [Expr.rename, Expr.toOmega_tmEps, HolOmega.Expr.rename, toOmega_rename p rho]
  | .tmAbs A p x, rho => by
      simp only [Expr.rename, Expr.toOmega_tmAbs, HolOmega.Expr.rename, toOmega_rename x rho]
  | .tmRep A p x, rho => by
      simp only [Expr.rename, Expr.toOmega_tmRep, HolOmega.Expr.rename, toOmega_rename x rho]

theorem Expr.toOmega_liftSub (sigma : Nat -> Tm Base) (n : Nat) :
    (liftSub sigma n).toOmega =
      HolOmega.liftTmSub (fun i => (sigma i).toOmega) n := by
  cases n with
  | zero => rfl
  | succ n => exact Expr.toOmega_rename (sigma n) Nat.succ

theorem Expr.toOmega_subst : (t : Tm Base) -> (sigma : Nat -> Tm Base) ->
    (t.subst sigma).toOmega = t.toOmega.subst (fun n => (sigma n).toOmega)
  | .tmVar n, sigma => by
      simp only [Expr.subst, Expr.toOmega_tmVar, HolOmega.Expr.subst]
  | .tmApp f x, sigma => by
      simp only [Expr.subst, Expr.toOmega_tmApp, HolOmega.Expr.subst,
        toOmega_subst f sigma, toOmega_subst x sigma]
  | .tmLam A t, sigma => by
      simp only [Expr.subst, Expr.toOmega_tmLam, HolOmega.Expr.subst,
        toOmega_subst t (liftSub sigma)]
      congr 1
      apply congrArg (fun tau => t.toOmega.subst tau)
      funext n
      exact Expr.toOmega_liftSub sigma n
  | .tmBool b, sigma => by
      simp only [Expr.subst, Expr.toOmega_tmBool, HolOmega.Expr.subst]
  | .tmEq A x y, sigma => by
      simp only [Expr.subst, Expr.toOmega_tmEq, HolOmega.Expr.subst,
        toOmega_subst x sigma, toOmega_subst y sigma]
  | .tmEps A p, sigma => by
      simp only [Expr.subst, Expr.toOmega_tmEps, HolOmega.Expr.subst, toOmega_subst p sigma]
  | .tmAbs A p x, sigma => by
      simp only [Expr.subst, Expr.toOmega_tmAbs, HolOmega.Expr.subst, toOmega_subst x sigma]
  | .tmRep A p x, sigma => by
      simp only [Expr.subst, Expr.toOmega_tmRep, HolOmega.Expr.subst, toOmega_subst x sigma]

theorem Expr.toOmega_inst (t x : Tm Base) :
    (t.inst x).toOmega = t.toOmega.inst x.toOmega := by
  simp only [Expr.inst, HolOmega.Expr.inst, Expr.toOmega_subst]
  congr
  funext n
  cases n <;> rfl

theorem HasType.toOmega' {Γ : Ctx Base} {t : Tm Base} {A : Ty Base}
    (h : HasType Γ t A) :
    HolOmega.HasType [] Γ.toOmega t.toOmega A.toOmega := by
  exact Judgement.toOmega h

theorem Kinded.toOmega' (h : Kinded A) :
    HolOmega.Kinded [] A.toOmega ⟨.star, 0⟩ := by
  exact Judgement.toOmega h

/-- Typed equality certificates for every equality rule of regular HOL. -/
inductive EqTm :
    (Γ : Ctx Base) -> Tm Base -> Tm Base -> Ty Base -> Prop
  | refl (ht : HasType Γ t A) : EqTm Γ t t A
  | symm : EqTm Γ t u A -> EqTm Γ u t A
  | trans : EqTm Γ t u A -> EqTm Γ u v A -> EqTm Γ t v A
  | app : EqTm Γ f g (.tyArr A B) -> EqTm Γ x y A ->
      EqTm Γ (.tmApp f x) (.tmApp g y) B
  | lam (hA : Kinded A) : EqTm (A :: Γ) t u B ->
      EqTm Γ (.tmLam A t) (.tmLam A u) (.tyArr A B)
  | beta (hA : Kinded A) (ht : HasType (A :: Γ) t B)
      (hx : HasType Γ x A) (hi : HasType Γ (t.inst x) B) :
      EqTm Γ (.tmApp (.tmLam A t) x) (t.inst x) B
  | eta (hf : HasType Γ f (.tyArr A B))
      (he : HasType Γ (.tmLam A (.tmApp (f.rename Nat.succ) (.tmVar 0)))
        (.tyArr A B)) :
      EqTm Γ (.tmLam A (.tmApp (f.rename Nat.succ) (.tmVar 0))) f (.tyArr A B)

def TypedHyps (Γ : Ctx Base) (H : List (Tm Base)) : Prop :=
  ∀ p, p ∈ H -> HasType Γ p .tyBool

/-- Typed theorem certificates for every theorem rule of regular HOL.

The premise of `repAbs` is a proof of the raw subtype predicate instantiated
at the represented term, rather than an oracle asserting semantic truth.
-/
inductive Proves (Γ : Ctx Base) :
    List (Tm Base) -> Tm Base -> Prop
  | hyp (hH : TypedHyps Γ H) (hp : p ∈ H) : Proves Γ H p
  | truth (hH : TypedHyps Γ H) : Proves Γ H (.tmBool true)
  | eqRefl (hH : TypedHyps Γ H) (hx : HasType Γ x A) (hA : Kinded A) :
      Proves Γ H (.tmEq A x x)
  | eqMp (hH : TypedHyps Γ H) (hp : HasType Γ p (.tyArr A .tyBool))
      (hx : HasType Γ x A) (hy : HasType Γ y A) (hA : Kinded A) :
      Proves Γ H (.tmEq A x y) -> Proves Γ H (.tmApp p x) ->
      Proves Γ H (.tmApp p y)
  | choice (hH : TypedHyps Γ H) (hp : HasType Γ p (.tyArr A .tyBool))
      (hx : HasType Γ x A) (hA : Kinded A) :
      Proves Γ H (.tmApp p x) -> Proves Γ H (.tmApp p (.tmEps A p))
  | convert (hH : TypedHyps Γ H) :
      EqTm Γ p q .tyBool -> Proves Γ H p -> Proves Γ H q
  | eqOfEqTm (hH : TypedHyps Γ H) (hA : Kinded A) :
      EqTm Γ x y A -> Proves Γ H (.tmEq A x y)
  | antisymm (hH : TypedHyps Γ H) (hp : HasType Γ p .tyBool)
      (hq : HasType Γ q .tyBool)
      (hpH : TypedHyps Γ (p :: H)) (hqH : TypedHyps Γ (q :: H)) :
      Proves Γ (p :: H) q -> Proves Γ (q :: H) p ->
      Proves Γ H (.tmEq .tyBool p q)
  | absRep (hH : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType [A] p .tyBool) (hx : HasType Γ x (.tySub A p)) :
      Proves Γ H (.tmEq (.tySub A p) (.tmAbs A p (.tmRep A p x)) x)
  | repAbs (hH : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType [A] p .tyBool) (hx : HasType Γ x A)
      (hpx : HasType Γ (p.inst x) .tyBool) :
      Proves Γ H (p.inst x) ->
      Proves Γ H (.tmEq A (.tmRep A p (.tmAbs A p x)) x)

variable {Γ Γ' : Ctx Base} {H : List (Tm Base)}
variable {t u v f g x y p q : Tm Base} {A B : Ty Base}

def Hyps.toOmega (H : List (Tm Base)) : HolOmega.Hyps Base := H.map Expr.toOmega

theorem TypedHyps.toOmega (h : TypedHyps Γ H) :
    HolOmega.TypedHyps [] (Ctx.toOmega Γ) (Hyps.toOmega H) := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact (h q hq).toOmega'

/-- The inclusion into HOL-omega preserves all seven equality rules. -/
theorem EqTm.toOmega (h : EqTm Γ t u A) :
    HolOmega.EqTm [] Γ.toOmega t.toOmega u.toOmega A.toOmega := by
  induction h with
  | refl ht => exact .refl ht.toOmega'
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ihf ihx => exact .app ihf ihx
  | lam hA _ ih => exact .lam hA.toOmega' ih
  | beta hA ht hx hi =>
      have hi' := hi.toOmega'
      rw [Expr.toOmega_inst] at hi'
      simpa only [Ctx.toOmega, Expr.toOmega_tmApp, Expr.toOmega_tmLam,
        Expr.toOmega_inst] using
        HolOmega.EqTm.beta hA.toOmega' ht.toOmega' hx.toOmega' hi'
  | eta hf he =>
      have he' := he.toOmega'
      simpa only [Expr.toOmega_tmLam, Expr.toOmega_tmApp, Expr.toOmega_tmVar,
        Expr.toOmega_tyArr, Expr.toOmega_rename] using HolOmega.EqTm.eta hf.toOmega'
          (by simpa only [Expr.toOmega_tmLam, Expr.toOmega_tmApp,
            Expr.toOmega_tmVar, Expr.toOmega_tyArr, Expr.toOmega_rename] using he')

/-- The inclusion into HOL-omega preserves all ten theorem rules. -/
theorem Proves.toOmega (h : Proves Γ H p) :
    HolOmega.Proves [] (Ctx.toOmega Γ) (Hyps.toOmega H) p.toOmega := by
  induction h with
  | hyp hH hp => exact .hyp hH.toOmega (List.mem_map.mpr ⟨_, hp, rfl⟩)
  | truth hH => exact .truth hH.toOmega
  | eqRefl hH hx hA => exact .eqRefl hH.toOmega hx.toOmega' hA.toOmega'
  | eqMp hH hp hx hy hA _ _ ih1 ih2 =>
      exact .eqMp hH.toOmega hp.toOmega' hx.toOmega' hy.toOmega' hA.toOmega' ih1 ih2
  | choice hH hp hx hA _ ih =>
      exact .choice hH.toOmega hp.toOmega' hx.toOmega' hA.toOmega' ih
  | convert hH he _ ih => exact .convert hH.toOmega he.toOmega ih
  | eqOfEqTm hH hA he => exact .eqOfEqTm hH.toOmega hA.toOmega' he.toOmega
  | antisymm hH hp hq hpH hqH _ _ ih1 ih2 =>
      exact .antisymm hH.toOmega hp.toOmega' hq.toOmega' hpH.toOmega hqH.toOmega ih1 ih2
  | absRep hH hA hp hx => exact .absRep hH.toOmega hA.toOmega' hp.toOmega' hx.toOmega'
  | repAbs hH hA hp hx hpx _ ih =>
      have hpx' := hpx.toOmega'
      rw [Expr.toOmega_inst] at hpx'
      simpa only [Expr.toOmega_tmEq, Expr.toOmega_tmRep, Expr.toOmega_tmAbs] using
        HolOmega.Proves.repAbs hH.toOmega hA.toOmega' hp.toOmega' hx.toOmega' hpx'
          (by simpa only [Expr.toOmega_inst] using ih)

end Nucleus.Hol
