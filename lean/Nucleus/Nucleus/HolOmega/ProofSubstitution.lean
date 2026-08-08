import Nucleus.HolOmega.Proof

/-! # Substitution of raw HOL-omega proof certificates -/

universe u

namespace Nucleus.HolOmega

theorem EqTm.subst {Base : Type u} (h : EqTm Δ Γ t u A)
    (hσ : TmSub Δ Γ Γ' σ) : EqTm Δ Γ' (t.subst σ) (u.subst σ) A := by
  induction h with
  | refl ht => exact .refl (ht.subst hσ)
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hσ) (ih₂ hσ)
  | app _ _ ihf ihx => simpa [Expr.subst] using EqTm.app (ihf hσ) (ihx hσ)
  | lam hA _ ih => simpa [Expr.subst] using EqTm.lam hA (ih hσ.lift)
  | tyApp hX _ ih => simpa [Expr.subst] using EqTm.tyApp hX (ih hσ)
  | tyLam _ ih => simpa [Expr.subst] using EqTm.tyLam (ih hσ.mapLiftTy)
  | beta hA hfun hx hinst =>
      simpa [Expr.subst] using EqTm.beta hA (hfun.subst hσ.lift)
        (hx.subst hσ) (hinst.subst hσ)
  | eta hf heta =>
      simpa [Expr.subst] using EqTm.eta (hf.subst hσ) (heta.subst hσ)
  | tyBeta hbody hX hinst =>
      simpa [Expr.subst] using EqTm.tyBeta hbody hX (hinst.subst hσ)
  | tyEta hf heta =>
      simpa [Expr.subst] using EqTm.tyEta (hf.subst hσ) (heta.subst hσ)

theorem Proves.subst {Base : Type u} (h : Proves Δ Γ H p)
    (hσ : TmSub Δ Γ Γ' σ) : Proves Δ Γ' (H.subst σ) (p.subst σ) := by
  induction h with
  | hyp hH hp => exact .hyp (hH.subst hσ) (Hyps.mem_subst hp)
  | truth hH => exact .truth (hH.subst hσ)
  | eqRefl hH hx hA =>
      simpa [Expr.subst] using Proves.eqRefl (hH.subst hσ) (hx.subst hσ) hA
  | eqMp hH hp hx hy hA _ _ iheq ihp =>
      simpa [Expr.subst] using Proves.eqMp (hH.subst hσ) (hp.subst hσ)
        (hx.subst hσ) (hy.subst hσ) hA (iheq hσ) (ihp hσ)
  | choice hH hp hx hA _ ih =>
      simpa [Expr.subst] using Proves.choice (hH.subst hσ) (hp.subst hσ)
        (hx.subst hσ) hA (ih hσ)
  | convert hH heq _ ih =>
      exact .convert (hH.subst hσ) (heq.subst hσ) (ih hσ)
  | eqOfEqTm hH hA heq =>
      simpa [Expr.subst] using Proves.eqOfEqTm (hH.subst hσ) hA (heq.subst hσ)
  | antisymm hH hp hq hpH hqH _ _ ihp ihq =>
      simpa [Hyps.subst, Expr.subst] using Proves.antisymm (hH.subst hσ)
        (hp.subst hσ) (hq.subst hσ) (hpH.subst hσ) (hqH.subst hσ)
        (ihp hσ) (ihq hσ)
  | absRep hH hA hp hx =>
      simpa [Expr.subst] using Proves.absRep (hH.subst hσ) hA hp (hx.subst hσ)
  | repAbs hH hA hp hx hpx _ ih =>
      simpa [Expr.subst] using Proves.repAbs (hH.subst hσ) hA hp
        (hx.subst hσ) (hpx.subst hσ) (ih hσ)

end Nucleus.HolOmega
