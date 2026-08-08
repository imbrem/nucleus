import Nucleus.Hol.Universe

/-! A self-contained semantic kernel for ordinary HOL. -/

universe u

namespace Nucleus.Hol.Kernel

open Nucleus.HolOmega

variable (U : Hol.Universe)

abbrev Ty := U.Code
def Ty.bool : Ty U := U.boolCode
def Ty.arr (A B : Ty U) : Ty U := U.arr A B
def Ty.sub (A : Ty U) (P : U.El A → Prop) : Ty U := U.subCode A P

abbrev Ctx := List (Ty U)
def Ctx.El : Ctx U → Type u
  | [] => PUnit
  | A :: Γ => U.El A × Ctx.El Γ

abbrev Tm (Γ : Ctx U) (A : Ty U) := Ctx.El U Γ → U.El A

namespace Tm

def vz : Tm U (A :: Γ) A := fun γ => γ.1
def vs (x : Tm U Γ A) : Tm U (B :: Γ) A := fun γ => x γ.2
def app (f : Tm U Γ (Ty.arr U A B)) (x : Tm U Γ A) : Tm U Γ B :=
  fun γ => U.arrEquiv A B (f γ) (x γ)
def lam (t : Tm U (A :: Γ) B) : Tm U Γ (Ty.arr U A B) :=
  fun γ => (U.arrEquiv A B).symm (fun x => t (x, γ))
def bool (b : Bool) : Tm U Γ (Ty.bool U) := fun _ => U.boolEquiv.symm b

noncomputable def equal (x y : Tm U Γ A) : Tm U Γ (Ty.bool U) := by
  classical
  exact fun γ => U.boolEquiv.symm (decide (x γ = y γ))

noncomputable def epsilon (p : Tm U Γ (Ty.arr U A (Ty.bool U))) : Tm U Γ A :=
  fun γ => by
    classical
    letI := U.inhabited A
    let q := fun x => U.boolEquiv (U.arrEquiv A U.boolCode (p γ) x)
    exact if h : ∃ x, q x = true then Classical.choose h else default

noncomputable def abs (P : U.El A → Prop) (x : Tm U Γ A) : Tm U Γ (Ty.sub U A P) :=
  fun γ => by
    letI := U.inhabited A
    exact (U.subEquiv A P).symm (TotalSubtype.abs P (x γ))

def rep (P : U.El A → Prop) (x : Tm U Γ (Ty.sub U A P)) : Tm U Γ A :=
  fun γ => TotalSubtype.rep (U.subEquiv A P (x γ))

@[simp] theorem beta (t : Tm U (A :: Γ) B) (x : Tm U Γ A) :
    app U (lam U t) x = fun γ => t (x γ, γ) := by
  funext γ
  change U.arrEquiv A B ((U.arrEquiv A B).symm (fun y => t (y, γ))) (x γ) = _
  rw [Equiv.apply_symm_apply]

theorem eta (f : Tm U Γ (Ty.arr U A B)) :
    lam U (app U (vs U f) (vz U)) = f := by
  funext γ
  change (U.arrEquiv A B).symm (fun x => U.arrEquiv A B (f γ) x) = f γ
  rw [show (fun x => U.arrEquiv A B (f γ) x) = U.arrEquiv A B (f γ) from rfl]
  exact (U.arrEquiv A B).symm_apply_apply _

theorem abs_rep (P : U.El A → Prop) (x : Tm U Γ (Ty.sub U A P)) :
    abs U P (rep U P x) = x := by
  funext γ
  letI := U.inhabited A
  change (U.subEquiv A P).symm
    (TotalSubtype.abs P (TotalSubtype.rep (U.subEquiv A P (x γ)))) = x γ
  apply (U.subEquiv A P).injective
  rw [Equiv.apply_symm_apply]
  exact TotalSubtype.abs_rep _

theorem rep_abs (P : U.El A → Prop) (x : Tm U Γ A) (hx : ∀ γ, P (x γ)) :
    rep U P (abs U P x) = x := by
  funext γ
  letI := U.inhabited A
  simp only [rep, abs, Equiv.apply_symm_apply]
  exact TotalSubtype.rep_abs_of (hx γ)

end Tm

/-- Equality rules of ordinary HOL. -/
inductive EqTm : {Γ : Ctx U} → {A : Ty U} → Tm U Γ A → Tm U Γ A → Prop
  | refl (t : Tm U Γ A) : EqTm t t
  | symm : EqTm t u → EqTm u t
  | trans : EqTm t u → EqTm u v → EqTm t v
  | app : EqTm f g → EqTm x y → EqTm (Tm.app U f x) (Tm.app U g y)
  | lam : EqTm t u → EqTm (Tm.lam U t) (Tm.lam U u)
  | beta (t : Tm U (A :: Γ) B) (x : Tm U Γ A) :
      EqTm (Tm.app U (Tm.lam U t) x) (fun γ => t (x γ, γ))
  | eta (f : Tm U Γ (Ty.arr U A B)) : EqTm (Tm.lam U (Tm.app U (Tm.vs U f) (Tm.vz U))) f

theorem EqTm.sound (h : EqTm U t u) : t = u := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | lam _ ih => simp [ih]
  | beta => exact Tm.beta U _ _
  | eta => exact Tm.eta U _

def Entails (H : List (Tm U Γ (Ty.bool U))) (p : Tm U Γ (Ty.bool U)) : Prop :=
  ∀ γ, (∀ q ∈ H, U.boolEquiv (q γ) = true) → U.boolEquiv (p γ) = true

theorem Tm.equal_true_iff (x y : Tm U Γ A) (γ) :
    U.boolEquiv (Tm.equal U x y γ) = true ↔ x γ = y γ := by
  classical
  simp [Tm.equal]

theorem Tm.epsilon_spec (p : Tm U Γ (Ty.arr U A (Ty.bool U))) (x : Tm U Γ A) (γ)
    (hx : U.boolEquiv (U.arrEquiv A U.boolCode (p γ) (x γ)) = true) :
    U.boolEquiv (U.arrEquiv A U.boolCode (p γ) (Tm.epsilon U p γ)) = true := by
  classical
  letI := U.inhabited A
  simp only [Tm.epsilon]
  split
  · exact Classical.choose_spec ‹_›
  · rename_i h
    exact False.elim (h (Exists.intro (x γ) hx))

/-- Every primitive theorem rule in the monomorphic kernel. -/
inductive Derives {Γ : Ctx U} : List (Tm U Γ (Ty.bool U)) → Tm U Γ (Ty.bool U) → Prop
  | hyp : p ∈ H → Derives H p
  | truth : Derives H (Tm.bool U true)
  | eqRefl (x : Tm U Γ A) : Derives H (Tm.equal U x x)
  | eqMp (p : Tm U Γ (Ty.arr U A (Ty.bool U))) (x y : Tm U Γ A) :
      Derives H (Tm.equal U x y) → Derives H (Tm.app U p x) → Derives H (Tm.app U p y)
  | choice (p : Tm U Γ (Ty.arr U A (Ty.bool U))) (x : Tm U Γ A) :
      Derives H (Tm.app U p x) → Derives H (Tm.app U p (Tm.epsilon U p))
  | convert : EqTm U p q → Derives H p → Derives H q
  | eqOfEqTm (x y : Tm U Γ A) : EqTm U x y → Derives H (Tm.equal U x y)
  | antisymm (p q : Tm U Γ (Ty.bool U)) :
      Derives (p :: H) q → Derives (q :: H) p → Derives H (Tm.equal U p q)
  | absRep (P : U.El A → Prop) (x : Tm U Γ (Ty.sub U A P)) :
      Derives H (Tm.equal U (Tm.abs U P (Tm.rep U P x)) x)
  | repAbs (P : U.El A → Prop) (x : Tm U Γ A) : (∀ γ, P (x γ)) →
      Derives H (Tm.equal U (Tm.rep U P (Tm.abs U P x)) x)

theorem Derives.sound (h : Derives U H p) : Entails U H p := by
  intro γ hH
  induction h with
  | hyp hp => exact hH _ hp
  | truth => simp [Tm.bool]
  | eqRefl x => exact (Tm.equal_true_iff U x x γ).2 rfl
  | eqMp p x y _ _ ihxy ihpx =>
      have heq := (Tm.equal_true_iff U x y γ).1 (ihxy hH)
      simpa [Tm.app, heq] using ihpx hH
  | choice p x _ ih => exact Tm.epsilon_spec U p x γ (ih hH)
  | convert heq _ ih => rw [← congrFun (heq.sound U) γ]; exact ih hH
  | eqOfEqTm x y heq => exact (Tm.equal_true_iff U x y γ).2 (congrFun (heq.sound U) γ)
  | antisymm p q _ _ ihp ihq =>
      apply (Tm.equal_true_iff U p q γ).2
      apply U.boolEquiv.injective
      cases hpv : U.boolEquiv (p γ) <;> cases hqv : U.boolEquiv (q γ) <;> try rfl
      · have bad := ihq (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact hqv
          · exact hH _ hr)
        rw [hpv] at bad
        contradiction
      · have bad := ihp (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact hpv
          · exact hH _ hr)
        rw [hqv] at bad
        contradiction
  | absRep P x => exact (Tm.equal_true_iff U _ _ γ).2 (congrFun (Tm.abs_rep U P x) γ)
  | repAbs P x hx => exact (Tm.equal_true_iff U _ _ γ).2 (congrFun (Tm.rep_abs U P x hx) γ)

end Nucleus.Hol.Kernel
