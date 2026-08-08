import Nucleus.Cov.Syntax

/-!
# Premise-driven Covalence proof rules for regular HOL

There is one constructor below for every raw HOL equality and theorem rule.
Soundness is universal in the shared filling: a Covalence derivation lowers
to a raw HOL derivation for *every* filling, not merely one successful repair.
-/

universe u

namespace Nucleus.Cov

open Hol

/-- A `Term` viewed at a particular type. -/
structure At (Base : Type u) (Γ : Ctx Base) (A : Ty Base) where
  term : Term Base Γ
  type_eq : term.ty = A

namespace At

variable {Base : Type u} {Γ : Ctx Base} {A B : Ty Base}

def lower (t : At Base Γ A) (e : Filling Base) : Tm Base := t.term.lower e

theorem typing (t : At Base Γ A) (e : Filling Base) : HasType Γ (t.lower e) A :=
  by
    have h := t.term.typing e
    rw [t.type_eq] at h
    exact h

def hole (name : HoleName) (A : Ty Base) (hA : Kinded A) : At Base Γ A :=
  ⟨Term.hole name A hA, rfl⟩

def closed (A : Ty Base) (hA : Kinded A) (t : Tm Base) (ht : HasType Γ t A) :
    At Base Γ A := ⟨Term.closed A hA t ht, rfl⟩

def bool (b : Bool) : At Base Γ .tyBool := ⟨Term.bool b, rfl⟩

def app (f : At Base Γ (.tyArr A B)) (x : At Base Γ A) : At Base Γ B :=
  ⟨Term.app f.term x.term A B f.type_eq x.type_eq, rfl⟩

def lam (hA : Kinded A) (body : At Base (A :: Γ) B) :
    At Base Γ (.tyArr A B) := ⟨Term.lam A hA body.term, congrArg (Expr.tyArr A) body.type_eq⟩

def equal (hA : Kinded A) (x y : At Base Γ A) : At Base Γ .tyBool :=
  ⟨Term.equal A hA x.term y.term x.type_eq y.type_eq, rfl⟩

def choice (hA : Kinded A) (p : At Base Γ (.tyArr A .tyBool)) : At Base Γ A :=
  ⟨Term.choice A hA p.term p.type_eq, rfl⟩

def inst (body : At Base (A :: Γ) B) (x : At Base Γ A)
    (hinst : ∀ e, HasType Γ ((body.lower e).inst (x.lower e)) B) : At Base Γ B where
  term :=
    { ty := B
      formed := by
        have h := body.term.formed
        rw [body.type_eq] at h
        exact h
      row := Row.mk .application (some body.term.row) (some x.term.row) none ⟨Γ.length⟩
      lower := fun e => (body.lower e).inst (x.lower e)
      typing := hinst }
  type_eq := rfl

def etaExpand (hA : Kinded A) (f : At Base Γ (.tyArr A B))
    (heta : ∀ e, HasType Γ
      (.tmLam A (.tmApp ((f.lower e).rename Nat.succ) (.tmVar 0))) (.tyArr A B)) :
    At Base Γ (.tyArr A B) where
  term :=
    { ty := .tyArr A B
      formed := .tyArr hA (by
        have hf := f.term.formed
        rw [f.type_eq] at hf
        cases hf with | tyArr _ hB => exact hB)
      row := Row.mk .abstraction (some f.term.row) none none ⟨Γ.length⟩
      lower := fun e => .tmLam A (.tmApp ((f.lower e).rename Nat.succ) (.tmVar 0))
      typing := heta }
  type_eq := rfl

def abs (A : Ty Base) (p : Tm Base) (hA : Kinded A)
    (hp : HasType [A] p .tyBool) (x : At Base Γ A) :
    At Base Γ (.tySub A p) where
  term :=
    { ty := .tySub A p
      formed := .tySub hA hp
      row := Row.mk .subtypeAbs (some x.term.row) none none ⟨Γ.length⟩
      lower := fun e => .tmAbs A p (x.lower e)
      typing := fun e => .tmAbs hA hp (x.typing e) }
  type_eq := rfl

def rep (A : Ty Base) (p : Tm Base) (hA : Kinded A)
    (hp : HasType [A] p .tyBool) (x : At Base Γ (.tySub A p)) : At Base Γ A where
  term :=
    { ty := A
      formed := hA
      row := Row.mk .subtypeRep (some x.term.row) none none ⟨Γ.length⟩
      lower := fun e => .tmRep A p (x.lower e)
      typing := fun e => .tmRep hA hp (x.typing e) }
  type_eq := rfl

def predInst (p : Tm Base) (x : At Base Γ A)
    (ht : ∀ e, HasType Γ (p.inst (x.lower e)) .tyBool) : At Base Γ .tyBool where
  term :=
    { ty := .tyBool
      formed := .tyBool
      row := Row.mk .application (some x.term.row) none none ⟨Γ.length⟩
      lower := fun e => p.inst (x.lower e)
      typing := ht }
  type_eq := rfl

end At

inductive Eq {Base : Type u} :
    (Γ : Ctx Base) -> (A : Ty Base) -> At Base Γ A -> At Base Γ A -> Prop
  | refl (t : At Base Γ A) : Eq Γ A t t
  | symm : Eq Γ A t u -> Eq Γ A u t
  | trans : Eq Γ A t u -> Eq Γ A u v -> Eq Γ A t v
  | app : Eq Γ (.tyArr A B) f g -> Eq Γ A x y ->
      Eq Γ B (At.app f x) (At.app g y)
  | lam (hA : Kinded A) : Eq (A :: Γ) B t u ->
      Eq Γ (.tyArr A B) (At.lam hA t) (At.lam hA u)
  | beta (hA : Kinded A) (body : At Base (A :: Γ) B) (x : At Base Γ A)
      (hi : ∀ e, HasType Γ ((body.lower e).inst (x.lower e)) B) :
      Eq Γ B (At.app (At.lam hA body) x) (At.inst body x hi)
  | eta (hA : Kinded A) (f : At Base Γ (.tyArr A B))
      (he : ∀ e, HasType Γ
        (.tmLam A (.tmApp ((f.lower e).rename Nat.succ) (.tmVar 0))) (.tyArr A B)) :
      Eq Γ (.tyArr A B) (At.etaExpand hA f he) f

theorem Eq.sound {Base : Type u} {Γ : Ctx Base} {A : Ty Base}
    {t u : At Base Γ A} (h : Eq Γ A t u) (e : Filling Base) :
    Hol.EqTm Γ (t.lower e) (u.lower e) A := by
  induction h with
  | refl t => exact .refl (t.typing e)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ihf ihx => exact .app ihf ihx
  | lam hA _ ih => exact .lam hA ih
  | beta hA body x hi =>
      simpa only [At.app, At.lam, At.inst, At.lower, Term.app, Term.lam] using
        Hol.EqTm.beta hA (body.typing e) (x.typing e) (hi e)
  | eta hA f he =>
      simpa [At.etaExpand, At.lower] using Hol.EqTm.eta (f.typing e) (he e)

def lowerHyps {Base : Type u} {Γ : Ctx Base}
    (e : Filling Base) (H : List (At Base Γ .tyBool)) : List (Tm Base) :=
  H.map (fun p => p.lower e)

theorem typed_lowerHyps {Base : Type u} {Γ : Ctx Base}
    (e : Filling Base) (H : List (At Base Γ .tyBool)) :
    Hol.TypedHyps Γ (lowerHyps e H) := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact q.typing e

inductive Proves {Base : Type u} (Γ : Ctx Base) :
    List (At Base Γ .tyBool) -> At Base Γ .tyBool -> Prop
  | hyp (hp : p ∈ H) : Proves Γ H p
  | truth : Proves Γ H (At.bool true)
  | eqRefl (hA : Kinded A) (x : At Base Γ A) : Proves Γ H (At.equal hA x x)
  | eqMp (hA : Kinded A) (p : At Base Γ (.tyArr A .tyBool))
      (x y : At Base Γ A) :
      Proves Γ H (At.equal hA x y) -> Proves Γ H (At.app p x) ->
      Proves Γ H (At.app p y)
  | choice (hA : Kinded A) (p : At Base Γ (.tyArr A .tyBool))
      (x : At Base Γ A) :
      Proves Γ H (At.app p x) -> Proves Γ H (At.app p (At.choice hA p))
  | convert : Eq Γ .tyBool p q -> Proves Γ H p -> Proves Γ H q
  | eqOfEq (hA : Kinded A) (h : Eq Γ A x y) : Proves Γ H (At.equal hA x y)
  | antisymm (p q : At Base Γ .tyBool) :
      Proves Γ (p :: H) q -> Proves Γ (q :: H) p ->
      Proves Γ H (At.equal .tyBool p q)
  | absRep (A : Ty Base) (p : Tm Base) (hA : Kinded A)
      (hp : HasType [A] p .tyBool) (x : At Base Γ (.tySub A p)) :
      Proves Γ H (At.equal (.tySub hA hp) (At.abs A p hA hp (At.rep A p hA hp x)) x)
  | repAbs (A : Ty Base) (p : Tm Base) (hA : Kinded A)
      (hp : HasType [A] p .tyBool) (x : At Base Γ A)
      (hpx : ∀ e, HasType Γ (p.inst (x.lower e)) .tyBool) :
      Proves Γ H (At.predInst p x hpx) ->
      Proves Γ H (At.equal hA (At.rep A p hA hp (At.abs A p hA hp x)) x)

theorem Proves.sound {Base : Type u} {Γ : Ctx Base}
    {H : List (At Base Γ .tyBool)} {p : At Base Γ .tyBool}
    (h : Proves Γ H p) (e : Filling Base) :
    Hol.Proves Γ (lowerHyps e H) (p.lower e) := by
  induction h with
  | hyp hp => exact .hyp (typed_lowerHyps e _) (List.mem_map.mpr ⟨_, hp, rfl⟩)
  | truth => exact .truth (typed_lowerHyps e _)
  | eqRefl hA x => exact .eqRefl (typed_lowerHyps e _) (x.typing e) hA
  | eqMp hA p x y _ _ ih1 ih2 =>
      exact .eqMp (typed_lowerHyps e _) (p.typing e) (x.typing e) (y.typing e) hA ih1 ih2
  | choice hA p x _ ih =>
      exact .choice (typed_lowerHyps e _) (p.typing e) (x.typing e) hA ih
  | convert he _ ih => exact .convert (typed_lowerHyps e _) (he.sound e) ih
  | eqOfEq hA he => exact .eqOfEqTm (typed_lowerHyps e _) hA (he.sound e)
  | antisymm p q _ _ ih1 ih2 =>
      exact .antisymm (typed_lowerHyps e _) (p.typing e) (q.typing e)
        (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact p.typing e
          · exact typed_lowerHyps e _ r hr)
        (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact q.typing e
          · exact typed_lowerHyps e _ r hr)
        ih1 ih2
  | absRep A p hA hp x =>
      exact .absRep (typed_lowerHyps e _) hA hp (x.typing e)
  | repAbs A p hA hp x hpx _ ih =>
      exact .repAbs (typed_lowerHyps e _) hA hp (x.typing e) (hpx e) ih

end Nucleus.Cov
