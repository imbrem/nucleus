import Mathlib
import Nucleus.HolOmega.Kernel
import Nucleus.HolOmega.Env
import Nucleus.HolOmega.Typing

/-!
# Relational semantics for raw HOL-omega trees

Raw trees do not synthesize a semantic value without a typing derivation: in
particular, `TY_ALL` needs a rank bound for its body.  Their semantics is
therefore a relation.  Types and terms are deliberately represented by one
indexed family, just as syntax and typing are.  The term half retains the
syntactic type as an index.  This is essential: application must join two
independently obtained denotations of its argument type, without assuming
that the universe's arrow-code operation is injective.

Every term value is tagged by its universe code.  Coherence below says that
two denotations of the same raw type have the same underlying code, and that
two denotations of the same type-indexed raw term are equal.
-/

universe u v

namespace Nucleus.HolOmega

open Kernel

/-- The single carrier in which raw term environments live. -/
def Omega (U : Kernel.Universe) := (c : U.Code) × U.El c

namespace Omega

def code {U : Kernel.Universe} (x : Omega U) : U.Code := x.1

def cast {U : Kernel.Universe} {A B : U.Code} (h : A = B) (x : U.El A) : U.El B :=
  h ▸ x

def arrApp {U : Kernel.Universe} {A B : U.Code}
    (f x : Omega U) (hf : f.code = U.arr A B) (hx : x.code = A) : Omega U :=
  ⟨B, U.arrEquiv A B (cast hf f.2) (cast hx x.2)⟩

def arrLam {U : Kernel.Universe} (A B : U.Code) (f : U.El A → Omega U)
    (hf : ∀ x, (f x).code = B) : Omega U :=
  ⟨U.arr A B, (U.arrEquiv A B).symm (fun x => cast (hf x) (f x).2)⟩

def allApp {U : Kernel.Universe} {K r F h}
    (f : Omega U) (hf : f.code = U.allCode K r F h)
    (X : Kernel.KindVal U.rank r K) : Omega U :=
  ⟨F X, U.allEquiv K r F h (cast hf f.2) X⟩

def allLam {U : Kernel.Universe} (K r : _) (F : Kernel.KindVal U.rank r K → U.Code)
    (h : ∃ s, ∀ X, U.rank (F X) ≤ s) (f : ∀ X, Omega U)
    (hf : ∀ X, (f X).code = F X) : Omega U :=
  ⟨U.allCode K r F h,
    (U.allEquiv K r F h).symm (fun X => cast (hf X) (f X).2)⟩

def bool (U : Kernel.Universe) (b : Bool) : Omega U :=
  ⟨U.boolCode, U.boolEquiv.symm b⟩

noncomputable def equal {U : Kernel.Universe} {A : U.Code}
    (x y : Omega U) (hx : x.code = A) (hy : y.code = A) : Omega U := by
  classical
  exact bool U (decide (cast hx x.2 = cast hy y.2))

noncomputable def epsilon {U : Kernel.Universe} {A : U.Code}
    (p : Omega U) (hp : p.code = U.arr A U.boolCode) : Omega U := by
  classical
  letI := U.inhabited A
  let q := fun x => U.boolEquiv (U.arrEquiv A U.boolCode (cast hp p.2) x)
  exact ⟨A, if hq : ∃ x, q x = true then Classical.choose hq else default⟩

noncomputable def abs {U : Kernel.Universe} {A : U.Code} (P : U.El A → Prop)
    (x : Omega U) (hx : x.code = A) : Omega U :=
  ⟨U.subCode A P,
    (U.subEquiv A P).symm (TotalSubtype.abs P (cast hx x.2))⟩

def rep {U : Kernel.Universe} {A : U.Code} (P : U.El A → Prop)
    (x : Omega U) (hx : x.code = U.subCode A P) : Omega U :=
  ⟨A, TotalSubtype.rep (U.subEquiv A P (cast hx x.2))⟩

end Omega

/-- Raw environments ignore the spelling of their type indices, but preserve
their length and de Bruijn layout. -/
def RawEnv {Base : Type u} (U : Kernel.Universe) (Γ : TmCtx Base) :=
  Env (fun _ => Omega U) Γ

def RawEnv.lookup {Base : Type u} {U : Kernel.Universe} {Γ : TmCtx Base}
    {n : Nat} {A : Ty Base}
    (h : Γ[n]? = some A) (γ : RawEnv U Γ) : Omega U := by
  induction Γ generalizing n A with
  | nil => simp at h
  | cons B Γ ih =>
    cases n with
    | zero =>
      simp at h
      subst B
      exact γ.1
    | succ n => exact ih (by simpa using h) γ.2

def RawEnv.liftTy {Base : Type u} {U : Kernel.Universe} :
    {Γ : TmCtx Base} → RawEnv U Γ → RawEnv U Γ.liftTy
  | [], _ => PUnit.unit
  | _ :: Γ, γ => (γ.1, RawEnv.liftTy γ.2)

def Kernel.Kind.Env.lookup {U : Kernel.Universe} {Δ : KindCtx} {n : Nat} {RK : RKind}
    (h : Δ[n]? = some RK) (ρ : Kernel.Kind.Env U Δ) : Kernel.Kind.Val U RK := by
  induction Δ generalizing n RK with
  | nil => simp at h
  | cons RK' Δ ih =>
    cases n with
    | zero =>
      simp at h
      subst RK'
      exact ρ.1
    | succ n => exact ih (by simpa using h) ρ.2

/-- Interpretation of base atoms.  Base codes live at rank zero, hence may be
viewed at every rank admitted by the raw `base` kinding rule. -/
structure BaseSemantics (Base : Type u) (U : Kernel.Universe) where
  code : Base → U.Code
  rank_code : ∀ c, U.rank (code c) = 0

/-- Indices for the common type/term denotation relation. -/
inductive DenoteIndex (Base : Type u) (U : Kernel.Universe.{v}) : Type (max u v + 1)
  | kinded (Δ : KindCtx) (ρ : Kernel.Kind.Env U Δ) (A : Ty Base)
      (RK : RKind) (v : Kernel.Kind.Val U RK)
  | hasType (Δ : KindCtx) (ρ : Kernel.Kind.Env U Δ) (Γ : TmCtx Base)
      (γ : RawEnv U Γ) (t : Tm Base) (A : Ty Base) (x : Omega U)

/-- Relational denotation of raw types and type-indexed raw terms. -/
inductive Denotes {Base : Type u} {U : Kernel.Universe.{v}} (B : BaseSemantics Base U) :
    DenoteIndex Base U → Prop
  | base {Δ ρ c r} : Denotes B (.kinded Δ ρ (.base c) ⟨.star, r⟩
      ⟨B.code c, by simp [B.rank_code]⟩)
  | tyVar {Δ ρ n RK} (h : Δ[n]? = some RK) :
      Denotes B (.kinded Δ ρ (.tyVar n) RK (ρ.lookup h))
  | tyLam {Δ ρ RK A L} {f : Kernel.Kind.Val U RK → Kernel.Kind.Val U ⟨L, RK.rank⟩}
      (h : ∀ X, Denotes B (.kinded (RK :: Δ) (X, ρ) A ⟨L, RK.rank⟩ (f X))) :
      Denotes B (.kinded Δ ρ (.tyLam RK A) ⟨.arr RK.kind L, RK.rank⟩ f)
  | tyApp {Δ ρ F X K L r} {f : Kernel.Kind.Val U ⟨.arr K L, r⟩}
      {x : Kernel.Kind.Val U ⟨K, r⟩}
      (hf : Denotes B (.kinded Δ ρ F ⟨.arr K L, r⟩ f))
      (hx : Denotes B (.kinded Δ ρ X ⟨K, r⟩ x)) :
      Denotes B (.kinded Δ ρ (.tyApp F X) ⟨L, r⟩ (f x))
  | tyAll {Δ ρ RK A s} {F : Kernel.Kind.Val U RK → U.Code}
      (hF : ∀ X, U.rank (F X) ≤ s)
      (hA : ∀ X, Denotes B (.kinded (RK :: Δ) (X, ρ) A ⟨.star, s⟩
        ⟨F X, hF X⟩)) :
      Denotes B (.kinded Δ ρ (.tyAll RK A) ⟨.star, max RK.rank s + 2⟩
        ⟨U.allCode RK.kind RK.rank F ⟨s, hF⟩,
          U.rank_allCode RK.kind RK.rank F _ s hF⟩)
  | tyBool {Δ ρ r} : Denotes B (.kinded Δ ρ .tyBool ⟨.star, r⟩
      ⟨U.boolCode, by simp [U.rank_boolCode]⟩)
  | tyArr {Δ ρ A C r} {a c : Kernel.Kind.Val U ⟨.star, r⟩}
      (hA : Denotes B (.kinded Δ ρ A ⟨.star, r⟩ a))
      (hC : Denotes B (.kinded Δ ρ C ⟨.star, r⟩ c)) :
      Denotes B (.kinded Δ ρ (.tyArr A C) ⟨.star, r⟩
        ⟨U.arr a.val c.val, Nat.le_trans (U.rank_arr a.val c.val)
          (Nat.max_le.2 ⟨a.property, c.property⟩)⟩)
  | tySub {Δ ρ A p r} {a : Kernel.Kind.Val U ⟨.star, r⟩}
      {pv : U.El a.val → Omega U}
      (hA : Denotes B (.kinded Δ ρ A ⟨.star, r⟩ a))
      (hp : ∀ x, Denotes B (.hasType Δ ρ [A] (⟨a.val, x⟩, PUnit.unit)
        p .tyBool (pv x))) :
      Denotes B (.kinded Δ ρ (.tySub A p) ⟨.star, r⟩
        ⟨U.subCode a.val (fun x => pv x = Omega.bool U true),
          Nat.le_trans (U.rank_subCode a.val _) a.property⟩)
  | subsume {Δ ρ A r s} {a : Kernel.Kind.Val U ⟨.star, r⟩}
      (hA : Denotes B (.kinded Δ ρ A ⟨.star, r⟩ a)) (hrs : r ≤ s) :
      Denotes B (.kinded Δ ρ A ⟨.star, s⟩ ⟨a.val, Nat.le_trans a.property hrs⟩)
  | tmVar {Δ ρ Γ γ n A} (h : Γ[n]? = some A) :
      Denotes B (.hasType Δ ρ Γ γ (.tmVar n) A (RawEnv.lookup h γ))
  | tmApp {Δ ρ Γ γ f x A C r} {a c : Kernel.Kind.Val U ⟨.star, r⟩} {fv xv}
      (hf : Denotes B (.hasType Δ ρ Γ γ f (.tyArr A C) fv))
      (hx : Denotes B (.hasType Δ ρ Γ γ x A xv))
      (hA : Denotes B (.kinded Δ ρ A ⟨.star, r⟩ a))
      (hC : Denotes B (.kinded Δ ρ C ⟨.star, r⟩ c))
      (hfc : fv.code = U.arr a.val c.val) (hxc : xv.code = a.val) :
      Denotes B (.hasType Δ ρ Γ γ (.tmApp f x) C (Omega.arrApp fv xv hfc hxc))
  | tmLam {Δ ρ Γ γ t A C r} {a c : Kernel.Kind.Val U ⟨.star, r⟩}
      {f : U.El a.val → Omega U}
      (hA : Denotes B (.kinded Δ ρ A ⟨.star, r⟩ a))
      (hC : Denotes B (.kinded Δ ρ C ⟨.star, r⟩ c))
      (ht : ∀ x, Denotes B (.hasType Δ ρ (A :: Γ) (⟨a.val, x⟩, γ) t C (f x)))
      (hfc : ∀ x, (f x).code = c.val) :
      Denotes B (.hasType Δ ρ Γ γ (.tmLam A t) (.tyArr A C)
        (Omega.arrLam a.val c.val f hfc))
  | tmTyApp {Δ ρ Γ γ f RK C X s} {F : Kernel.Kind.Val U RK → U.Code}
      {fv : Omega U} {x : Kernel.Kind.Val U RK}
      (hF : ∀ Y, U.rank (F Y) ≤ s)
      (hf : Denotes B (.hasType Δ ρ Γ γ f (.tyAll RK C) fv))
      (hC : ∀ Y, Denotes B (.kinded (RK :: Δ) (Y, ρ) C ⟨.star, s⟩
        ⟨F Y, hF Y⟩))
      (hX : Denotes B (.kinded Δ ρ X RK x))
      (hfc : fv.code = U.allCode RK.kind RK.rank F ⟨s, hF⟩) :
      Denotes B (.hasType Δ ρ Γ γ (.tmTyApp f X) (C.instTy X)
        (Omega.allApp fv hfc x))
  | tmTyLam {Δ ρ Γ γ RK t A s} {F : Kernel.Kind.Val U RK → U.Code}
      {f : ∀ X, Omega U}
      (hF : ∀ X, U.rank (F X) ≤ s)
      (hA : ∀ X, Denotes B (.kinded (RK :: Δ) (X, ρ) A ⟨.star, s⟩
        ⟨F X, hF X⟩))
      (ht : ∀ X, Denotes B (.hasType (RK :: Δ) (X, ρ) Γ.liftTy (RawEnv.liftTy γ)
        t A (f X)))
      (hfc : ∀ X, (f X).code = F X) :
      Denotes B (.hasType Δ ρ Γ γ (.tmTyLam RK t) (.tyAll RK A)
        (Omega.allLam RK.kind RK.rank F ⟨s, hF⟩ f hfc))
  | tmBool {Δ ρ Γ γ b} :
      Denotes B (.hasType Δ ρ Γ γ (.tmBool b) .tyBool (Omega.bool U b))
  | tmEq {Δ ρ Γ γ A x y r} {a : Kernel.Kind.Val U ⟨.star, r⟩} {xv yv}
      (hA : Denotes B (.kinded Δ ρ A ⟨.star, r⟩ a))
      (hx : Denotes B (.hasType Δ ρ Γ γ x A xv))
      (hy : Denotes B (.hasType Δ ρ Γ γ y A yv))
      (hxc : xv.code = a.val) (hyc : yv.code = a.val) :
      Denotes B (.hasType Δ ρ Γ γ (.tmEq A x y) .tyBool
        (Omega.equal xv yv hxc hyc))
  | tmEps {Δ ρ Γ γ A p r} {a : Kernel.Kind.Val U ⟨.star, r⟩} {pv}
      (hA : Denotes B (.kinded Δ ρ A ⟨.star, r⟩ a))
      (hp : Denotes B (.hasType Δ ρ Γ γ p (.tyArr A .tyBool) pv))
      (hpc : pv.code = U.arr a.val U.boolCode) :
      Denotes B (.hasType Δ ρ Γ γ (.tmEps A p) A (Omega.epsilon pv hpc))
  | tmAbs {Δ ρ Γ γ A p x r} {a : Kernel.Kind.Val U ⟨.star, r⟩}
      {pv : U.El a.val → Omega U} {xv}
      (hA : Denotes B (.kinded Δ ρ A ⟨.star, r⟩ a))
      (hp : ∀ y, Denotes B (.hasType Δ ρ [A] (⟨a.val, y⟩, PUnit.unit)
        p .tyBool (pv y)))
      (hx : Denotes B (.hasType Δ ρ Γ γ x A xv)) (hxc : xv.code = a.val) :
      Denotes B (.hasType Δ ρ Γ γ (.tmAbs A p x) (.tySub A p)
        (Omega.abs (fun y => pv y = Omega.bool U true) xv hxc))
  | tmRep {Δ ρ Γ γ A p x r} {a : Kernel.Kind.Val U ⟨.star, r⟩}
      {pv : U.El a.val → Omega U} {xv}
      (hA : Denotes B (.kinded Δ ρ A ⟨.star, r⟩ a))
      (hp : ∀ y, Denotes B (.hasType Δ ρ [A] (⟨a.val, y⟩, PUnit.unit)
        p .tyBool (pv y)))
      (hx : Denotes B (.hasType Δ ρ Γ γ x (.tySub A p) xv))
      (hxc : xv.code = U.subCode a.val (fun y => pv y = Omega.bool U true)) :
      Denotes B (.hasType Δ ρ Γ γ (.tmRep A p x) A
        (Omega.rep (fun y => pv y = Omega.bool U true) xv hxc))

abbrev TyDenotes {Base : Type u} {U : Kernel.Universe.{v}} {Δ : KindCtx}
    (B : BaseSemantics Base U) (ρ : Kernel.Kind.Env U Δ)
    (A : Ty Base) (RK : RKind) (v : Kernel.Kind.Val U RK) :=
  Denotes B (.kinded Δ ρ A RK v)

abbrev TmDenotes {Base : Type u} {U : Kernel.Universe.{v}} {Δ : KindCtx}
    {Γ : TmCtx Base} (B : BaseSemantics Base U) (ρ : Kernel.Kind.Env U Δ)
    (γ : RawEnv U Γ) (t : Tm Base) (A : Ty Base) (x : Omega U) :=
  Denotes B (.hasType Δ ρ Γ γ t A x)

/-- The simultaneous coherence property required by the eliminators.  At a
fixed ranked kind the semantic value is unique.  At `star`, changing only the
admissible rank can change the proof component of `CodeLE`, but not its code.
The term clause also records uniqueness of the synthesized raw type index. -/
def CoherentAt {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) : DenoteIndex Base U → Prop
  | .kinded Δ ρ A RK v =>
      (∀ w, TyDenotes B ρ A RK w → v = w) ∧
      match RK with
      | ⟨.star, _⟩ => ∀ s w, TyDenotes B ρ A ⟨.star, s⟩ w → v.val = w.val
      | _ => True
  | .hasType Δ ρ Γ γ t A x =>
      ∀ A' x', TmDenotes B ρ γ t A' x' → A = A' ∧ x = x'

set_option maxHeartbeats 800000 in
theorem Denotes.coherent {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {i : DenoteIndex Base U} (h : Denotes B i) :
    CoherentAt B i := by
  induction h <;> simp only [CoherentAt] at *
  all_goals aesop (add safe cases Denotes)

theorem TyDenotes.eq {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ ρ A RK} {v w : Kernel.Kind.Val U RK}
    (hv : TyDenotes B (Δ := Δ) ρ A RK v) (hw : TyDenotes B ρ A RK w) : v = w :=
  (hv.coherent).1 w hw

theorem TyDenotes.star_code_eq {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ ρ A r s}
    {v : Kernel.Kind.Val U ⟨.star, r⟩} {w : Kernel.Kind.Val U ⟨.star, s⟩}
    (hv : TyDenotes B (Δ := Δ) ρ A ⟨.star, r⟩ v)
    (hw : TyDenotes B ρ A ⟨.star, s⟩ w) : v.val = w.val :=
  (hv.coherent).2 s w hw

theorem TmDenotes.type_value_eq {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ ρ Γ γ t A A'} {x x' : Omega U}
    (hx : TmDenotes B (Δ := Δ) (Γ := Γ) ρ γ t A x)
    (hx' : TmDenotes B ρ γ t A' x') : A = A' ∧ x = x' :=
  hx.coherent A' x' hx'

theorem TmDenotes.eq {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ ρ Γ γ t A} {x x' : Omega U}
    (hx : TmDenotes B (Δ := Δ) (Γ := Γ) ρ γ t A x)
    (hx' : TmDenotes B ρ γ t A x') : x = x' :=
  (hx.type_value_eq hx').2


end Nucleus.HolOmega
