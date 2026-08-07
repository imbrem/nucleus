/-
SPDX-FileCopyrightText: 2026 Nucleus contributors
SPDX-License-Identifier: CC0-1.0
-/

import Nucleus.HolOmega.Kernel
import Nucleus.HolOmega.Soundness

/-!
# The kernel-facing specification

One module stating what the kernel must implement.

`Kind`, `Ty`, and `Tm` are the content-addressed raw trees. A `Certificate` is
another tree: each constructor checks only its immediate children and the
indicated context lookup, so there is no global well-formedness pass hidden in
this interface. That is the property that makes a derivation independently
checkable — and, later, independently addressable.

The formation and typing rules are the constructors of `Judgement`, whose
soundness is inherited for every `SoundModel`. The logical rules are exposed
separately because they need the stronger standard Tarskian universe of
`Kernel.lean`; their two soundness theorems cover every equality, choice, and
subtype rule.

Later layers re-state this interface against progressively more realistic
representations — the store's tag vocabulary, annotated single-type syntax,
typed holes, content-addressed resolution — and relate each back to here.
-/

universe u v

namespace Nucleus.HolOmega.Spec

variable {Base : Type u} {Ω : Type v}

abbrev Kind := HolOmega.Kind
abbrev Ty (Base : Type u) := HolOmega.Ty Base
abbrev Tm (Base : Type u) := HolOmega.Tm Base

abbrev KindCtx := HolOmega.KindCtx
abbrev TermCtx (Base : Type u) := HolOmega.TmCtx Base
abbrev Assumptions (Base : Type u) := HolOmega.Hyps Base

/-- The two forms of locally checkable goal. -/
abbrev Goal (Base : Type u) := HolOmega.JudgementIndex Base

/-- A content-addressable derivation tree. Its constructors are the complete
formation and typing rules for the raw language. -/
abbrev Certificate {Base : Type u} := @HolOmega.Judgement Base

namespace Rules

-- Kinds are the freely generated simple kinds `*` and `K ⇒ L`.
abbrev star : Kind := .star
abbrev kindArrow (K L : Kind) : Kind := .arr K L

-- Type formation.
theorem base {Base : Type u} (A : Base) :
    Certificate (.kinded Δ (.base A) .star) := .base

theorem tyVar (h : Δ[n]? = some K) :
    Certificate (Base := Base) (.kinded Δ (.tyVar n) K) := .tyVar h

theorem tyLam (body : Certificate (Base := Base) (.kinded (K :: Δ) A L)) :
    Certificate (.kinded Δ (.tyLam K A) (.arr K L)) := .tyLam body

theorem tyApp (fn : Certificate (Base := Base) (.kinded Δ F (.arr K L)))
    (arg : Certificate (.kinded Δ A K)) :
    Certificate (.kinded Δ (.tyApp F A) L) := .tyApp fn arg

theorem boolTy : Certificate (Base := Base) (.kinded Δ .tyBool .star) := .tyBool

theorem arrowTy (left : Certificate (Base := Base) (.kinded Δ A .star))
    (right : Certificate (.kinded Δ B .star)) :
    Certificate (.kinded Δ (.tyArr A B) .star) := .tyArr left right

theorem subtype (carrier : Certificate (Base := Base) (.kinded Δ A .star))
    (predicate : Certificate (.hasType Δ [A] p .tyBool)) :
    Certificate (.kinded Δ (.tySub A p) .star) := .tySub carrier predicate

-- Term typing.
theorem var (h : Γ[n]? = some A) :
    Certificate (Base := Base) (.hasType Δ Γ (.tmVar n) A) := .tmVar h

theorem app (fn : Certificate (Base := Base) (.hasType Δ Γ f (.tyArr A B)))
    (arg : Certificate (.hasType Δ Γ x A)) :
    Certificate (.hasType Δ Γ (.tmApp f x) B) := .tmApp fn arg

theorem lam (domain : Certificate (Base := Base) (.kinded Δ A .star))
    (body : Certificate (.hasType Δ (A :: Γ) t B)) :
    Certificate (.hasType Δ Γ (.tmLam A t) (.tyArr A B)) := .tmLam domain body

theorem typeApp (fn : Certificate (Base := Base) (.hasType Δ Γ f (.tyApp F X)))
    (arg : Certificate (.kinded Δ A K)) :
    Certificate (.hasType Δ Γ (.tmTyApp f A) (.tyApp F A)) := .tmTyApp fn arg

theorem typeLam (body : Certificate (Base := Base) (.hasType (K :: Δ) Γ t A)) :
    Certificate (.hasType Δ Γ (.tmTyLam K t) (.tyLam K A)) := .tmTyLam body

theorem bool (b : Bool) :
    Certificate (Base := Base) (.hasType Δ Γ (.tmBool b) .tyBool) := .tmBool

theorem equal (type : Certificate (Base := Base) (.kinded Δ A .star))
    (left : Certificate (.hasType Δ Γ x A))
    (right : Certificate (.hasType Δ Γ y A)) :
    Certificate (.hasType Δ Γ (.tmEq A x y) .tyBool) := .tmEq type left right

theorem choice (type : Certificate (Base := Base) (.kinded Δ A .star))
    (predicate : Certificate (.hasType Δ Γ p (.tyArr A .tyBool))) :
    Certificate (.hasType Δ Γ (.tmEps A p) A) := .tmEps type predicate

theorem abs (type : Certificate (Base := Base) (.kinded Δ A .star))
    (predicate : Certificate (.hasType Δ [A] p .tyBool))
    (value : Certificate (.hasType Δ Γ x A)) :
    Certificate (.hasType Δ Γ (.tmAbs A p x) (.tySub A p)) :=
  .tmAbs type predicate value

theorem rep (type : Certificate (Base := Base) (.kinded Δ A .star))
    (predicate : Certificate (.hasType Δ [A] p .tyBool))
    (value : Certificate (.hasType Δ Γ x (.tySub A p))) :
    Certificate (.hasType Δ Γ (.tmRep A p x) A) :=
  .tmRep type predicate value

end Rules

/-- A term context bundled with the local kinding certificates for its entries.
Checking extension therefore checks just the new head. -/
structure Context (Base : Type u) (Δ : KindCtx) where
  types : TermCtx Base
  valid : ∀ A, A ∈ types → Certificate (.kinded Δ A .star)

namespace Context

def empty (Base : Type u) (Δ : KindCtx) : Context Base Δ :=
  ⟨[], by simp⟩

def cons (A : Ty Base) (hA : Certificate (.kinded Δ A .star))
    (Γ : Context Base Δ) : Context Base Δ where
  types := A :: Γ.types
  valid B h := by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact hA
    · exact Γ.valid B h

@[simp] theorem empty_types : (empty Base Δ).types = [] := rfl

@[simp] theorem cons_types {A : Ty Base}
    {hA : Certificate (.kinded Δ A .star)} (Γ : Context Base Δ) :
    (cons A hA Γ).types = A :: Γ.types := rfl

end Context

/-- Soundness of every formation and typing rule, in one statement. -/
theorem certificateSound (M : HolOmega.SoundModel Base Ω)
    {i : Goal Base} (d : Certificate i) : HolOmega.Sound M i :=
  d.sound M

namespace Logic

/-! The logical layer uses the standard Tarskian model. Types and terms are
intrinsic here, so every rule constructor is impossible to form at the wrong
kind or type. `Proof` remains an ordinary inductive tree. -/

abbrev Universe := HolOmega.Kernel.Universe
abbrev SemanticTy (U : Universe) (Δ : List Kind) (K : Kind) :=
  HolOmega.Kernel.Ty U Δ K
abbrev SemanticTm (U : Universe) {Δ : List Kind}
    (Γ : HolOmega.Kernel.Ctx U Δ) (A : HolOmega.Kernel.Ty U Δ .star) :=
  HolOmega.Kernel.Tm U Γ A
abbrev Equality (U : Universe) {Δ : List Kind}
    (Γ : HolOmega.Kernel.Ctx U Δ) {A : HolOmega.Kernel.Ty U Δ .star}
    (x y : HolOmega.Kernel.Tm U Γ A) := HolOmega.Kernel.EqTm U Γ x y
abbrev Proof (U : Universe) {Δ : List Kind} {Γ : HolOmega.Kernel.Ctx U Δ}
    (H : List (HolOmega.Kernel.Tm U Γ (HolOmega.Kernel.Ty.boolCode U)))
    (p : HolOmega.Kernel.Tm U Γ (HolOmega.Kernel.Ty.boolCode U)) :=
  HolOmega.Kernel.Derives U H p
abbrev Entails (U : Universe) {Δ : List Kind} {Γ : HolOmega.Kernel.Ctx U Δ}
    (H : List (HolOmega.Kernel.Tm U Γ (HolOmega.Kernel.Ty.boolCode U)))
    (p : HolOmega.Kernel.Tm U Γ (HolOmega.Kernel.Ty.boolCode U)) :=
  HolOmega.Kernel.Entails U H p

/-- `Equality` has exactly these constructors: reflexivity, symmetry,
transitivity, application and abstraction congruence at both term and type
levels, and term/type beta and eta. -/
abbrev EqualityRules (U : Universe) := @HolOmega.Kernel.EqTm U

/-- `Proof` has exactly these constructors: assumption, truth, equality
reflexivity and substitution, choice, conversion, equality introduction,
Boolean antisymmetry, and both directions of the subtype isomorphism. -/
abbrev ProofRules (U : Universe) := @HolOmega.Kernel.Derives U

/-- Every equality rule denotes actual equality in the standard model. -/
theorem equalitySound {U : Universe} {Δ : List Kind}
    {Γ : HolOmega.Kernel.Ctx U Δ} {A : HolOmega.Kernel.Ty U Δ .star}
    {x y : HolOmega.Kernel.Tm U Γ A}
    (d : HolOmega.Kernel.EqTm U Γ x y) : x = y :=
  d.sound U

/-- Every logical rule preserves truth in the standard model. -/
theorem proofSound {U : Universe} {Δ : List Kind}
    {Γ : HolOmega.Kernel.Ctx U Δ}
    {H : List (HolOmega.Kernel.Tm U Γ (HolOmega.Kernel.Ty.boolCode U))}
    {p : HolOmega.Kernel.Tm U Γ (HolOmega.Kernel.Ty.boolCode U)}
    (d : HolOmega.Kernel.Derives U H p) : HolOmega.Kernel.Entails U H p :=
  d.sound U

end Logic

end Nucleus.HolOmega.Spec
