import Nucleus.HolE.FreeVariables
import Nucleus.HolE.Kernel

/-!
# Beta and eta reduction for HolE terms

Only lambda application and lambda extensionality compute. The remaining
term formers are opaque heads: the relations may reduce their term arguments,
but have no root rule for equality, choice, subtypes, or type existence.
-/

namespace Nucleus.HolE

universe u
set_option relaxedAutoImplicit true

namespace Reduction

/-- One full beta-reduction step, closed under every ordinary term argument. -/
inductive Beta {Sig : Signature.{u}} : {types : List Kind} → {depth : Nat} →
    Tm Sig types depth → Tm Sig types depth → Type u where
  | root (A : Ty Sig types) (body : Tm Sig types (depth + 1))
      (argument : Tm Sig types depth) :
      Beta (.app (.lam A body) argument) (openBound body argument)
  | appFunction : Beta function function' →
      Beta (.app function argument) (.app function' argument)
  | appArgument : Beta argument argument' →
      Beta (.app function argument) (.app function argument')
  | lam : Beta body body' → Beta (.lam A body) (.lam A body')
  | eqLeft : Beta left left' → Beta (.eq A left right) (.eq A left' right)
  | eqRight : Beta right right' → Beta (.eq A left right) (.eq A left right')
  | eps : Beta predicate predicate' → Beta (.eps A predicate) (.eps A predicate')
  | abs : Beta value value' → Beta (.abs A predicate value) (.abs A predicate value')
  | rep : Beta value value' → Beta (.rep A predicate value) (.rep A predicate value')
  | tyExists : Beta predicate predicate' →
      Beta (.tyExists predicate) (.tyExists predicate')

/-- One full eta-reduction step. The name witnesses the freshness premise of
the kernel rule; it does not occur in either endpoint. -/
inductive Eta {Sig : Signature.{u}} : {types : List Kind} → {depth : Nat} →
    Tm Sig types depth → Tm Sig types depth → Type u where
  | root (name : Nat) (fresh : Fresh name function) :
      Eta (.lam A (.app (weaken function) (.bv 0))) function
  | appFunction : Eta function function' →
      Eta (.app function argument) (.app function' argument)
  | appArgument : Eta argument argument' →
      Eta (.app function argument) (.app function argument')
  | lam : Eta body body' → Eta (.lam A body) (.lam A body')
  | eqLeft : Eta left left' → Eta (.eq A left right) (.eq A left' right)
  | eqRight : Eta right right' → Eta (.eq A left right) (.eq A left right')
  | eps : Eta predicate predicate' → Eta (.eps A predicate) (.eps A predicate')
  | abs : Eta value value' → Eta (.abs A predicate value) (.abs A predicate value')
  | rep : Eta value value' → Eta (.rep A predicate value) (.rep A predicate value')
  | tyExists : Eta predicate predicate' →
      Eta (.tyExists predicate) (.tyExists predicate')

/-- One beta-or-eta step. -/
abbrev BetaEta {Sig : Signature} {types : List Kind} {depth : Nat} :
    Tm Sig types depth → Tm Sig types depth → Prop :=
  fun source target => Nonempty (Beta source target) ∨ Nonempty (Eta source target)

/-- Reflexive-transitive beta-eta reduction. -/
abbrev BetaEtaSteps {Sig : Signature} {types : List Kind} {depth : Nat} :
    Tm Sig types depth → Tm Sig types depth → Prop :=
  Relation.ReflTransGen BetaEta

/-- A term is beta-eta normal when it has no outgoing reduction step. -/
def IsNormal {Sig : Signature} {types : List Kind} {depth : Nat}
    (term : Tm Sig types depth) : Prop :=
  ¬ ∃ target, BetaEta term target

private theorem typedCtx_extend {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types depth} {A : Ty Sig types}
    (typed : TypedCtx Γ) (hA : Kinded A) : TypedCtx (extendBound A Γ) :=
  fun index => Fin.cases hA typed index

namespace Beta

/-- Full beta reduction preserves syntax-directed typing. -/
theorem preserve {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types depth} {source target : Tm Sig types depth}
    {A : Ty Sig types} (step : Beta source target) (typed : TypedCtx Γ)
    (sourceTyping : HasType Γ source A) : HasType Γ target A := by
  induction step with
  | root domain body argument =>
      cases sourceTyping with
      | app functionTyping argumentTyping =>
        cases functionTyping with
        | lam _ hDomain bodyTyping =>
          exact HasType.openBound typed bodyTyping argumentTyping
  | appFunction step ih =>
      cases sourceTyping with
      | app functionTyping argumentTyping =>
        exact .app (ih typed functionTyping) argumentTyping
  | appArgument step ih =>
      cases sourceTyping with
      | app functionTyping argumentTyping =>
        exact .app functionTyping (ih typed argumentTyping)
  | lam step ih =>
      cases sourceTyping with
      | lam body hDomain bodyTyping =>
        exact .lam _ hDomain (ih (typedCtx_extend typed hDomain) bodyTyping)
  | eqLeft step ih =>
      cases sourceTyping with
      | eq hA leftTyping rightTyping => exact .eq hA (ih typed leftTyping) rightTyping
  | eqRight step ih =>
      cases sourceTyping with
      | eq hA leftTyping rightTyping => exact .eq hA leftTyping (ih typed rightTyping)
  | eps step ih =>
      cases sourceTyping with
      | eps hA predicateTyping => exact .eps hA (ih typed predicateTyping)
  | abs step ih =>
      cases sourceTyping with
      | abs hA predicateTyping valueTyping =>
        exact .abs hA predicateTyping (ih typed valueTyping)
  | rep step ih =>
      cases sourceTyping with
      | rep hA predicateTyping valueTyping =>
        exact .rep hA predicateTyping (ih typed valueTyping)
  | tyExists step ih =>
      cases sourceTyping with
      | tyExists predicateTyping =>
        exact .tyExists (ih (fun index => Fin.elim0 index) predicateTyping)

/-- Every well-typed beta step is inhabited by a kernel conversion certificate. -/
theorem eqTm_nonempty {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {Γ : BoundCtx Sig types depth} {source target : Tm Sig types depth}
    {A : Ty Sig types} (step : Beta source target) (typed : TypedCtx Γ)
    (sourceTyping : HasType Γ source A) : Nonempty (EqTm Γ source target A) := by
  induction step with
  | root domain body argument =>
      cases sourceTyping with
      | app functionTyping argumentTyping =>
        cases functionTyping with
        | lam _ hDomain bodyTyping =>
          let resultTyping := HasType.openBound typed bodyTyping argumentTyping
          exact ⟨.beta body argument hDomain typed
            (.app (.lam _ hDomain bodyTyping) argumentTyping)
            (.exact bodyTyping) (.exact argumentTyping) (.exact resultTyping)⟩
  | appFunction step ih =>
      cases sourceTyping with
      | app functionTyping argumentTyping =>
        let targetTyping := step.preserve typed functionTyping
        obtain ⟨functionEquality⟩ := ih typed functionTyping
        exact ⟨.app (.app functionTyping argumentTyping) (.app targetTyping argumentTyping)
          functionTyping argumentTyping targetTyping argumentTyping
          functionEquality (.refl (.exact argumentTyping))⟩
  | appArgument step ih =>
      cases sourceTyping with
      | app functionTyping argumentTyping =>
        let targetTyping := step.preserve typed argumentTyping
        obtain ⟨argumentEquality⟩ := ih typed argumentTyping
        exact ⟨.app (.app functionTyping argumentTyping) (.app functionTyping targetTyping)
          functionTyping argumentTyping functionTyping targetTyping
          (.refl (.exact functionTyping)) argumentEquality⟩
  | lam step ih =>
      cases sourceTyping with
      | lam body hDomain bodyTyping =>
        let extended := typedCtx_extend typed hDomain
        let targetTyping := step.preserve extended bodyTyping
        obtain ⟨bodyEquality⟩ := ih extended bodyTyping
        exact ⟨.lam (.lam _ hDomain bodyTyping) (.lam _ hDomain targetTyping) hDomain
          bodyEquality⟩
  | eqLeft step ih =>
      cases sourceTyping with
      | eq hA leftTyping rightTyping =>
        let targetTyping := step.preserve typed leftTyping
        obtain ⟨leftEquality⟩ := ih typed leftTyping
        exact ⟨.eq (.eq hA leftTyping rightTyping) (.eq hA targetTyping rightTyping) hA
          leftEquality (.refl (.exact rightTyping))⟩
  | eqRight step ih =>
      cases sourceTyping with
      | eq hA leftTyping rightTyping =>
        let targetTyping := step.preserve typed rightTyping
        obtain ⟨rightEquality⟩ := ih typed rightTyping
        exact ⟨.eq (.eq hA leftTyping rightTyping) (.eq hA leftTyping targetTyping) hA
          (.refl (.exact leftTyping)) rightEquality⟩
  | eps step ih =>
      cases sourceTyping with
      | eps hA predicateTyping =>
        let targetTyping := step.preserve typed predicateTyping
        obtain ⟨predicateEquality⟩ := ih typed predicateTyping
        exact ⟨.eps (.eps hA predicateTyping) (.eps hA targetTyping) hA
          predicateEquality⟩
  | abs step ih =>
      cases sourceTyping with
      | abs hA predicateTyping valueTyping =>
        let targetTyping := step.preserve typed valueTyping
        obtain ⟨valueEquality⟩ := ih typed valueTyping
        exact ⟨.abs (.abs hA predicateTyping valueTyping)
          (.abs hA predicateTyping targetTyping) hA predicateTyping valueEquality⟩
  | rep step ih =>
      cases sourceTyping with
      | rep hA predicateTyping valueTyping =>
        let targetTyping := step.preserve typed valueTyping
        obtain ⟨valueEquality⟩ := ih typed valueTyping
        exact ⟨.rep (.rep hA predicateTyping valueTyping)
          (.rep hA predicateTyping targetTyping) hA predicateTyping valueEquality⟩
  | tyExists step ih =>
      cases sourceTyping with
      | tyExists predicateTyping =>
        let targetTyping := step.preserve (Γ := emptyBound)
          (fun (index : Fin 0) => Fin.elim0 index) predicateTyping
        obtain ⟨predicateEquality⟩ := ih (Γ := emptyBound) (A := .boolTy)
          (fun (index : Fin 0) => Fin.elim0 index) predicateTyping
        exact ⟨.tyExists (.tyExists predicateTyping) (.tyExists targetTyping)
          predicateEquality⟩

/-- Select the kernel certificate guaranteed by `eqTm_nonempty`. -/
noncomputable def toEqTm {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {Γ : BoundCtx Sig types depth} {source target : Tm Sig types depth}
    {A : Ty Sig types} (step : Beta source target) (typed : TypedCtx Γ)
    (sourceTyping : HasType Γ source A) : EqTm Γ source target A :=
  Classical.choice (step.eqTm_nonempty typed sourceTyping)

end Beta

namespace Eta

/-- Full eta reduction preserves syntax-directed typing. -/
theorem preserve {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types depth} {source target : Tm Sig types depth}
    {A : Ty Sig types} (step : Eta source target) (typed : TypedCtx Γ)
    (sourceTyping : HasType Γ source A) : HasType Γ target A := by
  induction step with
  | root name fresh =>
      cases sourceTyping with
      | lam body hDomain bodyTyping =>
        cases bodyTyping with
        | app functionTyping argumentTyping =>
          cases argumentTyping with
          | bv hArgument lookup =>
            have domainEqual := lookup
            simp only [extendBound, Fin.cases_zero] at domainEqual
            cases domainEqual
            exact HasType.ofWeaken functionTyping
  | appFunction step ih =>
      cases sourceTyping with
      | app functionTyping argumentTyping =>
        exact .app (ih typed functionTyping) argumentTyping
  | appArgument step ih =>
      cases sourceTyping with
      | app functionTyping argumentTyping =>
        exact .app functionTyping (ih typed argumentTyping)
  | lam step ih =>
      cases sourceTyping with
      | lam body hDomain bodyTyping =>
        exact .lam _ hDomain (ih (typedCtx_extend typed hDomain) bodyTyping)
  | eqLeft step ih =>
      cases sourceTyping with
      | eq hA leftTyping rightTyping => exact .eq hA (ih typed leftTyping) rightTyping
  | eqRight step ih =>
      cases sourceTyping with
      | eq hA leftTyping rightTyping => exact .eq hA leftTyping (ih typed rightTyping)
  | eps step ih =>
      cases sourceTyping with
      | eps hA predicateTyping => exact .eps hA (ih typed predicateTyping)
  | abs step ih =>
      cases sourceTyping with
      | abs hA predicateTyping valueTyping =>
        exact .abs hA predicateTyping (ih typed valueTyping)
  | rep step ih =>
      cases sourceTyping with
      | rep hA predicateTyping valueTyping =>
        exact .rep hA predicateTyping (ih typed valueTyping)
  | tyExists step ih =>
      cases sourceTyping with
      | tyExists predicateTyping =>
        exact .tyExists (ih (fun index => Fin.elim0 index) predicateTyping)

/-- Every well-typed eta step is inhabited by a kernel conversion certificate. -/
theorem eqTm_nonempty {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {Γ : BoundCtx Sig types depth} {source target : Tm Sig types depth}
    {A : Ty Sig types} (step : Eta source target) (typed : TypedCtx Γ)
    (sourceTyping : HasType Γ source A) : Nonempty (EqTm Γ source target A) := by
  induction step with
  | root name fresh =>
      cases sourceTyping with
      | lam body hDomain bodyTyping =>
        cases bodyTyping with
        | app functionTyping argumentTyping =>
          cases argumentTyping with
          | bv hArgument lookup =>
            have domainEqual := lookup
            simp only [extendBound, Fin.cases_zero] at domainEqual
            cases domainEqual
            exact ⟨.eta name fresh typed (.exact (HasType.ofWeaken functionTyping))
              (.exact (.lam _ hDomain (.app functionTyping (.bv hArgument lookup))))⟩
  | appFunction step ih =>
      cases sourceTyping with
      | app functionTyping argumentTyping =>
        let targetTyping := step.preserve typed functionTyping
        obtain ⟨functionEquality⟩ := ih typed functionTyping
        exact ⟨.app (.app functionTyping argumentTyping) (.app targetTyping argumentTyping)
          functionTyping argumentTyping targetTyping argumentTyping
          functionEquality (.refl (.exact argumentTyping))⟩
  | appArgument step ih =>
      cases sourceTyping with
      | app functionTyping argumentTyping =>
        let targetTyping := step.preserve typed argumentTyping
        obtain ⟨argumentEquality⟩ := ih typed argumentTyping
        exact ⟨.app (.app functionTyping argumentTyping) (.app functionTyping targetTyping)
          functionTyping argumentTyping functionTyping targetTyping
          (.refl (.exact functionTyping)) argumentEquality⟩
  | lam step ih =>
      cases sourceTyping with
      | lam body hDomain bodyTyping =>
        let extended := typedCtx_extend typed hDomain
        let targetTyping := step.preserve extended bodyTyping
        obtain ⟨bodyEquality⟩ := ih extended bodyTyping
        exact ⟨.lam (.lam _ hDomain bodyTyping) (.lam _ hDomain targetTyping) hDomain
          bodyEquality⟩
  | eqLeft step ih =>
      cases sourceTyping with
      | eq hA leftTyping rightTyping =>
        let targetTyping := step.preserve typed leftTyping
        obtain ⟨leftEquality⟩ := ih typed leftTyping
        exact ⟨.eq (.eq hA leftTyping rightTyping) (.eq hA targetTyping rightTyping) hA
          leftEquality (.refl (.exact rightTyping))⟩
  | eqRight step ih =>
      cases sourceTyping with
      | eq hA leftTyping rightTyping =>
        let targetTyping := step.preserve typed rightTyping
        obtain ⟨rightEquality⟩ := ih typed rightTyping
        exact ⟨.eq (.eq hA leftTyping rightTyping) (.eq hA leftTyping targetTyping) hA
          (.refl (.exact leftTyping)) rightEquality⟩
  | eps step ih =>
      cases sourceTyping with
      | eps hA predicateTyping =>
        let targetTyping := step.preserve typed predicateTyping
        obtain ⟨predicateEquality⟩ := ih typed predicateTyping
        exact ⟨.eps (.eps hA predicateTyping) (.eps hA targetTyping) hA
          predicateEquality⟩
  | abs step ih =>
      cases sourceTyping with
      | abs hA predicateTyping valueTyping =>
        let targetTyping := step.preserve typed valueTyping
        obtain ⟨valueEquality⟩ := ih typed valueTyping
        exact ⟨.abs (.abs hA predicateTyping valueTyping)
          (.abs hA predicateTyping targetTyping) hA predicateTyping valueEquality⟩
  | rep step ih =>
      cases sourceTyping with
      | rep hA predicateTyping valueTyping =>
        let targetTyping := step.preserve typed valueTyping
        obtain ⟨valueEquality⟩ := ih typed valueTyping
        exact ⟨.rep (.rep hA predicateTyping valueTyping)
          (.rep hA predicateTyping targetTyping) hA predicateTyping valueEquality⟩
  | tyExists step ih =>
      cases sourceTyping with
      | tyExists predicateTyping =>
        let targetTyping := step.preserve (Γ := emptyBound)
          (fun (index : Fin 0) => Fin.elim0 index) predicateTyping
        obtain ⟨predicateEquality⟩ := ih (Γ := emptyBound) (A := .boolTy)
          (fun (index : Fin 0) => Fin.elim0 index) predicateTyping
        exact ⟨.tyExists (.tyExists predicateTyping) (.tyExists targetTyping)
          predicateEquality⟩

/-- Select the kernel certificate guaranteed by `eqTm_nonempty`. -/
noncomputable def toEqTm {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {Γ : BoundCtx Sig types depth} {source target : Tm Sig types depth}
    {A : Ty Sig types} (step : Eta source target) (typed : TypedCtx Γ)
    (sourceTyping : HasType Γ source A) : EqTm Γ source target A :=
  Classical.choice (step.eqTm_nonempty typed sourceTyping)

end Eta

namespace BetaEta

/-- A beta-or-eta step preserves syntax-directed typing. -/
theorem preserve {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types depth} {source target : Tm Sig types depth}
    {A : Ty Sig types} (step : BetaEta source target) (typed : TypedCtx Γ)
    (sourceTyping : HasType Γ source A) : HasType Γ target A := by
  cases step with
  | inl beta => exact beta.elim fun certificate => certificate.preserve typed sourceTyping
  | inr eta => exact eta.elim fun certificate => certificate.preserve typed sourceTyping

/-- Every well-typed beta-or-eta step is kernel conversion. -/
theorem eqTm_nonempty {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {Γ : BoundCtx Sig types depth} {source target : Tm Sig types depth}
    {A : Ty Sig types} (step : BetaEta source target) (typed : TypedCtx Γ)
    (sourceTyping : HasType Γ source A) : Nonempty (EqTm Γ source target A) := by
  cases step with
  | inl beta => exact beta.elim fun certificate => certificate.eqTm_nonempty typed sourceTyping
  | inr eta => exact eta.elim fun certificate => certificate.eqTm_nonempty typed sourceTyping

end BetaEta

end Reduction

end Nucleus.HolE
