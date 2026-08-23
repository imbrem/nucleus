import Nucleus.Hol.Ethane.Arena.OneBased.Kernel
import Nucleus.Hol.Ethane.Conversion

/-!
# Sound equality micro-rules for one-based Ethane kernels

The Rust kernel checks alpha, root type beta, root term beta, and root term
eta directly over arena rows, then joins the endpoints' union-find classes.
This file gives the corresponding proof-theoretic boundary.  It deliberately
contains no beta or eta congruence beneath `Model`.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true

namespace Value

private theorem termTyping {type : EmptyTy} {term : EmptyTm}
    (wellFormed : WellFormed (.term type term)) :
    Nucleus.Hol.Ethane.HasType (.nil : TyScope [])
      (.nil : TmScope ArenaSig 0) Nucleus.HolE.emptyBound term type :=
  wellFormed

private theorem namedTermTyping {type : EmptyTy} {term : EmptyTm}
    (wellFormed : WellFormed (.term type term)) :
    Nucleus.HolE.Named.HasType (.nil : TyScope [])
      (.nil : TmScope ArenaSig 0) Nucleus.HolE.emptyBound
      term.toHolE type.toHolE := by
  rcases termTyping wellFormed with
    ⟨loweredTerm, loweredClassification, termLowering,
      classificationLowering, typing⟩
  exact ⟨loweredTerm, loweredClassification, termLowering,
    classificationLowering, typing⟩

/-- Direct named alpha comparison is a sound family equality. No existing
union-find equality is used to establish the comparison. -/
theorem equal_family_alpha {kind : Kind}
    {left right : EmptyExpr (.kind kind)}
    (equivalent : Nucleus.Hol.Ethane.Expr.Alpha
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0) left right) :
    Equal (.family kind left) (.family kind right) := by
  rcases equivalent with ⟨lowered, leftLowering, rightLowering⟩
  exact .family ⟨{
    loweredLeft := lowered
    loweredRight := lowered
    leftLowering := leftLowering
    rightLowering := rightLowering
    derivation := .refl }⟩

/-- Direct named alpha comparison is a sound term equality. -/
theorem equal_term_alpha {type : EmptyTy} {left right : EmptyTm}
    (leftWellFormed : WellFormed (.term type left))
    (equivalent : Nucleus.Hol.Ethane.Expr.Alpha
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0) left right) :
    Equal (.term type left) (.term type right) := by
  rcases equivalent with ⟨alphaLowered, leftAlpha, rightAlpha⟩
  rcases termTyping leftWellFormed with
    ⟨typedLowered, loweredClassification, leftTyping,
      typeClassification, typing⟩
  cases loweredClassification with
  | tm loweredType =>
      rw [leftAlpha] at leftTyping
      have same := Option.some.inj leftTyping
      subst typedLowered
      have typeLowering : type.lowerTy (.nil : TyScope []) = some loweredType := by
        change (do
          let lowered ← type.lowerTy (.nil : TyScope [])
          pure (Nucleus.HolE.Classification.tm lowered)) =
            some (Nucleus.HolE.Classification.tm loweredType) at typeClassification
        cases lowered : type.lowerTy (.nil : TyScope []) <;>
          simp [lowered] at typeClassification
        simpa [lowered] using typeClassification
      exact .term ⟨Nucleus.Hol.Ethane.Reference.EqTm.complete
        leftAlpha rightAlpha typeLowering (.refl (.exact typing))⟩

/-- A well-kinded root family-beta check is a sound family equality. -/
theorem equal_family_beta {kind : Kind}
    {source target : EmptyExpr (.kind kind)}
    (step : Nucleus.HolE.Named.FamBeta
      (.nil : TyScope []) source.toHolE target.toHolE)
    (bodyKinded : Nucleus.HolE.Kinded step.body)
    (argumentKinded : Nucleus.HolE.Kinded step.argument) :
    Equal (.family kind source) (.family kind target) :=
  .family ⟨step.toFamEq bodyKinded argumentKinded⟩

private theorem equal_term_of_conversion {type : EmptyTy} {left right : EmptyTm}
    (conversion : Nucleus.HolE.Named.EqTm
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      Nucleus.HolE.emptyBound left.toHolE right.toHolE type.toHolE) :
    Equal (.term type left) (.term type right) :=
  .term ⟨{
    loweredLeft := conversion.loweredLeft
    loweredRight := conversion.loweredRight
    loweredType := conversion.loweredType
    leftLowering := conversion.leftLowering
    rightLowering := conversion.rightLowering
    typeLowering := conversion.typeLowering
    derivation := conversion.derivation }⟩

/-- A well-typed root term-beta check is a sound term equality. -/
theorem equal_term_beta {type : EmptyTy} {source target : EmptyTm}
    (sourceWellFormed : WellFormed (.term type source))
    (step : Nucleus.HolE.Named.TmBeta
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      source.toHolE target.toHolE) :
    Equal (.term type source) (.term type target) := by
  obtain ⟨conversion⟩ := step.toTmConv
    (fun index => Fin.elim0 index) (namedTermTyping sourceWellFormed)
  exact equal_term_of_conversion conversion

/-- A well-typed root term-eta check is a sound term equality. -/
theorem equal_term_eta {type : EmptyTy} {source target : EmptyTm}
    (sourceWellFormed : WellFormed (.term type source))
    (step : Nucleus.HolE.Named.TmEta
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      source.toHolE target.toHolE) :
    Equal (.term type source) (.term type target) := by
  obtain ⟨conversion⟩ := step.toTmConv
    (fun index => Fin.elim0 index) (namedTermTyping sourceWellFormed)
  exact equal_term_of_conversion conversion

end Value

/-- The Ethane reduction relation has no family-beta step rooted at a model.
This is the Lean counterpart of Rust `Kernel::ty_beta` rejecting `ty.model`
before it inspects any predicate row. -/
theorem no_beta_from_model (name : Nat) (predicate : EmptyTm) (target : EmptyTy) :
    IsEmpty (Nucleus.Hol.Ethane.Reduction.FamBeta
      (.nil : TyScope []) (.model name predicate) target) :=
  Nucleus.Hol.Ethane.Reduction.noBetaFromModel name predicate target

end Nucleus.Hol.Ethane.OneBased
