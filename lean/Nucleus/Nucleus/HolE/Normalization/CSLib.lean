import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.StrongNorm
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence

/-!
# CSLib normalization frontier

This module records the external metatheorems used by the HolE normalization
development. The translation itself remains separate: HolE has additional
opaque term formers and intrinsically scoped de Bruijn indices, while CSLib's
lambda calculus uses cofinite locally nameless opening.
-/

namespace Nucleus.HolE.Normalization.CSLib

set_option relaxedAutoImplicit true
set_option linter.unusedDecidableInType false

open Cslib

namespace Lambda

abbrev Term (Var : Type) := LambdaCalculus.LocallyNameless.Untyped.Term Var
abbrev FullBeta (Var : Type) : Term Var → Term Var → Prop :=
  @LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta Var
abbrev FullEta (Var : Type) : Term Var → Term Var → Prop :=
  @LambdaCalculus.LocallyNameless.Untyped.Term.FullEta Var
abbrev FullBetaEta (Var : Type) : Term Var → Term Var → Prop :=
  @LambdaCalculus.LocallyNameless.Untyped.Term.FullBetaEta Var

/-- CSLib's Church-Rosser theorem for full beta-eta reduction. -/
theorem betaEta_confluent {Var : Type} [HasFresh Var] [DecidableEq Var] :
    Relation.Confluent (FullBetaEta Var) :=
  LambdaCalculus.LocallyNameless.Untyped.Term.confluent_beta_eta

end Lambda

namespace Stlc

abbrev Ty (Base : Type) := LambdaCalculus.LocallyNameless.Stlc.Ty Base
abbrev Typing (Var Base : Type) :=
  @LambdaCalculus.LocallyNameless.Stlc.Typing Var Base

/-- CSLib's strong-normalization theorem for full beta reduction of STLC. -/
theorem beta_stronglyNormalizing {Var Base : Type}
    [DecidableEq Var] [HasFresh Var]
    {Γ : LambdaCalculus.LocallyNameless.Context Var (Ty Base)}
    {term : Lambda.Term Var} {A : Ty Base}
    (typing : LambdaCalculus.LocallyNameless.Stlc.Typing Γ term A) :
    Relation.SN (Lambda.FullBeta Var) term :=
  LambdaCalculus.LocallyNameless.Stlc.strong_norm typing

end Stlc

end Nucleus.HolE.Normalization.CSLib
