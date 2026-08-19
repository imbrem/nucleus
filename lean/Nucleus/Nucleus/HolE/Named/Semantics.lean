import Nucleus.HolE.Semantics
import Nucleus.HolE.Named.Typing

/-! # Relational semantics of named HolE by lowering -/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

abbrev EmptySig := Nucleus.HolE.EmptySig

/-- A named family denotes exactly when its locally nameless lowering denotes. -/
def DenotesFam (typeScope : TyScope) (typeEnv : Nucleus.HolE.TypeEnv typeScope.kinds)
    (family : Fam EmptySig kind) (semantic : Nucleus.HolE.DenoteKind kind) : Prop :=
  ∃ lowered,
    lowerFam typeScope family = some lowered ∧
    Nucleus.HolE.DenotesFam typeEnv lowered semantic

/-- Evaluation of named terms is evaluation of their locally nameless lowering. -/
def Eval (typeScope : TyScope) (termScope : TmScope EmptySig)
    (typeEnv : Nucleus.HolE.TypeEnv typeScope.kinds)
    (Γ : Nucleus.HolE.BoundCtx EmptySig typeScope.kinds termScope.length)
    (boundEnv : Nucleus.HolE.RawBoundEnv termScope.length)
    (term : Tm EmptySig) (A : Ty EmptySig) (semantic : Nucleus.HolE.Pointed)
    (value : semantic.carrier) : Prop :=
  ∃ loweredTerm loweredType,
    lowerTm typeScope termScope term = some loweredTerm ∧
    lowerTy typeScope A = some loweredType ∧
    Nucleus.HolE.Eval typeEnv Γ boundEnv loweredTerm loweredType semantic value

end Nucleus.HolE.Named
