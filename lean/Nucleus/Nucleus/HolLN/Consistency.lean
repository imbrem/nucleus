import Nucleus.HolLN.Soundness

/-!
# Empty-context consistency

The theorem is closed and assumption-free.  It instantiates the internal fixed
model at empty free and bound environments; literal false evaluates only to
`false`, while sound entailment would require it to evaluate to `true`.
-/

namespace Nucleus.HolLN

universe u

abbrev ClosedProves {Base : Type u} (hypotheses : List (ClosedTm Base))
    (conclusion : ClosedTm Base) : Type u :=
  Proves (emptyBound : BoundCtx Base 0) hypotheses conclusion

theorem empty_not_proves_false {Base : Type u} :
    ¬ Nonempty (Proves (emptyBound : BoundCtx Base 0) [] (.bool false)) := by
  rintro ⟨proof⟩
  have mustBeTrue := proof.sound (defaultFreeEnv : FreeEnv Base)
    (emptyBoundEnv : BoundEnv (emptyBound : BoundCtx Base 0)) (by
      intro p member
      contradiction)
  have isFalse : Eval emptyBound defaultFreeEnv
      emptyBoundEnv (.bool false : ClosedTm Base) .boolTy false := .boolean false
  exact Bool.noConfusion (mustBeTrue.unique isFalse)

end Nucleus.HolLN
