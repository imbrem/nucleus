import Nucleus.Classical.Refutation
import Nucleus.Classical.Tagged.Runtime.EncodeCorrect
import Nucleus.Classical.Tagged.Runtime.Mutate

/-!
# Refutation contracts for the checked tagged runtime

SAT nodes always quantify over fresh uninterpreted Boolean variables.  These
theorems connect that abstract meaning to a validated runtime arena and to the
existing RUP/RAT development.  Certificate parsing and hint lookup remain
outside this checked layer.
-/

namespace Nucleus.Classical.Tagged.Runtime.Refutation

open Nucleus.Classical
open Nucleus.Hol.Ethane.ClassicalMatrix
open Nucleus.Classical.Tagged.Runtime

namespace Abstract
export Nucleus.Classical.Refutation.Tagged
  (sequent satSequent sequent_syllogism_iff satSequent_entailsAt_iff)
end Abstract

namespace Matrix
export Nucleus.Classical.Refutation.Matrix
  (BooleanUnsat booleanUnsat_iff_legacy)
end Matrix

namespace Certificate
export Nucleus.Classical.Refutation.Certificate
  (learned rat_unsat_iff rup_unsat_iff)
end Certificate

variable {payloadWidth : Nat}

/-- One decoded sequent occurs in a checked runtime arena. -/
def Contains (checked : Checked payloadWidth)
    (sequent : Tagged.Sequent Nat) : Prop :=
  sequent ∈ checked.decoded.sequents

/-- Runtime theoremhood specializes to every decoded member. -/
theorem entailsAt_member {known : PartialAssignment Nat}
    {checked : Checked payloadWidth} {sequent : Tagged.Sequent Nat}
    (holds : Mutate.EntailsAt known checked)
    (member : Contains checked sequent) : sequent.EntailsAt known := by
  intro assignment completes
  exact holds assignment completes sequent member

/-- A checked universal `CNF ⊢ false` member is exactly a Boolean
refutation of that CNF. -/
theorem unsat_of_sequent {checked : Checked payloadWidth} {value : Cnf Nat}
    (holds : Mutate.Syllogism checked)
    (member : Contains checked (Abstract.sequent value)) :
    Matrix.BooleanUnsat value := by
  exact (Abstract.sequent_syllogism_iff value).mp
    (entailsAt_member holds member)

/-- A checked closed `sat(CNF) ⊢ false` member has the same refutation
meaning under any ambient partial assignment. -/
theorem unsat_of_satSequent {known : PartialAssignment Nat}
    {checked : Checked payloadWidth} {value : Cnf Nat}
    (holds : Mutate.EntailsAt known checked)
    (member : Contains checked (Abstract.satSequent value)) :
    Matrix.BooleanUnsat value := by
  exact (Abstract.satSequent_entailsAt_iff known value).mp
    (entailsAt_member holds member)

/-- The canonical runtime can represent a refutation goal whenever its public
resource bound holds. -/
theorem packSequent_complete {value : Cnf Nat}
    (fits : Encode.Fits payloadWidth [Abstract.sequent value]) :
    ∃ checked,
      Encode.pack? payloadWidth [Abstract.sequent value] = some checked ∧
      checked.decoded.sequents = [Abstract.sequent value] := by
  obtain ⟨checked, packed⟩ := Encode.pack?_complete fits
  exact ⟨checked, packed, (Encode.pack?_result packed).2.1⟩

/-- General RAT preserves the runtime refutation goal in both directions. -/
theorem rat_preserves_unsat {formula : Cnf Nat} {clause : Clause Nat}
    (rat : Nucleus.Hol.Ethane.ClassicalRefutation.Rat formula clause) :
    Matrix.BooleanUnsat (Certificate.learned formula clause) ↔
      Matrix.BooleanUnsat formula := by
  rw [Matrix.booleanUnsat_iff_legacy, Matrix.booleanUnsat_iff_legacy]
  exact Certificate.rat_unsat_iff rat

/-- RUP is the consequence-producing special case and likewise preserves the
runtime refutation goal. -/
theorem rup_preserves_unsat {formula : Cnf Nat} {clause : Clause Nat}
    (rup : Nucleus.Hol.Ethane.ClassicalRefutation.Rup formula clause) :
    Matrix.BooleanUnsat (Certificate.learned formula clause) ↔
      Matrix.BooleanUnsat formula := by
  rw [Matrix.booleanUnsat_iff_legacy, Matrix.booleanUnsat_iff_legacy]
  exact Certificate.rup_unsat_iff rup

end Nucleus.Classical.Tagged.Runtime.Refutation
