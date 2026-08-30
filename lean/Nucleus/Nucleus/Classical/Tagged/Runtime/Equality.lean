import Nucleus.Classical.Tagged.Runtime

/-!
# Checked runtime equality and hashing

The Rust-facing equality boundary validates an untrusted arena once, then
compares the decoded sequent lists rather than allocation addresses.  Hashing
feeds the same abstract structure to a caller-selected hasher.  The formal
model exposes that feed as a deterministic list of natural numbers, avoiding a
commitment to one machine hash while proving the `Eq`/`Hash` contract.
-/

namespace Nucleus.Classical.Tagged.Runtime

open Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/-- A runtime arena paired with the exact result of its executable validator.
Rust should expose the constructor only through `check?`. -/
structure Checked (payloadWidth : Nat) where
  arena : Arena payloadWidth
  decoded : Decoded
  valid : arena.decodeState? = some decoded

/-- Validate an untrusted runtime arena and retain its decoded ownership. -/
def check? (arena : Arena payloadWidth) : Option (Checked payloadWidth) :=
  match decoded : arena.decodeState? with
  | none => none
  | some value => some ⟨arena, value, decoded⟩

theorem check?_valid {arena : Arena payloadWidth} {checked : Checked payloadWidth}
    (result : check? arena = some checked) :
    checked.arena = arena ∧ checked.arena.decodeState? = some checked.decoded := by
  unfold check? at result
  split at result
  · contradiction
  · simp only [Option.some.injEq] at result
    subst checked
    exact ⟨rfl, by assumption⟩

/- Structural formula data fed to a runtime `Hash` implementation. -/
mutual
  def hashFormula : Tagged.Formula Nat → List Nat
    | .literal value => [3, value.negative.toNat, value.atom]
    | .and negative children =>
        0 :: negative.toNat :: children.length :: hashFormulas children
    | .or negative children =>
        1 :: negative.toNat :: children.length :: hashFormulas children
    | .sat negative children =>
        2 :: negative.toNat :: children.length :: hashFormulas children
    termination_by formula => sizeOf formula

  /-- Concatenated child traces; every formula node records its arity. -/
  def hashFormulas : List (Tagged.Formula Nat) → List Nat
    | [] => []
    | formula :: formulas => hashFormula formula ++ hashFormulas formulas
    termination_by formulas => sizeOf formulas
end

/-- Structural data fed for one sequent.  Formula traces are self-delimiting
through their constructor arities. -/
def hashSequent (sequent : Tagged.Sequent Nat) : List Nat :=
  hashFormula sequent.premise ++ hashFormula sequent.conclusion

/-- Structural data fed for the complete sequent table. -/
def hashSequents (sequents : List (Tagged.Sequent Nat)) : List Nat :=
  sequents.length :: (sequents.flatMap hashSequent)

namespace Checked

/-- `PartialEq` for checked arenas: compare the complete decoded sequent
lists, recursively comparing every list named by the sequent table. -/
def equal (left right : Checked payloadWidth) : Bool :=
  decide (left.decoded.sequents = right.decoded.sequents)

theorem equal_eq_true (left right : Checked payloadWidth) :
    left.equal right = true ↔
      left.decoded.sequents = right.decoded.sequents := by
  simp [equal]

/-- The exact structural feed for a Rust `Hash` implementation. -/
def hashTrace (checked : Checked payloadWidth) : List Nat :=
  hashSequents checked.decoded.sequents

/-- The required `Eq`/`Hash` law. -/
theorem hashTrace_eq_of_equal {left right : Checked payloadWidth}
    (equal : left.equal right = true) :
    left.hashTrace = right.hashTrace := by
  unfold hashTrace
  rw [(equal_eq_true left right).mp equal]

end Checked

end Nucleus.Classical.Tagged.Runtime
