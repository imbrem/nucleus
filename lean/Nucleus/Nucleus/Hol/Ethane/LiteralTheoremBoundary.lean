import Nucleus.Hol.Ethane.ClassicalMatrix

/-!
# Local theorem atoms and global Boolean constants

Signed term references and classical literal polarity are distinct. Theorems
store only positive local references as atoms. Boolean constants normalize to
empty matrices or empty rows, with the CNF/DNF side determining their meaning.
This is the value-level checked boundary, not a proof of container parsing.
-/

namespace Nucleus.Hol.Ethane.LiteralTheoremBoundary

open ClassicalMatrix

abbrev LocalAtom := { reference : Int // 0 < reference ∧ reference < 2 ^ 31 - 1 }

def localAtom? (reference : Int) : Option LocalAtom :=
  if valid : 0 < reference ∧ reference < 2 ^ 31 - 1 then some ⟨reference, valid⟩ else none

@[simp] theorem negative_not_atom (reference : Int) (negative : reference < 0) :
    localAtom? reference = none := by
  unfold localAtom?
  rw [dif_neg (by omega)]

@[simp] theorem local_atom_roundtrip (atom : LocalAtom) :
    localAtom? atom.val = some atom := by
  unfold localAtom?
  rw [dif_pos atom.property]

/-- Polarity belongs to this pair, never to the sign of a term reference. -/
abbrev LocalLiteral := Lit LocalAtom

def constantCnf (value : Bool) : Cnf LocalAtom :=
  if value then ⟨[]⟩ else ⟨[⟨[]⟩]⟩

def constantDnf (value : Bool) : Dnf LocalAtom :=
  if value then ⟨[⟨[]⟩]⟩ else ⟨[]⟩

@[simp] theorem constantCnf_holds (valuation : Valuation LocalAtom) (value : Bool) :
    (constantCnf value).Holds valuation ↔ value = true := by
  cases value <;> simp [constantCnf, Cnf.Holds, Clause.Holds]

@[simp] theorem constantDnf_holds (valuation : Valuation LocalAtom) (value : Bool) :
    (constantDnf value).Holds valuation ↔ value = true := by
  cases value <;> simp [constantDnf, Dnf.Holds, Cube.Holds]

/-- Negation is normalized before selecting the side's empty representation. -/
def polarized (value negative : Bool) : Bool := if negative then !value else value

theorem polarized_holds (value negative : Bool) :
    polarized value negative = true ↔ if negative then value ≠ true else value = true := by
  cases value <;> cases negative <;> decide

end Nucleus.Hol.Ethane.LiteralTheoremBoundary
