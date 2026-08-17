import Nucleus.SExpr.Basic
import Nucleus.Cbor.Bytes

/-!
# Forsp literal tables

Forsp runtime objects use binary S-expressions, but non-symbol scalar values
live in a side table.  A value at table index `i` is represented by the
improper S-expression `(i . magic)`.  Distinct magic atoms make the three
literal domains disjoint and let decoding validate the table entry's type.
-/

namespace Nucleus.SExpr2.Forsp

/-- Scalar literals supported by the extended Forsp reader. -/
inductive Literal where
  | integer (value : Int)
  | string (value : String)
  | bytes (value : Bytes)
  deriving DecidableEq

/-- The unforgeable trailing atom of an indirect literal representation. -/
inductive Magic where
  | integer
  | string
  | bytes
  | closure
  deriving DecidableEq, Repr

/-- Atoms used by the concrete S-expression object representation. -/
inductive Atom where
  | symbol (name : String)
  | index (value : Nat)
  | magic (value : Magic)
  deriving DecidableEq, Repr

abbrev Object := SExpr2 Atom
abbrev LiteralTable := List Literal

def Literal.magic : Literal → Magic
  | .integer _ => .integer
  | .string _ => .string
  | .bytes _ => .bytes

/-- The requested `(INDEX_INTO_TABLE . MAGIC_SYMBOL)` representation. -/
def literalReference (index : Nat) (magic : Magic) : Object :=
  .cons (.atom (.index index)) (.atom (.magic magic))

/-- Allocate a literal at the end of its table and return its object handle. -/
def LiteralTable.allocate (table : LiteralTable) (literal : Literal) :
    LiteralTable × Object :=
  (table ++ [literal], literalReference table.length literal.magic)

/-- Decode a table reference, rejecting forged indices or mismatched tags. -/
def LiteralTable.decode? (table : LiteralTable) : Object → Option Literal
  | .cons (.atom (.index index)) (.atom (.magic magic)) => do
      let literal ← table[index]?
      if literal.magic = magic then some literal else none
  | _ => none

@[simp] theorem LiteralTable.decode?_allocate (table : LiteralTable)
    (literal : Literal) :
    (table.allocate literal).1.decode? (table.allocate literal).2 = some literal := by
  simp [LiteralTable.allocate, LiteralTable.decode?, literalReference, Literal.magic]

theorem LiteralTable.decode?_reference_some_iff (table : LiteralTable)
    (index : Nat) (magic : Magic) (literal : Literal) :
    table.decode? (literalReference index magic) = some literal ↔
      table[index]? = some literal ∧ literal.magic = magic := by
  cases hfound : table[index]? with
  | none => simp [LiteralTable.decode?, literalReference, hfound]
  | some found =>
      by_cases hmagic : found.magic = magic
      · constructor
        · intro h
          have heq : found = literal := by
            simpa [LiteralTable.decode?, literalReference, hfound, hmagic] using h
          subst literal
          exact ⟨rfl, hmagic⟩
        · rintro ⟨hliteral, _⟩
          have : found = literal := Option.some.inj hliteral
          subst literal
          simp [LiteralTable.decode?, literalReference, hfound, hmagic]
      · constructor
        · simp [LiteralTable.decode?, literalReference, hfound, hmagic]
        · rintro ⟨hliteral, hliteralMagic⟩
          have : found = literal := Option.some.inj hliteral
          subst literal
          exact (hmagic hliteralMagic).elim

theorem LiteralTable.allocate_preserves (table : LiteralTable) (literal : Literal)
    {object : Object} {value : Literal} (h : table.decode? object = some value) :
    (table.allocate literal).1.decode? object = some value := by
  cases object with
  | nil => simp [LiteralTable.decode?] at h
  | atom atom => simp [LiteralTable.decode?] at h
  | cons car cdr =>
      cases car with
      | nil => simp [LiteralTable.decode?] at h
      | cons _ _ => simp [LiteralTable.decode?] at h
      | atom head =>
          cases head with
          | symbol _ => simp [LiteralTable.decode?] at h
          | magic _ => simp [LiteralTable.decode?] at h
          | index index =>
              cases cdr with
              | nil => simp [LiteralTable.decode?] at h
              | cons _ _ => simp [LiteralTable.decode?] at h
              | atom tail =>
                  cases tail with
                  | symbol _ => simp [LiteralTable.decode?] at h
                  | index _ => simp [LiteralTable.decode?] at h
                  | magic magic =>
                      change table.decode? (literalReference index magic) = some value at h
                      change (table ++ [literal]).decode?
                        (literalReference index magic) = some value
                      rw [LiteralTable.decode?_reference_some_iff] at h ⊢
                      refine ⟨?_, h.2⟩
                      have hi : index < table.length :=
                        List.getElem?_eq_some_iff.mp h.1 |>.1
                      rw [List.getElem?_append_left hi]
                      exact h.1

end Nucleus.SExpr2.Forsp
