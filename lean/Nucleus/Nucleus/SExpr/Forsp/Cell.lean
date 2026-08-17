import Nucleus.SExpr.Forsp.Tree
import Nucleus.SExpr.Cell

/-!
# Cell-memory representation of Forsp objects

Addresses are paths from a root.  This deliberately simple allocation policy
makes sharing absent but exposes the same pointer operations as a conventional
heap: every allocated entry is a nil, atom, or cons cell containing two
addresses.  It is an executable stepping stone to the shared allocator model.
-/

namespace Nucleus.SExpr2.Forsp.Cell

open Nucleus.SExpr2.Forsp

abbrev Address := List Bool

structure Memory where
  cells : Address → Option (Nucleus.SExpr2.Cell Address Atom)

/-- Follow a path in a finite tree; `false` is car and `true` is cdr. -/
def atPath : Object → Address → Option Object
  | object, [] => some object
  | .cons car _, false :: tail => atPath car tail
  | .cons _ cdr, true :: tail => atPath cdr tail
  | _, _ :: _ => none

theorem atPath_append {object subtree : Object} {path : Address}
    (h : atPath object path = some subtree) (suffix : Address) :
    atPath object (path ++ suffix) = atPath subtree suffix := by
  induction path generalizing object with
  | nil =>
      have : object = subtree := Option.some.inj (by simpa [atPath] using h)
      subst subtree
      rfl
  | cons direction tail ih =>
      cases object with
      | nil => simp [atPath] at h
      | atom atom => simp [atPath] at h
      | cons car cdr =>
          cases direction <;> simp only [atPath] at h ⊢
          · exact ih h
          · exact ih h

/-- Turn the object found at an address into its stored cell. -/
private def toCell (address : Address) : Object → Nucleus.SExpr2.Cell Address Atom
  | Nucleus.SExpr2.nil => Nucleus.SExpr2.Cell.nil
  | Nucleus.SExpr2.atom value => Nucleus.SExpr2.Cell.atom value
  | Nucleus.SExpr2.cons _ _ =>
      Nucleus.SExpr2.Cell.cons ⟨address ++ [false], address ++ [true]⟩

/-- Allocate every node of an object at its path from the root. -/
def ofObject (object : Object) : Memory where
  cells address := (atPath object address).map (toCell address)

/-- Fuelled pointer dereference; zero gas distinguishes nontermination from
the allocated nil cell. -/
def Memory.deref (memory : Memory) : Nat → Address → Option Object
  | 0, _ => none
  | gas + 1, address => match memory.cells address with
    | none => none
    | some Nucleus.SExpr2.Cell.nil => some .nil
    | some (Nucleus.SExpr2.Cell.atom value) => some (Nucleus.SExpr2.atom value)
    | some (Nucleus.SExpr2.Cell.cons pointers) =>
        .cons <$> memory.deref gas pointers.car <*> memory.deref gas pointers.cdr

def height : Object → Nat
  | .nil | .atom _ => 0
  | .cons car cdr => max (height car) (height cdr) + 1

theorem deref_ofObject_at {object subtree : Object} {address : Address}
    (hpath : atPath object address = some subtree) {gas : Nat}
    (hgas : height subtree < gas) :
    (ofObject object).deref gas address = some subtree := by
  induction subtree generalizing address gas with
  | nil =>
      cases gas with
      | zero => simp at hgas
      | succ gas => simp [Memory.deref, ofObject, toCell, hpath]
  | atom atom =>
      cases gas with
      | zero => simp at hgas
      | succ gas => simp [Memory.deref, ofObject, toCell, hpath]
  | cons car cdr ihCar ihCdr =>
      cases gas with
      | zero => simp at hgas
      | succ gas =>
          have hcarPath : atPath object (address ++ [false]) = some car := by
            rw [atPath_append hpath]
            simp [atPath]
          have hcdrPath : atPath object (address ++ [true]) = some cdr := by
            rw [atPath_append hpath]
            simp [atPath]
          have hcarGas : height car < gas := by
            simp [height] at hgas
            omega
          have hcdrGas : height cdr < gas := by
            simp [height] at hgas
            omega
          change (match (ofObject object).cells address with
            | none => none
            | some Nucleus.SExpr2.Cell.nil => some Nucleus.SExpr2.nil
            | some (Nucleus.SExpr2.Cell.atom value) => some (Nucleus.SExpr2.atom value)
            | some (Nucleus.SExpr2.Cell.cons pointers) =>
                Nucleus.SExpr2.cons <$> (ofObject object).deref gas pointers.car <*>
                  (ofObject object).deref gas pointers.cdr) =
                    some (Nucleus.SExpr2.cons car cdr)
          rw [show (ofObject object).cells address = some
              (Nucleus.SExpr2.Cell.cons ⟨address ++ [false], address ++ [true]⟩) by
            simp [ofObject, hpath, toCell]]
          change (Nucleus.SExpr2.cons <$>
            (ofObject object).deref gas (address ++ [false]) <*>
            (ofObject object).deref gas (address ++ [true])) =
              some (Nucleus.SExpr2.cons car cdr)
          rw [ihCar hcarPath hcarGas, ihCdr hcdrPath hcdrGas]
          rfl

/-- Every finite object round-trips through its concrete cell memory with one
more unit of gas than its height. -/
@[simp] theorem deref_ofObject (object : Object) :
    (ofObject object).deref (height object + 1) [] = some object := by
  apply deref_ofObject_at (object := object) (subtree := object)
  · simp [atPath]
  · omega

/-- A closed pointer object carrying the gas bound required to read it. -/
structure StoredObject where
  memory : Memory
  root : Address
  gas : Nat

def StoredObject.decode? (object : StoredObject) : Option Object :=
  object.memory.deref object.gas object.root

def StoredObject.encode (object : Object) : StoredObject :=
  ⟨ofObject object, [], height object + 1⟩

@[simp] theorem StoredObject.decode?_encode (object : Object) :
    (StoredObject.encode object).decode? = some object :=
  deref_ofObject object

end Nucleus.SExpr2.Forsp.Cell
