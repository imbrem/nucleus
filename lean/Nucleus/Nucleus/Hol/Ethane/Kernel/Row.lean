/-!
# Private kernel-row contract

This is the Lean counterpart of Rust's private `row.rs`. A semantic row is an
expression plus optional kernel-relative equality and sorting facts. The Serde
view is mechanical data; `ofSerde` performs constructor-specific arity checks.
-/

namespace Nucleus.Hol.Ethane.Kernel

/-- The deliberately minimal expression slice implemented by Rust. -/
inductive Expr where
  | kindStar
  | boolTy
  | bool (value : Bool)
  deriving DecidableEq, Repr

/-- A kernel-relative row. Facts are references on the row, never standalone
objects. -/
structure Row where
  expr : Expr
  eq : Option Int64 := none
  sort : Option Int64 := none
  deriving DecidableEq, Repr

/-- Stable Serde discriminants for the minimal expression slice. -/
inductive Tag where
  | kindStar
  | boolTy
  | boolFalse
  | boolTrue
  deriving DecidableEq, Repr

/-- Mechanical Serde view. Rust uses `SmallVec<[i64; MAX_CHILDREN]>`; a Lean
list carries the same ordered child sequence without imposing storage policy. -/
structure RowSerde where
  tag : Tag
  ixs : List Int64
  eq : Option Int64 := none
  sort : Option Int64 := none
  deriving DecidableEq, Repr

inductive RowError where
  | wrongChildCount (expected actual : Nat)
  deriving DecidableEq, Repr

/-- Convert a semantic row into its mechanical Serde view. -/
def Row.toSerde (row : Row) : RowSerde :=
  { tag := match row.expr with
      | .kindStar => .kindStar
      | .boolTy => .boolTy
      | .bool false => .boolFalse
      | .bool true => .boolTrue
    ixs := []
    eq := row.eq
    sort := row.sort }

/-- Validate constructor arity and recover a semantic row. -/
def Row.ofSerde (row : RowSerde) : Except RowError Row := do
  if row.ixs.length = 0 then
    let expr := match row.tag with
      | .kindStar => .kindStar
      | .boolTy => .boolTy
      | .boolFalse => .bool false
      | .boolTrue => .bool true
    .ok { expr, eq := row.eq, sort := row.sort }
  else
    .error (.wrongChildCount 0 row.ixs.length)

@[simp] theorem Row.ofSerde_toSerde (row : Row) :
    Row.ofSerde row.toSerde = .ok row := by
  cases row with
  | mk expr eq sort =>
      cases expr with
      | kindStar | boolTy => simp [Row.toSerde, Row.ofSerde]
      | bool value => cases value <;> simp [Row.toSerde, Row.ofSerde]

theorem Row.ofSerde_wrongArity (tag : Tag) (child : Int64)
    (eq sort : Option Int64) :
    Row.ofSerde ⟨tag, [child], eq, sort⟩ =
      .error (.wrongChildCount 0 1) := by
  simp [Row.ofSerde]

end Nucleus.Hol.Ethane.Kernel
