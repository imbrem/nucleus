import Nucleus.Hol.Ethane.Arena

/-!
# Signed dense Ethane arenas

This file models the raw Rust representation in `crates/logic/hol`.  Rows may
be malformed, forward-referencing, ill-sorted, or ill-typed.  Their optional
`eq` and `sort` members are claims made by the arena, not checked facts.
-/

namespace Nucleus.Hol.Ethane.Dense

open Nucleus.Hol.Ethane

/-- The Rust boundary uses one opaque `u64` namespace for names and primitive
symbols at every Ethane syntactic sort. -/
abbrev NumericSig : Signature := fun _ => UInt64

/-- The expression payload hidden by Rust's public `Arena` API. -/
inductive Expr where
  | pair (left right : Int64)
  | kindStar
  | kindArr (domain codomain : Int64)
  | boolTy
  | arr (domain codomain : Int64)
  | tyApp (kinds arguments : Int64)
  | tyLam (name : UInt64) (kinds body : Int64)
  | tyFv (name : UInt64) (kind : Int64)
  | tyExists (name : UInt64) (predicate : Int64)
  | model (name : UInt64) (predicate : Int64)
  | primFam (symbol : UInt64) (kind : Int64)
  | primTm (symbol : UInt64)
  | tmFv (name : UInt64) (type : Int64)
  | app (function argument : Int64)
  | lam (binder body : Int64)
  | bool (value : Bool)
  | eq (type operands : Int64)
  | eps (type predicate : Int64)
  deriving DecidableEq, Repr

/-- Stable string-tag discriminants exposed by Rust's `Arena.tag`. -/
inductive Tag where
  | pair
  | kindStar
  | kindArr
  | boolTy
  | arr
  | tyApp
  | tyLam
  | tyFv
  | tyExists
  | model
  | primFam
  | primTm
  | tmFv
  | app
  | lam
  | bool
  | eq
  | eps
  deriving DecidableEq, Repr

def Expr.tag : Expr → Tag
  | .pair .. => .pair
  | .kindStar => .kindStar
  | .kindArr .. => .kindArr
  | .boolTy => .boolTy
  | .arr .. => .arr
  | .tyApp .. => .tyApp
  | .tyLam .. => .tyLam
  | .tyFv .. => .tyFv
  | .tyExists .. => .tyExists
  | .model .. => .model
  | .primFam .. => .primFam
  | .primTm .. => .primTm
  | .tmFv .. => .tmFv
  | .app .. => .app
  | .lam .. => .lam
  | .bool .. => .bool
  | .eq .. => .eq
  | .eps .. => .eps

/-- A raw expression plus the two optional relation members carried inline. -/
structure Row where
  expr : Expr
  eq : Option Int64 := none
  sort : Option Int64 := none
  deriving DecidableEq, Repr

/-- The two scalar payload forms accepted by Rust's untagged Serde value. -/
inductive Scalar where
  | nat (value : UInt64)
  | bool (value : Bool)
  deriving DecidableEq, Repr

/-- Exact field-level Serde view of a private Rust row. -/
structure SerdeRow where
  tag : Tag
  ixs : Array Int64
  val : Option Scalar := none
  eq : Option Int64 := none
  sort : Option Int64 := none
  deriving DecidableEq, Repr

def Row.toSerde (row : Row) : SerdeRow :=
  let data : Tag × Array Int64 × Option Scalar := match row.expr with
    | .pair left right => (.pair, #[left, right], none)
    | .kindStar => (.kindStar, #[], none)
    | .kindArr domain codomain => (.kindArr, #[domain, codomain], none)
    | .boolTy => (.boolTy, #[], none)
    | .arr domain codomain => (.arr, #[domain, codomain], none)
    | .tyApp kinds arguments => (.tyApp, #[kinds, arguments], none)
    | .tyLam name kinds body => (.tyLam, #[kinds, body], some (.nat name))
    | .tyFv name kind => (.tyFv, #[kind], some (.nat name))
    | .tyExists name predicate => (.tyExists, #[predicate], some (.nat name))
    | .model name predicate => (.model, #[predicate], some (.nat name))
    | .primFam symbol kind => (.primFam, #[kind], some (.nat symbol))
    | .primTm symbol => (.primTm, #[], some (.nat symbol))
    | .tmFv name type => (.tmFv, #[type], some (.nat name))
    | .app function argument => (.app, #[function, argument], none)
    | .lam binder body => (.lam, #[binder, body], none)
    | .bool value => (.bool, #[], some (.bool value))
    | .eq type operands => (.eq, #[type, operands], none)
    | .eps type predicate => (.eps, #[type, predicate], none)
  ⟨data.1, data.2.1, data.2.2, row.eq, row.sort⟩

/-- Check constructor arity and scalar form while recovering a raw row. -/
def SerdeRow.decode (row : SerdeRow) : Option Row := do
  let expr ← match row.tag, row.ixs.toList, row.val with
    | .pair, [left, right], none => some (.pair left right)
    | .kindStar, [], none => some .kindStar
    | .kindArr, [domain, codomain], none => some (.kindArr domain codomain)
    | .boolTy, [], none => some .boolTy
    | .arr, [domain, codomain], none => some (.arr domain codomain)
    | .tyApp, [kinds, arguments], none => some (.tyApp kinds arguments)
    | .tyLam, [kinds, body], some (.nat name) => some (.tyLam name kinds body)
    | .tyFv, [kind], some (.nat name) => some (.tyFv name kind)
    | .tyExists, [predicate], some (.nat name) => some (.tyExists name predicate)
    | .model, [predicate], some (.nat name) => some (.model name predicate)
    | .primFam, [kind], some (.nat symbol) => some (.primFam symbol kind)
    | .primTm, [], some (.nat symbol) => some (.primTm symbol)
    | .tmFv, [type], some (.nat name) => some (.tmFv name type)
    | .app, [function, argument], none => some (.app function argument)
    | .lam, [binder, body], none => some (.lam binder body)
    | .bool, [], some (.bool value) => some (.bool value)
    | .eq, [type, operands], none => some (.eq type operands)
    | .eps, [type, predicate], none => some (.eps type predicate)
    | _, _, _ => none
  return ⟨expr, row.eq, row.sort⟩

@[simp] theorem SerdeRow.decode_toSerde (row : Row) :
    row.toSerde.decode = some row := by
  rcases row with ⟨expr, eq, sort⟩
  cases expr <;> simp [Row.toSerde, SerdeRow.decode]

/-- The root arena has no parent payload in this first representation. -/
inductive Parent
  deriving DecidableEq, Repr

/-- The only arena variant implemented by the Rust crate in this PR. -/
structure Arena where
  parent : Option Parent := none
  offset : Int64
  defs : Array Row
  deriving DecidableEq, Repr

namespace Arena

def empty : Arena := ⟨none, 0, #[]⟩

def length (arena : Arena) : Nat := arena.defs.size

def isEmpty (arena : Arena) : Bool := arena.defs.isEmpty

/-- Mathematical range check corresponding to Rust's `i64::checked_sub`. -/
def I64Valid (value : Int) : Prop :=
  -(2 ^ 63 : Int) ≤ value ∧ value < (2 ^ 63 : Int)

/-- Resolve an absolute signed index into the local definition array. -/
def row? (arena : Arena) (index : Int64) : Option Row := do
  let relative := index.toInt - arena.offset.toInt
  if _ : -(2 ^ 63 : Int) ≤ relative then
    if _ : relative < (2 ^ 63 : Int) then
      if _ : 0 ≤ relative then arena.defs[relative.toNat]?
      else none
    else none
  else none

def tag? (arena : Arena) (index : Int64) : Option Tag :=
  (arena.row? index).map fun row => row.expr.tag

def eq? (arena : Arena) (index : Int64) : Option Int64 :=
  (arena.row? index).bind Row.eq

def sort? (arena : Arena) (index : Int64) : Option Int64 :=
  (arena.row? index).bind Row.sort

/-- Equality claims are part of the Lean meaning of an arena.  Mathematical
integers avoid silently wrapping an oversized arena's derived local indices. -/
def eqClaimsFrom : Int → List Row → List (Int × Int)
  | _, [] => []
  | index, row :: rows =>
      (row.eq.map (fun right => (index, right.toInt))).toList ++
        eqClaimsFrom (index + 1) rows

def eqClaims (arena : Arena) : List (Int × Int) :=
  eqClaimsFrom arena.offset.toInt arena.defs.toList

/-- Syntactic-sort or term-type claims made by local rows. -/
def sortClaimsFrom : Int → List Row → List (Int × Int)
  | _, [] => []
  | index, row :: rows =>
      (row.sort.map (fun sort => (index, sort.toInt))).toList ++
        sortClaimsFrom (index + 1) rows

def sortClaims (arena : Arena) : List (Int × Int) :=
  sortClaimsFrom arena.offset.toInt arena.defs.toList

end Arena

/-! ## Forest meaning -/

abbrev Value := Nucleus.Hol.Ethane.Arena.Value NumericSig UInt64
abbrev Forest := Int → Option Value

def lookup (forest : Forest) (reference : Int64) : Option Value :=
  forest reference.toInt

/-- Interpret one expression row against a previously elaborated forest. -/
def Expr.elaborate (forest : Forest) : Expr → Option Value
  | .pair left right => return .pair (← lookup forest left) (← lookup forest right)
  | .kindStar => some (.kind .star)
  | .kindArr domain codomain => do
      match ← lookup forest domain, ← lookup forest codomain with
      | .kind domain, .kind codomain => some (.kind (.arr domain codomain))
      | _, _ => none
  | .boolTy => some (.syntax .boolTy)
  | .arr domain codomain => do
      match ← lookup forest domain, ← lookup forest codomain with
      | .syntax domain, .syntax codomain => some (.syntax (.arr domain codomain))
      | _, _ => none
  | .tyApp kinds arguments => do
      match ← lookup forest kinds, ← lookup forest arguments with
      | .pair (.kind domain) (.kind codomain),
          .pair (.syntax function) (.syntax argument) =>
          some (.syntax (.tyApp domain codomain function argument))
      | _, _ => none
  | .tyLam name kinds body => do
      match ← lookup forest kinds, ← lookup forest body with
      | .pair (.kind domain) (.kind codomain), .syntax body =>
          some (.syntax (.tyLam domain codomain name body))
      | _, _ => none
  | .tyFv name kind => do
      match ← lookup forest kind with
      | .kind kind => some (.syntax (.tyFv name kind))
      | _ => none
  | .tyExists name predicate => do
      match ← lookup forest predicate with
      | .syntax predicate => some (.syntax (.tyExists name predicate))
      | _ => none
  | .model name predicate => do
      match ← lookup forest predicate with
      | .syntax predicate => some (.syntax (.model name predicate))
      | _ => none
  | .primFam symbol kind => do
      match ← lookup forest kind with
      | .kind kind => some (.syntax (.primFam kind symbol))
      | _ => none
  | .primTm symbol => some (.syntax (.primTm symbol))
  | .tmFv name type => do
      match ← lookup forest type with
      | .syntax type => some (.syntax (.tmFv name type))
      | _ => none
  | .app function argument => do
      match ← lookup forest function, ← lookup forest argument with
      | .syntax function, .syntax argument => some (.syntax (.app function argument))
      | _, _ => none
  | .lam binder body => do
      match ← lookup forest binder, ← lookup forest body with
      | .syntax (.tmFv name domain), .syntax body =>
          some (.syntax (.lam name domain body))
      | _, _ => none
  | .bool value => some (.syntax (.bool value))
  | .eq type operands => do
      match ← lookup forest type, ← lookup forest operands with
      | .syntax type, .pair (.syntax left) (.syntax right) =>
          some (.syntax (.eq type left right))
      | _, _ => none
  | .eps type predicate => do
      match ← lookup forest type, ← lookup forest predicate with
      | .syntax type, .syntax predicate => some (.syntax (.eps type predicate))
      | _, _ => none

def Row.elaborate (forest : Forest) (row : Row) : Option Value :=
  row.expr.elaborate forest

private def set (forest : Forest) (index : Int) (value : Option Value) : Forest :=
  fun wanted => if wanted = index then value else forest wanted

def elaborateRows : Forest → Int → List Row → Forest
  | forest, _, [] => forest
  | forest, index, row :: rows =>
      elaborateRows (set forest index (row.elaborate forest)) (index + 1) rows

/-- The partial Ethane forest denoted by the raw arena. -/
def Arena.forest (arena : Arena) : Forest :=
  elaborateRows (fun _ => none) arena.offset.toInt arena.defs.toList

def Arena.value? (arena : Arena) (index : Int64) : Option Value :=
  arena.forest index.toInt

def Arena.expression? (arena : Arena) (index : Int64) : Option (Syn NumericSig UInt64) := do
  match ← arena.value? index with
  | .syntax expression => some expression
  | .kind _ | .pair _ _ => none

end Nucleus.Hol.Ethane.Dense
