import Nucleus.Hol.Ethane.Arena.OneBased
import Nucleus.Hol.Ethane.Amber.Row

/-!
# Structural validity of one-based Ethane arenas

Only ordinary constructor operands are local graph edges.  Import IDs,
foreign references are not children. A dense arena is structurally valid when every local child
points to an earlier row.
-/

namespace Nucleus.Hol.Ethane.OneBased

/-- Non-edge row fields, in wire order. -/
inductive RowExtra where
  | nat (value : UInt64)
  | bool (value : Bool)
  | source (value : ImportId)
  | foreign (value : Ref)
  deriving DecidableEq

namespace detail.Expr

/-- Ordinary local children in constructor order. -/
def children : detail.Expr → List Ref
  | .kindStar | .boolTy | .bool _ | .tmRef .. | .tyRef .. | .kindRef .. => []
  | .kindArr left right | .tyArr left right | .tyApp left right |
      .tyLam left right | .app left right | .lam left right |
      .eps left right | .op2 _ left right => [left, right]
  | .eq type left right => [type, left, right]
  | .op1 _ child => [child]
  | .tyFv _ child | .tyExists _ child | .tyForall _ child | .model _ child |
      .tmFv _ child => [child]

@[simp] theorem children_tmRef (source : ImportId) (foreign : Ref) :
    (detail.Expr.tmRef source foreign).children = [] := rfl

@[simp] theorem children_tyRef (source : ImportId) (foreign : Ref) :
    (detail.Expr.tyRef source foreign).children = [] := rfl

@[simp] theorem children_kindRef (source : ImportId) (foreign : Ref) :
    (detail.Expr.kindRef source foreign).children = [] := rfl

theorem children_length_le_three (expression : detail.Expr) :
    expression.children.length ≤ 3 := by
  cases expression <;> simp [children]

end detail.Expr

namespace detail.Row

def children (row : detail.Row) : List Ref := row.expr.children

def extras (row : detail.Row) : List RowExtra :=
  let expression := match row.expr with
    | .tyFv name _ | .tyExists name _ | .tyForall name _ | .model name _ |
        .tmFv name _ => [.nat name]
    | .bool value => [.bool value]
    | .op1 op _ => [.nat op.code.toUInt64]
    | .op2 op _ _ => [.nat op.code.toUInt64]
    | .tmRef source foreign | .tyRef source foreign | .kindRef source foreign =>
        [.source source, .foreign foreign]
    | _ => []
  expression

end detail.Row

instance : Nucleus.Hol.Ethane.Amber.Row detail.Row Tag Ref RowExtra where
  tag row := row.expr.tag
  children := detail.Row.children
  extra := detail.Row.extras

/-- Every local child is among the already allocated one-based references. -/
def RowValid (allocated : Nat) (row : detail.Row) : Prop :=
  ∀ child ∈ row.children, child.value.toNat ≤ allocated

/-- Left-to-right validity of a dense row suffix. -/
def RowsValid : Nat → List detail.Row → Prop
  | _, [] => True
  | allocated, row :: rows =>
      RowValid allocated row ∧ RowsValid (allocated + 1) rows

/-- Structural validity of a self-contained one-based dense arena. -/
def Arena.syntaxRows (arena : Arena) : List detail.Row :=
  arena.dense.defs.map fun expr => { expr }

def Arena.StructurallyValid (arena : Arena) : Prop := RowsValid 0 arena.syntaxRows

/-- Whether a row can be appended to an arena. -/
def Arena.CanPush (arena : Arena) (row : detail.Row) : Prop :=
  RowValid arena.dense.defs.length row

/-- Append one raw row without claiming that it is logically valid. -/
def Arena.pushRaw (arena : Arena) (row : detail.Row) : Arena :=
  match arena with
  | .mk imports axs dense synFacts synFree ctx assume assert =>
      .mk imports axs { dense with defs := dense.defs ++ [row.expr] }
        synFacts synFree ctx assume assert

theorem rowsValid_append (allocated : Nat) (left right : List detail.Row) :
    RowsValid allocated (left ++ right) ↔
      RowsValid allocated left ∧ RowsValid (allocated + left.length) right := by
  induction left generalizing allocated with
  | nil => simp [RowsValid]
  | cons row left ih =>
      simp only [List.cons_append, RowsValid, List.length_cons]
      rw [ih (allocated + 1)]
      constructor
      · rintro ⟨rowValid, leftValid, rightValid⟩
        refine ⟨⟨rowValid, leftValid⟩, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rightValid
      · rintro ⟨⟨rowValid, leftValid⟩, rightValid⟩
        refine ⟨rowValid, leftValid, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rightValid

@[simp] theorem structurallyValid_pushRaw_iff (arena : Arena) (row : detail.Row) :
    (arena.pushRaw row).StructurallyValid ↔
      arena.StructurallyValid ∧ arena.CanPush row := by
  cases arena with
  | mk imports axs dense synFacts synFree ctx assume assert =>
      change RowsValid 0
          ((dense.defs ++ [row.expr]).map fun expr => detail.Row.mk expr) ↔
        RowsValid 0 (dense.defs.map fun expr => detail.Row.mk expr) ∧
          RowValid dense.defs.length row
      rw [List.map_append]
      change RowsValid 0
          (dense.defs.map (fun expr => detail.Row.mk expr) ++ [row]) ↔ _
      rw [rowsValid_append]
      simp [RowsValid]

theorem Arena.StructurallyValid.pushRaw {arena : Arena}
    (valid : arena.StructurallyValid) {row : detail.Row}
    (ready : arena.CanPush row) : (arena.pushRaw row).StructurallyValid :=
  (structurallyValid_pushRaw_iff arena row).2 ⟨valid, ready⟩

end Nucleus.Hol.Ethane.OneBased
