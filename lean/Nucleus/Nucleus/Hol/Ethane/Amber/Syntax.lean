import Nucleus.Hol.Ethane.Amber.Forest
import Nucleus.Hol.Ethane.Arena

/-!
# Ethane syntax rows in Amber

The existing Ethane arena row is the auditable constructor enum.  This file
gives it Amber's generic row interface and an exact checked projection from
the canonical `(tag, children, extra)` view.
-/

namespace Nucleus.Hol.Ethane.Amber

open Nucleus.Hol.Ethane
universe u
set_option relaxedAutoImplicit true

/-- Constructor tags contain no scalar payloads. -/
inductive SyntaxTag where
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
  deriving DecidableEq

/-- Non-recursive fields carried by Ethane syntax rows. -/
inductive SyntaxExtra (Sig : Signature.{u}) (Name : Type) where
  | name (value : Name)
  | fam (value : Σ kind, Sig (.kind kind))
  | tm (value : Sig .tm)
  | bool (value : Bool)

namespace SyntaxRow

abbrev T (Sig : Signature.{u}) (Name : Type) (Ix : Type := Int) :=
  Arena.Row Sig Name Ix
abbrev Extra (Sig : Signature.{u}) (Name : Type) := SyntaxExtra Sig Name
abbrev View (Sig : Signature.{u}) (Name : Type) (Ix : Type := Int) :=
  Row.View SyntaxTag Ix (Extra Sig Name)

/-- Separate the tag from all constructor payloads. -/
def tag : T Sig Name Ix → SyntaxTag
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

/-- Scalar fields in constructor order. -/
def extra : T Sig Name Ix → List (Extra Sig Name)
  | .tyLam name .. | .tyFv name .. | .tyExists name .. | .model name .. |
      .tmFv name .. | .lam name .. => [.name name]
  | @Arena.Row.primFam _ _ _ kind symbol _ => [.fam ⟨kind, symbol⟩]
  | .primTm symbol => [.tm symbol]
  | .bool value => [.bool value]
  | .pair .. | .kindStar | .kindArr .. | .boolTy | .arr .. | .tyApp .. |
      .app .. | .eq .. | .eps .. => []

instance : Row (T Sig Name Ix) SyntaxTag Ix (Extra Sig Name) where
  tag := tag
  children := Arena.Row.children
  extra := extra

@[simp] theorem row_tag (row : T Sig Name Ix) : Row.tag row = tag row := rfl

@[simp] theorem row_children (row : T Sig Name Ix) :
    Row.children row = Arena.Row.children row := rfl

@[simp] theorem row_extra (row : T Sig Name Ix) : Row.extra row = extra row := rfl

/-- Check a generic row view against the exact Ethane constructor arities and
payload variants. -/
def ofView? : View Sig Name Ix → Option (T Sig Name Ix)
  | ⟨.pair, [left, right], []⟩ => some (.pair left right)
  | ⟨.kindStar, [], []⟩ => some .kindStar
  | ⟨.kindArr, [domain, codomain], []⟩ => some (.kindArr domain codomain)
  | ⟨.boolTy, [], []⟩ => some .boolTy
  | ⟨.arr, [domain, codomain], []⟩ => some (.arr domain codomain)
  | ⟨.tyApp, [kinds, arguments], []⟩ => some (.tyApp kinds arguments)
  | ⟨.tyLam, [kinds, body], [.name name]⟩ => some (.tyLam name kinds body)
  | ⟨.tyFv, [kind], [.name name]⟩ => some (.tyFv name kind)
  | ⟨.tyExists, [predicate], [.name name]⟩ => some (.tyExists name predicate)
  | ⟨.model, [predicate], [.name name]⟩ => some (.model name predicate)
  | ⟨.primFam, [kindNode], [.fam ⟨_kind, symbol⟩]⟩ =>
      some (.primFam symbol kindNode)
  | ⟨.primTm, [], [.tm symbol]⟩ => some (.primTm symbol)
  | ⟨.tmFv, [type], [.name name]⟩ => some (.tmFv name type)
  | ⟨.app, [function, argument], []⟩ => some (.app function argument)
  | ⟨.lam, [domain, body], [.name name]⟩ => some (.lam name domain body)
  | ⟨.bool, [], [.bool value]⟩ => some (.bool value)
  | ⟨.eq, [type, operands], []⟩ => some (.eq type operands)
  | ⟨.eps, [type, predicate], []⟩ => some (.eps type predicate)
  | _ => none

@[simp] theorem ofView?_view (row : T Sig Name Ix) :
    ofView? (Row.view row) = some row := by
  cases row <;> rfl

end SyntaxRow

/-- Ethane rows elaborate using the existing, constructor-by-constructor
definition. -/
instance : Elaborates (Arena.Row Sig Name Nat) (Arena.Value Sig Name) Nat where
  elaborate := Arena.Row.elaborate

instance : Elaborates (Arena.Row Sig Name Int) (Arena.Value Sig Name) Int where
  elaborate := Arena.Row.elaborate

/-- An Amber forest of Ethane syntax rows. -/
abbrev SyntaxForest (Key : Type) (Sig : Signature.{u}) (Name : Type := Nat) :=
  Dense Key (Arena.Row Sig Name Nat)

namespace SyntaxForest

/-- Canonical self-contained postorder encoding of one Ethane expression. -/
def ofSyn (expression : Syn Sig Name) : SyntaxForest Key Sig Name :=
  ⟨none, (Arena.Encoder.run expression).rows⟩

/-- The canonical expression root is the final emitted row. -/
def root? (forest : SyntaxForest Key Sig Name) : Option Nat :=
  if forest.rows.isEmpty then none else some (forest.next - 1)

/-- Read an Ethane expression at one index of a resolved forest. -/
def expressionAt? (denotation : Dense.Denotation (Arena.Value Sig Name))
    (index : Nat) : Option (Syn Sig Name) := do
  match ← denotation.get index with
  | .syntax expression => some expression
  | .kind _ | .pair _ _ => none

@[simp] theorem ofSyn_offset (expression : Syn Sig Name) :
    (ofSyn (Key := Key) expression).offset = 0 := rfl

/-- The old encoder emits exactly one more row than its zero-based root. -/
theorem encoder_length_eq_root_succ (expression : Syn Sig Name) :
    (Arena.Encoder.run expression).rows.length =
      (Arena.Encoder.run expression).root + 1 := by
  let initial : Arena.Encoder.State Sig Name := ⟨0, []⟩
  cases encodedEq : Arena.Encoder.encode expression initial with
  | mk root state =>
      obtain ⟨suffix, rowsEq, nextEq, rootEq, _lookup⟩ :=
        Arena.Encoder.encode_correct expression initial
          (fun _ : Nat => (none : Option (Arena.Value Sig Name)))
      rw [encodedEq] at rowsEq nextEq rootEq
      simp only at rowsEq nextEq rootEq
      have runEq : Arena.Encoder.run expression = ⟨state.rows, root⟩ := by
        simp [Arena.Encoder.run, initial, encodedEq]
      rw [runEq]
      change state.rows.length = root + 1
      have rowsLength := congrArg List.length rowsEq
      simp [initial] at rowsLength nextEq
      omega

/-- The old encoder's public root is exactly its final emitted row. -/
theorem encoder_root_eq_last (expression : Syn Sig Name) :
    (Arena.Encoder.run expression).root =
      (Arena.Encoder.run expression).rows.length - 1 := by
  have lengthEq := encoder_length_eq_root_succ expression
  omega

@[simp] theorem root?_ofSyn (expression : Syn Sig Name) :
    root? (ofSyn (Key := Key) expression) =
      some (Arena.Encoder.run expression).root := by
  rw [root?]
  have lengthEq := encoder_length_eq_root_succ expression
  have rootEq := encoder_root_eq_last expression
  have nonempty : (Arena.Encoder.run expression).rows ≠ [] := by
    intro empty
    rw [empty] at lengthEq
    simp at lengthEq
  simp [ofSyn, Dense.next, nonempty, rootEq]

end SyntaxForest

end Nucleus.Hol.Ethane.Amber
