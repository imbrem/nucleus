import Nucleus.Hol.Propane.Syntax

/-!
# Fixed equality-only definitions of Boolean builtin constants

These are the de Bruijn spellings of Rust `Kernel::boolean_definition` and
its `not_tm`, `and_tm`, `or_tm`, and `imp_tm` helpers. No caller-supplied name,
initialization manifest, or definition package supplies builtin meaning.
-/

namespace Nucleus.Hol.Propane

def Tm.booleanNot (term : Tm Γ .bool) : Tm Γ .bool := .eq term (.bool false)

def Tm.booleanAnd (left right : Tm Γ .bool) : Tm Γ .bool :=
  .eq
    (.lam (.app (.app (.bv (.zero : Var ((.arr .bool (.arr .bool .bool)) :: Γ)
      (.arr .bool (.arr .bool .bool)))) (left.rename weakenRen)) (right.rename weakenRen)))
    (.lam (.app (.app (.bv .zero) (.bool true)) (.bool true)))

def Tm.booleanOr (left right : Tm Γ .bool) : Tm Γ .bool :=
  (left.booleanNot.booleanAnd right.booleanNot).booleanNot

def Tm.booleanImp (left right : Tm Γ .bool) : Tm Γ .bool :=
  (left.booleanAnd right.booleanNot).booleanNot

@[reducible] def BoolOp.inputs (op : BoolOp) : List LiteralTy :=
  List.replicate (if op = .not then 1 else 2) .bool

def BoolOp.term (op : BoolOp) : Tm Γ (Ty.arrows op.inputs .bool) :=
  .builtin (.bool op) rfl

def BoolOp.definition : (op : BoolOp) → Tm Γ (Ty.arrows op.inputs .bool)
  | .not => .lam ((Tm.bv .zero).booleanNot)
  | .and => .lam (.lam ((Tm.bv (.succ .zero)).booleanAnd (.bv .zero)))
  | .or => .lam (.lam ((Tm.bv (.succ .zero)).booleanOr (.bv .zero)))
  | .imp => .lam (.lam ((Tm.bv (.succ .zero)).booleanImp (.bv .zero)))
  | .iff => .lam (.lam (.eq (.bv (.succ .zero)) (.bv .zero)))

end Nucleus.Hol.Propane
