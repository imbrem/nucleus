import Nucleus.HolSurface.Cbor

/-! # Exact Lean model of Rust's static v0 initialization arena -/

namespace Nucleus.HolSurface.Init

private def r (value : Nat) (positive : 0 < value := by omega)
    (bounded : value ≤ maxRef := by decide) : Ref :=
  ⟨value, positive, bounded⟩

def defs : List Expr := [
  .kindStar,
  .tyBool,
  .tmBool false,
  .tmBool true,
  .tmBv 0,
  .tmEq (r 2) (r 5) (r 3),
  .tmLam (r 2) (r 6),
  .tyArr (r 2) (r 2),
  .tyArr (r 2) (r 8),
  .tmBv 0,
  .tmBv 2,
  .tmApp (r 10) (r 11),
  .tmBv 1,
  .tmApp (r 12) (r 13),
  .tmLam (r 9) (r 14),
  .tmBv 0,
  .tmApp (r 16) (r 4),
  .tmApp (r 17) (r 4),
  .tmLam (r 9) (r 18),
  .tyArr (r 9) (r 2),
  .tmEq (r 20) (r 15) (r 19),
  .tmLam (r 2) (r 21),
  .tmLam (r 2) (r 22),
  .tmBv 1,
  .tmApp (r 7) (r 24),
  .tmBv 0,
  .tmApp (r 7) (r 26),
  .tmApp (r 23) (r 25),
  .tmApp (r 28) (r 27),
  .tmApp (r 7) (r 29),
  .tmLam (r 2) (r 30),
  .tmLam (r 2) (r 31),
  .tyBv 0,
  .tyArr (r 33) (r 33),
  .tmBv 3,
  .tmBv 1,
  .tmBv 0,
  .tmApp (r 35) (r 36),
  .tmApp (r 35) (r 37),
  .tmEq (r 33) (r 38) (r 39),
  .tmEq (r 33) (r 36) (r 37),
  .tmEq (r 2) (r 40) (r 41),
  .tyArr (r 33) (r 2),
  .tmLam (r 33) (r 42),
  .tmLam (r 33) (r 4),
  .tmEq (r 43) (r 44) (r 45),
  .tyArr (r 33) (r 2),
  .tmLam (r 33) (r 46),
  .tmLam (r 33) (r 4),
  .tmEq (r 47) (r 48) (r 49),
  .tmBv 2,
  .tmBv 1,
  .tmBv 0,
  .tmApp (r 51) (r 53),
  .tmEq (r 33) (r 54) (r 52),
  .tmApp (r 7) (r 55),
  .tyArr (r 33) (r 2),
  .tmLam (r 33) (r 56),
  .tmLam (r 33) (r 4),
  .tmEq (r 57) (r 58) (r 59),
  .tmApp (r 23) (r 50),
  .tmApp (r 61) (r 60),
  .tmLam (r 33) (r 62),
  .tmEps (r 33) (r 63),
  .tmApp (r 63) (r 64),
  .tmLam (r 34) (r 65),
  .tmEps (r 34) (r 66),
  .tmApp (r 66) (r 67),
  .tyExists (r 68),
  .tyModel (r 68),
  .tyArr (r 70) (r 70),
  .tmBv 3,
  .tmBv 1,
  .tmBv 0,
  .tmApp (r 72) (r 73),
  .tmApp (r 72) (r 74),
  .tmEq (r 70) (r 75) (r 76),
  .tmEq (r 70) (r 73) (r 74),
  .tmEq (r 2) (r 77) (r 78),
  .tyArr (r 70) (r 2),
  .tmLam (r 70) (r 79),
  .tmLam (r 70) (r 4),
  .tmEq (r 80) (r 81) (r 82),
  .tyArr (r 70) (r 2),
  .tmLam (r 70) (r 83),
  .tmLam (r 70) (r 4),
  .tmEq (r 84) (r 85) (r 86),
  .tmBv 2,
  .tmBv 1,
  .tmBv 0,
  .tmApp (r 88) (r 90),
  .tmEq (r 70) (r 91) (r 89),
  .tmApp (r 7) (r 92),
  .tyArr (r 70) (r 2),
  .tmLam (r 70) (r 93),
  .tmLam (r 70) (r 4),
  .tmEq (r 94) (r 95) (r 96),
  .tmApp (r 23) (r 87),
  .tmApp (r 98) (r 97),
  .tmLam (r 70) (r 99),
  .tmEps (r 70) (r 100),
  .tmApp (r 100) (r 101),
  .tmLam (r 71) (r 102),
  .tmEps (r 71) (r 103),
  .tmBv 1,
  .tmBv 0,
  .tmApp (r 104) (r 105),
  .tmApp (r 104) (r 106),
  .tmEq (r 70) (r 107) (r 108),
  .tmEq (r 70) (r 105) (r 106),
  .tmEq (r 2) (r 109) (r 110),
  .tyArr (r 70) (r 2),
  .tmLam (r 70) (r 111),
  .tmLam (r 70) (r 4),
  .tmEq (r 112) (r 113) (r 114),
  .tyArr (r 70) (r 2),
  .tmLam (r 70) (r 115),
  .tmLam (r 70) (r 4),
  .tmEq (r 116) (r 117) (r 118),
  .tmBv 1,
  .tmBv 0,
  .tmApp (r 104) (r 121),
  .tmEq (r 70) (r 122) (r 120),
  .tmApp (r 7) (r 123),
  .tyArr (r 70) (r 2),
  .tmLam (r 70) (r 124),
  .tmLam (r 70) (r 4),
  .tmEq (r 125) (r 126) (r 127),
  .tmApp (r 23) (r 119),
  .tmApp (r 129) (r 128),
  .tmLam (r 70) (r 130),
  .tmEps (r 70) (r 131)
]

def arena : StaticArena := ⟨none, ⟨[]⟩, 1, ⟨defs⟩⟩

def boolTy : Ref := r 2
def false_ : Ref := r 3
def true_ : Ref := r 4
def not : Ref := r 7
def and : Ref := r 23
def or : Ref := r 32
def infinity : Ref := r 69
def natTy : Ref := r 70
def succ : Ref := r 104
def zero : Ref := r 132

@[simp] theorem infinity_definition : defs[68]? = some (.tyExists (r 68)) := rfl

@[simp] theorem nat_model_definition : defs[69]? = some (.tyModel (r 68)) := rfl

@[simp] theorem succ_definition : defs[103]? = some (.tmEps (r 71) (r 103)) := rfl

@[simp] theorem zero_definition : defs[131]? = some (.tmEps (r 70) (r 131)) := rfl

@[simp] theorem cbor_roundtrip : Cbor.decodeArena? (Cbor.encodeStaticArena arena) =
    some arena.toOwned := Cbor.decodeArena?_encodeStatic arena

def IsLiteral : Expr → Bool
  | .tmNat _ | .tmBytes _ => true
  | _ => false

set_option maxRecDepth 10000 in
theorem defs_literal_free : ∀ expression ∈ defs, IsLiteral expression = false := by
  decide

end Nucleus.HolSurface.Init
