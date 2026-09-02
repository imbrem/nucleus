import Mathlib.Data.Fin.Basic

/-!
# WebAssembly integer words

The small WebAssembly reference models share only the mathematical carrier for
an `i32`: an unsigned residue modulo `2^32`. Syntax and execution remain local
to each model so their agreement is not true merely by definition.
-/

namespace Nucleus.Wasm

/-- A WebAssembly `i32`, represented by its 32 bits. -/
abbrev I32 := Fin (2 ^ 32)

/-- WebAssembly integer addition wraps modulo `2^32`. -/
def i32Add (left right : I32) : I32 := left + right

/-- The residue representation makes the selected SpecTec `$iadd_(32, ...)`
equation explicit. -/
@[simp] theorem i32Add_val (left right : I32) :
    (i32Add left right).val = (left.val + right.val) % (2 ^ 32 : Nat) := by
  rfl

end Nucleus.Wasm
