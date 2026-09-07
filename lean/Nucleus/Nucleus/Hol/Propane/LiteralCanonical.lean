import Nucleus.Hol.Propane.LiteralRegistryBuiltin

/-! # Canonical builtin aliases preserve signatures and mathematical evaluation -/

namespace Nucleus.Hol.Propane.LiteralRegistry

set_option maxRecDepth 8192

private theorem signatures_check : allBuiltins.all
    (fun op => (canonicalBuiltin op).signature == op.signature) = true := by decide

theorem canonical_signature (op : Builtin) : (canonicalBuiltin op).signature = op.signature := by
  exact beq_iff_eq.mp (List.all_eq_true.mp signatures_check op (allBuiltins_complete op))

private theorem idempotent_check : allBuiltins.all
    (fun op => canonicalBuiltin (canonicalBuiltin op) == canonicalBuiltin op) = true := by decide

theorem canonical_idempotent (op : Builtin) :
    canonicalBuiltin (canonicalBuiltin op) = canonicalBuiltin op := by
  exact beq_iff_eq.mp (List.all_eq_true.mp idempotent_check op (allBuiltins_complete op))

private theorem decode_i8 (bytes : List UInt8) :
    decodeWord .i8 .little bytes = decodeWord .i8 .big bytes := by
  cases bytes with
  | nil => rfl
  | cons byte rest =>
      cases rest with
      | nil => rfl
      | cons second rest => simp [decodeWord, Width.bits]

theorem canonical_evalRaw (op : Builtin) (args : List LiteralValue) :
    (canonicalBuiltin op).evalRaw args = op.evalRaw args := by
  cases op with
  | bool op => rfl
  | word width op => rfl
  | nat op => rfl
  | int op => rfl
  | bytes op =>
      cases op <;> try rfl
      all_goals rename_i width endian
      all_goals cases width <;> cases endian <;> try rfl
      all_goals simp [canonicalBuiltin, Builtin.evalRaw, BytesOp.eval, decode_i8]
  | cast op =>
      cases op <;> try rfl
      all_goals rename_i source target
      all_goals by_cases equal : source = target
      all_goals try { simp only [canonicalBuiltin, equal, ↓reduceIte] }
      all_goals subst target
      all_goals simp [canonicalBuiltin, Builtin.evalRaw, CastOp.eval,
        BitVec.ofNat_toNat, BitVec.ofInt_toInt]

theorem canonical_eval (op : Builtin) (args : List LiteralValue) :
    (canonicalBuiltin op).eval args = op.eval args := by
  simp only [Builtin.eval, canonical_signature, canonical_evalRaw]

end Nucleus.Hol.Propane.LiteralRegistry
