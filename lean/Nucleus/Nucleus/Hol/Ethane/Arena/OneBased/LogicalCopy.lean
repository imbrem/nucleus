import Nucleus.Hol.Ethane.Arena.OneBased.Copy
import Nucleus.Hol.Ethane.LogicalOpcode

/-!
# Opcode-lowering cross-kernel copy

This module specifies the checked transport used by the Rust
`copy_terms_lowered_from` API. It strengthens ordinary denotation-preserving
DAG copy with the representation guarantee that every newly appended row is
free of compact logical opcodes. `LogicalOpcode` proves that the replacement
applications have exactly the opcode rows' existing HOL denotation.
-/

namespace Nucleus.Hol.Ethane.OneBased

set_option relaxedAutoImplicit true

/-- A raw row is in the opcode-free init vocabulary. -/
def detail.Expr.OpcodeFree : detail.Expr → Prop
  | .op1 .. | .op2 .. => False
  | _ => True

/-- One resident arena row is not a compact logical opcode. -/
def OpcodeFreeAt (arena : Arena) (reference : Ref) : Prop :=
  ∀ row, arena.row? reference = some row → row.OpcodeFree

/-- Observable contract of a successful recursively lowered copy.

The inherited `CopyResult` supplies root correspondence, prefix identity,
typing, structural validity, and denotation preservation. `baseLength` is the
destination length before the transactional operation; every row appended by
the operation, including the partial application introduced for a binary
opcode, is opcode-free. -/
structure LogicalCopyResult (resolve : Resolver) (source destination : Arena)
    extends CopyResult resolve source destination where
  baseLength : Nat
  appendedOpcodeFree : ∀ reference,
    baseLength < reference.value.toNat →
    reference.value.toNat ≤ destination.dense.defs.length →
    OpcodeFreeAt destination reference

namespace LogicalCopyResult

/-- A mapped source row allocated after the old destination boundary is
represented without compact logical opcodes. -/
theorem mapped_opcode_free
    (copy : LogicalCopyResult resolve source destination)
    {reference : Ref}
    (newRow : copy.baseLength < (copy.map reference).value.toNat)
    (resident : (copy.map reference).value.toNat ≤ destination.dense.defs.length) :
    OpcodeFreeAt destination (copy.map reference) :=
  copy.appendedOpcodeFree (copy.map reference) newRow resident

/-- Lowered copy retains the ordinary copy theorem that every resolved source
value is denoted by its mapped destination row. For opcode rows this combines
with `LogicalOpcode.op1_eval_iff_lower` or `op2_eval_iff_lower`: changing the
physical row does not change its HOL meaning. -/
theorem denotation_preserved
    (copy : LogicalCopyResult resolve source destination)
    {reference : Ref} {value : Value}
    (denotes : Resolves resolve source reference value) :
    Resolves resolve destination (copy.map reference) value :=
  copy.toCopyResult.denotation_preserved denotes

/-- Inline classifier typing is inherited unchanged from ordinary checked
cross-kernel copy. -/
theorem typing_preserved
    (copy : LogicalCopyResult resolve source destination)
    {reference : Ref}
    (typed : SortingClaim resolve source reference) :
    SortingClaim resolve destination (copy.map reference) :=
  copy.toCopyResult.typing_preserved typed

end LogicalCopyResult

end Nucleus.Hol.Ethane.OneBased
