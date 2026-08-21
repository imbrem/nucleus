"""Build the first persistent HOL kernel slice from Python."""

from covalence.logic.hol import Kernel

empty = Kernel.empty()
with_type, bool_ty = empty.bool_ty()
with_false, false_term = with_type.bool_const(False)
with_true, true_term = with_false.bool_const(True)

print(type(bool_ty).__name__, type(false_term).__name__, type(true_term).__name__)
print(type(empty).__name__, type(with_true).__name__)
