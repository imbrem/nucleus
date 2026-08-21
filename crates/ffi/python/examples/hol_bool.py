"""Build the first mutable HOL kernel slice from Python."""

from covalence.logic.hol import Kernel

kernel = Kernel.empty()
bool_ty = kernel.bool_ty()
false_term = kernel.bool_const(False)
true_term = kernel.bool_const(True)

print(type(bool_ty).__name__, type(false_term).__name__, type(true_term).__name__)
print(type(kernel).__name__)
