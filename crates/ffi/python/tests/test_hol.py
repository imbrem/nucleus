"""The Python HOL API is a thin, mutable wrapper over the Rust kernel."""

import pytest

from covalence.logic.hol import Kernel, Tm, Ty


def test_empty_and_boolean_operations_return_opaque_handles() -> None:
    kernel = Kernel.empty()
    bool_ty = kernel.bool_ty()
    false_term = kernel.bool_const(False)
    true_term = kernel.bool_const(True)

    assert isinstance(kernel, Kernel)
    assert isinstance(bool_ty, Ty)
    assert isinstance(false_term, Tm)
    assert isinstance(true_term, Tm)


def test_kernel_mutates_in_place() -> None:
    kernel = Kernel.empty()
    assert isinstance(kernel.bool_const(False), Tm)
    assert isinstance(kernel.bool_const(True), Tm)


@pytest.mark.parametrize("opaque", [Kernel, Ty, Tm])
def test_opaque_values_have_no_public_constructor(opaque: type[object]) -> None:
    with pytest.raises(TypeError):
        opaque()
