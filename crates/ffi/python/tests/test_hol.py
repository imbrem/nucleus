"""The Python HOL API is a thin, persistent wrapper over the Rust kernel."""

import pytest

from covalence.logic.hol import Kernel, Tm, Ty


def test_empty_and_boolean_operations_return_opaque_handles() -> None:
    empty = Kernel.empty()
    with_type, bool_ty = empty.bool_ty()
    with_false, false_term = with_type.bool_const(False)
    with_true, true_term = with_false.bool_const(True)

    assert isinstance(with_type, Kernel)
    assert isinstance(with_false, Kernel)
    assert isinstance(with_true, Kernel)
    assert isinstance(bool_ty, Ty)
    assert isinstance(false_term, Tm)
    assert isinstance(true_term, Tm)


def test_persistent_kernel_can_branch() -> None:
    empty = Kernel.empty()
    left, _ = empty.bool_const(False)
    right, _ = empty.bool_const(True)

    assert isinstance(left, Kernel)
    assert isinstance(right, Kernel)


@pytest.mark.parametrize("opaque", [Kernel, Ty, Tm])
def test_opaque_values_have_no_public_constructor(opaque: type[object]) -> None:
    with pytest.raises(TypeError):
        opaque()
