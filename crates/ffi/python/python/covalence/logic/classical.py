"""Owned classical syntax, checked arenas, and universal syllogisms."""

from collections.abc import Callable
from typing import TypeVar

from .._covalence import (
    ClassicalArena as Arena,
)
from .._covalence import (
    ClassicalCheckedArena as CheckedArena,
)
from .._covalence import (
    ClassicalFormula as Formula,
)
from .._covalence import (
    ClassicalFormulaView as FormulaView,
)
from .._covalence import (
    ClassicalKernel,
    Cnf,
    Dnf,
    Refutation,
)
from .._covalence import (
    ClassicalModelWitness as ModelWitness,
)
from .._covalence import (
    ClassicalPath as Path,
)
from .._covalence import (
    ClassicalSequent as Sequent,
)
from .._covalence import (
    ClassicalSequentView as SequentView,
)
from .._covalence import (
    ClassicalTheorem as Theorem,
)

__all__ = [
    "Arena",
    "CheckedArena",
    "ClassicalKernel",
    "Cnf",
    "Dnf",
    "Formula",
    "FormulaView",
    "ModelWitness",
    "Path",
    "Refutation",
    "Sequent",
    "SequentView",
    "Theorem",
    "contradiction",
    "dedup",
    "sort_by_key",
]

_K = TypeVar("_K")


def _formula_at(theorem: Theorem, path: Path) -> Formula:
    sequent = theorem.sequents[path.sequent]
    formula = sequent.premise if path.side == "left" else sequent.conclusion
    for index in path.indices:
        formula = formula.children[index]
    return formula


def sort_by_key(
    theorem: Theorem,
    path: Path,
    key: Callable[[Formula], _K],
) -> None:
    """Sort one junction using an untrusted Python key function.

    The kernel checks the resulting index permutation before applying it.
    """
    formula = _formula_at(theorem, path)
    children = formula.children
    order = sorted(range(len(children)), key=lambda index: key(children[index]))
    theorem.permute(path, order)


def contradiction(theorem: Theorem, path: Path) -> None:
    """Find complementary children and ask the kernel to check them."""
    children = _formula_at(theorem, path).children
    for first, formula in enumerate(children):
        complement = formula.negated()
        for second in range(first + 1, len(children)):
            if children[second] == complement:
                theorem.contradiction_local(path, first, second)
                return
    raise ValueError("junction has no complementary children")


def dedup(theorem: Theorem, path: Path) -> None:
    """Remove repeated children through checked local deduplication."""
    children = _formula_at(theorem, path).children
    index = 0
    while index < len(children):
        retain = next(
            (prior for prior in range(index) if children[prior] == children[index]),
            None,
        )
        if retain is None:
            index += 1
        else:
            theorem.dedup_local(path, index, retain)
            children.pop(index)
