from __future__ import annotations

import shutil
from typing import Any

import pytest
from covalence.logic.classical import ClassicalKernel, Cnf, Dnf, Refutation
from covalence.logic.hol import Kernel
from covalence.logic.lrat import (
    read_theorem,
    replay_into_classical,
    replay_into_syllogisms,
    replay_into_theorems,
    solve_cadical,
)

DIMACS = b"p cnf 1 2\n1 0\n-1 0\n"
TEXT_LRAT = "3 0 1 2 0\n"
BINARY_LRAT = bytes([ord("a"), 6, 0, 2, 4, 0])


def assert_refutation_sequent(theorem: Any) -> None:
    assert theorem.premise.kind == "and" and theorem.premise.children == []
    assert theorem.conclusion.kind == "sat" and theorem.conclusion.negative


def test_non_normal_matrices_and_both_lrat_encodings() -> None:
    cnf = Cnf([[2, 1, 2], [2, 1, 2]])
    dnf = Dnf([[-1, -2, -1]])
    assert cnf.rows == [[2, 1, 2], [2, 1, 2]]
    assert dnf.rows == [[-1, -2, -1]]
    cnf.normalize()
    dnf.normalize()
    assert cnf.rows == [[1, 2]]
    assert dnf.rows == [[-2, -1]]

    problem = Cnf.from_dimacs(DIMACS)
    assert Cnf.from_binary_dimacs(problem.to_binary_dimacs()).rows == problem.rows
    text = Refutation.from_text_lrat(problem, TEXT_LRAT)
    binary = Refutation.from_binary_lrat(problem, BINARY_LRAT)
    assert text.cnf.rows == binary.cnf.rows == [[1], [-1]]


def test_refutations_copy_into_all_three_checked_targets() -> None:
    refutation = Refutation.from_text_lrat(Cnf.from_dimacs(DIMACS), TEXT_LRAT)
    classical = ClassicalKernel()
    theorem = classical.copy_refutation(refutation)
    assert_refutation_sequent(classical.theorem(theorem))
    assert_refutation_sequent(read_theorem(Cnf.from_dimacs(DIMACS), TEXT_LRAT).sequents[0])

    hol = Kernel()
    assert hol.copy_refutation_to_syllogisms(refutation) == 1
    theorem = hol.copy_refutation_to_theorems(refutation)
    assert hol.theorem(theorem) == ([[1], [-1]], [])

    problem = Cnf.from_dimacs(DIMACS)
    assert_refutation_sequent(replay_into_classical(problem, TEXT_LRAT).theorem(1))
    hol = Kernel()
    assert replay_into_syllogisms(hol, problem, BINARY_LRAT, binary=True) == 1
    theorem = replay_into_theorems(hol, problem, TEXT_LRAT)
    assert hol.theorem(theorem) == ([[1], [-1]], [])


@pytest.mark.skipif(shutil.which("cadical") is None, reason="CaDiCaL is unavailable")
@pytest.mark.parametrize("binary", [False, True])
def test_cadical_full_replay(binary: bool) -> None:
    refutation = solve_cadical(Cnf.from_dimacs(DIMACS), binary=binary)
    assert refutation.cnf.rows == [[1], [-1]]


@pytest.mark.skipif(shutil.which("cadical") is None, reason="CaDiCaL is unavailable")
def test_cadical_replays_a_nontrivial_pigeonhole_refutation() -> None:
    rows = [
        [1, 2],
        [3, 4],
        [5, 6],
        [-1, -2],
        [-3, -4],
        [-5, -6],
        [-1, -3],
        [-1, -5],
        [-3, -5],
        [-2, -4],
        [-2, -6],
        [-4, -6],
    ]
    assert solve_cadical(Cnf(rows)).cnf.rows == rows
