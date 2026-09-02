from pathlib import Path

import pytest
from covalence.logic.alethe import AletheError, check_qf_uf, solve_qf_uf

FIXTURE = (
    Path(__file__).parents[3]
    / "proof"
    / "alethe"
    / "tests"
    / "fixtures"
    / "cvc5-qf-uf"
)
PROBLEM = (FIXTURE / "problem.smt2").read_text()
PROOF = (FIXTURE / "proof.alethe").read_text()


def test_checks_cvc5_output() -> None:
    checked = check_qf_uf(PROBLEM, f"unsat\n(\n{PROOF}\n)")
    assert checked.theorem > 0
    assert len(checked.assertions) == 3
    assert checked.kernel_len > 0


def test_rejects_non_refutation_output() -> None:
    with pytest.raises(AletheError, match="unsat status"):
        check_qf_uf(PROBLEM, "sat\n")


def test_solves_qf_uf_with_cvc5() -> None:
    result = solve_qf_uf(PROBLEM)
    assert result.refutation.theorem > 0
    assert result.proof_output.startswith("unsat\n")
    assert result.version.startswith("cvc5 ")
    assert "--proof-format-mode=alethe" in result.options
