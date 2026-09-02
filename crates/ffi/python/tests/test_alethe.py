from pathlib import Path

import pytest
from covalence.logic.alethe import AletheError, check_qf_uf, solve_qf_uf

FIXTURE = (
    Path(__file__).parents[3] / "proof" / "alethe" / "tests" / "fixtures" / "cvc5-qf-uf"
)
PROBLEM = (FIXTURE / "problem.smt2").read_text()
PROOF = (FIXTURE / "proof.alethe").read_text()
ITE_PROBLEM = """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const p Bool)
(assert p)
(assert (not (= (ite p a b) a)))
(check-sat)
"""


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
    assert "--proof-granularity=dsl-rewrite-strict" in result.options
    assert "--no-proof-allow-trust" in result.options


def test_solves_semantic_ite_with_cvc5() -> None:
    result = solve_qf_uf(ITE_PROBLEM)
    assert result.refutation.theorem > 0
    assert len(result.refutation.assertions) == 2
    assert "ite-true-cond" in result.proof_output
