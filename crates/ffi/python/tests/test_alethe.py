import inspect
import subprocess
from pathlib import Path

import pytest
from covalence.logic import alethe
from covalence.logic.alethe import (
    AletheError,
    QfUfRefutation,
    check_qf_uf,
    solve_qf_uf,
)
from covalence.logic.hol import Kernel

FIXTURE = (
    Path(__file__).parents[3] / "proof" / "alethe" / "tests" / "fixtures" / "cvc5-qf-uf"
)
PROBLEM = (FIXTURE / "problem.smt2").read_text()
PROOF = (FIXTURE / "proof.alethe").read_text()
FINAL_STEP = "(step t4 (cl) :rule resolution :premises (a2 t3))"
LAST_ASSUMPTION = "(assume a2 (! (p b) :named @p_4))"
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


def output(proof: str) -> str:
    """Wrap an Alethe proof body the way cvc5 prints it."""
    return f"unsat\n(\n{proof}\n)"


def test_checks_cvc5_output() -> None:
    checked = check_qf_uf(PROBLEM, output(PROOF))
    assert checked.theorem > 0
    assert len(checked.assertions) == 3
    assert checked.kernel_len > 0


def test_rejects_non_refutation_output() -> None:
    with pytest.raises(AletheError, match="unsat status"):
        check_qf_uf(PROBLEM, "sat\n")


def test_rejects_a_proof_without_the_empty_clause() -> None:
    """The refutation is the final step, not the steps that lead to it."""
    truncated = PROOF.replace(FINAL_STEP, "")
    assert FINAL_STEP not in truncated
    with pytest.raises(AletheError, match="does not derive the empty clause"):
        check_qf_uf(PROBLEM, output(truncated))


def test_rejects_a_forged_final_clause() -> None:
    forged = PROOF.replace("(step t4 (cl)", "(step t4 (cl @p_4)")
    with pytest.raises(AletheError, match="derived clause"):
        check_qf_uf(PROBLEM, output(forged))


def test_rejects_an_assumption_the_problem_does_not_assert() -> None:
    smuggled = PROOF.replace(LAST_ASSUMPTION, f"{LAST_ASSUMPTION}\n(assume a3 (= b a))")
    assert "(assume a3 " in smuggled
    with pytest.raises(AletheError, match="not asserted by the requested problem"):
        check_qf_uf(PROBLEM, output(smuggled))


def test_rejects_a_proof_for_a_different_problem() -> None:
    """The proof is checked against the problem the caller asked about."""
    other = PROBLEM.replace("(assert (p b))", "(assert (p a))")
    assert other != PROBLEM
    with pytest.raises(AletheError, match="not asserted by the requested problem"):
        check_qf_uf(other, output(PROOF))
    with pytest.raises(AletheError):
        check_qf_uf(ITE_PROBLEM, output(PROOF))


def test_rejects_a_hole_step() -> None:
    """A trusted cvc5 step has no checked replay, whatever it concludes."""
    holed = PROOF.replace(
        FINAL_STEP, '(step t4 (cl) :rule hole :args ("untranslated rewrite"))'
    )
    with pytest.raises(AletheError, match='rule "hole"'):
        check_qf_uf(PROBLEM, output(holed))


def test_a_refutation_cannot_be_built_from_python() -> None:
    with pytest.raises(TypeError):
        QfUfRefutation()


def test_indices_address_the_refutation_kernel() -> None:
    checked = check_qf_uf(PROBLEM, output(PROOF))
    kernel = checked.kernel()
    assert checked.kernel() is kernel
    assert isinstance(kernel, Kernel)
    assert checked.theorem_in(kernel) == checked.theorem
    assert checked.assertions_in(kernel) == checked.assertions
    premises, conclusions = kernel.theorem(checked.theorem)
    assert sorted(premises) == sorted([literal] for literal in checked.assertions)
    assert conclusions == []


def test_rejects_indices_read_against_another_kernel() -> None:
    checked = check_qf_uf(PROBLEM, output(PROOF))
    other = check_qf_uf(PROBLEM, output(PROOF))
    for foreign in (Kernel(), other.kernel()):
        with pytest.raises(AletheError, match="different kernel"):
            checked.theorem_in(foreign)
        with pytest.raises(AletheError, match="different kernel"):
            checked.assertions_in(foreign)


class _FakeRun:
    """Records every argv `solve_qf_uf` builds and answers with fixed output."""

    def __init__(self, stdout: str = output(PROOF), returncode: int = 0) -> None:
        self.commands: list[list[str]] = []
        self.timeouts: list[float | None] = []
        self.stdout = stdout
        self.returncode = returncode

    def __call__(
        self, command: list[str], **options: object
    ) -> subprocess.CompletedProcess[str]:
        self.commands.append(list(command))
        self.timeouts.append(options.get("timeout"))  # type: ignore[arg-type]
        if command[1:] == ["--version"]:
            return subprocess.CompletedProcess(command, 0, "cvc5 version 1.3.4\n", "")
        return subprocess.CompletedProcess(
            command, self.returncode, self.stdout, "solver said no\n"
        )


def test_the_caller_cannot_weaken_the_required_flags(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The solver argv is the module's, not the caller's."""
    assert set(inspect.signature(solve_qf_uf).parameters) == {
        "problem",
        "executable",
        "timeout",
    }
    with pytest.raises(TypeError):
        solve_qf_uf(PROBLEM, options=("--proof-granularity=macro",))  # type: ignore[call-arg]

    fake = _FakeRun()
    monkeypatch.setattr(alethe.subprocess, "run", fake)
    result = solve_qf_uf(PROBLEM, "cvc5-under-test")
    assert result.refutation.theorem > 0
    assert fake.commands[0] == ["cvc5-under-test", *alethe._PROOF_OPTIONS]
    assert "--proof-granularity=dsl-rewrite" in fake.commands[0]
    assert "--no-proof-allow-trust" in fake.commands[0]
    assert all(timeout is not None for timeout in fake.timeouts)


def test_rejects_a_failed_solver_run(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(alethe.subprocess, "run", _FakeRun(returncode=1))
    with pytest.raises(AletheError, match="solver said no"):
        solve_qf_uf(PROBLEM)


def test_rejects_a_truncated_proof(monkeypatch: pytest.MonkeyPatch) -> None:
    """A partial proof is output like any other: it has to replay."""
    truncated = output(PROOF)[: len(output(PROOF)) // 2]
    monkeypatch.setattr(alethe.subprocess, "run", _FakeRun(stdout=truncated))
    with pytest.raises(AletheError):
        solve_qf_uf(PROBLEM)


def test_bounds_the_solver_run(monkeypatch: pytest.MonkeyPatch) -> None:
    def expire(command: list[str], **options: object) -> None:
        raise subprocess.TimeoutExpired(command, 0.5)

    monkeypatch.setattr(alethe.subprocess, "run", expire)
    with pytest.raises(AletheError, match="did not finish within"):
        solve_qf_uf(PROBLEM, timeout=0.5)


def test_solves_qf_uf_with_cvc5() -> None:
    result = solve_qf_uf(PROBLEM)
    assert result.refutation.theorem > 0
    assert result.proof_output.startswith("unsat\n")
    assert result.version.startswith("cvc5 ")
    assert "--proof-format-mode=alethe" in result.options
    assert "--proof-granularity=dsl-rewrite" in result.options
    assert "--no-proof-allow-trust" in result.options


def test_solves_semantic_ite_with_cvc5() -> None:
    result = solve_qf_uf(ITE_PROBLEM)
    assert result.refutation.theorem > 0
    assert len(result.refutation.assertions) == 2
    assert "ite-true-cond" in result.proof_output
