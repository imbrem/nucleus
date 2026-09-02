"""Generate Alethe with cvc5 and replay it through the checked HOL kernel."""

import subprocess
from dataclasses import dataclass

from .._covalence import AletheError, QfUfRefutation, check_qf_uf

__all__ = [
    "AletheError",
    "Cvc5Result",
    "QfUfRefutation",
    "check_qf_uf",
    "solve_qf_uf",
]

_PROOF_OPTIONS = (
    "--produce-proofs",
    "--proof-format-mode=alethe",
    "--proof-granularity=dsl-rewrite-strict",
    "--no-proof-allow-trust",
    "--dump-proofs",
    "--lang=smt2",
)


@dataclass(frozen=True, slots=True)
class Cvc5Result:
    """Checked result plus the untrusted bytes and solver provenance."""

    refutation: QfUfRefutation
    problem: str
    proof_output: str
    executable: str
    version: str
    options: tuple[str, ...]


def solve_qf_uf(problem: str, executable: str = "cvc5") -> Cvc5Result:
    """Run cvc5 synchronously and check its QF_UF Alethe refutation."""
    if not isinstance(problem, str):
        raise TypeError("SMT-LIB problem must be str")
    result = subprocess.run(
        [executable, *_PROOF_OPTIONS],
        input=problem,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        message = result.stderr.strip()
        raise AletheError(message or f"cvc5 exited with status {result.returncode}")
    refutation = check_qf_uf(problem, result.stdout)
    version_result = subprocess.run(
        [executable, "--version"],
        capture_output=True,
        text=True,
        check=False,
    )
    version = (
        version_result.stdout.splitlines()[0] if version_result.stdout else "unknown"
    )
    return Cvc5Result(
        refutation=refutation,
        problem=problem,
        proof_output=result.stdout,
        executable=executable,
        version=version,
        options=_PROOF_OPTIONS,
    )
