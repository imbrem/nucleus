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

# The whole solving argv, fixed here. There is deliberately no caller-facing
# option parameter: `--proof-granularity=dsl-rewrite` is what keeps cvc5 from
# emitting `hole` steps, and `--no-proof-allow-trust` refuses trusted steps at
# the source. Neither is the guarantee — replay rejects an unknown rule anyway —
# but both keep a checkable proof on stdout instead of an unreplayable one.
_PROOF_OPTIONS = (
    "--produce-proofs",
    "--proof-format-mode=alethe",
    "--proof-granularity=dsl-rewrite",
    "--no-proof-allow-trust",
    "--dump-proofs",
    "--lang=smt2",
)

#: Wall-clock bound on one solver run, in seconds.
DEFAULT_TIMEOUT = 300.0

_VERSION_TIMEOUT = 30.0


@dataclass(frozen=True, slots=True)
class Cvc5Result:
    """Checked result plus the untrusted bytes and solver provenance."""

    refutation: QfUfRefutation
    problem: str
    proof_output: str
    executable: str
    version: str
    options: tuple[str, ...]


def _run(
    command: list[str], input_text: str | None, timeout: float | None
) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command,
            input=input_text,
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as expired:
        raise AletheError(
            f"{command[0]} did not finish within {timeout} seconds"
        ) from expired
    except OSError as error:
        raise AletheError(f"could not run {command[0]}: {error}") from error


def solve_qf_uf(
    problem: str,
    executable: str = "cvc5",
    *,
    timeout: float | None = DEFAULT_TIMEOUT,
) -> Cvc5Result:
    """Run cvc5 synchronously and check its QF_UF Alethe refutation.

    The solver runs under `timeout` seconds with the fixed `_PROOF_OPTIONS`
    argv; the problem goes on stdin and never onto the command line. A
    non-zero exit, a timeout, or output that is not a replayable refutation
    all raise `AletheError`.
    """
    if not isinstance(problem, str):
        raise TypeError("SMT-LIB problem must be str")
    result = _run([executable, *_PROOF_OPTIONS], problem, timeout)
    if result.returncode != 0:
        message = result.stderr.strip()
        raise AletheError(message or f"cvc5 exited with status {result.returncode}")
    refutation = check_qf_uf(problem, result.stdout)
    version_result = _run([executable, "--version"], None, _VERSION_TIMEOUT)
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
