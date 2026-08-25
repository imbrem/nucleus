"""Untrusted typed LRAT parsing.

Proof admission lives in userspace Rust and drives the checked HOL kernel.
"""

import subprocess
import tempfile
from pathlib import Path

from .._covalence import (
    LratError,
    RatGroup,
    Step,
    parse_binary,
    parse_text,
)
from .classical import ClassicalKernel, Cnf, Refutation
from .hol import Kernel

__all__ = [
    "LratError",
    "RatGroup",
    "Step",
    "parse_binary",
    "parse_text",
    "replay_into_classical",
    "replay_into_syllogisms",
    "replay_into_theorems",
    "solve_cadical",
    "solve_cadical_into_classical",
    "solve_cadical_into_syllogisms",
    "solve_cadical_into_theorems",
]


def _replay(cnf: Cnf, proof: str | bytes, binary: bool) -> Refutation:
    if binary:
        if not isinstance(proof, bytes):
            raise TypeError("binary LRAT must be bytes")
        return Refutation.from_binary_lrat(cnf, proof)
    if not isinstance(proof, str):
        raise TypeError("text LRAT must be str")
    return Refutation.from_text_lrat(cnf, proof)


def replay_into_classical(
    cnf: Cnf, proof: str | bytes, *, binary: bool = False
) -> ClassicalKernel:
    """Replay LRAT and return a classical kernel containing its certificate."""
    kernel = ClassicalKernel()
    kernel.copy_refutation(_replay(cnf, proof, binary))
    return kernel


def replay_into_syllogisms(
    kernel: Kernel, cnf: Cnf, proof: str | bytes, *, binary: bool = False
) -> int:
    """Replay LRAT and copy its certificate into a HOL syllogism arena."""
    return kernel.copy_refutation_to_syllogisms(_replay(cnf, proof, binary))


def replay_into_theorems(
    kernel: Kernel, cnf: Cnf, proof: str | bytes, *, binary: bool = False
) -> int:
    """Replay LRAT and copy its certificate into a HOL theorem arena."""
    return kernel.copy_refutation_to_theorems(_replay(cnf, proof, binary))


def solve_cadical(
    cnf: Cnf,
    executable: str = "cadical",
    *,
    binary: bool = True,
) -> Refutation:
    """Run CaDiCaL synchronously and replay its LRAT proof before returning it."""
    with tempfile.TemporaryDirectory(prefix="covalence-lrat-") as directory:
        root = Path(directory)
        problem = root / "problem.cnf"
        proof = root / "proof.lrat"
        problem.write_bytes(cnf.to_dimacs())
        command = [executable, "--lrat"]
        command.append("--binary" if binary else "--no-binary")
        command.extend([str(problem), str(proof)])
        result = subprocess.run(command, capture_output=True, check=False)
        if result.returncode == 10:
            raise LratError("CaDiCaL reports that the CNF is satisfiable")
        if result.returncode != 20:
            message = result.stderr.decode(errors="replace").strip()
            fallback = f"CaDiCaL exited with status {result.returncode}"
            raise LratError(message or fallback)
        encoded = proof.read_bytes()
        if binary:
            return Refutation.from_binary_lrat(cnf, encoded)
        return Refutation.from_text_lrat(cnf, encoded.decode("ascii"))


def solve_cadical_into_classical(
    cnf: Cnf, executable: str = "cadical", *, binary: bool = True
) -> ClassicalKernel:
    """Run CaDiCaL and return a classical kernel containing the certificate."""
    kernel = ClassicalKernel()
    kernel.copy_refutation(solve_cadical(cnf, executable, binary=binary))
    return kernel


def solve_cadical_into_syllogisms(
    kernel: Kernel,
    cnf: Cnf,
    executable: str = "cadical",
    *,
    binary: bool = True,
) -> int:
    """Run CaDiCaL and copy the certificate into a HOL syllogism arena."""
    refutation = solve_cadical(cnf, executable, binary=binary)
    return kernel.copy_refutation_to_syllogisms(refutation)


def solve_cadical_into_theorems(
    kernel: Kernel,
    cnf: Cnf,
    executable: str = "cadical",
    *,
    binary: bool = True,
) -> int:
    """Run CaDiCaL and copy the certificate into a HOL theorem arena."""
    refutation = solve_cadical(cnf, executable, binary=binary)
    return kernel.copy_refutation_to_theorems(refutation)
