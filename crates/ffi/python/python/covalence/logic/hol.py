"""Raw and checked one-based Ethane arenas, plus reusable proof components."""

from __future__ import annotations

from .._covalence import AmbPred
from .._covalence import HolArena as Arena
from .._covalence import HolDefinition as Definition
from .._covalence import HolKernel as Kernel
from .._covalence import HolKind as Kind
from .._covalence import HolLink as Link
from .._covalence import HolProver as _Prover
from .._covalence import HolRewriteResult as RewriteResult
from .._covalence import HolSynFact as SynFact
from .._covalence import HolTm as Tm
from .._covalence import HolTy as Ty
from ..lib.hash import O256, ZERO_O256

__all__ = [
    "Arena",
    "Definition",
    "Kernel",
    "RewriteResult",
    "Kind",
    "Link",
    "Prover",
    "AmbPred",
    "SynFact",
    "Tm",
    "Ty",
    "get_default_cas",
    "load_proof",
    "set_default_cas",
]

_UNSET = object()
_default_cas: object | None = None


def get_default_cas() -> object | None:
    """Return the process-level external CAS used when `cas` is omitted."""
    return _default_cas


def set_default_cas(cas: object | None) -> None:
    """Set the process-level external CAS; `None` disables the default."""
    global _default_cas
    _default_cas = cas


class Prover:
    """One live proof component which may serve any number of requests.

    Omitting ``cas`` uses :func:`get_default_cas`; explicitly passing ``None``
    attaches no external provider. An O256 source always needs the selected CAS
    in order to retrieve and validate the component bytes.
    """

    __slots__ = ("_prover",)

    def __init__(self, source: object, /, cas: object = _UNSET) -> None:
        selected = get_default_cas() if cas is _UNSET else cas
        self._prover = _Prover(source, cas=selected)

    def prove(
        self,
        name: str | bytes | int | O256 | None = None,
        kernel: Kernel | None = None,
    ) -> Kernel:
        """Run one named request and atomically extend ``kernel`` on success."""
        return self._prover.prove(name, kernel)

    def prove_addr(self, name: O256, kernel: Kernel | None = None) -> Kernel:
        return self._prover.prove_addr(name, kernel)

    def prove_name(self, name: str, kernel: Kernel | None = None) -> Kernel:
        return self._prover.prove_name(name, kernel)

    def prove_bytes(self, name: bytes, kernel: Kernel | None = None) -> Kernel:
        return self._prover.prove_bytes(name, kernel)

    def prove_ix(self, ix: int, kernel: Kernel | None = None) -> Kernel:
        return self._prover.prove_ix(ix, kernel)


def load_proof(source: object, /, cas: object = _UNSET) -> Kernel:
    """Instantiate ``source`` and request the all-zero default target."""
    return Prover(source, cas=cas).prove(ZERO_O256, None)
