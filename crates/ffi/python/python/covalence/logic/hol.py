"""Raw and checked one-based Ethane arenas, plus reusable proof components."""

from __future__ import annotations

from .._covalence import AmbPred
from .._covalence import HolArena as Arena
from .._covalence import HolDefinition as Definition
from .._covalence import HolKernel as Kernel
from .._covalence import HolKind as Kind
from .._covalence import HolLink as Link
from .._covalence import HolStrategy as _Strategy
from .._covalence import HolRewriteResult as RewriteResult
from .._covalence import HolSynFact as SynFact
from .._covalence import HolTm as Tm
from .._covalence import HolTy as Ty
from ..lib.hash import O256

__all__ = [
    "Arena",
    "Definition",
    "Kernel",
    "RewriteResult",
    "Kind",
    "Link",
    "Strategy",
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


class Strategy:
    """One live proof component which may serve any number of requests.

    Omitting ``cas`` uses :func:`get_default_cas`; explicitly passing ``None``
    attaches no external provider. An O256 source always needs the selected CAS
    in order to retrieve and validate the component bytes.
    """

    __slots__ = ("_strategy",)

    def __init__(self, source: object, /, cas: object = _UNSET) -> None:
        selected = get_default_cas() if cas is _UNSET else cas
        self._strategy = _Strategy(source, cas=selected)

    def apply_tactic(
        self,
        tactic_id: int,
        arguments: bytes = b"",
        kernel: Kernel | None = None,
    ) -> Kernel:
        """Apply a compact strategy-local tactic atomically."""
        return self._strategy.apply_tactic(tactic_id, arguments, kernel)

    def apply_tactic_name(self, name: str, kernel: Kernel | None = None) -> Kernel:
        return self._strategy.apply_tactic_name(name, kernel)

    def prove_addr(self, addr: O256) -> Kernel:
        return self._strategy.prove_addr(addr)


def load_proof(source: object, /, cas: object = _UNSET) -> Kernel:
    """Instantiate ``source`` and request tactic zero with empty arguments."""
    return Strategy(source, cas=cas).apply_tactic(0)
