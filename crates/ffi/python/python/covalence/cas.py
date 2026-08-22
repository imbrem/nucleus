"""LCF-style whole-object CAS facts and userspace storage.

``CasAssertion`` is unchecked data. Its ``check()`` method hashes the complete
blob before returning an opaque ``CasFact``. Storage implementations remain
ordinary userspace code; only successful checking introduces a fact.
"""

from collections.abc import Buffer
from typing import Protocol

from ._covalence import (
    CasAddressMismatchError,
    CasAssertion,
    CasCheckError,
    CasDigestMismatchError,
    CasFact,
    CasLookupError,
    CasNotFoundError,
    IndexCas,
    get_checked,
)
from .lib.hash import O256


class Cas(Protocol):
    """A read-only source of untrusted content-addressed bytes."""

    def get(self, address: O256, /) -> Buffer:
        """Return complete bytes for ``address`` or raise an exception."""
        ...


class CheckedCas(Cas, Protocol):
    """A CAS able to avoid rehashing by returning checked facts."""

    def get_fact(self, address: O256, /) -> CasFact:
        """Return a checked candidate for ``address`` or raise an exception."""
        ...


__all__ = [
    "Cas",
    "CasAddressMismatchError",
    "CasAssertion",
    "CasCheckError",
    "CasDigestMismatchError",
    "CasFact",
    "CasLookupError",
    "CasNotFoundError",
    "CheckedCas",
    "IndexCas",
    "get_checked",
]
