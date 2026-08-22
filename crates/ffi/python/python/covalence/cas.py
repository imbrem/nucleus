"""LCF-style checked facts and ordinary userspace CAS providers.

``CasAssertion`` is unchecked data. Calling :meth:`CasAssertion.try_into`
hashes the complete blob in Rust and returns an opaque ``CasFact`` only when
the claim is true. ``MemoryCas`` and arbitrary Python providers are not part of
that trusted boundary; they can only return already checked facts.

The :class:`TrustedCas` protocol describes the deliberately duck-typed
provider shape. :func:`get_exact` always checks that a provider's returned
fact carries the requested address, even though the fact itself is valid.
"""

from typing import Protocol

from ._covalence import (
    CasAddressMismatchError,
    CasAdmissionError,
    CasAssertion,
    CasCollisionError,
    CasDigestMismatchError,
    CasFact,
    CasNotFoundError,
    MemoryCas,
    get_exact,
)
from .lib.hash import O256


class TrustedCas(Protocol):
    """Any Python object able to return checked whole-object facts."""

    def get(self, address: O256, /) -> CasFact:
        """Return a checked candidate for ``address`` or raise an exception."""
        ...


__all__ = [
    "CasAddressMismatchError",
    "CasAdmissionError",
    "CasAssertion",
    "CasCollisionError",
    "CasDigestMismatchError",
    "CasFact",
    "CasNotFoundError",
    "MemoryCas",
    "TrustedCas",
    "get_exact",
]
