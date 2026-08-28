"""LCF-style CAS facts over whole blobs and byte ranges, and userspace storage.

``CasAssertion`` is unchecked data. Its ``check()`` method hashes the complete
blob before returning an opaque ``CasFact``. Storage implementations remain
ordinary userspace code; only successful checking introduces a fact.

A ``CasRangeFact`` says that particular bytes sit at a particular range of a
blob. Four rules introduce one: ``CasFact.range`` derives it from a whole-blob
fact, ``CasRangeFact.slice`` narrows one, ``CasRangeFact.fuse`` joins two that
overlap or touch, and ``CasRangeAssertion.check`` verifies a ``RangeProof``
without holding the rest of the blob.

Ranges carry an ``end`` of ``None`` when they run to the end of the blob, which
is the stronger claim: such a fact also knows the blob's length, readable
through ``blob_len``. Rust decides that by type, with a separate range type per
shape, and erases to this one shape at the boundary, so here the distinction
lives in ``end`` rather than in the class. A fact whose ``end`` is ``None`` and
whose bytes are empty is exactly a length claim.
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
    CasProofError,
    CasRangeAssertion,
    CasRangeError,
    CasRangeFact,
    IndexCas,
    RangeProof,
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
    "CasProofError",
    "CasRangeAssertion",
    "CasRangeError",
    "CasRangeFact",
    "CheckedCas",
    "IndexCas",
    "RangeProof",
    "get_checked",
]
