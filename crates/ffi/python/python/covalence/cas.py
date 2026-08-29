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

Above those sits an equality calculus over *blob expressions*. A ``BlobExpr``
is syntax: a digest, literal bytes, a run of zeros, a concatenation, or a
slice. What one means is a partial function of a *model*, a total injective map
from every address to bytes that agrees with the CAS wherever the CAS is
defined, and ``BlobEq`` is the claim that two expressions denote the same byte
string in every model. ``BlobFact`` is the checked form, introduced only by the
rules ``refl``, ``symm``, ``trans``, ``cat``, ``slice``, ``erase`` and
``check``, or by the bridges up from an already-checked CAS fact —
``CasFact.to_blob_fact``, ``CasRangeFact.to_blob_fact`` and
``IndexCas.blob_fact``. ``BlobFact.to_range_fact`` reads one back down, and is
partial: it wants a digest or a slice of one on the left and literal bytes on
the right, and ``symm`` is how to ask for the mirrored shape.

``BlobExpr.blake3(h)`` is the blob *named by* ``h``, never the 32 bytes of the
digest. Observations there are three-valued: ``BlobEq.decide`` answers ``None``
when the rules do not settle a question, and ``BlobExpr.len_bytes`` and
``BlobExpr.eval`` answer ``None`` when a digest hides the answer, when a slice
is out of range, or when the expression is too large to walk. ``None`` is the
normal sound answer in each case and never an error.

The two structural constructors have operator spellings, so an expression reads
the way the bytes it denotes would: ``left + right`` is ``BlobExpr.cat``, and
``blob[3:7]`` is ``BlobExpr.slice`` with ``blob[3:]`` the open case running to
the end of ``blob``. A step is refused, because a stride is not a sub-range and
the calculus has no expression denoting one, and offsets are absolute rather
than counted back from an end that may be unknown. ``BlobFact`` wears both
spellings, and on it they are the two congruence rules: ``fact[3:7]`` is
``fact.slice(3, 7)`` and ``head + tail`` is ``head.cat(tail)``, each applying
one operation to both sides of the equality at once. ``+`` there concatenates
what the facts are about rather than joining the facts themselves, which is why
its operands read in the order the bytes appear in.

There is deliberately no ``len()`` on a ``BlobExpr``. ``__len__`` must return
an ``int``, so it cannot express a length that is unknown: it would have to
raise exactly where ``len_bytes`` answers ``None``, turning the normal sound
answer into an exception, and since ``bool()`` falls back on ``__len__``,
``if blob:`` would raise as well. It could not report the known cases either,
being capped at ``sys.maxsize`` while ``BlobExpr.zero(2 ** 64 - 1)`` has a
perfectly definite length. ``len_bytes`` is the total accessor, and the only
one. ``IndexCas`` does have ``len()`` and ``in``, because how many blobs a
store holds, and whether it holds a given one, are questions a store always
answers.

``IndexCas`` is where the calculus meets stored bytes. ``blob_fact(address)``
reads a resident blob as ``Blake3(h) = Bytes(b)``, which is the one step
``BlobExpr`` cannot take alone, nothing in it reading a store; ``range`` and
``prove`` answer about a byte range of a resident blob without copying the
whole blob into Python on the way past.
"""

from collections.abc import Buffer
from typing import Protocol

from ._covalence import (
    BlobEq,
    BlobExpr,
    BlobFact,
    BlobRuleError,
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
    "BlobEq",
    "BlobExpr",
    "BlobFact",
    "BlobRuleError",
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
