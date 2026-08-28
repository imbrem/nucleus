"""Range facts carry their claim to Python without carrying a way to forge one."""

import pickle

import pytest
from covalence.cas import (
    CasDigestMismatchError,
    CasFact,
    CasProofError,
    CasRangeAssertion,
    CasRangeError,
    CasRangeFact,
    RangeProof,
)
from covalence.lib.hash import O256

BLOB = bytes(index % 251 for index in range(11 * 1024 + 7))
BLOCK = 1024


def whole() -> CasFact:
    return CasFact.from_bytes(BLOB)


def test_ranges_derive_from_a_whole_blob_fact() -> None:
    fact = whole()
    middle = fact.range(3, 7)

    assert isinstance(middle, CasRangeFact)
    assert middle.hash == fact.hash
    assert middle.start == 3
    assert middle.end == 7
    assert middle.bytes == BLOB[3:7]
    assert middle.extent == (3, 7)


def test_an_open_end_is_the_stronger_claim() -> None:
    fact = whole()
    suffix = fact.range(4)

    # `end` of None means the end of the blob, so the fact knows the length.
    assert suffix.end is None
    assert suffix.bytes == BLOB[4:]
    assert suffix.blob_len == len(BLOB)

    # A closed range knows nothing about how long the blob is. It must not
    # mistake its own end for the blob's.
    assert fact.range(0, len(BLOB)).blob_len is None
    assert fact.range(3, 7).blob_len is None


def test_an_empty_open_range_is_a_length_claim() -> None:
    fact = whole()
    length_only = fact.range(len(BLOB))

    assert length_only.bytes == b""
    assert length_only.end is None
    assert length_only.blob_len == len(BLOB)

    # One byte earlier pins the same length but carries a byte.
    assert fact.range(len(BLOB) - 1).blob_len == len(BLOB)
    assert fact.range(len(BLOB) - 1).bytes == BLOB[-1:]


def test_slicing_uses_absolute_offsets_and_refuses_what_it_lacks() -> None:
    middle = whole().range(3, 9)

    assert middle.slice(4, 6).bytes == BLOB[4:6]
    with pytest.raises(CasRangeError):
        middle.slice(2, 6)
    with pytest.raises(CasRangeError):
        middle.slice(4, 12)
    with pytest.raises(CasRangeError):
        middle.slice(6, 4)
    # A bounded fact does not know where the blob ends, so it cannot answer an
    # open request.
    with pytest.raises(CasRangeError):
        middle.slice(4)


def test_fusing_covers_the_union_and_refuses_gaps() -> None:
    fact = whole()
    fused = fact.range(1, 5).fuse(fact.range(3, 8))

    assert fused.start == 1
    assert fused.end == 8
    assert fused.bytes == BLOB[1:8]
    # Touching ranges fuse; a gap does not.
    assert fact.range(1, 4).fuse(fact.range(4, 6)).bytes == BLOB[1:6]
    with pytest.raises(CasRangeError):
        fact.range(1, 3).fuse(fact.range(5, 7))
    with pytest.raises(CasRangeError):
        fact.range(1, 5).fuse(CasFact.from_bytes(b"other").range(0, 3))


def test_a_prefix_and_a_suffix_fuse_into_the_whole_blob() -> None:
    fact = whole()
    fused = fact.range(0, 6).fuse(fact.range(4))

    assert fused.start == 0
    assert fused.end is None
    assert fused.blob_len == len(BLOB)
    assert fused.whole() == fact

    # A fact that does not reach both ends is not the whole blob.
    with pytest.raises(CasRangeError):
        fact.range(1).whole()
    with pytest.raises(CasRangeError):
        fact.range(0, len(BLOB)).whole()


def test_range_proofs_check_without_the_rest_of_the_blob() -> None:
    address = O256.hash(BLOB)
    for level in (0, 1, 2):
        block = BLOCK << level
        # A closed range must sit on block boundaries, so the last usable one
        # ends at the final complete block. The short tail needs an open range.
        start, end = block, 2 * block
        assert end <= len(BLOB)
        proof = RangeProof.prove(level, start, end, BLOB)
        assert proof.level == level
        assert proof.block_len == block

        fact = proof.check(address, start, end, BLOB[start:end])
        assert fact.hash == address
        assert fact.bytes == BLOB[start:end]
        assert fact.start == start
        assert fact.end == end
        assert fact.blob_len is None

        # The proof carries only the spines, not the rest of the blob.
        assert len(proof.left) + len(proof.right) < len(BLOB) // block + 2


def test_an_assertion_becomes_a_fact_only_through_a_proof() -> None:
    address = O256.hash(BLOB)
    assertion = CasRangeAssertion(address, BLOCK, 2 * BLOCK, BLOB[BLOCK : 2 * BLOCK])
    proof = RangeProof.prove(0, BLOCK, 2 * BLOCK, BLOB)

    assert assertion.check(proof).bytes == BLOB[BLOCK : 2 * BLOCK]
    # There is no argument-free conversion.
    assert not hasattr(assertion, "try_into")
    with pytest.raises(TypeError):
        assertion.check()  # type: ignore[call-arg]


def test_proofs_reject_tampering() -> None:
    address = O256.hash(BLOB)
    proof = RangeProof.prove(0, BLOCK, 2 * BLOCK, BLOB)
    good = BLOB[BLOCK : 2 * BLOCK]

    tampered = bytearray(good)
    tampered[0] ^= 1
    with pytest.raises(CasDigestMismatchError):
        proof.check(address, BLOCK, 2 * BLOCK, bytes(tampered))

    # A proof cannot relocate its bytes to another offset.
    with pytest.raises(CasDigestMismatchError):
        proof.check(address, 2 * BLOCK, 3 * BLOCK, good)

    # Nor authenticate them against another blob.
    with pytest.raises(CasDigestMismatchError):
        proof.check(O256.hash(b"other"), BLOCK, 2 * BLOCK, good)

    # A forged spine is rejected.
    forged = RangeProof(0, [bytes(32) for _ in proof.left], proof.right)
    with pytest.raises(CasDigestMismatchError):
        forged.check(address, BLOCK, 2 * BLOCK, good)


def test_proofs_reject_unusable_ranges_and_spines() -> None:
    address = O256.hash(BLOB)
    proof = RangeProof.prove(0, BLOCK, 2 * BLOCK, BLOB)

    # Closed ranges must sit on block boundaries.
    with pytest.raises(CasProofError):
        proof.check(address, 100, 2 * BLOCK, BLOB[100 : 2 * BLOCK])
    # The byte count must match the range.
    with pytest.raises(CasProofError):
        proof.check(address, BLOCK, 2 * BLOCK, BLOB[BLOCK : BLOCK + 8])
    # A chaining value is 32 bytes.
    with pytest.raises(CasProofError):
        RangeProof(0, [b"short"], [])
    # A level whose block length overflows is refused.
    with pytest.raises(CasProofError):
        RangeProof.prove(64, 0, None, BLOB)


def test_an_open_range_proof_carries_no_right_spine() -> None:
    address = O256.hash(BLOB)
    # The tail runs to the end of the blob, so nothing lies to its right.
    tail = RangeProof.prove(0, 8 * BLOCK, None, BLOB)
    assert tail.right == []
    fact = tail.check(address, 8 * BLOCK, None, BLOB[8 * BLOCK :])
    assert fact.blob_len == len(BLOB)

    # Attaching one would let a prefix of the blob pass as the whole of it.
    prefix = RangeProof.prove(0, 0, 8 * BLOCK, BLOB)
    assert prefix.right != []
    smuggled = RangeProof(0, prefix.left, prefix.right)
    with pytest.raises(CasProofError):
        smuggled.check(address, 0, None, BLOB[: 8 * BLOCK])


def test_facts_are_opaque_values() -> None:
    fact = whole()
    first = fact.range(3, 7)
    second = fact.range(3, 7)

    assert first == second
    assert hash(first) == hash(second)
    assert first != fact.range(3, 8)
    assert {first, second} == {first}
    assert "3..7" in repr(first)

    # A fact hands back its assertion without handing back a way to mint one.
    assertion = first.assertion
    assert isinstance(assertion, CasRangeAssertion)
    assert assertion.hash == first.hash
    assert assertion.start == 3
    assert assertion.end == 7
    assert assertion.bytes == first.bytes
    # Nothing hands Python a way to mint one: no constructor, no subclass to
    # override, no unpickling back into existence, and no mutable field.
    with pytest.raises(TypeError):
        CasRangeFact()  # type: ignore[call-arg]
    with pytest.raises(TypeError):

        class ForgedRangeFact(CasRangeFact):  # type: ignore[misc]
            pass

    with pytest.raises(AttributeError):
        first.bytes = b"forged"  # type: ignore[misc]
    with pytest.raises((TypeError, pickle.PicklingError)):
        pickle.dumps(first)
