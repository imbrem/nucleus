"""Whole-object CAS facts keep storage and Python outside the LCF boundary."""

import array
import pickle

import pytest
from covalence.cas import (
    CasAddressMismatchError,
    CasAdmissionError,
    CasAssertion,
    CasDigestMismatchError,
    CasFact,
    CasNotFoundError,
    MemoryCas,
    get_exact,
)
from covalence.lib.hash import O256


@pytest.mark.parametrize(
    "buffer",
    [b"whole blob", bytearray(b"whole blob"), memoryview(b"whole blob")],
)
def test_whole_assertions_check_buffer_inputs(buffer: object) -> None:
    address = O256.hash(b"whole blob")
    assertion = CasAssertion(address, buffer)
    fact = assertion.try_into()

    assert assertion.hash == address
    assert assertion.blob == b"whole blob"
    assert fact.hash == address
    assert fact.blob == b"whole blob"
    assert fact.assertion == assertion


def test_mutable_buffer_is_snapshotted_before_checking() -> None:
    source = bytearray(b"before")
    assertion = CasAssertion(O256.hash(source), source)
    source[:] = b"after!"

    assert assertion.blob == b"before"
    assert assertion.try_into().blob == b"before"


def test_non_bytes_input_is_rejected() -> None:
    with pytest.raises(TypeError):
        CasAssertion(O256.hash(b"blob"), "blob")

    non_contiguous = memoryview(array.array("B", range(8)))[::2]
    with pytest.raises(TypeError):
        CasAssertion(O256.hash(b"blob"), non_contiguous)


def test_wrong_claimed_hash_is_rejected_by_the_rust_checker() -> None:
    assertion = CasAssertion(O256.hash(b"other"), b"blob")

    with pytest.raises(CasDigestMismatchError, match="does not match"):
        assertion.try_into()


def test_checked_fact_can_be_introduced_by_hashing_bytes() -> None:
    fact = CasFact.from_bytes(b"computed")

    assert fact.hash == O256.hash(b"computed")
    assert fact.blob == b"computed"
    assert fact.assertion.try_into() == fact


def test_checked_fact_cannot_be_constructed_subclassed_pickled_or_mutated() -> None:
    fact = CasFact.from_bytes(b"opaque")

    with pytest.raises(TypeError):
        CasFact()
    with pytest.raises(TypeError):

        class ForgedFact(CasFact):
            pass

    with pytest.raises(AttributeError):
        fact.blob = b"forged"
    with pytest.raises((TypeError, pickle.PicklingError)):
        pickle.dumps(fact)


def test_memory_cas_stores_checked_facts_and_deduplicates_exact_pairs() -> None:
    cas = MemoryCas()
    fact = CasFact.from_bytes(b"resident")

    assert cas.insert(fact)
    assert not cas.insert(fact)
    assert len(cas) == 1
    assert cas.facts == [fact]
    assert cas.contains(fact.hash)
    assert cas.get(fact.hash) == fact


def test_memory_cas_put_remove_and_absence() -> None:
    cas = MemoryCas()
    fact = cas.put(b"resident")

    assert get_exact(cas, fact.hash) == fact
    assert cas.remove(fact.hash)
    assert not cas.remove(fact.hash)
    with pytest.raises(CasNotFoundError):
        cas.get(fact.hash)


def test_memory_cas_enforces_its_admission_limit_without_mutation() -> None:
    cas = MemoryCas(limit=4)

    with pytest.raises(CasAdmissionError):
        cas.put(b"large")
    assert cas.facts == []


class DictCas:
    """An arbitrary Python provider which stores raw, unchecked bytes."""

    def __init__(self, blobs: dict[object, bytes]) -> None:
        self.blobs = blobs

    def get(self, address: O256) -> CasFact:
        try:
            blob = self.blobs[address]
        except KeyError as error:
            raise CasNotFoundError(str(address)) from error
        return CasAssertion(address, blob).try_into()


def test_plain_python_dict_provider_supplies_arbitrary_resolution_logic() -> None:
    blob = b"provided by Python"
    address = O256.hash(blob)
    provider = DictCas({address: blob})

    fact = get_exact(provider, address)
    assert fact.hash == address
    assert fact.blob == blob


def test_python_provider_cannot_return_a_fact_for_the_wrong_address() -> None:
    requested = O256.hash(b"requested")
    returned = CasFact.from_bytes(b"returned")

    class LyingCas:
        def get(self, _address: O256) -> CasFact:
            return returned

    with pytest.raises(CasAddressMismatchError, match="returned address"):
        get_exact(LyingCas(), requested)


def test_python_provider_cannot_return_an_unchecked_or_wrong_typed_value() -> None:
    requested = O256.hash(b"requested")

    class UncheckedCas:
        def get(self, address: O256) -> object:
            return CasAssertion(address, b"requested")

    with pytest.raises(TypeError, match="CasFact"):
        get_exact(UncheckedCas(), requested)


def test_python_provider_failure_propagates_unchanged() -> None:
    requested = O256.hash(b"requested")

    class OfflineCas:
        def get(self, _address: O256) -> CasFact:
            raise ConnectionError("offline")

    with pytest.raises(ConnectionError, match="offline"):
        get_exact(OfflineCas(), requested)
