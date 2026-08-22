"""Whole-object CAS facts keep storage and Python outside the mint boundary."""

import array
import pickle

import pytest
from covalence.cas import (
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
from covalence.lib.hash import O256


@pytest.mark.parametrize(
    "buffer",
    [b"whole blob", bytearray(b"whole blob"), memoryview(b"whole blob")],
)
def test_whole_assertions_check_buffer_inputs(buffer: object) -> None:
    address = O256.hash(b"whole blob")
    assertion = CasAssertion(address, buffer)
    fact = assertion.check()

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
    assert assertion.check().blob == b"before"


def test_non_bytes_input_is_rejected() -> None:
    with pytest.raises(TypeError):
        CasAssertion(O256.hash(b"blob"), "blob")

    non_contiguous = memoryview(array.array("B", range(8)))[::2]
    with pytest.raises(TypeError):
        CasAssertion(O256.hash(b"blob"), non_contiguous)


def test_check_errors_form_one_value_error_family() -> None:
    assertion = CasAssertion(O256.hash(b"other"), b"blob")

    with pytest.raises(CasDigestMismatchError, match="does not match") as caught:
        assertion.check()
    assert isinstance(caught.value, CasCheckError)
    assert isinstance(caught.value, ValueError)


def test_fact_convenience_constructors_all_check() -> None:
    address = O256.hash(b"computed")
    assertion = CasAssertion(address, b"computed")

    assert CasFact(address, b"computed") == assertion.check()
    assert CasFact.from_assertion(assertion) == assertion.check()
    assert CasFact.from_bytes(b"computed") == assertion.check()

    with pytest.raises(CasDigestMismatchError):
        CasFact(O256.hash(b"other"), b"computed")


def test_fact_is_a_refinement_not_an_assertion_subclass() -> None:
    fact = CasFact.from_bytes(b"opaque")

    assert not isinstance(fact, CasAssertion)
    assert fact.assertion.check() == fact
    with pytest.raises(TypeError):
        CasFact()
    with pytest.raises(TypeError):

        class ForgedFact(CasFact):
            pass

    with pytest.raises(AttributeError):
        fact.blob = b"forged"
    with pytest.raises((TypeError, pickle.PicklingError)):
        pickle.dumps(fact)


def test_assertions_and_facts_are_ordered_and_hashable() -> None:
    facts = [CasFact.from_bytes(blob) for blob in (b"c", b"a", b"b")]
    assertions = [fact.assertion for fact in facts]

    assert sorted(facts) == sorted(facts, key=lambda fact: (fact.hash, fact.blob))
    assert sorted(assertions) == sorted(
        assertions, key=lambda assertion: (assertion.hash, assertion.blob)
    )
    assert len(set(facts + [facts[0]])) == 3
    assert len(set(assertions + [assertions[0]])) == 3


def test_index_cas_exposes_stable_ids_for_hashes_and_bytes() -> None:
    cas = IndexCas()
    first = CasFact.from_bytes(b"first")
    second = CasFact.from_bytes(b"second")

    first_id = cas.insert(first)
    second_id = cas.put(b"second")
    assert first_id == 0
    assert second_id == 1
    assert cas.insert(first) == first_id
    assert cas.id(first.hash) == first_id
    assert cas.id_bytes(b"first") == first_id
    assert cas.fact(first_id) == first
    assert cas.items() == [(first_id, first), (second_id, second)]
    assert cas.get(first.hash) == b"first"
    assert cas.get_fact(first.hash) == first

    assert cas.remove(first.hash)
    assert cas.fact(first_id) is None
    assert cas.fact(second_id) == second
    assert cas.put(b"third") == 2


def test_index_lookup_errors_share_one_lookup_base() -> None:
    cas = IndexCas()
    address = O256.hash(b"absent")

    with pytest.raises(CasNotFoundError) as caught:
        cas.get(address)
    assert isinstance(caught.value, CasLookupError)
    assert isinstance(caught.value, LookupError)


class DictCas:
    """An arbitrary Python CAS storing raw, unchecked bytes."""

    def __init__(self, blobs: dict[object, bytes]) -> None:
        self.blobs = blobs

    def get(self, address: O256) -> bytes:
        try:
            return self.blobs[address]
        except KeyError as error:
            raise CasNotFoundError(str(address)) from error


def test_raw_python_cas_is_checked_at_the_boundary() -> None:
    blob = b"provided by Python"
    address = O256.hash(blob)
    fact = get_checked(DictCas({address: blob}), address)

    assert fact.hash == address
    assert fact.blob == blob


def test_checked_provider_avoids_rehash_but_must_answer_the_request() -> None:
    requested = O256.hash(b"requested")
    returned = CasFact.from_bytes(b"returned")

    class LyingCas:
        def get(self, _address: O256) -> bytes:
            raise AssertionError("optimized lookup should be used")

        def get_fact(self, _address: O256) -> CasFact:
            return returned

    with pytest.raises(CasAddressMismatchError, match="returned address") as caught:
        get_checked(LyingCas(), requested)
    assert isinstance(caught.value, CasLookupError)


def test_raw_provider_returning_wrong_bytes_fails_the_check() -> None:
    requested = O256.hash(b"requested")

    class LyingCas:
        def get(self, _address: O256) -> bytes:
            return b"returned"

    with pytest.raises(CasDigestMismatchError):
        get_checked(LyingCas(), requested)


def test_python_provider_failure_propagates_unchanged() -> None:
    requested = O256.hash(b"requested")

    class OfflineCas:
        def get(self, _address: O256) -> bytes:
            raise ConnectionError("offline")

    with pytest.raises(ConnectionError, match="offline"):
        get_checked(OfflineCas(), requested)
