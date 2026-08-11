"""The hash API, checked against the vectors the Rust crate is checked against.

The digests here are official BLAKE3, SHA-256, SHA-1, and Git values, and the
Covalence roots are the ones checked into `covalence-lib-hash`. Reusing them is
the point: it is what makes this a check that Python reaches the same
implementation rather than a check that Python agrees with itself.
"""

import array
import base64
import itertools
import operator

import pytest
from covalence import (
    COV,
    COV_ROOT,
    COV_ROOT_CTX_KEY,
    O256,
    Blake3,
    ContextKey,
    GitHash,
    InvalidBase64Error,
    InvalidHexError,
    InvalidLengthError,
    Obj,
    Sha1,
    Sha256,
    git_blob,
    git_object,
)

WIDE = (O256, Blake3, Sha256, ContextKey)
NARROW = (Sha1, GitHash)
EVERY = WIDE + NARROW

BLAKE3_EMPTY = "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
BLAKE3_ABC = "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85"
SHA256_EMPTY = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
SHA256_ABC = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
SHA1_ABC = "a9993e364706816aba3e25717850c26c9cd0d89d"
GIT_BLOB_EMPTY = "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"
GIT_BLOB_HELLO = "b6fc4c620b67d95f953a5c1c1230aaab5db5a1b0"


def sample(cls: type) -> object:
    """A value of `cls` that does not depend on hashing to construct."""
    return cls(bytes(range(cls.BYTES)))


# Published vectors.


def test_blake3_matches_its_official_vectors() -> None:
    assert Blake3.hash(b"").hex() == BLAKE3_EMPTY
    assert Blake3.hash(b"abc").hex() == BLAKE3_ABC


def test_covalence_content_hashing_is_blake3() -> None:
    """Covalence embeds BLAKE3, which is why the bytes agree."""
    assert O256.hash(b"").hex() == BLAKE3_EMPTY
    assert O256.hash(b"abc").hex() == BLAKE3_ABC
    assert bytes(O256.hash(b"abc")) == bytes(Blake3.hash(b"abc"))


def test_sha256_matches_its_official_vectors() -> None:
    assert Sha256.hash(b"").hex() == SHA256_EMPTY
    assert Sha256.hash(b"abc").hex() == SHA256_ABC


def test_sha1_matches_its_official_vector() -> None:
    assert Sha1.hash(b"abc").hex() == SHA1_ABC


def test_git_names_objects_the_way_git_does() -> None:
    assert git_blob(b"").hex() == GIT_BLOB_EMPTY
    assert git_blob(b"hello").hex() == GIT_BLOB_HELLO
    assert git_blob(b"hello") == git_object("blob", b"hello")


def test_git_framing_is_not_raw_sha1() -> None:
    """Git hashes a type-and-length header first, so the two never agree."""
    assert bytes(git_blob(b"hello")) != bytes(Sha1.hash(b"hello"))
    assert git_object("blob", b"hello") != git_object("tree", b"hello")


# The Covalence hierarchy.


def test_the_checked_in_roots_are_reproducible() -> None:
    assert COV == ContextKey.derive(COV_ROOT_CTX_KEY)
    assert COV_ROOT == COV.root()
    assert COV_ROOT == COV.tag(b"")
    assert COV_ROOT == O256.root()


def test_the_context_string_is_versioned_and_carries_its_root() -> None:
    assert COV_ROOT_CTX_KEY.startswith("covalence ")
    assert ContextKey.derive(COV_ROOT_CTX_KEY + " ") != COV


def test_tagging_is_keyed_hashing_under_the_parent() -> None:
    child = COV_ROOT.tag(b"sexpr").tag(b"list")
    assert child == O256.keyed(O256.keyed(COV_ROOT, b"sexpr"), b"list")


def test_a_context_string_and_its_derived_key_agree() -> None:
    context = "covalence test context"
    assert O256.derive_key(context, b"payload") == O256.with_context(
        ContextKey.derive(context), b"payload"
    )


def test_keying_by_an_object_differs_from_keying_by_a_context() -> None:
    """Distinct BLAKE3 modes, and mixing them up must not go unnoticed."""
    key = O256(bytes(32))
    assert O256.keyed(key, b"payload") != O256.with_context(
        ContextKey(bytes(32)), b"payload"
    )


# Values.


@pytest.mark.parametrize("cls", EVERY)
def test_bytes_hex_and_text_agree(cls: type) -> None:
    value = sample(cls)
    assert len(bytes(value)) == cls.BYTES
    assert bytes(value) == bytes(range(cls.BYTES))
    assert value.hex() == bytes(value).hex()
    assert str(value) == value.hex()
    assert cls.from_hex(value.hex()) == value


@pytest.mark.parametrize("cls", EVERY)
def test_repr_names_the_class_and_round_trips(cls: type) -> None:
    value = sample(cls)
    assert repr(value) == f"{cls.__name__}.from_hex('{value.hex()}')"
    assert eval(repr(value), {cls.__name__: cls}) == value  # noqa: S307


@pytest.mark.parametrize("cls", EVERY)
def test_hex_parsing_accepts_either_case_only(cls: type) -> None:
    value = sample(cls)
    assert cls.from_hex(value.hex().upper()) == value
    for rejected in (f"0x{value.hex()}", f" {value.hex()}", f"{value.hex()} "):
        with pytest.raises(ValueError):
            cls.from_hex(rejected)


@pytest.mark.parametrize("cls", EVERY)
def test_base64_round_trips_and_is_canonical(cls: type) -> None:
    value = sample(cls)
    assert cls.from_base64(base64.b64encode(bytes(value)).decode()) == value


@pytest.mark.parametrize("cls", EVERY)
def test_values_are_ordered_bytewise_and_hashable(cls: type) -> None:
    low = cls(bytes(cls.BYTES))
    high = cls(bytes(cls.BYTES - 1) + b"\x01")
    assert low < high
    assert high > low
    assert low <= cls(bytes(cls.BYTES))
    assert sorted([high, low]) == [low, high]
    assert hash(low) == hash(cls(bytes(cls.BYTES)))
    assert len({low, high, cls(bytes(cls.BYTES))}) == 2
    assert {low: "value"}[cls(bytes(cls.BYTES))] == "value"


@pytest.mark.parametrize("cls", EVERY)
def test_values_are_immutable(cls: type) -> None:
    value = sample(cls)
    with pytest.raises(AttributeError):
        value.anything = 1


# The shared base.


@pytest.mark.parametrize("cls", EVERY)
def test_every_namespace_is_an_obj(cls: type) -> None:
    assert issubclass(cls, Obj)
    assert isinstance(sample(cls), Obj)
    assert cls.__mro__ == (cls, Obj, object)


@pytest.mark.parametrize("cls", EVERY)
def test_the_value_protocol_comes_from_the_base(cls: type) -> None:
    """Shared behaviour is shared, not repeated once per namespace."""
    for member in ("hex", "__bytes__", "__len__", "__str__", "__repr__", "__hash__"):
        assert getattr(cls, member) is getattr(Obj, member)


@pytest.mark.parametrize("cls", EVERY)
def test_length_is_the_namespace_width(cls: type) -> None:
    assert len(sample(cls)) == cls.BYTES


def test_the_base_cannot_be_instantiated() -> None:
    """A value with no namespace is what the type distinction rules out."""
    with pytest.raises(TypeError):
        Obj()
    with pytest.raises(TypeError):
        Obj(bytes(32))
    assert not hasattr(Obj, "BYTES")


# Namespaces stay apart.


@pytest.mark.parametrize(("left", "right"), itertools.permutations(WIDE, 2))
def test_matching_bytes_do_not_make_namespaces_equal(left: type, right: type) -> None:
    assert left(bytes(32)) != right(bytes(32))
    assert not left(bytes(32)) == right(bytes(32))


@pytest.mark.parametrize(("left", "right"), itertools.permutations(WIDE, 2))
def test_namespaces_do_not_hash_together(left: type, right: type) -> None:
    assert len({left(bytes(32)), right(bytes(32))}) == 2


@pytest.mark.parametrize(("left", "right"), itertools.permutations(EVERY, 2))
def test_namespaces_cannot_be_ordered_against_each_other(
    left: type, right: type
) -> None:
    with pytest.raises(TypeError):
        operator.lt(left(bytes(left.BYTES)), right(bytes(right.BYTES)))


@pytest.mark.parametrize("cls", EVERY)
def test_a_namespace_will_not_accept_another(cls: type) -> None:
    """No implicit coercion: a value is not bytes-like just because it has bytes."""
    for other in EVERY:
        if other is cls:
            continue
        with pytest.raises(TypeError):
            cls(sample(other))


def test_the_conversions_that_exist_are_the_ones_rust_has() -> None:
    digest = Blake3.hash(b"abc")
    assert bytes(digest.to_o256()) == bytes(digest)
    assert digest.to_o256() == O256.hash(b"abc")

    name = git_blob(b"hello")
    assert name.to_sha1().to_git() == name
    assert bytes(name.to_sha1()) == bytes(name)


def test_there_is_no_conversion_back_into_a_narrower_claim() -> None:
    """Every Covalence object is not a BLAKE3 digest, so there is no `to_blake3`."""
    assert not hasattr(O256, "to_blake3")
    assert not hasattr(O256, "coerce")


# Rejection.


@pytest.mark.parametrize("cls", EVERY)
def test_the_wrong_width_is_rejected(cls: type) -> None:
    for width in (0, cls.BYTES - 1, cls.BYTES + 1):
        with pytest.raises(InvalidLengthError):
            cls(bytes(width))


@pytest.mark.parametrize("cls", EVERY)
def test_malformed_hex_is_reported_precisely(cls: type) -> None:
    with pytest.raises(InvalidLengthError):
        cls.from_hex("00" * (cls.BYTES - 1))
    with pytest.raises(InvalidLengthError):
        cls.from_hex("00" * (cls.BYTES + 1))
    with pytest.raises(InvalidHexError):
        cls.from_hex("g0" + "00" * (cls.BYTES - 1))
    with pytest.raises(InvalidHexError):
        cls.from_hex("0_" + "00" * (cls.BYTES - 1))


@pytest.mark.parametrize("cls", EVERY)
def test_malformed_base64_is_reported_precisely(cls: type) -> None:
    encoded = base64.b64encode(bytes(cls.BYTES)).decode()
    with pytest.raises(InvalidLengthError):
        cls.from_base64(encoded[:-4])
    with pytest.raises(InvalidBase64Error):
        cls.from_base64("!" + encoded[1:])


@pytest.mark.parametrize("cls", EVERY)
def test_non_canonical_base64_trailing_bits_are_rejected(cls: type) -> None:
    """Both widths leave spare bits in the final quantum, which must be zero.

    20 and 32 are each two more than a multiple of three, so every value ends
    in a two-byte group written as three characters and one `=`. The last of
    those characters carries two bits the value does not use.
    """
    canonical = base64.b64encode(bytes(cls.BYTES)).decode()
    assert canonical.endswith("=") and not canonical.endswith("==")
    assert cls.from_base64(canonical) == cls(bytes(cls.BYTES))
    # 'A' is six zero bits; 'B' sets the lowest of the two spare ones, which
    # encodes the same bytes and so is not the canonical spelling of them.
    assert canonical[-2] == "A"
    with pytest.raises(InvalidBase64Error):
        cls.from_base64(f"{canonical[:-2]}B=")


@pytest.mark.parametrize("cls", EVERY)
def test_text_is_not_bytes(cls: type) -> None:
    """Accepting `str` would mean choosing an encoding for the caller."""
    with pytest.raises(TypeError):
        cls("0" * (cls.BYTES * 2))


def test_hashing_rejects_things_that_are_not_bytes_like() -> None:
    for rejected in ("abc", 42, None, [1, 2, 3]):
        with pytest.raises(TypeError):
            O256.hash(rejected)
        with pytest.raises(TypeError):
            git_blob(rejected)


def test_the_exceptions_are_all_value_errors() -> None:
    """One `except ValueError` catches every malformed input."""
    for exception in (InvalidLengthError, InvalidHexError, InvalidBase64Error):
        assert issubclass(exception, ValueError)
    assert InvalidLengthError.__module__ == "covalence"


# Input shapes.


@pytest.mark.parametrize(
    "make",
    [bytes, bytearray, memoryview, lambda data: array.array("B", data)],
    ids=["bytes", "bytearray", "memoryview", "array"],
)
def test_any_contiguous_buffer_can_be_hashed(make: object) -> None:
    assert O256.hash(make(b"abc")).hex() == BLAKE3_ABC
    assert Sha256.hash(make(b"abc")).hex() == SHA256_ABC
    assert git_blob(make(b"hello")).hex() == GIT_BLOB_HELLO


@pytest.mark.parametrize(
    "make",
    [bytes, bytearray, memoryview],
    ids=["bytes", "bytearray", "memoryview"],
)
def test_any_contiguous_buffer_can_name_a_value(make: object) -> None:
    assert O256(make(bytes(range(32)))) == O256(bytes(range(32)))


def test_a_non_contiguous_buffer_is_rejected_rather_than_misread() -> None:
    every_other = memoryview(bytes(range(64)))[::2]
    assert not every_other.c_contiguous
    with pytest.raises(TypeError):
        O256.hash(every_other)


def test_a_multi_byte_buffer_is_rejected_rather_than_reinterpreted() -> None:
    with pytest.raises(TypeError):
        O256.hash(array.array("I", [1, 2, 3]))


def test_large_inputs_hash_in_one_piece() -> None:
    """Large enough that the hasher takes a multi-block path, and the GIL is
    released while it does."""
    data = bytes(range(256)) * 16384  # 4 MiB
    assert O256.hash(data) == O256.hash(bytearray(data))
    assert O256.hash(data) == O256.hash(memoryview(data))
    assert Sha256.hash(data) == Sha256.hash(memoryview(data))
    assert O256.hash(data) != O256.hash(data + b"\x00")


def test_hashing_releases_the_gil() -> None:
    """Another thread makes progress while a large hash is running."""
    import threading

    data = bytes(1) * (32 * 1024 * 1024)
    ticks = 0
    done = threading.Event()

    def spin() -> None:
        nonlocal ticks
        while not done.is_set():
            ticks += 1

    spinner = threading.Thread(target=spin)
    spinner.start()
    try:
        for _ in range(4):
            O256.hash(data)
    finally:
        done.set()
        spinner.join()
    assert ticks > 0
