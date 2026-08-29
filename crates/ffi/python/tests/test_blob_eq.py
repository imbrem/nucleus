"""The blob equality calculus crosses into Python without losing its answers.

Four things have to survive the boundary. Declining is an answer, not a
failure: ``decide`` says ``None`` when the rules do not settle a question and
``len_bytes`` says ``None`` when no length is known, and neither may collapse
into ``False``, into ``0``, or into an exception. Introducing a fact stays the
privilege of the rules, exactly as it is for ``CasRangeFact``. A digest names a
blob rather than being one. And the operator spellings — ``+`` for ``cat`` and
``[a:b]`` for ``slice`` — mean exactly what the methods mean, refusing the
shapes Python has and this calculus does not rather than approximating them.
"""

import operator
import pickle

import pytest
from covalence.cas import (
    BlobEq,
    BlobExpr,
    BlobFact,
    BlobRuleError,
    CasCheckError,
    CasFact,
    CasNotFoundError,
    CasRangeError,
    CasRangeFact,
    IndexCas,
)
from covalence.lib.hash import O256

BLOB = b"0123456789"


def whole() -> CasFact:
    return CasFact.from_bytes(BLOB)


def head() -> BlobFact:
    """``cat("ab", "c") = "abc"``: a real fact whose sides differ."""
    joined = BlobExpr.cat(BlobExpr.bytes(b"ab"), BlobExpr.bytes(b"c"))
    return BlobFact.check(BlobEq(joined, BlobExpr.bytes(b"abc")))


def doubled(levels: int) -> BlobExpr:
    """A shared doubling DAG: ``levels`` new nodes over a tree of ``2**levels``."""
    expr = BlobExpr.bytes(b"x")
    for _ in range(levels):
        expr = BlobExpr.cat(expr, expr)
    return expr


def test_every_variant_has_a_constructor() -> None:
    fact = whole()

    named = BlobExpr.blake3(fact.hash)
    literal = BlobExpr.bytes(b"abc")
    zeros = BlobExpr.zero(2)
    joined = BlobExpr.cat(literal, zeros)
    part = BlobExpr.slice(literal, 1, 2)

    assert literal.eval() == b"abc"
    assert zeros.eval() == b"\0\0"
    assert joined.eval() == b"abc\0\0"
    assert part.eval() == b"b"
    # A digest is a leaf whatever the size of the blob it names.
    assert named.size == 1
    assert literal.size == 1
    assert joined.size == 3
    assert part.size == 2


def test_a_digest_names_a_blob_and_is_not_its_own_bytes() -> None:
    fact = whole()
    named = BlobExpr.blake3(fact.hash)
    digest = BlobExpr.bytes(bytes(fact.hash))

    assert named != digest
    # `named` denotes some byte string in every model, but not the same one in
    # all of them, so neither its length nor its bytes are readable here.
    assert named.len_bytes is None
    assert named.eval() is None
    # Those are the 32 bytes of the address, which is a different expression.
    assert digest.len_bytes == 32
    assert digest.eval() == bytes(fact.hash)
    # And nothing relates the two, in either direction.
    assert BlobEq(named, digest).decide() is None


def test_an_unknown_length_is_none_and_never_zero() -> None:
    fact = whole()

    # Behind a digest.
    assert BlobExpr.blake3(fact.hash).len_bytes is None
    # Past `u64`, which must not wrap to a small number.
    past = BlobExpr.cat(BlobExpr.zero(2**64 - 1), BlobExpr.zero(2**64 - 1))
    assert past.len_bytes is None
    assert past.size == 3
    # A `cat` is known only when both sides are.
    mixed = BlobExpr.cat(BlobExpr.bytes(b"abc"), BlobExpr.blake3(fact.hash))
    assert mixed.len_bytes is None

    # A length that is merely enormous is still known, and still refuses to be
    # materialised.
    enormous = BlobExpr.zero(2**64 - 1)
    assert enormous.len_bytes == 2**64 - 1
    assert enormous.eval() is None


def test_out_of_range_slicing_denotes_nothing_rather_than_clamping() -> None:
    two = BlobExpr.bytes(b"ab")

    assert BlobExpr.slice(two, 5, 9).len_bytes is None
    assert BlobExpr.slice(two, 5, 9).eval() is None
    # Not clamped to the bytes that are there, and not to a shorter width.
    assert BlobExpr.slice(two, 1, 4).eval() is None
    assert BlobExpr.slice(two, 3).eval() is None

    # Two out-of-range slices of different widths are undefined in every model,
    # so they are EQUAL. Refuting them from their span widths would be a false
    # fact, and proving them would be a guess: `None` is the sound answer.
    assert BlobEq(BlobExpr.slice(two, 5, 9), BlobExpr.slice(two, 5, 7)).decide() is None

    # A backwards span is refused at the boundary rather than built.
    with pytest.raises(CasRangeError):
        BlobExpr.slice(two, 7, 3)


def test_a_whole_blob_span_normalises_away() -> None:
    ten = BlobExpr.bytes(BLOB)

    assert BlobExpr.slice(ten, 0) == ten
    assert BlobExpr.slice(ten, 0, 10) != ten
    assert BlobExpr.slice(ten, 3).eval() == BLOB[3:]
    assert BlobExpr.slice(ten, 3, 6).eval() == BLOB[3:6]


def test_traversals_decline_past_the_size_limit() -> None:
    """A hyperblob is built and then declined, never answered wrongly."""
    inside = doubled(9)
    assert inside.size == 1023
    assert inside.len_bytes == 512
    assert inside.eval() == b"x" * 512

    # One level more is 2047 tree nodes. Every observation declines rather
    # than walking them, and declining is `None` rather than an exception.
    outside = doubled(10)
    assert outside.size == 2047
    assert outside.len_bytes is None
    assert outside.eval() is None
    assert BlobEq(outside, outside).decide() is None

    # REFL is a rule, not an observation, so it still applies: the conclusion
    # follows whatever the size, and only `decide` stops confirming it.
    assert BlobFact.refl(outside).prop.lhs == outside


def test_decide_is_three_valued() -> None:
    fact = whole()
    abc = BlobExpr.bytes(b"abc")

    # Proved by evaluation, in both directions.
    joined = BlobExpr.cat(BlobExpr.bytes(b"ab"), BlobExpr.bytes(b"c"))
    assert BlobEq(joined, abc).decide()
    assert BlobEq(abc, BlobExpr.bytes(b"abd")).decide() is False
    # Refuted by length alone, without materialising either side.
    assert BlobEq(BlobExpr.zero(2**40), abc).decide() is False
    # Two different digests are refuted: a model is injective.
    other = CasFact.from_bytes(b"other").hash
    assert BlobEq(BlobExpr.blake3(fact.hash), BlobExpr.blake3(other)).decide() is False
    # The same digest goes to reflexivity, never to `False`.
    assert BlobEq(BlobExpr.blake3(fact.hash), BlobExpr.blake3(fact.hash)).decide()
    # And a digest against anything else is unsettled, not refuted.
    assert BlobEq(BlobExpr.blake3(fact.hash), abc).decide() is None


def test_a_regrouped_concatenation_is_never_refuted() -> None:
    """The `cat` trap: same bytes, different tree.

    Concatenation is associative in what it denotes and not in how it is
    written, so structurally different expressions routinely denote the same
    byte string. A rule that read the syntax would refute them. Every pair here
    must come back ``True`` or ``None`` — never ``False``, which would be a
    false disequality — and the unsettled ones are unsettled because a
    traversal declined, not because the syntax differed.
    """
    left = BlobExpr.cat(BlobExpr.bytes(b"ab"), BlobExpr.bytes(b"c"))
    right = BlobExpr.cat(BlobExpr.bytes(b"a"), BlobExpr.bytes(b"bc"))
    spine = BlobExpr.bytes(b"a") + (BlobExpr.bytes(b"b") + BlobExpr.bytes(b"c"))
    ten = BlobExpr.bytes(BLOB)
    # Past the node limit, against the bytes it denotes: the flat side has a
    # length and the deep side declines to report one, which must not be read
    # as a disagreement.
    hyper = doubled(10)
    flat = BlobExpr.bytes(b"x" * 1024)
    # And a grouping with an unresolvable digest in it, which no evaluation
    # reaches: appending nothing changes nothing, whatever the digest names.
    named = BlobExpr.blake3(whole().hash)

    settled = ((left, right), (left, spine), (ten[0:4] + ten[4:10], ten))
    unsettled = ((hyper, flat), (named + BlobExpr.zero(0), named))

    for first, second in settled + unsettled:
        # Structurally different, as the trap requires.
        assert first != second
        assert BlobEq(first, second).decide() is not False
        assert BlobEq(second, first).decide() is not False
    for first, second in settled:
        assert BlobEq(first, second).decide() is True
    for first, second in unsettled:
        assert BlobEq(first, second).decide() is None

    # The same trap for slicing: different subjects, same bytes.
    inner = BlobExpr.slice(BlobExpr.bytes(b"xabcx"), 1, 4)
    outer = BlobExpr.slice(BlobExpr.bytes(b"yabcy"), 1, 4)
    assert inner != outer
    assert BlobEq(inner, outer).decide() is True


def test_check_introduces_a_fact_only_from_a_proof() -> None:
    fact = head()
    assert fact.prop.rhs == BlobExpr.bytes(b"abc")

    # A refutation is not a fact: there is no fact type for a disequality.
    with pytest.raises(BlobRuleError, match="refuted"):
        BlobFact.check(BlobEq(BlobExpr.bytes(b"abc"), BlobExpr.bytes(b"abd")))
    # Nor is an unsettled question, and the two are told apart by the message
    # rather than conflated.
    unknown = BlobEq(BlobExpr.blake3(whole().hash), BlobExpr.bytes(b"abc"))
    assert unknown.decide() is None
    with pytest.raises(BlobRuleError, match="do not settle"):
        BlobFact.check(unknown)

    # It stays inside the existing hierarchy rather than starting a new one.
    assert issubclass(BlobRuleError, CasCheckError)


def test_refl_holds_where_nothing_else_does() -> None:
    named = BlobExpr.blake3(whole().hash)
    unreadable = BlobExpr.slice(named, 3, 9)

    assert unreadable.len_bytes is None
    assert unreadable.eval() is None
    assert BlobFact.refl(unreadable).prop == BlobEq(unreadable, unreadable)


def test_the_equivalence_rules_compose() -> None:
    first = head()
    second = BlobFact.check(
        BlobEq(BlobExpr.bytes(b"abc"), BlobExpr.slice(BlobExpr.bytes(b"xabcx"), 1, 4))
    )

    swapped = first.symm()
    assert swapped.prop.lhs == first.prop.rhs
    assert swapped.symm() == first

    composed = first.trans(second)
    assert composed.prop.lhs == first.prop.lhs
    assert composed.prop.rhs == second.prop.rhs

    # Nothing in the types forces the middles to agree, so the check is what
    # keeps `a = b` and `c = d` from composing into `a = d`.
    with pytest.raises(BlobRuleError, match="middle"):
        first.trans(BlobFact.refl(BlobExpr.bytes(b"zz")))


def test_the_congruence_rules_are_total() -> None:
    first = head()
    tail = BlobFact.refl(BlobExpr.zero(1))

    joined = first.cat(tail)
    assert joined.prop.lhs.eval() == b"abc\0"
    assert joined.prop.rhs.eval() == b"abc\0"

    part = first.slice(0, 2)
    assert part.prop.lhs.eval() == b"ab"
    assert part.prop.rhs.eval() == b"ab"

    # One span for both sides, so equal subjects sliced differently is not
    # expressible; a backwards one is refused rather than built.
    with pytest.raises(CasRangeError):
        first.slice(7, 3)

    # Python only ever holds the erased form, so erasing is the identity here.
    assert first.erase() == first


def test_the_bridge_carries_a_range_fact_up_and_back() -> None:
    fact = whole()
    equality = fact.to_blob_fact()

    # A whole-blob fact loses its span on the way up, the whole-blob span
    # normalising away, so it arrives as `Blake3(h) = Bytes(b)`.
    assert equality.prop.lhs == BlobExpr.blake3(fact.hash)
    assert equality.prop.rhs == BlobExpr.bytes(BLOB)
    assert equality.to_range_fact() == fact.range(0)

    # A sub-range keeps its span.
    middle = fact.range(3, 7)
    sliced = middle.to_blob_fact()
    assert sliced.prop.lhs == BlobExpr.slice(BlobExpr.blake3(fact.hash), 3, 7)
    assert sliced.prop.rhs == BlobExpr.bytes(BLOB[3:7])

    recovered = sliced.to_range_fact()
    assert isinstance(recovered, CasRangeFact)
    assert recovered == middle
    assert recovered.hash == fact.hash
    assert recovered.start == 3
    assert recovered.end == 7
    assert recovered.bytes == BLOB[3:7]


def test_coming_back_down_is_partial_in_the_shapes_it_can_express() -> None:
    fact = whole()
    equality = fact.to_blob_fact()

    # Bytes on the left is the mirrored shape, and `symm` is how to ask for it.
    with pytest.raises(CasRangeError):
        equality.symm().to_range_fact()
    assert equality.symm().symm().to_range_fact() == fact.range(0)

    # Neither a concatenation nor a run of zeros is a range fact's shape.
    with pytest.raises(CasRangeError):
        BlobFact.refl(BlobExpr.zero(3)).to_range_fact()
    with pytest.raises(CasRangeError):
        equality.cat(equality).to_range_fact()


def test_facts_carry_their_claim_without_a_way_to_forge_one() -> None:
    fact = head()

    assert fact == head()
    assert hash(fact) == hash(head())
    assert {fact, head()} == {fact}
    assert "BlobFact(" in repr(fact)

    # Nothing hands Python a way to mint one: no constructor, no subclass to
    # override, no unpickling back into existence, and no mutable field.
    with pytest.raises(TypeError):
        BlobFact()  # type: ignore[call-arg]
    with pytest.raises(TypeError):

        class ForgedBlobFact(BlobFact):  # type: ignore[misc]
            pass

    with pytest.raises(AttributeError):
        fact.prop = BlobEq(BlobExpr.zero(0), BlobExpr.zero(1))  # type: ignore[misc]
    with pytest.raises((TypeError, pickle.PicklingError)):
        pickle.dumps(fact)

    # The proposition beneath it is ordinary data anyone may build.
    assert BlobEq(BlobExpr.zero(0), BlobExpr.zero(1)).decide() is False


def test_expressions_hash_consistently_with_equality() -> None:
    literal = BlobExpr.bytes(b"abc")
    same = BlobExpr.bytes(b"abc")

    assert literal == same
    assert hash(literal) == hash(same)
    assert len({literal, same}) == 1
    assert literal != BlobExpr.zero(3)
    assert literal != 3

    # Two independently built copies of a shared DAG are equal, and hash alike
    # without either being walked.
    assert doubled(9) == doubled(9)
    assert hash(doubled(9)) == hash(doubled(9))

    # Ordering is not defined anywhere in the calculus. Defining `__eq__` fills
    # the one comparison slot, so all six methods exist; the four unused ones
    # answer `NotImplemented`, which is a `TypeError` at the operator.
    for left, right in (
        (literal, same),
        (BlobEq(literal, same), BlobEq(same, literal)),
        (BlobFact.refl(literal), BlobFact.refl(same)),
    ):
        assert left == right
        assert not left != right
        with pytest.raises(TypeError):
            operator.lt(left, right)
        with pytest.raises(TypeError):
            operator.ge(left, right)


def test_plus_is_concatenation_and_never_coerces_an_operand() -> None:
    left = BlobExpr.bytes(b"ab")
    right = BlobExpr.zero(2)

    assert left + right == BlobExpr.cat(left, right)
    assert (left + right).eval() == b"ab\0\0"
    # Associativity is a fact about the bytes, not about the syntax: the two
    # groupings are different expressions that denote the same thing.
    tail = BlobExpr.bytes(b"c")
    assert (left + right) + tail != left + (right + tail)
    assert BlobEq((left + right) + tail, left + (right + tail)).decide() is True

    # `bytes` is not coerced, in either direction. A 32-byte value is
    # `BlobExpr.bytes(b)` or `BlobExpr.blake3(h)`, two different expressions,
    # and a coercion would have to guess which was meant.
    with pytest.raises(TypeError):
        left + b"c"  # type: ignore[operator]  # noqa: B015
    with pytest.raises(TypeError):
        b"c" + left  # type: ignore[operator]  # noqa: B015

    # `+` fills one slot, so the reflected form exists as well. It concatenates
    # in the order it is written, which is the only thing it could mean.
    assert BlobExpr.__radd__(left, right) == right + left


def test_brackets_are_slicing_in_the_calculus_coordinates() -> None:
    ten = BlobExpr.bytes(BLOB)

    assert ten[3:7] == BlobExpr.slice(ten, 3, 7)
    assert ten[3:7].eval() == BLOB[3:7]
    # An omitted stop is the open case, which runs to the end of the subject.
    assert ten[3:] == BlobExpr.slice(ten, 3)
    assert ten[3:].eval() == BLOB[3:]
    # An omitted start is zero, and omitting both is the whole-blob span, which
    # normalises away rather than wrapping anything.
    assert ten[:7] == BlobExpr.slice(ten, 0, 7)
    assert ten[:] == ten

    # A slice of known-length bytes has the width of its span.
    assert ten[3:7].len_bytes == 4

    # Slicing a digest is the shape a range fact has, and stays unreadable.
    named = BlobExpr.blake3(whole().hash)
    assert named[3:7] == BlobExpr.slice(named, 3, 7)
    assert named[3:7].eval() is None
    # Its length is unknown too, though the span is closed: a slice is as long
    # as its span only where the span is known to be in range, and nothing here
    # knows how long the named blob is. Answering `4` from the span alone would
    # refute `named[3:7] == named[3:9]`, which is false whenever the blob is
    # shorter than seven bytes and both sides denote nothing at all.
    assert named[3:7].len_bytes is None
    assert BlobEq(named[3:7], named[3:9]).decide() is None

    # Where it parts company with `bytes`: out of range denotes nothing rather
    # than narrowing to what is there, and a backwards span is refused.
    assert BLOB[5:99] == BLOB[5:]
    assert ten[5:99].eval() is None
    with pytest.raises(CasRangeError):
        ten[7:3]


def test_a_slice_with_a_step_is_refused() -> None:
    ten = BlobExpr.bytes(BLOB)

    # A stride is not a sub-range, and there is no expression denoting one.
    with pytest.raises(CasRangeError, match="step"):
        ten[::2]
    with pytest.raises(CasRangeError, match="step"):
        ten[3:7:2]
    # Including the identity stride: accepting `1` and refusing `2` would read
    # as support for a notion the calculus does not have.
    with pytest.raises(CasRangeError, match="step"):
        ten[3:7:1]
    # A reversal is a step too, and is refused rather than silently emptied.
    with pytest.raises(CasRangeError, match="step"):
        ten[::-1]


def test_offsets_are_absolute_and_a_position_is_not_an_index() -> None:
    ten = BlobExpr.bytes(BLOB)

    # Counting back from the end would need a length that an expression need
    # not have: `BlobExpr.blake3(h)[-4:]` has no meaning to give.
    with pytest.raises(CasRangeError, match="absolute"):
        ten[-4:]
    with pytest.raises(CasRangeError, match="absolute"):
        ten[:-4]

    # One byte of a blob expression is a one-byte expression, not an `int`, so
    # a position is a type error rather than a silently different answer.
    with pytest.raises(TypeError, match="position"):
        ten[3]
    assert ten[3:4].eval() == BLOB[3:4]

    # Which also means an expression does not iterate. Falling through to the
    # old sequence protocol reaches the same refusal rather than looping.
    with pytest.raises(TypeError, match="position"):
        list(ten)


def test_there_is_no_len_because_a_length_may_be_unknown() -> None:
    """``len()`` must return an ``int``, and this length is three-valued."""
    ten = BlobExpr.bytes(BLOB)

    with pytest.raises(TypeError, match="len"):
        len(ten)  # type: ignore[arg-type]
    # `len_bytes` is the total accessor, and answers where `len()` could not:
    # `None` rather than an exception behind a digest, and a number past
    # `sys.maxsize`, which a `__len__` may not return.
    assert ten.len_bytes == len(BLOB)
    assert BlobExpr.blake3(whole().hash).len_bytes is None
    assert BlobExpr.zero(2**64 - 1).len_bytes == 2**64 - 1

    # `bool()` falls back on `__len__`, so adding one would have made
    # `if blob:` raise on exactly the expressions that most need a guard.
    # Without one every expression is truthy, including the empty one.
    assert bool(ten)
    assert bool(BlobExpr.zero(0))
    assert bool(BlobExpr.blake3(whole().hash))


def test_repr_rebuilds_what_it_prints_and_summarises_what_it_cannot() -> None:
    scope = {"BlobExpr": BlobExpr, "O256": O256}
    for expr in (
        BlobExpr.bytes(b"ab\n'"),
        BlobExpr.zero(7),
        BlobExpr.blake3(whole().hash),
        BlobExpr.bytes(b"ab") + BlobExpr.zero(2),
        BlobExpr.bytes(BLOB)[3:7],
        BlobExpr.bytes(BLOB)[3:],
    ):
        assert eval(repr(expr), scope) == expr  # noqa: S307

    # Past the bound it summarises, because a `repr` may not walk a tree of
    # `2 ** 64` nodes. The root and the size are O(1) and say what it is.
    hyper = doubled(10)
    assert repr(hyper) == "BlobExpr.cat(size=2047)"
    assert repr(BlobExpr.bytes(bytes(64))) == "BlobExpr.bytes(len=64)"
    # The compound reprs are built from the same rendering, so neither of them
    # walks one either.
    assert repr(BlobEq(hyper, hyper)) == f"BlobEq(lhs={hyper!r}, rhs={hyper!r})"
    assert repr(BlobFact.refl(hyper)) == f"BlobFact(lhs={hyper!r}, rhs={hyper!r})"


def test_slicing_a_fact_is_the_congruence_rule() -> None:
    fact = head()

    assert fact[0:2] == fact.slice(0, 2)
    assert fact[0:] == fact.slice(0)
    assert fact[0:2].prop.lhs.eval() == b"ab"
    assert fact[0:2].prop.rhs.eval() == b"ab"

    # One span for both sides, so the unsound shape is unreachable through the
    # brackets as well as through the method.
    with pytest.raises(CasRangeError, match="step"):
        fact[::2]
    with pytest.raises(CasRangeError):
        fact[7:3]
    with pytest.raises(TypeError, match="position"):
        fact[0]


def test_concatenating_facts_is_the_other_congruence_rule() -> None:
    first = head()
    tail = BlobFact.refl(BlobExpr.zero(1))

    assert first + tail == first.cat(tail)
    assert (first + tail).prop.lhs.eval() == b"abc\0"
    assert (first + tail).prop.rhs.eval() == b"abc\0"

    # `+` concatenates what the facts are about, so it reads in the order the
    # bytes appear in and is not commutative.
    assert (tail + first).prop.rhs.eval() == b"\0abc"
    assert first + tail != tail + first

    # It says nothing about the operands standing in any relation to each
    # other: a fact about `"abc"` and one about a zero byte concatenate, and
    # the conclusion mentions neither an `"abc" = "\0"` nor anything like it.
    assert first.prop.rhs != tail.prop.rhs
    assert (first + tail).prop == BlobEq(
        BlobExpr.cat(first.prop.lhs, tail.prop.lhs),
        BlobExpr.cat(first.prop.rhs, tail.prop.rhs),
    )

    # A fact is not an expression and neither coerces into the other, so the
    # two `+`s never quietly mix.
    with pytest.raises(TypeError):
        first + BlobExpr.zero(1)  # type: ignore[operator]  # noqa: B015
    with pytest.raises(TypeError):
        BlobExpr.zero(1) + first  # type: ignore[operator]  # noqa: B015


def test_a_store_is_where_the_calculus_learns_what_a_digest_names() -> None:
    cas = IndexCas()
    cas.put(BLOB)
    address = O256.hash(BLOB)

    # Nothing in `BlobExpr` reads a store, so resolving a digest is exactly
    # what it cannot do alone. This is the step that supplies one.
    named = BlobExpr.blake3(address)
    assert named.eval() is None
    assert BlobEq(named, BlobExpr.bytes(BLOB)).decide() is None

    fact = cas.blob_fact(address)
    assert fact == cas.get_fact(address).to_blob_fact()
    assert fact.prop.lhs == named
    assert fact.prop.rhs == BlobExpr.bytes(BLOB)
    # And with it in hand, the rules read the range out of the digest. The
    # congruence rule alone yields `Slice(Blake3(h), 3..7) = Slice(b, 3..7)`,
    # whose right side is still a slice rather than the literal bytes a range
    # fact names, so it is evaluation that finishes the job.
    sliced = fact[3:7]
    assert sliced.prop.rhs.eval() == BLOB[3:7]
    with pytest.raises(CasRangeError, match="shape"):
        sliced.to_range_fact()

    evaluated = BlobFact.check(BlobEq(sliced.prop.rhs, BlobExpr.bytes(BLOB[3:7])))
    read_out = sliced.trans(evaluated)
    assert read_out.prop.rhs == BlobExpr.bytes(BLOB[3:7])
    assert read_out.to_range_fact() == cas.range(address, 3, 7)

    # Residency is a question a store always answers, so `in` is honest here
    # in the way `len()` would not be on an expression.
    assert address in cas
    assert O256.hash(b"absent") not in cas
    assert len(cas) == 1
    with pytest.raises(CasNotFoundError):
        cas.blob_fact(O256.hash(b"absent"))
