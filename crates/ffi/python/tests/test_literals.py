"""Typed symbolic construction and the actual checked computation boundary."""

import pytest
from covalence import _covalence
from covalence.logic.hol import Arena, Kernel
from covalence.logic.literals import Context, Expr, Function, Type


@pytest.mark.parametrize(
    "value",
    [
        0,
        127,
        128,
        -128,
        -129,
        -(2**63),
        2**63 - 1,
        2**63,
        -(2**63) - 1,
        2**256,
        -(2**256),
        2**20000,
        -(2**20000),
    ],
    ids=lambda value: (
        f"{'negative' if value < 0 else 'positive'}-{value.bit_length()}bits"
    ),
)
def test_python_integers_are_exact_int_literals(value):
    ctx = Context()
    term = ctx(value)
    assert term.type is Type.INT
    assert term.value == value
    result = term.evaluate()
    assert result.value == value
    lhs, rhs = ctx.kernel.theorem(result.theorem)
    assert lhs == []
    assert len(rhs) == 1 and len(rhs[0]) == 1


def test_bool_is_not_an_integer_and_bytes_roundtrip():
    ctx = Context()
    assert ctx(True).type is Type.BOOL
    assert ctx(False).value is False
    assert ctx(b"\x00\xffWASM").value == b"\x00\xffWASM"
    for constructor in (ctx.int, ctx.nat, ctx.i8, ctx.i16, ctx.i32, ctx.i64):
        with pytest.raises(TypeError):
            constructor(True)
    for value in ("123", 1.25, [], bytearray(b"abc"), None):
        with pytest.raises(TypeError):
            ctx(value)


@pytest.mark.parametrize("left", [False, True])
@pytest.mark.parametrize("right", [False, True])
def test_boolean_builtins_follow_truth_tables(left, right):
    ctx = Context()
    a, b = ctx(left), ctx(right)
    cases = [
        (~a, not left),
        (a & b, left and right),
        (a | b, left or right),
        (a ^ b, left != right),
        (a.implies(b), (not left) or right),
        (a.iff(b), left == right),
        (a == b, left == right),
        (a != b, left != right),
    ]
    for expression, expected in cases:
        evaluation = expression.evaluate()
        assert evaluation.value is expected
        assert ctx.kernel.theorem(evaluation.theorem)[0] == []


def test_builtin_aliases_have_one_canonical_function():
    ctx = Context()
    aliases = [
        ("bool.eq", "bool.iff"),
        ("bytes.encode.i8.little", "bytes.encode.i8.big"),
        ("bytes.decode.i8.little", "bytes.decode.i8.big"),
        ("cast.i32.i32.wrap", "cast.i32.i32.zero_extend"),
        ("cast.i32.i32.wrap", "cast.i32.i32.sign_extend"),
    ]
    for left, right in aliases:
        a, b = ctx.builtin_function(left), ctx.builtin_function(right)
        assert a.term.reference == b.term.reference


def test_implicit_references_are_not_theorem_polarity():
    ctx = Context()
    for value in (ctx(True), ctx(False), ctx.i8(1), ctx.i64(1), ctx.nat(1)):
        assert value.term.reference < 0
        assert ctx.kernel.tm(value.term.reference).reference == value.term.reference
        assert ctx.kernel.arena.definition(value.term.reference) is not None
        with pytest.raises(ValueError):
            ctx.kernel.lit(value.term.reference)
        with pytest.raises(ValueError):
            ctx.kernel.lit(value.term.reference, negated=True)
    assert ctx.kernel.theorem(ctx.kernel.true_right()) == ([], [[]])
    assert ctx.kernel.theorem(ctx.kernel.false_left()) == ([[]], [])
    proposition = ctx.variable(17, Type.BOOL)
    literal = ctx.kernel.lit(proposition.term.reference)
    assert ctx.kernel.theorem(ctx.kernel.identity(literal)) == (
        [[literal]],
        [[literal]],
    )


def test_context_capability_is_explicit_and_existing_kernel_is_preserved():
    assert Context().kernel.arena.axioms == ["ax.inf"]
    kernel = Kernel()
    ctx = Context(kernel)
    assert ctx.kernel is kernel
    with pytest.raises(ValueError):
        ctx.int(1)
    assert kernel.arena.axioms == []
    kernel.add_axiom("ax.inf")
    assert ctx.int(1).value == 1


@pytest.mark.parametrize("ty", [Type.I8, Type.I16, Type.I32, Type.I64])
def test_word_constructor_ranges_and_explicit_wrapping(ty):
    ctx = Context()
    width = ty.width
    sign = 1 << (width - 1)
    modulus = 1 << width
    for value in (-sign, -1, 0, sign - 1):
        term = ctx.literal(ty, value)
        assert term.value == value % modulus
        assert term.signed_value == value
    assert ctx.literal(ty, modulus - 1, signed=False).value == modulus - 1
    for value in (-sign - 1, sign):
        with pytest.raises(OverflowError):
            ctx.literal(ty, value)
    for value in (-1, modulus):
        with pytest.raises(OverflowError):
            ctx.literal(ty, value, signed=False)
    assert ctx.literal(ty, 2**512 + 3, wrap=True).value == 3
    assert ctx.literal(ty, -(2**512) - 3, wrap=True).value == modulus - 3


def test_symbolic_operations_do_not_gain_python_truthiness():
    ctx = Context()
    x = ctx.variable(12, Type.I32)
    term = (x + ctx.i32(3)) == ctx.i32(5)
    assert term.type is Type.BOOL
    assert (ctx(True) == ctx(False)).evaluate().value is False
    assert (ctx(True) != ctx(False)).evaluate().value is True
    for value in (x, term, ctx(True), ctx.i32(0)):
        with pytest.raises(TypeError, match="truth value"):
            bool(value)
        with pytest.raises(TypeError):
            hash(value)
    with pytest.raises(ValueError):
        _ = x.value
    with pytest.raises(ValueError):
        term.evaluate()
    with pytest.raises(TypeError, match="ordering"):
        _ = x < ctx.i32(2)


def test_other_context_and_wrong_types_fail_before_trusting_evidence():
    ctx, other = Context(), Context()
    a, b = ctx.i32(1), other.i32(1)
    with pytest.raises(ValueError, match="another context"):
        a + b
    with pytest.raises(TypeError, match="expected i32"):
        a + ctx.int(1)
    with pytest.raises(ValueError, match="another kernel"):
        ctx.kernel._literal_builtin("i32.add", [a.term, b.term])
    with pytest.raises(ValueError):
        ctx.kernel._literal_builtin("i32.add", [a.term, ctx.int(1).term])
    with pytest.raises(TypeError):
        _covalence.HolLiteralReduction()


def test_evaluation_evidence_checks_its_owner_and_live_statement():
    ctx = Context()
    result = (ctx.i32(20) + ctx.i32(22)).evaluate()
    assert result.evidence.source.reference != result.evidence.result.reference
    with pytest.raises(ValueError, match="another kernel"):
        result.evidence.theorem(Context().kernel)
    theorem = result.theorem
    assert ctx.kernel.remove_theorem(theorem)
    _ = (ctx.i32(1) + ctx.i32(1)).evaluate()
    with pytest.raises(ValueError):
        _ = result.theorem
    assert result.value == 42


def test_builtin_functions_use_typed_partial_application():
    ctx = Context()
    add = ctx.builtin_function("i32.add")
    assert isinstance(add, Function)
    assert add.parameters == (Type.I32, Type.I32)
    assert add.result_type is Type.I32
    assert add() is add
    increment = add(ctx.i32(1))
    assert isinstance(increment, Function)
    assert increment.parameters == (Type.I32,)
    assert increment(ctx.i32(41)).evaluate().value == 42
    assert add(ctx.i32(20), ctx.i32(22)).evaluate().value == 42
    assert ctx.builtin("i32.add", ctx.i32(20), ctx.i32(22)).evaluate().value == 42
    assert isinstance(ctx.builtin_function("bytes.empty"), Expr)
    assert ctx.builtin_function("bytes.empty").evaluate().value == b""
    assert ctx.builtin_function("int.add")(2**256)(1).evaluate().value == 2**256 + 1
    with pytest.raises(TypeError, match="truth value"):
        bool(add)
    with pytest.raises(TypeError, match="expected i32"):
        add(1)
    with pytest.raises(TypeError, match="at most"):
        add(ctx.i32(1), ctx.i32(2), ctx.i32(3))


def test_partial_application_preserves_ownership_and_checks_every_argument():
    ctx = Context()
    add = ctx.builtin_function("i32.add")
    a, b = ctx.i32(1), ctx.int(2)
    other = Context()
    foreign = other.i32(3)
    before = ctx.kernel.arena.to_cbor()
    with pytest.raises(ValueError, match="another context"):
        add(foreign)
    with pytest.raises(ValueError, match="another kernel"):
        ctx.kernel._literal_apply(add.term, [foreign.term])
    with pytest.raises(ValueError):
        ctx.kernel._literal_apply(add.term, [a.term, b.term])
    assert ctx.kernel.arena.to_cbor() == before


@pytest.mark.parametrize("ty", [Type.I8, Type.I16, Type.I32, Type.I64])
def test_word_operations_are_checked_at_every_width(ty):
    ctx = Context()

    def word(n):
        return ctx.literal(ty, n)

    mask = (1 << ty.width) - 1
    a, b = word(-7), word(3)
    cases = [
        (a + b, mask - 3),
        (a - b, mask - 9),
        (a * b, mask - 20),
        (a.div_s(b), mask - 1),
        (a.rem_s(b), mask),
        (a.div_u(b), (mask - 6) // 3),
        (a.rem_u(b), (mask - 6) % 3),
        (a & b, 1),
        (a | b, mask - 4),
        (a ^ b, mask - 5),
        (~a, 6),
        (word(1).shl(word(ty.width + 1)), 2),
        (a.shr_s(1), mask - 3),
        (a.shr_u(1), (mask - 6) >> 1),
        (word(1).rotl(1), 2),
        (word(2).rotr(1), 1),
        (word(1).clz(), ty.width - 1),
        (word(8).ctz(), 3),
        (a.popcnt(), ty.width - 2),
        (word(0).eqz(), True),
        (a == b, False),
        (a != b, True),
        (a.lt_s(b), True),
        (a.lt_u(b), False),
        (a.le_s(b), True),
        (a.le_u(b), False),
        (a.gt_s(b), False),
        (a.gt_u(b), True),
        (a.ge_s(b), False),
        (a.ge_u(b), True),
    ]
    for term, expected in cases:
        result = term.evaluate()
        assert result.value == expected
        assert ctx.kernel.theorem(result.theorem)[0] == []
    assert ((word(2) + word(3)) * word(4)).evaluate().value == 20


@pytest.mark.parametrize("natural", [False, True])
def test_unbounded_arithmetic_bitwise_and_order(natural):
    ctx = Context()
    make = ctx.nat if natural else ctx.int
    a, b = make(25), make(4)
    cases = [
        (a + b, 29),
        (a - b, 21),
        (a * b, 100),
        (a.div(b), 6),
        (a.rem(b), 1),
        (a.succ(), 26),
        (a.pred(), 24),
        (a.pow(2), 625),
        (a.min(b), 4),
        (a.max(b), 25),
        (a & b, 0),
        (a | b, 29),
        (a ^ b, 29),
        (a.shl(3), 200),
        (a.shr(3), 3),
        (a == b, False),
        (a != b, True),
        (a < b, False),
        (a <= b, False),
        (a > b, True),
        (a >= b, True),
    ]
    for term, expected in cases:
        assert term.evaluate().value == expected
    if natural:
        assert (b - a).evaluate().value == 0
    else:
        assert (-a).evaluate().value == -25
        assert abs(-a).evaluate().result.type is Type.NAT
        assert abs(-a).evaluate().value == 25
        assert (~a).evaluate().value == -26
        assert ctx(-7).div(3).evaluate().value == -2
        assert ctx(-7).rem(3).evaluate().value == -1


@pytest.mark.parametrize("ty", [Type.I8, Type.I16, Type.I32, Type.I64])
def test_casts_and_word_byte_codecs(ty):
    ctx = Context()
    mask = (1 << ty.width) - 1
    value = ctx.literal(ty, -1)
    assert value.to_nat().evaluate().value == mask
    assert value.to_int().evaluate().value == -1
    assert value.to_int(signed=False).evaluate().value == mask
    assert ctx.nat(mask).to_word(ty).evaluate().value == mask
    assert ctx(-1).to_word(ty).evaluate().value == mask
    assert ctx(mask).to_word(ty, signed=False).evaluate().value == mask
    assert ctx.nat(mask + 2).to_word(ty, wrap=True).evaluate().value == 1
    assert ctx(-1).to_word(ty, wrap=True).evaluate().value == mask
    for byteorder in ("little", "big"):
        sample = ctx.literal(ty, 0x41)
        encoded = sample.to_bytes(byteorder)
        assert encoded.evaluate().value == (0x41).to_bytes(ty.width // 8, byteorder)
        assert encoded.decode_word(ty, byteorder).evaluate().value == 0x41
        backing = ctx.bytes(b"!" + b"\x00" * (ty.width // 8) + b"?")
        assert (
            backing.write_word(1, sample, byteorder)
            .read_word(1, ty, byteorder)
            .evaluate()
            .value
            == 0x41
        )


def test_explicit_extensions_and_unbounded_casts():
    ctx = Context()
    assert ctx.i8(-1).zero_extend(Type.I64).evaluate().value == 255
    assert ctx.i8(-1).sign_extend(Type.I64).evaluate().result.signed_value == -1
    assert ctx.i64(256).wrap_to(Type.I8).evaluate().value == 0
    assert ctx.i16(255).to_word(Type.I8, signed=False).evaluate().value == 255
    assert ctx.i16(-1).to_word(Type.I8).evaluate().result.signed_value == -1
    assert ctx.i16(256).to_word(Type.I8, wrap=True).evaluate().value == 0
    with pytest.raises(ValueError):
        ctx.i16(255).to_word(Type.I8).evaluate()
    assert ctx.i32(255).extend_sign(Type.I8).evaluate().result.signed_value == -1
    assert ctx.nat(2**256).to_int().evaluate().value == 2**256
    assert ctx(2**256).to_nat().evaluate().value == 2**256
    with pytest.raises(ValueError):
        ctx(-1).to_nat().evaluate()
    with pytest.raises(ValueError):
        ctx.i64(256).zero_extend(Type.I8)


def test_byte_lists_ranges_and_persistent_updates():
    ctx = Context()
    source = ctx.bytes(b"abc")
    assert source.length.evaluate().value == 3
    assert source[1].evaluate().value == ord("b")
    assert source[1:3].evaluate().value == b"bc"
    assert source[1:100].evaluate().value == b"bc"
    assert source[3:1].evaluate().value == b""
    assert source[:].evaluate().value == b"abc"
    assert source.slice(1, 2).evaluate().value == b"bc"
    assert source.replace(1, 1, b"xyz").evaluate().value == b"axyzc"
    assert source.set(1, 255).evaluate().value == b"a\xffc"
    assert source.value == b"abc"
    assert (source + b"d").evaluate().value == b"abcd"
    assert (b"!" + source).evaluate().value == b"!abc"
    assert source.cons(255).snoc(0).evaluate().value == b"\xffabc\x00"
    assert [x.evaluate().value for x in source.split_at(1)] == [b"a", b"bc"]
    assert ctx.bytes_from([1, ctx.i8(-1), 3]).evaluate().value == b"\x01\xff\x03"
    assert ctx.repeat_byte(255, 3).evaluate().value == b"\xff" * 3
    assert (source < ctx.bytes(b"b")).evaluate().value is True
    assert (source == ctx.bytes(b"abc")).evaluate().value is True


def test_undefined_and_resource_limited_evaluations_produce_no_theorem():
    ctx = Context()
    failures = [
        ctx.i32(1).div_u(0),
        ctx.i8(-128).div_s(-1),
        ctx.nat(1).div(0),
        ctx(-1).to_word(Type.I8, signed=False),
        ctx.nat(256).to_word(Type.I8),
        ctx.bytes(b"a")[1],
        ctx.bytes(b"a").slice(0, 2),
        ctx.bytes(b"a").decode_word(Type.I32),
    ]
    for term in failures:
        before = ctx.kernel.arena.to_cbor()
        with pytest.raises(ValueError):
            term.evaluate()
        assert ctx.kernel.arena.to_cbor() == before
    term = ctx.repeat_byte(0, 1024)
    before = ctx.kernel.arena.to_cbor()
    with pytest.raises(ValueError):
        term.evaluate(max_bytes=16)
    assert ctx.kernel.arena.to_cbor() == before
    with pytest.raises(ValueError):
        ctx.nat(-1)
    with pytest.raises(ValueError):
        ctx.bytes(b"abc")[-1]
    with pytest.raises(ValueError):
        ctx.bytes(b"abc")[::2]


def test_serialization_keeps_literal_values_and_builtin_rows():
    ctx = Context()
    terms = [
        ctx(2**256),
        ctx(-(2**256)),
        ctx.nat(2**63),
        ctx.i64(-1),
        ctx.bytes(b"\0\xff"),
    ]
    result = (terms[0] + 1).evaluate()
    wire = ctx.kernel.arena.to_cbor()
    assert Arena.from_cbor(wire).to_cbor() == wire
    assert result.value == 2**256 + 1


def test_builtin_matching_pairs_with_construction_without_evaluation():
    ctx = Context()
    x, y = ctx.variable(1, Type.I32), ctx.i32(7)
    add = ctx.builtin_function("i32.add")
    application = add(x, y)
    before = ctx.kernel.arena.to_cbor()
    for matched in (add.match(application), application.match_builtin("i32.add")):
        assert matched is not None
        assert [arg.term.reference for arg in matched] == [
            x.term.reference,
            y.term.reference,
        ]
    assert ctx.kernel.arena.to_cbor() == before
    assert application.match_builtin("i32.sub") is None
    assert add.match(x) is None
    assert add(x).match(application)[0].term.reference == y.term.reference
    assert add(y).match(application) is None
    with pytest.raises(ValueError, match="context"):
        add.match(Context().i32(7))
    with pytest.raises(TypeError, match="Expr"):
        add.match(7)

    conjunction = ctx.and_(True, False)
    assert [arg.value for arg in conjunction.match_builtin("bool.and")] == [True, False]
    assert ctx.not_(False).evaluate().value is True
    assert ctx.or_(False, True).evaluate().value is True
    assert ctx.implies(True, False).evaluate().value is False
    assert ctx.iff(True, False).match_builtin("bool.eq") is not None
    assert ctx.builtin_function("bytes.empty").match_builtin("bytes.empty") == ()
