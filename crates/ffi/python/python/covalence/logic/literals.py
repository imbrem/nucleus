"""Typed symbolic literals and checked computation in a HOL kernel.

``Context`` owns construction; ``Expr`` owns no storage policy. Python ``int``
becomes mathematical ``Int`` (including arbitrarily large values), ``bool``
becomes ``Bool``, and ``bytes`` becomes ``Bytes``. Expressions are symbolic:
even equality builds a proposition, and Python truth testing always raises.
Call ``evaluate()`` explicitly to obtain kernel-checked computation evidence.
"""

from __future__ import annotations

from enum import StrEnum
from typing import TYPE_CHECKING

from .hol import Kernel

if TYPE_CHECKING:
    from .._covalence import HolLiteralReduction, HolTm

__all__ = ["Context", "Expr", "Function", "Type", "Evaluation"]


class Type(StrEnum):
    """Logical types; signedness belongs to operations on fixed-width words."""

    BOOL = "bool"
    I8 = "i8"
    I16 = "i16"
    I32 = "i32"
    I64 = "i64"
    NAT = "nat"
    INT = "int"
    BYTES = "bytes"

    @property
    def width(self) -> int | None:
        return {Type.I8: 8, Type.I16: 16, Type.I32: 32, Type.I64: 64}.get(self)


def _integer(value: object) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError("expected an integer, excluding bool")
    return value


class Context:
    """A convenient typed surface over an existing or fresh checked kernel.

    A fresh context records ``ax.inf``, which supplies the literal carriers.
    An existing kernel must already enable that capability; attaching a Context
    does not silently extend its assumptions.

    Fixed-width constructors accept signed values by default. ``signed=False``
    accepts unsigned bit patterns; ``wrap=True`` explicitly reduces any Python
    integer modulo the width. Ordinary constructors never silently truncate.
    """

    __slots__ = ("_kernel",)

    def __init__(self, kernel: Kernel | None = None) -> None:
        self._kernel = Kernel() if kernel is None else kernel
        if kernel is None:
            self._kernel.add_axiom("ax.inf")

    @property
    def kernel(self) -> Kernel:
        """The checked kernel, for composing these terms with general HOL."""
        return self._kernel

    def __call__(self, value: Expr | bool | int | bytes) -> Expr:
        if isinstance(value, Expr):
            if value._context is not self:
                raise ValueError("expression belongs to another context")
            return value
        if isinstance(value, bool):
            return self.literal(Type.BOOL, value)
        if isinstance(value, int):
            return self.int(value)
        if isinstance(value, bytes):
            return self.bytes(value)
        raise TypeError("expected an expression, bool, integer, or bytes")

    def _wrap(self, term: HolTm) -> Expr:
        return Expr(self, term, Type(self._kernel._literal_type(term)))

    def literal(
        self,
        ty: Type,
        value: bool | int | bytes,
        *,
        signed: bool = True,
        wrap: bool = False,
    ) -> Expr:
        """Construct a literal, checking its type and range before allocation."""
        ty = Type(ty)
        if ty.width is not None:
            value = _integer(value)
            width = ty.width
            if not wrap:
                low = -(1 << (width - 1)) if signed else 0
                high = (1 << (width - int(signed))) - 1
                if not low <= value <= high:
                    interpretation = "signed" if signed else "unsigned"
                    raise OverflowError(
                        f"value is outside {ty.value}'s {interpretation} range"
                    )
            value %= 1 << width
        elif signed is not True or wrap:
            raise TypeError("signed and wrap apply only to fixed-width literals")
        elif ty in (Type.NAT, Type.INT):
            value = _integer(value)
            if ty is Type.NAT and value < 0:
                raise ValueError("a natural literal cannot be negative")
        elif ty is Type.BOOL:
            if not isinstance(value, bool):
                raise TypeError("a Bool literal requires bool")
        elif not isinstance(value, bytes):
            raise TypeError("a Bytes literal requires bytes")
        return self._wrap(self._kernel._literal(ty.value, value))

    def bool(self, value: bool) -> Expr:
        return self.literal(Type.BOOL, value)

    def int(self, value: int) -> Expr:
        return self.literal(Type.INT, value)

    def nat(self, value: int) -> Expr:
        return self.literal(Type.NAT, value)

    def bytes(self, value: bytes) -> Expr:
        return self.literal(Type.BYTES, value)

    def bytes_from(self, values: list[Expr | int] | tuple[Expr | int, ...]) -> Expr:
        """Build a finite byte list, including symbolic octets."""
        if not isinstance(values, (list, tuple)):
            raise TypeError("expected a list or tuple of octets")
        if all(
            isinstance(value, int) and not isinstance(value, bool) for value in values
        ):
            return self.bytes(bytes(values))
        result = self.bytes(b"")
        for value in values:
            result = result.snoc(value)
        return result

    def repeat_byte(self, value: Expr | int, count: Expr | int) -> Expr:
        byte = self(value) if isinstance(value, Expr) else self.i8(value, signed=False)
        length = self(count) if isinstance(count, Expr) else self.nat(count)
        return self.builtin("bytes.repeat", byte, length)

    def i8(self, value: int, *, signed: bool = True, wrap: bool = False) -> Expr:
        return self.literal(Type.I8, value, signed=signed, wrap=wrap)

    def i16(self, value: int, *, signed: bool = True, wrap: bool = False) -> Expr:
        return self.literal(Type.I16, value, signed=signed, wrap=wrap)

    def i32(self, value: int, *, signed: bool = True, wrap: bool = False) -> Expr:
        return self.literal(Type.I32, value, signed=signed, wrap=wrap)

    def i64(self, value: int, *, signed: bool = True, wrap: bool = False) -> Expr:
        return self.literal(Type.I64, value, signed=signed, wrap=wrap)

    def variable(self, name: int, ty: Type) -> Expr:
        """Construct a free variable using the kernel's numeric name space."""
        return self._wrap(
            self._kernel._literal_variable(_integer(name), Type(ty).value)
        )

    def builtin(self, operation: str, *arguments: Expr | bool | int | bytes) -> Expr:
        """Build a typed builtin application; the kernel checks its signature.

        Names are qualified, for example ``i32.add``, ``nat.mul``, and
        ``bytes.append``. Plain Python integers remain Int here; use explicit
        constructors when the signature requires Nat or a fixed-width word.
        """
        terms = [self(argument)._term for argument in arguments]
        return self._wrap(self._kernel._literal_builtin(operation, terms))

    def not_(self, value: Expr | bool) -> Expr:
        return self.builtin("bool.not", value)

    def and_(self, left: Expr | bool, right: Expr | bool) -> Expr:
        return self.builtin("bool.and", left, right)

    def or_(self, left: Expr | bool, right: Expr | bool) -> Expr:
        return self.builtin("bool.or", left, right)

    def implies(self, left: Expr | bool, right: Expr | bool) -> Expr:
        return self.builtin("bool.imp", left, right)

    def iff(self, left: Expr | bool, right: Expr | bool) -> Expr:
        return self.builtin("bool.iff", left, right)

    def builtin_function(self, operation: str) -> Function | Expr:
        """Construct a first-class builtin with its checked function type.

        Applying fewer arguments produces a Function with the remaining
        parameters. Nullary builtins such as ``bytes.empty`` are already
        scalar terms and return Expr directly.
        """
        term, parameters, result = self._kernel._literal_function(operation)
        if not parameters:
            return self._wrap(term)
        return Function(self, term, tuple(Type(ty) for ty in parameters), Type(result))


class Function:
    """A callable checked term with scalar parameters and a scalar result.

    This is a wrapper over ordinary HOL function application. Arguments use
    Context's normal conversion policy: Python integers become Int; use
    explicit constructors for Nat and fixed-width parameters. Partial
    application keeps the remaining semantic signature. Function wrappers
    have Python identity equality; compare applied Exprs to state propositions.
    """

    __slots__ = ("_context", "_term", "_parameters", "_result_type")

    def __init__(
        self, context: Context, term: HolTm, parameters: tuple[Type, ...], result: Type
    ) -> None:
        self._context = context
        self._term = term
        self._parameters = parameters
        self._result_type = result

    @property
    def term(self) -> HolTm:
        return self._term

    @property
    def parameters(self) -> tuple[Type, ...]:
        return self._parameters

    @property
    def result_type(self) -> Type:
        return self._result_type

    def __bool__(self) -> bool:
        raise TypeError("symbolic functions have no Python truth value")

    def __repr__(self) -> str:
        signature = " -> ".join(ty.value for ty in (*self.parameters, self.result_type))
        return f"Function({signature})"

    def __call__(self, *arguments: Expr | bool | int | bytes) -> Function | Expr:
        if len(arguments) > len(self.parameters):
            raise TypeError(f"expected at most {len(self.parameters)} arguments")
        if not arguments:
            return self
        terms = [self._context(argument) for argument in arguments]
        for argument, expected in zip(terms, self.parameters, strict=False):
            if argument.type is not expected:
                raise TypeError(f"expected {expected.value}, got {argument.type.value}")
        term = self._context.kernel._literal_apply(
            self._term, [arg.term for arg in terms]
        )
        remaining = self.parameters[len(arguments) :]
        if remaining:
            return Function(self._context, term, remaining, self.result_type)
        return self._context._wrap(term)

    def match(self, expression: Expr) -> tuple[Expr, ...] | None:
        """Match a saturated application, returning its remaining arguments.

        Partial functions also require their captured argument references to
        match exactly. This inspects syntax, not semantic equality or evidence.
        """
        if not isinstance(expression, Expr):
            raise TypeError("matching requires an Expr")
        expression = self._context(expression)
        arguments = self._context.kernel._literal_match(self.term, expression.term)
        if arguments is None:
            return None
        return tuple(self._context._wrap(argument) for argument in arguments)


class Expr:
    """A symbolic typed term tied to one Context.

    ``==`` and ``!=`` build propositions. Expressions are unhashable and cannot
    be used as Python conditions; evaluate a closed Boolean explicitly. Fixed
    integer arithmetic wraps; division, remainder, ordering and right shift
    require explicitly signed or unsigned methods. ``Int.div`` truncates
    toward zero. Nat subtraction is truncated at zero.
    """

    __slots__ = ("_context", "_term", "_type")
    __hash__ = None

    def __init__(self, context: Context, term: HolTm, ty: Type) -> None:
        self._context = context
        self._term = term
        self._type = ty

    @property
    def type(self) -> Type:
        return self._type

    @property
    def term(self) -> HolTm:
        """Opaque kernel term handle for general HOL composition."""
        return self._term

    def match_builtin(self, operation: str) -> tuple[Expr, ...] | None:
        """Inspect a fully applied builtin, returning typed arguments or None.

        Matching is structural and creates no theorem facts. Canonical aliases
        match the same builtin; arguments retain their opaque term handles.
        """
        function = self._context.builtin_function(operation)
        arguments = self._context.kernel._literal_match(function.term, self.term)
        if arguments is None:
            return None
        return tuple(self._context._wrap(argument) for argument in arguments)

    @property
    def value(self) -> bool | int | bytes:
        """Read a literal; fixed-width values are returned as unsigned bits.

        Symbolic expressions raise ValueError. Reading a literal does not
        evaluate a builtin or create theorem evidence.
        """
        return self._context.kernel._literal_value(self._term)

    @property
    def signed_value(self) -> int:
        """Read a fixed-width literal as a two's-complement Python integer."""
        width = self.type.width
        if width is None:
            raise TypeError("signed_value requires a fixed-width literal")
        value = self.value
        assert isinstance(value, int)
        return value - (1 << width) if value >= 1 << (width - 1) else value

    def __bool__(self) -> bool:
        raise TypeError(
            "symbolic expressions have no Python truth value; evaluate explicitly"
        )

    def __repr__(self) -> str:
        try:
            value = self.value
        except ValueError:
            detail = "symbolic"
        else:
            if isinstance(value, int) and value.bit_length() > 256:
                detail = f"<{value.bit_length()}-bit integer>"
            elif isinstance(value, bytes) and len(value) > 64:
                detail = f"<{len(value)} bytes>"
            else:
                detail = repr(value)
        return f"Expr({self.type.value}, {detail})"

    def _coerce(self, other: Expr | bool | int | bytes, ty: Type | None = None) -> Expr:
        ty = self.type if ty is None else ty
        if isinstance(other, Expr):
            result = self._context(other)
            if result.type is not ty:
                raise TypeError(f"expected {ty.value}, got {result.type.value}")
            return result
        return self._context.literal(ty, other)

    def _op(self, operation: str, *arguments: Expr) -> Expr:
        return self._context.builtin(f"{self.type.value}.{operation}", self, *arguments)

    def _binary(self, operation: str, other: Expr | int | bytes | bool) -> Expr:
        return self._op(operation, self._coerce(other))

    def __eq__(self, other: object) -> Expr:
        return self._binary("eq", other)

    def __ne__(self, other: object) -> Expr:
        return self._binary("ne", other)

    def __add__(self, other: Expr | int | bytes) -> Expr:
        return self._binary("append" if self.type is Type.BYTES else "add", other)

    def __radd__(self, other: int | bytes) -> Expr:
        return self._coerce(other).__add__(self)

    def __sub__(self, other: Expr | int) -> Expr:
        return self._binary("sub", other)

    def __rsub__(self, other: int) -> Expr:
        return self._coerce(other).__sub__(self)

    def __mul__(self, other: Expr | int) -> Expr:
        return self._binary("mul", other)

    def __rmul__(self, other: int) -> Expr:
        return self.__mul__(other)

    def __neg__(self) -> Expr:
        if self.type.width is not None:
            return self._context.literal(self.type, 0) - self
        return self._op("neg")

    def __abs__(self) -> Expr:
        return self._op("abs")

    def __and__(self, other: Expr | int) -> Expr:
        return self._binary("and", other)

    def __or__(self, other: Expr | int) -> Expr:
        return self._binary("or", other)

    def __xor__(self, other: Expr | int) -> Expr:
        return self._binary("xor", other)

    def __invert__(self) -> Expr:
        return self._op("not")

    def implies(self, other: Expr | bool) -> Expr:
        return self._binary("imp", other)

    def iff(self, other: Expr | bool) -> Expr:
        return self._binary("iff", other)

    def _ordered(self, operation: str, other: Expr | int) -> Expr:
        if self.type.width is not None:
            raise TypeError(
                "fixed-width ordering requires lt_s/lt_u, le_s/le_u, "
                "gt_s/gt_u, or ge_s/ge_u"
            )
        return self._binary(operation, other)

    def __lt__(self, other: Expr | int) -> Expr:
        return self._ordered("lt", other)

    def __le__(self, other: Expr | int) -> Expr:
        return self._ordered("le", other)

    def __gt__(self, other: Expr | int) -> Expr:
        return self._ordered("gt", other)

    def __ge__(self, other: Expr | int) -> Expr:
        return self._ordered("ge", other)

    def div(self, other: Expr | int) -> Expr:
        return self._binary("div", other)

    def rem(self, other: Expr | int) -> Expr:
        return self._binary("rem", other)

    def succ(self) -> Expr:
        return self._op("succ")

    def pred(self) -> Expr:
        return self._op("pred")

    def pow(self, exponent: Expr | int) -> Expr:
        return self._op("pow", self._coerce(exponent, Type.NAT))

    def min(self, other: Expr | int) -> Expr:
        return self._binary("min", other)

    def max(self, other: Expr | int) -> Expr:
        return self._binary("max", other)

    def div_s(self, other: Expr | int) -> Expr:
        return self._binary("div_s", other)

    def div_u(self, other: Expr | int) -> Expr:
        return self._binary("div_u", other)

    def rem_s(self, other: Expr | int) -> Expr:
        return self._binary("rem_s", other)

    def rem_u(self, other: Expr | int) -> Expr:
        return self._binary("rem_u", other)

    def lt_s(self, other: Expr | int) -> Expr:
        return self._binary("lt_s", other)

    def lt_u(self, other: Expr | int) -> Expr:
        return self._binary("lt_u", other)

    def le_s(self, other: Expr | int) -> Expr:
        return self._binary("le_s", other)

    def le_u(self, other: Expr | int) -> Expr:
        return self._binary("le_u", other)

    def gt_s(self, other: Expr | int) -> Expr:
        return self._binary("gt_s", other)

    def gt_u(self, other: Expr | int) -> Expr:
        return self._binary("gt_u", other)

    def ge_s(self, other: Expr | int) -> Expr:
        return self._binary("ge_s", other)

    def ge_u(self, other: Expr | int) -> Expr:
        return self._binary("ge_u", other)

    def eqz(self) -> Expr:
        return self._op("eqz")

    def clz(self) -> Expr:
        return self._op("clz")

    def ctz(self) -> Expr:
        return self._op("ctz")

    def popcnt(self) -> Expr:
        return self._op("popcnt")

    def _shift(self, operation: str, count: Expr | int) -> Expr:
        ty = self.type if self.type.width is not None else Type.NAT
        return self._op(operation, self._coerce(count, ty))

    def shl(self, count: Expr | int) -> Expr:
        return self._shift("shl", count)

    def shr(self, count: Expr | int) -> Expr:
        return self._shift("shr", count)

    def shr_s(self, count: Expr | int) -> Expr:
        return self._shift("shr_s", count)

    def shr_u(self, count: Expr | int) -> Expr:
        return self._shift("shr_u", count)

    def rotl(self, count: Expr | int) -> Expr:
        return self._shift("rotl", count)

    def rotr(self, count: Expr | int) -> Expr:
        return self._shift("rotr", count)

    def to_nat(self) -> Expr:
        """Unsigned word conversion; conversion of negative Int is partial."""
        if self.type is Type.NAT:
            return self
        return self._context.builtin(f"cast.{self.type.value}.nat", self)

    def to_int(self, *, signed: bool = True) -> Expr:
        if self.type is Type.INT:
            return self
        suffix = (
            f".{'signed' if signed else 'unsigned'}"
            if self.type.width is not None
            else ""
        )
        return self._context.builtin(f"cast.{self.type.value}.int{suffix}", self)

    def to_word(self, ty: Type, *, signed: bool = True, wrap: bool = False) -> Expr:
        """Convert an integer to a word; range failures decline evaluation.

        Nat uses the unsigned range. Int uses the selected signed or unsigned
        range. Words use that interpretation for both source and destination.
        ``wrap=True`` explicitly reduces modulo the destination width.
        """
        ty = Type(ty)
        if ty.width is None:
            raise TypeError("to_word requires a fixed-width destination")
        if self.type.width is not None:
            return self.to_int(signed=signed).to_word(ty, signed=signed, wrap=wrap)
        if self.type not in (Type.NAT, Type.INT):
            raise TypeError("to_word requires an integer source")
        mode = (
            "wrap"
            if wrap
            else "checked"
            if self.type is Type.NAT
            else "signed"
            if signed
            else "unsigned"
        )
        return self._context.builtin(f"cast.{self.type.value}.{ty.value}.{mode}", self)

    def _word_cast(self, ty: Type, mode: str) -> Expr:
        ty = Type(ty)
        if self.type.width is None or ty.width is None:
            raise TypeError("word casts require fixed-width source and destination")
        return self._context.builtin(f"cast.{self.type.value}.{ty.value}.{mode}", self)

    def wrap_to(self, ty: Type) -> Expr:
        """Truncate to an equal or narrower word."""
        return self._word_cast(ty, "wrap")

    def zero_extend(self, ty: Type) -> Expr:
        return self._word_cast(ty, "zero_extend")

    def sign_extend(self, ty: Type) -> Expr:
        return self._word_cast(ty, "sign_extend")

    def extend_sign(self, from_type: Type) -> Expr:
        """Sign-extend low bits within this word, as Wasm extend8_s etc."""
        return self._context.builtin(
            f"{self.type.value}.extend_sign.{Type(from_type).value}", self
        )

    def to_bytes(self, byteorder: str = "little") -> Expr:
        return self._context.builtin(
            f"bytes.encode.{self.type.value}.{byteorder}", self
        )

    def decode_word(self, ty: Type, byteorder: str = "little") -> Expr:
        """Decode Bytes of exactly the word's byte length."""
        return self._context.builtin(f"bytes.decode.{Type(ty).value}.{byteorder}", self)

    def read_word(self, index: Expr | int, ty: Type, byteorder: str = "little") -> Expr:
        return self._context.builtin(
            f"bytes.read.{Type(ty).value}.{byteorder}",
            self,
            self._coerce(index, Type.NAT),
        )

    def write_word(
        self, index: Expr | int, value: Expr, byteorder: str = "little"
    ) -> Expr:
        value = self._context(value)
        return self._context.builtin(
            f"bytes.write.{value.type.value}.{byteorder}",
            self,
            self._coerce(index, Type.NAT),
            value,
        )

    @property
    def length(self) -> Expr:
        """Symbolic byte length as Nat; use instead of Python len()."""
        return self._op("len")

    def __getitem__(self, index: Expr | int | slice) -> Expr:
        if self.type is not Type.BYTES:
            raise TypeError("indexing requires Bytes")
        if isinstance(index, slice):
            if index.step not in (None, 1):
                raise ValueError("symbolic byte slices do not support a step")
            start = self._coerce(0 if index.start is None else index.start, Type.NAT)
            prefix = self if index.stop is None else self.take(index.stop)
            return prefix.drop(start)
        return self._op("get", self._coerce(index, Type.NAT))

    def slice(self, start: Expr | int, length: Expr | int) -> Expr:
        """Exact range; unlike Python slicing, an out-of-bounds range fails."""
        return self._op(
            "slice", self._coerce(start, Type.NAT), self._coerce(length, Type.NAT)
        )

    def replace(
        self, start: Expr | int, length: Expr | int, replacement: Expr | bytes
    ) -> Expr:
        return self._op(
            "replace",
            self._coerce(start, Type.NAT),
            self._coerce(length, Type.NAT),
            self._coerce(replacement, Type.BYTES),
        )

    def take(self, count: Expr | int) -> Expr:
        return self._op("take", self._coerce(count, Type.NAT))

    def drop(self, count: Expr | int) -> Expr:
        return self._op("drop", self._coerce(count, Type.NAT))

    def split_at(self, index: Expr | int) -> tuple[Expr, Expr]:
        return self.take(index), self.drop(index)

    def cons(self, value: Expr | int) -> Expr:
        byte = (
            self._coerce(value, Type.I8)
            if isinstance(value, Expr)
            else self._context.i8(value, signed=False)
        )
        return self._context.builtin("bytes.cons", byte, self)

    def snoc(self, value: Expr | int) -> Expr:
        byte = (
            self._coerce(value, Type.I8)
            if isinstance(value, Expr)
            else self._context.i8(value, signed=False)
        )
        return self._op("snoc", byte)

    def set(self, index: Expr | int, value: Expr | int) -> Expr:
        """Return Bytes with one octet replaced (indices are nonnegative)."""
        byte = (
            value if isinstance(value, Expr) else self._context.i8(value, signed=False)
        )
        return self._op(
            "set", self._coerce(index, Type.NAT), self._coerce(byte, Type.I8)
        )

    def evaluate(
        self, *, max_bytes: int = 1024 * 1024, max_steps: int = 1_000_000
    ) -> Evaluation:
        """Reduce a closed expression and retain the checked equality proof.

        Invalid operands, open terms, or resource limits raise ValueError;
        they never turn into an assumed equality or a fabricated result.
        This reduces literal/builtin/equality trees. Other HOL connectives use
        the ordinary HOL proof API.
        """
        reduction = self._context.kernel._literal_evaluate(
            self._term, _integer(max_bytes), _integer(max_steps)
        )
        return Evaluation(self._context, reduction)


class Evaluation:
    """A kernel-produced equality between the input and its literal result."""

    __slots__ = ("_context", "_evidence")

    def __init__(self, context: Context, evidence: HolLiteralReduction) -> None:
        self._context = context
        self._evidence = evidence

    @property
    def result(self) -> Expr:
        return self._context._wrap(self._evidence.result)

    @property
    def value(self) -> bool | int | bytes:
        return self.result.value

    @property
    def evidence(self) -> HolLiteralReduction:
        """The sealed Rust record, retaining the exact checked theorem."""
        return self._evidence

    @property
    def theorem(self) -> int:
        """The live theorem ID, checked against the saved owner and statement.

        Removing or overwriting its slot invalidates this accessor. Reading
        the computed value remains possible because term rows are immutable.
        """
        return self._evidence.theorem(self._context.kernel)
