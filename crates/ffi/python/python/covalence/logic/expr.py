"""Immutable userspace expressions over the checked HOL kernel.

This module is convenience, not authority. Every construction eventually calls
the public checked :class:`~covalence.logic.hol.Kernel` API, and a broken custom
handler can only request a construction which that kernel accepts or rejects.

Python has no overloadable ``and`` operator, so ``left & right`` constructs
logical conjunction. ``left == right`` constructs an HOL equality term rather
than comparing Python wrappers. Expression truth-testing is deliberately an
error, preventing an HOL proposition from silently becoming a Python Boolean.
"""

from __future__ import annotations

from dataclasses import dataclass
from types import NotImplementedType
from typing import Protocol

from .hol import Kernel
from .hol import Tm as RawTm

__all__ = [
    "ConstructionHandler",
    "Context",
    "DefaultConstructionHandler",
    "Expr",
    "Tm",
    "Variable",
]


class ConstructionHandler(Protocol):
    """Pluggable, untrusted expression construction.

    ``convert`` is the extension point for ordinary Python objects. A handler
    may support integers, floats, lists, domain objects, or any other input;
    returning ``NotImplemented`` asks :class:`Context` to report an unsupported
    conversion. The two construction methods remain explicit so a handler may
    choose higher-level encodings without changing operator classes.
    """

    def convert(self, context: Context, value: object, /) -> Tm | NotImplementedType:
        """Convert one Python object into a term, or decline it."""

    def conjunction(self, context: Context, left: Tm, right: Tm, /) -> Tm:
        """Construct logical conjunction."""

    def equality(self, context: Context, left: Tm, right: Tm, /) -> Tm:
        """Construct term equality."""


class DefaultConstructionHandler:
    """Direct checked-kernel construction with Boolean conversion."""

    def convert(self, context: Context, value: object, /) -> Tm | NotImplementedType:
        if isinstance(value, Tm):
            return value
        # Exact type is intentional: ``bool`` is an ``int`` subclass, while a
        # later integer handler needs to see integers as a separate domain.
        if type(value) is bool:
            reference = context.kernel.bool(context.bool_type, value)
            return context.term(reference)
        return NotImplemented

    def conjunction(self, context: Context, left: Tm, right: Tm, /) -> Tm:
        reference = context.kernel.logical_and(left.reference, right.reference)
        return context.term(reference)

    def equality(self, context: Context, left: Tm, right: Tm, /) -> Tm:
        reference = context.kernel.eq(
            context.bool_type,
            left.reference,
            right.reference,
        )
        return context.term(reference)


class Context:
    """A kernel-affine construction context.

    A context lazily creates one ``bool`` type for Python Boolean conversion and
    equality results. It does not own or hide the kernel: callers may continue
    using the raw checked API. Terms from distinct contexts cannot be combined,
    even when their integer references happen to coincide. This stronger rule
    also keeps each context's userspace type conventions coherent.
    """

    __slots__ = ("_bool_type", "handler", "kernel")

    def __init__(
        self,
        kernel: Kernel,
        handler: ConstructionHandler | None = None,
    ) -> None:
        self.kernel = kernel
        self.handler = handler or DefaultConstructionHandler()
        self._bool_type: int | None = None

    @property
    def bool_type(self) -> int:
        """The context's lazily allocated checked Boolean type reference."""
        if self._bool_type is None:
            self._bool_type = self.kernel.bool_ty(self.kernel.star())
        return self._bool_type

    def term(self, reference: int) -> Tm:
        """Check and wrap a resident term reference."""
        # The opaque handle is retained so this layer cannot manufacture a term
        # merely by storing an integer which has not passed the checked API.
        return Tm(self, self.kernel.tm(reference))

    def variable(self, name: int, type_reference: int) -> Variable:
        """Construct and wrap a free term variable."""
        reference = self.kernel.tm_fv(name, type_reference)
        return Variable(self, self.kernel.tm(reference), name, type_reference)

    def convert(self, value: object) -> Tm:
        """Convert a Python object with the configured handler.

        Raises:
            TypeError: if the handler declines or returns something other than
                a term.
            ValueError: if the term belongs to another context.
        """
        converted = self.handler.convert(self, value)
        if converted is NotImplemented:
            raise TypeError(
                f"{type(self.handler).__name__} cannot convert "
                f"{type(value).__name__} to an HOL term"
            )
        if not isinstance(converted, Tm):
            raise TypeError("construction handlers must return Tm or NotImplemented")
        self._check(converted)
        return converted

    def _check(self, term: Tm) -> None:
        if term.context is not self:
            raise ValueError("terms belong to different construction contexts")

    def _result(self, value: object) -> Tm:
        if not isinstance(value, Tm):
            raise TypeError("construction handlers must construct a Tm")
        self._check(value)
        return value


@dataclass(frozen=True, slots=True, eq=False)
class Expr:
    """Base class for immutable, kernel-affine expressions."""

    context: Context

    def __bool__(self) -> bool:
        raise TypeError("HOL expressions do not have a Python truth value")


@dataclass(frozen=True, slots=True, eq=False)
class Tm(Expr):
    """An immutable userspace view of an opaque checked term handle."""

    raw: RawTm

    @property
    def reference(self) -> int:
        """The underlying one-based arena reference."""
        return self.raw.reference

    def __and__(self, other: object) -> Tm:
        right = self.context.convert(other)
        return self.context._result(
            self.context.handler.conjunction(self.context, self, right)
        )

    def __rand__(self, other: object) -> Tm:
        left = self.context.convert(other)
        return self.context._result(
            self.context.handler.conjunction(self.context, left, self)
        )

    def __eq__(self, other: object) -> Tm:  # type: ignore[override]
        right = self.context.convert(other)
        return self.context._result(
            self.context.handler.equality(self.context, self, right)
        )

    def same_reference(self, other: object) -> bool:
        """Compare wrapper identity without constructing an HOL equality."""
        return (
            isinstance(other, Tm)
            and other.context is self.context
            and other.reference == self.reference
        )

    __hash__ = None


@dataclass(frozen=True, slots=True, eq=False)
class Variable(Tm):
    """A checked free-variable term with its userspace declaration metadata."""

    name: int
    type_reference: int
