"""Immutable JSON documents that act like dicts and lists.

:class:`Json` wraps an ``Arc``-backed immutable tree. It reads like the
pile-of-dicts the stdlib ``json`` module produces — indexing, iteration,
``in``, ``len`` — while enforcing what that module leaves to convention:
object keys are strings, a duplicate key is an error rather than a silent
overwrite, numbers are finite and fit 64 bits, and output is compact with
sorted keys unless asked to be pretty.

Access unwraps leaves and wraps containers: ``doc["port"]`` is an ``int``,
``doc["server"]`` is another :class:`Json` sharing the same tree, so taking a
subtree copies nothing.

Equality is structural against anything that converts (``doc == {"a": 1}``),
with one strictness Python's numbers lack: ``1`` and ``1.0`` are distinct
JSON values, so ``Json(1) != 1.0`` even though ``1 == 1.0``. Compare
unwrapped values when Python's numeric semantics are wanted.

    >>> from covalence.data.json import Json, loads
    >>> doc = loads('{"zeta": 1, "alpha": {"nested": true}}')
    >>> doc.dumps()
    '{"alpha":{"nested":true},"zeta":1}'
    >>> doc["zeta"] + 1
    2
    >>> doc["alpha"] == {"nested": True}
    True
    >>> loads('{"k": 1, "k": 2}')
    Traceback (most recent call last):
        ...
    covalence.data.json.InvalidJsonError: duplicate object key "k" ...
"""

from .._covalence import InvalidJsonError, Json

JsonValue = None | bool | int | float | str | Json
"""What access to a :class:`Json` returns: an unwrapped leaf or a wrapped
container."""


def loads(text: str) -> Json:
    """Parses strict JSON text, as :meth:`Json.loads`."""
    return Json.loads(text)


def dumps(value: object, *, pretty: bool = False) -> str:
    """Validates ``value`` and serializes it with sorted keys."""
    return Json(value).dumps(pretty=pretty)


__all__ = ["InvalidJsonError", "Json", "JsonValue", "dumps", "loads"]
