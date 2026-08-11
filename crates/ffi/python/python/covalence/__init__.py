"""Python bindings for Covalence.

The compiled module is private. Everything callers are meant to use is named
here, so the public surface is a decision rather than whatever the Rust module
happens to export.

Each namespace has its own class, all of them deriving from `Obj`. They wrap
20 or 32 bytes, and keeping them apart is the point: a `GitHash` and an
`O256` are not the same thing because their widths agree, so comparing
across namespaces is `False` and ordering across them raises `TypeError`.
`Obj` is the type to name when any namespace will do — `isinstance(value,
Obj)` — and is not instantiable itself.

    >>> from covalence import O256, git_blob
    >>> O256.hash(b"abc")
    O256.from_hex('6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85')
    >>> str(git_blob(b""))
    'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391'

Constructing from bytes or hex names a value; it does not check that anything
ever hashed to it. What is checked is the width and the encoding, and a failure
raises `InvalidLengthError`, `InvalidHexError`, or `InvalidBase64Error` — all of them
`ValueError`, so `except ValueError` catches the lot.
"""

from ._covalence import (
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
    __version__,
    git_blob,
    git_object,
)

__all__ = [
    "COV",
    "COV_ROOT",
    "COV_ROOT_CTX_KEY",
    "Blake3",
    "ContextKey",
    "GitHash",
    "InvalidBase64Error",
    "InvalidHexError",
    "InvalidLengthError",
    "O256",
    "Obj",
    "Sha1",
    "Sha256",
    "__version__",
    "git_blob",
    "git_object",
]
