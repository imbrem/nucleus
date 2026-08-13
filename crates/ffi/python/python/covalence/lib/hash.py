"""Fixed-width names and hashing operations.

Each namespace has its own class, all deriving from :class:`Obj`. Keeping the
namespaces apart is the point: a :class:`GitHash` and an :class:`O256` are not
the same thing merely because their widths agree. Equality across namespaces
is false and ordering across them raises :class:`TypeError`.

Constructing from bytes or hex names a value; it does not check that anything
ever hashed to it. Invalid widths and encodings raise the corresponding
``ValueError`` subclass.

    >>> from covalence.lib.hash import O256, git_blob
    >>> O256.hash(b"abc")
    O256.from_hex('6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85')
    >>> str(git_blob(b""))
    'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391'
"""

from .._covalence import (
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
    "git_blob",
    "git_object",
]
