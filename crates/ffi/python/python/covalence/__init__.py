"""Python bindings for Covalence.

The compiled module is private. Everything callers are meant to use is named
here, so the public surface is a decision rather than whatever the Rust module
happens to export.
"""

from ._covalence import __version__

__all__ = ["__version__"]
