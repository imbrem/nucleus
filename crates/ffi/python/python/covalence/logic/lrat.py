"""Parser-independent typed LRAT clause validation.

The kernel accepts clauses and proof hints as Python sequences. Failed proof
steps raise :class:`LratError` and leave the kernel unchanged.
"""

from .._covalence import Kernel, LratError, RatGroup

__all__ = ["Kernel", "LratError", "RatGroup"]
