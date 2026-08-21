"""Persistent, assumption-tracking HOL kernel handles.

All values here are opaque wrappers around the Rust kernel API. Operations
return a replacement kernel; Python performs no independent logical checks.
Handles carry no kernel identity and may be supplied across kernels as later
operations begin accepting them.
"""

from .._covalence import HolError, HolKernel, Tm, Ty

Kernel = HolKernel

__all__ = ["HolError", "Kernel", "Tm", "Ty"]
