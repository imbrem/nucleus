"""Type information for the compiled module.

PyO3 does not emit stubs, so this file is written by hand and has to be kept in
step with `crates/ffi/python/src`. `tests/test_package.py` checks that the two
agree on which names exist.
"""

__version__: str
