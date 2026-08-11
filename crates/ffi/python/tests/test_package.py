"""The package builds, imports, and is what it claims to be.

These run against the staged package `glu` builds, not against the source tree,
so a failure here means the artifact an interpreter would actually load is
wrong.
"""

import pathlib

import covalence
from covalence import _covalence


def test_package_imports_and_reports_a_version() -> None:
    assert isinstance(covalence.__version__, str)
    assert covalence.__version__ == _covalence.__version__


def test_compiled_module_is_the_one_inside_the_package() -> None:
    """One deliberate package, not an extension module loose on the path."""
    assert _covalence.__name__ == "covalence._covalence"
    assert _covalence.__file__.endswith((".so", ".pyd"))


def test_the_package_ships_typing_metadata() -> None:
    """`py.typed` is what makes the stubs visible to a type checker."""
    root = pathlib.Path(covalence.__path__[0])
    assert (root / "py.typed").is_file()
    assert (root / "_covalence.pyi").is_file()


def test_the_stubs_name_everything_the_module_exports() -> None:
    """No type checker runs in CI, so agreement is checked directly."""
    root = pathlib.Path(covalence.__path__[0])
    stubs = (root / "_covalence.pyi").read_text()
    exported = [
        name
        for name in vars(_covalence)
        if not name.startswith("__") or name == "__version__"
    ]
    missing = [name for name in exported if name not in stubs]
    assert not missing, f"undocumented in _covalence.pyi: {missing}"


def test_public_names_are_declared() -> None:
    for name in covalence.__all__:
        assert hasattr(covalence, name), name
