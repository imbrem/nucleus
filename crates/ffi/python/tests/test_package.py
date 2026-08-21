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


def test_public_apis_follow_their_crate_paths() -> None:
    assert covalence.__all__ == ["data", "lib", "logic", "__version__"]
    assert covalence.data.__all__ == ["cbor"]
    assert covalence.data.cbor.__name__ == "covalence.data.cbor"
    assert covalence.data.cbor.Cbor is _covalence.Cbor
    assert covalence.lib.__all__ == ["hash"]
    assert covalence.lib.hash.__name__ == "covalence.lib.hash"
    assert covalence.lib.hash.O256 is _covalence.O256
    assert not hasattr(covalence, "O256")
    assert not hasattr(covalence, "hash")


def test_lrat_follows_its_crate_path() -> None:
    assert covalence.logic.__all__ == ["lrat", "metamath", "sat"]
    assert covalence.logic.lrat.__name__ == "covalence.logic.lrat"
    assert covalence.logic.lrat.Kernel is _covalence.Kernel
    assert covalence.logic.lrat.RatGroup is _covalence.RatGroup
    assert covalence.logic.metamath.Database is _covalence.Database
    assert covalence.logic.sat.__name__ == "covalence.logic.sat"
    assert covalence.logic.sat.Formula is _covalence.Formula


def test_hash_objects_report_their_public_module() -> None:
    for name in covalence.lib.hash.__all__:
        value = getattr(covalence.lib.hash, name)
        if isinstance(value, type) or callable(value):
            assert value.__module__ == "covalence.lib.hash", name


def test_compiled_module_is_the_one_inside_the_package() -> None:
    """One deliberate package, not an extension module loose on the path."""
    assert _covalence.__name__ == "covalence._covalence"
    assert _covalence.__file__.endswith((".so", ".pyd"))


def test_the_package_ships_typing_metadata() -> None:
    """`py.typed` is what makes the stubs visible to a type checker."""
    root = pathlib.Path(covalence.__path__[0])
    assert (root / "py.typed").is_file()
    assert (root / "lib" / "__init__.py").is_file()
    assert (root / "lib" / "hash.py").is_file()
    assert (root / "logic" / "__init__.py").is_file()
    assert (root / "logic" / "lrat.py").is_file()
    assert (root / "logic" / "metamath.py").is_file()
    assert (root / "logic" / "sat.py").is_file()
    assert (root / "data" / "__init__.py").is_file()
    assert (root / "data" / "cbor.py").is_file()
    assert (root / "_covalence.pyi").is_file()


def test_public_names_are_declared() -> None:
    for name in covalence.__all__:
        assert hasattr(covalence, name), name
    for name in covalence.data.cbor.__all__:
        assert hasattr(covalence.data.cbor, name), name
    for name in covalence.lib.hash.__all__:
        assert hasattr(covalence.lib.hash, name), name
    for name in covalence.logic.lrat.__all__:
        assert hasattr(covalence.logic.lrat, name), name
    for name in covalence.logic.sat.__all__:
        assert hasattr(covalence.logic.sat, name), name
