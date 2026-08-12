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


def test_hash_is_a_regular_public_submodule() -> None:
    assert covalence.__all__ == ["data", "hash", "__version__"]
    assert covalence.hash.__name__ == "covalence.hash"
    assert covalence.hash.O256 is _covalence.O256
    assert not hasattr(covalence, "O256")


def test_data_json_is_a_regular_public_submodule() -> None:
    assert covalence.data.__all__ == ["json"]
    assert covalence.data.json.__name__ == "covalence.data.json"
    assert covalence.data.json.Json is _covalence.Json
    assert not hasattr(covalence, "Json")


def test_hash_objects_report_their_public_module() -> None:
    for name in covalence.hash.__all__:
        value = getattr(covalence.hash, name)
        if isinstance(value, type) or callable(value):
            assert value.__module__ == "covalence.hash", name


def test_compiled_module_is_the_one_inside_the_package() -> None:
    """One deliberate package, not an extension module loose on the path."""
    assert _covalence.__name__ == "covalence._covalence"
    assert _covalence.__file__.endswith((".so", ".pyd"))


def test_the_package_ships_typing_metadata() -> None:
    """`py.typed` is what makes the stubs visible to a type checker."""
    root = pathlib.Path(covalence.__path__[0])
    assert (root / "py.typed").is_file()
    assert (root / "hash.py").is_file()
    assert (root / "data" / "json.py").is_file()
    assert (root / "_covalence.pyi").is_file()


def test_public_names_are_declared() -> None:
    for name in covalence.__all__:
        assert hasattr(covalence, name), name
    for name in covalence.hash.__all__:
        assert hasattr(covalence.hash, name), name
