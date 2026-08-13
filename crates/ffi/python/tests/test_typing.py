"""The stubs describe the module that is actually built.

No type checker runs in CI, and PyO3 emits no stubs, so `_covalence.pyi` is
hand-written and would otherwise drift silently. These checks are structural:
they compare the names and members the stub declares against the ones the
compiled module has, in both directions.
"""

import ast
import pathlib

import covalence
from covalence import _covalence
from covalence.lib import hash as public_hash
from covalence.logic import lrat as public_lrat
from covalence.logic import sat as public_sat

PACKAGE = pathlib.Path(covalence.__path__[0])
STUB = ast.parse((PACKAGE / "_covalence.pyi").read_text())


def _declared_names() -> set[str]:
    names = set()
    for node in STUB.body:
        if isinstance(node, ast.ClassDef | ast.FunctionDef):
            names.add(node.name)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            names.add(node.target.id)
    return names


def _declared_members(class_name: str) -> set[str]:
    for node in STUB.body:
        if isinstance(node, ast.ClassDef) and node.name == class_name:
            members = set()
            for member in node.body:
                if isinstance(member, ast.FunctionDef):
                    members.add(member.name)
                elif isinstance(member, ast.AnnAssign) and isinstance(
                    member.target, ast.Name
                ):
                    members.add(member.target.id)
            return members
    raise AssertionError(f"{class_name} is not declared in _covalence.pyi")


def _exported_names() -> set[str]:
    return {
        name
        for name in vars(_covalence)
        if not name.startswith("__") or name == "__version__"
    }


def test_every_exported_name_is_declared() -> None:
    missing = sorted(_exported_names() - _declared_names())
    assert not missing, f"undeclared in _covalence.pyi: {missing}"


def test_every_declared_name_exists() -> None:
    extra = sorted(_declared_names() - _exported_names())
    assert not extra, f"declared in _covalence.pyi but not built: {extra}"


def test_every_public_name_is_reexported() -> None:
    """Public modules select names from the private compiled module."""
    for public_module in (public_hash, public_lrat, public_sat):
        assert set(public_module.__all__) <= _exported_names()
        for name in public_module.__all__:
            assert getattr(public_module, name) is getattr(_covalence, name)


def test_declared_members_exist_on_each_class() -> None:
    for name in _declared_names():
        declared = getattr(_covalence, name)
        if not isinstance(declared, type) or issubclass(declared, BaseException):
            continue
        for member in _declared_members(name):
            assert hasattr(declared, member), f"{name}.{member}"


# Attributes Python or PyO3 put on every class, which say nothing about the API.
# `__new__` is here because the stub describes construction as `__init__`.
MACHINERY = frozenset(
    {
        "__dict__",
        "__doc__",
        "__firstlineno__",
        "__getstate__",
        "__init__",
        "__module__",
        "__new__",
        "__static_attributes__",
        "__weakref__",
    }
)


def _runtime_members(cls: type) -> set[str]:
    """Everything the class defines itself, machinery aside.

    Compared against `object` rather than filtered by name, so an overridden
    dunder such as `__eq__` counts and an inherited one does not.
    """
    return {
        member
        for member in vars(cls)
        if member not in MACHINERY
        and getattr(cls, member, None) is not getattr(object, member, None)
    }


def test_the_stub_does_not_omit_class_members() -> None:
    for name in (
        "Obj",
        "O256",
        "Blake3",
        "Sha256",
        "ContextKey",
        "Sha1",
        "GitHash",
        "Kernel",
        "RatGroup",
        "Literal",
        "Clause",
        "Formula",
    ):
        missing = sorted(
            _runtime_members(getattr(_covalence, name)) - _declared_members(name)
        )
        assert not missing, f"undeclared members of {name}: {missing}"


def test_the_base_declares_the_shared_protocol() -> None:
    """The stub inherits the way the classes do, rather than repeating itself."""
    shared = _declared_members("Obj")
    assert {"hex", "__bytes__", "__len__", "__hash__", "__eq__"} <= shared
    for name in ("O256", "Blake3", "Sha256", "ContextKey", "Sha1", "GitHash"):
        assert not shared & _declared_members(name)
