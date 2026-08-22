import pytest
from covalence.logic.metamath import Database, MetamathError

DEMO = """
$c term 0 $.
tze $a term 0 $.
th $p term 0 $= ( tze ) A $.
"""


def test_parse_validate_and_inspect() -> None:
    database = Database.parse(DEMO)

    assert len(database) == 3
    assert database.assertion_count == 2
    assert database.theorem_count == 1
    assert database.validate() == 1
    assert database.symbols("constant") == ["0", "term"]
    assert database.labels() == ["tze", "th"]

    theorem = database.assertion("th")
    assert theorem is not None
    assert theorem.is_theorem
    assert theorem.proof_encoding == "compressed"
    assert str(theorem.conclusion) == "term 0"
    assert database.assertion("missing") is None


def test_invalid_proof_raises_metamath_error() -> None:
    database = Database.parse(DEMO.replace(" A $.", " B $."))
    with pytest.raises(MetamathError):
        database.validate()


def test_load_resolves_includes(tmp_path) -> None:
    (tmp_path / "defs.mm").write_text("$c term 0 $. tze $a term 0 $.")
    root = tmp_path / "root.mm"
    root.write_text("$[ defs.mm $] th $p term 0 $= tze $.")

    assert Database.load(str(root)).validate() == 1
