from __future__ import annotations

import pytest

from covalence.logic.classical import (
    Arena,
    CheckedArena,
    Cnf,
    Formula,
    ModelWitness,
    Path,
    Refutation,
    Sequent,
    Theorem,
    contradiction as rewrite_contradiction,
    dedup,
    sort_by_key,
)


def test_checked_round_trip_and_borrowed_views() -> None:
    atom = Formula.literal(7, False)
    premise = Formula.and_([atom], False)
    conclusion = Formula.or_([atom.negated()], False)
    unchecked = Arena([Sequent(premise, conclusion)])
    checked = unchecked.check()

    restored = checked.to_arena().check()
    assert len(restored) == 1
    view = restored.sequent(0)
    assert view.premise.kind == "and"
    assert len(view.premise) == 1
    assert view.premise.child(0).atom == 7
    assert restored.formula(Path(0, "left", [0])).atom == 7
    assert view.conclusion.child(0).negative
    assert view.premise.child(0).structurally_equal(checked.sequent(0).premise.child(0))
    with pytest.raises(ValueError):
        view.premise.child(1)


def test_paths_are_immutable_values() -> None:
    root = Path(0, "left", [])
    child = root.child(3)
    assert root.sequent == 0 and root.side == "left" and root.indices == []
    assert child.sequent == 0 and child.side == "left" and child.indices == [3]
    with pytest.raises(ValueError):
        Path(0, "middle", [])


def test_theorem_rules_do_not_accept_unchecked_syntax() -> None:
    atom = Formula.literal(2, False)
    identity = Theorem.identity(atom)
    assert identity.sequents[0].premise.atom == 2
    assert identity.sequents[0].conclusion.atom == 2


def test_path_rewrites_and_models() -> None:
    p = Formula.literal(1)
    q = Formula.literal(2)
    root = Path(0, "left", [])

    theorem = Theorem.identity(Formula.and_([q, p, q]))
    sort_by_key(theorem, root, lambda formula: formula.atom)
    assert [child.atom for child in theorem.sequents[0].premise.children] == [1, 2, 2]
    theorem.dedup_local(root, 2, 1)
    assert [child.atom for child in theorem.sequents[0].premise.children] == [1, 2]
    theorem.permute(root, [1, 0])
    assert [child.atom for child in theorem.sequents[0].premise.children] == [2, 1]

    nested = Theorem.identity(Formula.and_([p, Formula.and_([q])]))
    nested.flatten(root, 1)
    assert [child.atom for child in nested.sequents[0].premise.children] == [1, 2]

    duplicate = Theorem.identity(Formula.and_([p, p, q, p]))
    dedup(duplicate, root)
    assert [child.atom for child in duplicate.sequents[0].premise.children] == [1, 2]

    contradictory = Theorem.identity(Formula.or_([p, p.negated()]))
    rewrite_contradiction(contradictory, root)
    assert contradictory.sequents[0].premise.kind == "and"
    assert contradictory.sequents[0].premise.children == []

    negated_and = Formula.and_([p], negative=True)
    equivalent = Theorem.identity(negated_and)
    equivalent.demorgan(root)
    assert equivalent.sequents[0].premise.kind == "or"
    assert equivalent.sequents[0].premise.children[0].negative

    forward = Theorem.identity(negated_and)
    forward.demorgan(Path(0, "right", []))
    backward = Theorem.identity(negated_and)
    backward.demorgan(root)
    target = Theorem.identity(negated_and)
    target.rewrite_equivalent(Path(0, "right", []), forward, backward)
    assert target.sequents[0].conclusion.kind == "or"

    witness = ModelWitness.check([p, Formula.or_([q.negated(), p])], [1])
    proved = Theorem.prove_sat(witness).sequents[0]
    assert proved.premise.kind == "and" and proved.premise.children == []
    assert proved.conclusion.kind == "sat" and not proved.conclusion.negative
    assert Theorem.sat_intro([p]).sequents[0].conclusion.kind == "sat"
    assert (
        Theorem.model_sat_implication(witness, witness).sequents[0].premise.kind
        == "sat"
    )
    assert Theorem.truth_intro(p).sequents[0].conclusion.kind == "and"
    with pytest.raises(ValueError):
        ModelWitness.check([p.negated()], [1])


def test_checked_lrat_result_has_negative_sat_conclusion() -> None:
    problem = Cnf.from_dimacs(b"p cnf 1 2\n1 0\n-1 0\n")
    refutation = Refutation.from_text_lrat(problem, "3 0 1 2 0\n")
    result = Theorem.from_refutation(refutation).sequents[0]

    assert result.premise.kind == "and" and result.premise.children == []
    assert result.conclusion.kind == "sat" and result.conclusion.negative
    clauses = result.conclusion.children
    assert [clause.kind for clause in clauses] == ["or", "or"]
    assert [[literal.atom for literal in clause.children] for clause in clauses] == [
        [1],
        [1],
    ]
    assert [clause.children[0].negative for clause in clauses] == [False, True]

    theorem = Theorem.from_refutation(refutation)
    theorem.refutation_to_false(0)
    converted = theorem.sequents[0]
    assert converted.premise.kind == "and"
    assert converted.conclusion.kind == "or" and converted.conclusion.children == []
    theorem.push(0, "left", Formula.literal(9, False))
    assert len(theorem.sequents[0].premise.children) == 3
    theorem.cross(0, "left")
    assert len(theorem.sequents[0].premise.children) == 2
    assert len(theorem.sequents[0].conclusion.children) == 1

    poppable = Theorem.identity(Formula.or_([Formula.literal(4, False)], False))
    poppable.pop(0, "left")
    assert poppable.sequents[0].premise.children == []
