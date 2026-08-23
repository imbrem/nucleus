"""The Ethane Python API keeps raw arenas separate from checked kernels."""

import pytest
from covalence.logic.hol import Arena, Kernel, Kind, SynFact, Tm, Ty


def test_raw_arena_roundtrip_and_normalized_sets() -> None:
    arena = Arena()
    bool_ty = arena.bool_ty()
    true = arena.bool(True)
    arena.add_axiom("ax.inf")
    arena.add_axiom("ax.inf")
    arena.add_context(true)
    arena.add_context(true)

    decoded = Arena.from_cbor(arena.to_cbor())
    assert decoded.addr() == arena.addr()
    assert decoded.axioms == ["ax.inf"]
    assert decoded.context == [true]
    assert decoded.definition(bool_ty).tag == "ty.bool"
    assert [definition.reference for definition in decoded.definitions] == [1, 2]
    with pytest.raises(ValueError, match="one-based"):
        decoded.definition(0)


def test_checked_kernel_uses_raw_integer_indices_and_optional_wrappers() -> None:
    kernel = Kernel()
    empty_addr = kernel.addr()
    star = kernel.star()
    bool_ty = kernel.bool_ty(star)
    variable = kernel.tm_fv(7, bool_ty)
    identity = kernel.lam(variable, variable)
    true = kernel.bool(bool_ty, True)
    redex = kernel.app(identity, true)

    assert kernel.category(star) == "kind"
    assert kernel.category(bool_ty) == "ty"
    assert kernel.category(redex) == "tm"
    assert isinstance(kernel.kind(star), Kind)
    assert isinstance(kernel.ty(bool_ty), Ty)
    assert isinstance(kernel.tm(redex), Tm)
    assert kernel.tm(redex).reference == redex
    assert kernel.addr() != empty_addr
    assert kernel.addr() == kernel.arena.addr()
    for opaque in (Kind, Ty, Tm, SynFact):
        with pytest.raises(TypeError):
            opaque()


def test_cached_substitution_drives_beta_and_union() -> None:
    kernel = Kernel()
    star = kernel.star()
    bool_ty = kernel.bool_ty(star)
    variable = kernel.tm_fv(7, bool_ty)
    identity = kernel.lam(variable, variable)
    true = kernel.bool(bool_ty, True)
    redex = kernel.app(identity, true)

    substitution = kernel.syn_sub_var(variable, true)
    assert substitution.id == 1
    assert substitution.relation == "syn"
    assert (substitution.var, substitution.val) == (variable, true)
    beta = kernel.tm_beta(redex, substitution)
    assert beta.relation == "conv"
    assert (beta.input, beta.output) == (redex, true)
    assert not kernel.equivalent(redex, true)
    kernel.union_syn_fact(beta)
    assert kernel.equivalent(redex, true)


def test_fact_slots_reuse_free_entries_and_truncate_temporary_suffixes() -> None:
    kernel = Kernel()
    star = kernel.star()
    bool_ty = kernel.bool_ty(star)
    first = kernel.syn_refl("syn", star)
    second = kernel.syn_refl("alpha", bool_ty)
    assert (first.id, second.id) == (1, 2)

    assert kernel.remove_syn_fact(first)
    reused = kernel.syn_refl("conv", bool_ty)
    assert reused.id == first.id
    with pytest.raises(ValueError, match="overwritten"):
        kernel.syn_refine(first, "alpha")
    keep = kernel.syn_fact_len()
    temporary = kernel.syn_refl("syn", star)
    assert temporary.id == 3
    kernel.truncate_syn_facts(keep)
    with pytest.raises(ValueError, match="absent"):
        kernel.syn_fact(temporary.id)


def test_facts_cannot_cross_kernel_boundaries() -> None:
    left = Kernel()
    right = Kernel()
    left_star = left.star()
    right_star = right.star()
    fact = left.syn_refl("syn", left_star)
    with pytest.raises(ValueError, match="different kernel"):
        right.syn_refine(fact, "alpha")
    assert right.syn_refl("syn", right_star).id == 1
