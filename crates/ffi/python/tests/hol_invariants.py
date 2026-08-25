"""Shared scaffolding for the Ethane Python tests.

Everything here drives `covalence.logic.hol` from outside the kernel, through
the same public surface a user has. Nothing reaches into the extension module
or reconstructs kernel state by hand: a helper that needed private access
would be testing the kernel against itself.

The three pieces that carry the most weight elsewhere:

* `bool_kernel`, which is the `star`/`bool` prelude nearly every checked test
  opens with;
* `assert_kernel_invariants`, a whole-kernel consistency sweep cheap enough to
  run after any interesting sequence of operations;
* `RAW_REFERENCE_CALLS` and `KERNEL_REFERENCE_CALLS`, which enumerate every
  entry point taking a one-based index so the boundary checks can be
  parametrized over the whole API rather than a sample of it.
"""

from collections.abc import Callable, Iterable

from covalence.logic.hol import Arena, Definition, Kernel, SynFact

KIND_TAGS = frozenset({"kind.star", "kind.arr", "kind.ref"})
TY_TAGS = frozenset(
    {"ty.bool", "ty.arr", "ty.app", "ty.lam", "ty.fv", "ty.model", "ty.ref"}
)
TM_TAGS = frozenset(
    {
        "tm.ty_exists",
        "tm.fv",
        "tm.app",
        "tm.lam",
        "tm.bool",
        "tm.eq",
        "tm.eps",
        "tm.ref",
    }
)
TAGS = KIND_TAGS | TY_TAGS | TM_TAGS
CATEGORY_TAGS = {"kind": KIND_TAGS, "ty": TY_TAGS, "tm": TM_TAGS}

RELATIONS = ("syn", "alpha", "conv")

# The one axiom capability the checked kernel recognizes.
SUPPORTED_AXIOM = "ax.inf"


def bool_kernel() -> tuple[Kernel, int, int]:
    """An empty kernel carrying just `kind.star` and `ty.bool`."""
    kernel = Kernel()
    star = kernel.star()
    return kernel, star, kernel.bool_ty(star)


def roundtrip(arena: Arena) -> Arena:
    """The arena as it survives a CBOR encode/decode cycle."""
    return Arena.from_cbor(arena.to_cbor())


def definitions_by_reference(arena: Arena) -> dict[int, Definition]:
    """Every row of `arena`, keyed by its one-based reference."""
    return {definition.reference: definition for definition in arena.definitions}


def fact_tuple(fact: SynFact) -> tuple[str, int | None, int | None, int, int]:
    """A syntactic fact's payload, without its ephemeral slot number."""
    return (fact.relation, fact.var, fact.val, fact.input, fact.output)


def reflexive_children(kernel: Kernel, reference: int) -> list[SynFact]:
    """Reflexivity evidence for each child of `reference`, in order."""
    definition = kernel.arena.definition(reference)
    assert definition is not None, reference
    return [kernel.syn_refl("syn", child) for child in definition.children]


def congruent(kernel: Kernel, left: int, right: int) -> SynFact:
    """Syntactic congruence between two rows with reflexively equal children."""
    return kernel.syn_congr("syn", left, right, reflexive_children(kernel, left))


def merge_congruent(kernel: Kernel, left: int, right: int) -> None:
    """Union two structurally identical rows through checked congruence.

    Distinct constructions of the same type — the two `bool -> bool` rows a
    pair of lambdas allocate, say — are separate rows until something proves
    them equal. Rules that compare classifiers consult the union-find, so this
    is the usual way to make an independently built row usable.
    """
    kernel.union_syn_fact(congruent(kernel, left, right))


# The empty arena's exact CBOR encoding, and the offset of its `import` array.
# Hand-assembling the wire form is what lets the decoder be probed with inputs
# no sequence of Python calls could build.
EMPTY_ARENA_CBOR = bytes.fromhex(
    "a563746167656172656e6166696d706f72748063616d62a46470726564806261"
    "788063637478806374686d806470726564a16373796c8063686f6ca564646566"
    "73806261788063637478806374686d806373796ea0"
)
_IMPORTS_KEY = b"\x66import"
_IMPORTS_AT = EMPTY_ARENA_CBOR.index(_IMPORTS_KEY) + len(_IMPORTS_KEY)


def nested_import_cbor(depth: int) -> bytes:
    """CBOR for an arena whose literal imports nest `depth` levels deep.

    Grows linearly with `depth`, unlike `add_literal_import`, which copies the
    whole inner arena at every level.
    """
    prefix = EMPTY_ARENA_CBOR[:_IMPORTS_AT]
    suffix = EMPTY_ARENA_CBOR[_IMPORTS_AT + 1 :]
    encoded = EMPTY_ARENA_CBOR
    for _ in range(depth):
        encoded = prefix + b"\x81" + encoded + suffix
    return encoded


def nested_import_arena(depth: int) -> Arena:
    """An arena whose literal imports nest `depth` levels deep."""
    arena = Arena()
    for _ in range(depth):
        outer = Arena()
        outer.add_literal_import(arena)
        arena = outer
    return arena


def import_depth(arena: Arena) -> int:
    """How many literal imports `arena` nests before running out."""
    depth = 0
    while arena.imports:
        (entry,) = arena.imports
        assert isinstance(entry, Arena)
        arena = entry
        depth += 1
    return depth


def assert_arena_invariants(arena: Arena) -> None:
    """Representation invariants every raw arena satisfies, valid or not.

    Deserialization establishes only these. Nothing here implies the rows are
    well kinded, well typed, or even that their children exist.
    """
    definitions = arena.definitions
    assert len(definitions) == len(arena)
    assert [definition.reference for definition in definitions] == list(
        range(1, len(arena) + 1)
    )
    for definition in definitions:
        assert definition.tag in TAGS, definition.tag
        assert arena.definition(definition.reference).tag == definition.tag
        assert all(child >= 1 for child in definition.children)
        assert definition.value is None or definition.tag == "tm.bool"
        assert (definition.source is None) == (definition.foreign is None)
    assert arena.context == sorted(set(arena.context))
    assert arena.axioms == sorted(set(arena.axioms))
    assert arena.definition(len(arena) + 1) is None
    decoded = roundtrip(arena)
    assert decoded.addr() == arena.addr()
    assert decoded.to_cbor() == arena.to_cbor()


def assert_kernel_invariants(kernel: Kernel) -> None:
    """Everything a checked kernel promises about its own rows.

    Run after any sequence of operations: it is a whole-kernel sweep, but the
    kernels these tests build are small enough for that to stay cheap.
    """
    arena = kernel.arena
    assert len(kernel) == len(arena)
    assert kernel.addr() == arena.addr()
    assert_arena_invariants(arena)

    assert len(arena.eq) == len(arena.syn_eq) == len(arena.conv) == len(arena)
    for definition, equal, raw_conv in zip(
        arena.definitions, arena.eq, arena.conv, strict=True
    ):
        reference = definition.reference
        category = kernel.category(reference)
        assert definition.tag in CATEGORY_TAGS[category]
        assert all(child <= len(kernel) for child in definition.children)

        if category != "kind":
            classifier = kernel.classifier(reference)
            assert classifier <= len(kernel)
            assert kernel.category(classifier) == ("kind" if category == "ty" else "ty")

        # A fused conversion cell is either a same-category parent link or the
        # conversion root's cross-category classifier. Kinds have only the
        # former because they are themselves classifiers.
        if raw_conv is not None:
            target_category = kernel.category(raw_conv)
            assert (
                target_category == category
                or (category == "tm" and target_category == "ty")
                or (category == "ty" and target_category == "kind")
            )

        # A class is represented by its smallest member, and finding is
        # idempotent whether or not the path is compressed.
        root = kernel.find(reference)
        assert root <= reference
        assert kernel.find(root) == root
        assert kernel.equivalent(reference, root)
        assert kernel.category(root) == category
        if equal is not None:
            assert kernel.category(equal) == category
            assert kernel.equivalent(reference, equal)

    for proposition in arena.context:
        assert kernel.category(proposition) == "tm"
    assert set(arena.axioms) <= {SUPPORTED_AXIOM}

    for slot in range(1, kernel.syn_fact_len() + 1):
        try:
            fact = kernel.syn_fact(slot)
        except ValueError:
            continue  # A removed slot, which stays allocated until truncation.
        assert fact.id == slot
        assert fact.relation in RELATIONS
        assert 1 <= fact.input <= len(kernel)
        assert 1 <= fact.output <= len(kernel)
        assert fact.var is None or 1 <= fact.var <= len(kernel)
        # `val` without `var` is reserved and has no checked meaning.
        assert not (fact.val is not None and fact.var is None)


def _raw_reference_calls() -> list[tuple[str, Callable[[Arena], object]]]:
    """Every raw-arena entry point taking a one-based index, with it zeroed."""
    return [
        ("definition", lambda arena: arena.definition(0)),
        ("add_context", lambda arena: arena.add_context(0)),
        ("amb_ctx_arena_ok", lambda arena: arena.amb_ctx_arena_ok(0)),
        ("amb_thm_arena_ok", lambda arena: arena.amb_thm_arena_ok(0)),
        ("amb_ctx_hol_sort.source", lambda arena: arena.amb_ctx_hol_sort(0, 1, 1)),
        ("amb_ctx_hol_sort.reference", lambda arena: arena.amb_ctx_hol_sort(1, 0, 1)),
        ("amb_ctx_hol_sort.classifier", lambda arena: arena.amb_ctx_hol_sort(1, 1, 0)),
        ("amb_thm_hol_sort.source", lambda arena: arena.amb_thm_hol_sort(0, 1, 1)),
        ("amb_thm_hol_sort.reference", lambda arena: arena.amb_thm_hol_sort(1, 0, 1)),
        ("amb_thm_hol_sort.classifier", lambda arena: arena.amb_thm_hol_sort(1, 1, 0)),
        ("kind_arr.domain", lambda arena: arena.kind_arr(0, 1)),
        ("kind_arr.codomain", lambda arena: arena.kind_arr(1, 0)),
        ("ty_arr.domain", lambda arena: arena.ty_arr(0, 1)),
        ("ty_arr.codomain", lambda arena: arena.ty_arr(1, 0)),
        ("ty_app.function", lambda arena: arena.ty_app(0, 1)),
        ("ty_app.argument", lambda arena: arena.ty_app(1, 0)),
        ("ty_lam.binder", lambda arena: arena.ty_lam(0, 1)),
        ("ty_lam.body", lambda arena: arena.ty_lam(1, 0)),
        ("ty_fv.kind", lambda arena: arena.ty_fv(1, 0)),
        ("ty_exists.predicate", lambda arena: arena.ty_exists(1, 0)),
        ("model.predicate", lambda arena: arena.model(1, 0)),
        ("tm_fv.ty", lambda arena: arena.tm_fv(1, 0)),
        ("app.function", lambda arena: arena.app(0, 1)),
        ("app.argument", lambda arena: arena.app(1, 0)),
        ("lam.binder", lambda arena: arena.lam(0, 1)),
        ("lam.body", lambda arena: arena.lam(1, 0)),
        ("tm_eq.left", lambda arena: arena.tm_eq(0, 1)),
        ("tm_eq.right", lambda arena: arena.tm_eq(1, 0)),
        ("eps.ty", lambda arena: arena.eps(0, 1)),
        ("eps.predicate", lambda arena: arena.eps(1, 0)),
        ("tm_ref.source", lambda arena: arena.tm_ref(0, 1)),
        ("tm_ref.foreign", lambda arena: arena.tm_ref(1, 0)),
        ("ty_ref.source", lambda arena: arena.ty_ref(0, 1)),
        ("ty_ref.foreign", lambda arena: arena.ty_ref(1, 0)),
        ("kind_ref.source", lambda arena: arena.kind_ref(0, 1)),
        ("kind_ref.foreign", lambda arena: arena.kind_ref(1, 0)),
    ]


def _kernel_reference_calls() -> list[tuple[str, Callable[[Kernel], object]]]:
    """Every kernel entry point taking a one-based index, with it zeroed."""
    return [
        ("category", lambda kernel: kernel.category(0)),
        ("classifier", lambda kernel: kernel.classifier(0)),
        ("find", lambda kernel: kernel.find(0)),
        ("find_mut", lambda kernel: kernel.find_mut(0)),
        ("equivalent.left", lambda kernel: kernel.equivalent(0, 1)),
        ("equivalent.right", lambda kernel: kernel.equivalent(1, 0)),
        ("kind", lambda kernel: kernel.kind(0)),
        ("ty", lambda kernel: kernel.ty(0)),
        ("tm", lambda kernel: kernel.tm(0)),
        ("kind_arr.domain", lambda kernel: kernel.kind_arr(0, 1)),
        ("kind_arr.codomain", lambda kernel: kernel.kind_arr(1, 0)),
        ("bool_ty", lambda kernel: kernel.bool_ty(0)),
        ("ty_arr.domain", lambda kernel: kernel.ty_arr(0, 2)),
        ("ty_arr.codomain", lambda kernel: kernel.ty_arr(2, 0)),
        ("ty_fv.kind", lambda kernel: kernel.ty_fv(1, 0)),
        ("ty_app.function", lambda kernel: kernel.ty_app(0, 2)),
        ("ty_app.argument", lambda kernel: kernel.ty_app(2, 0)),
        ("ty_lam.binder", lambda kernel: kernel.ty_lam(0, 2)),
        ("ty_lam.body", lambda kernel: kernel.ty_lam(2, 0)),
        ("model.predicate", lambda kernel: kernel.model(1, 0)),
        ("ty_exists.predicate", lambda kernel: kernel.ty_exists(1, 0)),
        ("tm_fv.ty", lambda kernel: kernel.tm_fv(1, 0)),
        ("app.function", lambda kernel: kernel.app(0, 1)),
        ("app.argument", lambda kernel: kernel.app(1, 0)),
        ("lam.binder", lambda kernel: kernel.lam(0, 1)),
        ("lam.body", lambda kernel: kernel.lam(1, 0)),
        ("bool", lambda kernel: kernel.bool(0, True)),
        ("eq.bool_ty", lambda kernel: kernel.eq(0, 1, 1)),
        ("eq.left", lambda kernel: kernel.eq(2, 0, 1)),
        ("eq.right", lambda kernel: kernel.eq(2, 1, 0)),
        ("eps.ty", lambda kernel: kernel.eps(0, 1)),
        ("eps.predicate", lambda kernel: kernel.eps(2, 0)),
        ("add_context", lambda kernel: kernel.add_context(0)),
        ("syn_fact", lambda kernel: kernel.syn_fact(0)),
        ("syn_refl.input", lambda kernel: kernel.syn_refl("syn", 0)),
        ("syn_refl.target", lambda kernel: kernel.syn_refl("syn", 1, 0)),
        ("syn_sub_var.var", lambda kernel: kernel.syn_sub_var(0, 1)),
        ("syn_sub_var.val", lambda kernel: kernel.syn_sub_var(1, 0)),
        ("syn_sub_leaf.var", lambda kernel: kernel.syn_sub_leaf(0, 1, 1)),
        ("syn_sub_leaf.val", lambda kernel: kernel.syn_sub_leaf(1, 0, 1)),
        ("syn_sub_leaf.input", lambda kernel: kernel.syn_sub_leaf(1, 1, 0)),
        ("syn_congr.input", lambda kernel: kernel.syn_congr("syn", 0, 1, [])),
        ("syn_congr.output", lambda kernel: kernel.syn_congr("syn", 1, 0, [])),
        ("syn_congr.var", lambda kernel: kernel.syn_congr("syn", 1, 1, [], 0)),
        ("syn_congr.val", lambda kernel: kernel.syn_congr("syn", 1, 1, [], 1, 0)),
        ("tm_eta.source", lambda kernel: kernel.tm_eta(0)),
    ]


RAW_REFERENCE_CALLS = _raw_reference_calls()
KERNEL_REFERENCE_CALLS = _kernel_reference_calls()


def call_names(calls: Iterable[tuple[str, object]]) -> list[str]:
    """Parameter ids for a table of named calls."""
    return [name for name, _ in calls]
