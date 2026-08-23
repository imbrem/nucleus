"""Userspace helpers for driving the checked Ethane kernel from Python.

The kernel deliberately ships small local rules and no proof search, no cache
policy, and no structural equality. Everything here is ordinary Python built
on the public `covalence.logic.hol` surface: it holds no privilege the tests
do not already have, and a bug in it can only make a test fail, never make the
kernel accept something it would otherwise reject.

Three groups of helpers live here.

* Value views. The snapshot classes are opaque handles without `__eq__`, so
  `fact_view` and friends project them onto tuples that compare structurally.
* Row access. `Rows` caches `Kernel.arena`, which returns a fresh copy of the
  whole arena on every access.
* Proof construction. `prove_congruence` and `substitute` walk rows and emit
  the corresponding kernel rules, which is how a real client would drive
  conversion. `substitute` is what makes beta reduction reachable.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator

from covalence.logic.hol import Arena, Definition, Kernel, Link, Meta, SynFact

__all__ = [
    "BINDER_TAGS",
    "IMPLICIT_BINDER_TAGS",
    "LEAF_TAGS",
    "PROXY_TAGS",
    "VARIABLE_TAGS",
    "Basis",
    "CannotProveError",
    "Rows",
    "arena_view",
    "basis",
    "beta",
    "child_ids",
    "definition_view",
    "fact_view",
    "implicit_binder",
    "import_view",
    "link_view",
    "meta_view",
    "prove_congruence",
    "substitute",
    "unify",
]

LEAF_TAGS = frozenset({"kind.star", "ty.bool", "tm.bool"})
VARIABLE_TAGS = frozenset({"ty.fv", "tm.fv"})
BINDER_TAGS = frozenset({"ty.lam", "tm.lam"})
IMPLICIT_BINDER_TAGS = frozenset({"ty.model", "tm.ty_exists"})
PROXY_TAGS = frozenset({"kind.ref", "ty.ref", "tm.ref"})


class CannotProveError(Exception):
    """A helper declined to build a derivation the kernel would reject."""


def fact_view(fact: SynFact) -> tuple[str, int | None, int | None, int, int]:
    """The payload of a syntactic fact, without its ephemeral slot ID."""
    return (fact.relation, fact.var, fact.val, fact.input, fact.output)


def definition_view(definition: Definition) -> tuple[object, ...]:
    """Every member of one row snapshot, in stub declaration order."""
    return (
        definition.reference,
        definition.tag,
        tuple(definition.children),
        definition.name,
        definition.value,
        definition.source,
        definition.foreign,
        definition.equal,
        definition.classifier,
    )


def meta_view(meta: Meta) -> tuple[str, int, int | None, int | None]:
    """Every member of one premise or conclusion snapshot."""
    return (meta.tag, meta.source, meta.reference, meta.classifier)


def link_view(link: Link) -> tuple[str, bytes]:
    """Every member of one import link."""
    return (link.format, bytes(link.blake3))


def import_view(entry: None | Arena | Link) -> object:
    """One import entry, projected recursively onto comparable values."""
    if entry is None:
        return None
    if isinstance(entry, Link):
        return link_view(entry)
    return arena_view(entry)


def arena_view(arena: Arena) -> dict[str, object]:
    """A structural snapshot of everything an arena exposes to Python.

    `Arena.addr` already distinguishes two arenas, but it says nothing about
    *where* they differ; this is what a failing round-trip assertion reads.
    """
    return {
        "definitions": [definition_view(row) for row in arena.definitions],
        "imports": [import_view(entry) for entry in arena.imports],
        "axioms": list(arena.axioms),
        "context": list(arena.context),
        "assumptions": [meta_view(meta) for meta in arena.assumptions],
        "assertions": [meta_view(meta) for meta in arena.assertions],
    }


def child_ids(facts: Iterable[SynFact]) -> list[int]:
    """Slot IDs for `Kernel.syn_congr`, which takes IDs rather than handles."""
    return [fact.id for fact in facts]


class Basis:
    """The two rows every non-trivial kernel needs before anything else."""

    __slots__ = ("bool_ty", "kernel", "star")

    def __init__(self, kernel: Kernel) -> None:
        self.kernel = kernel
        self.star = kernel.star()
        self.bool_ty = kernel.bool_ty(self.star)

    def var(self, name: int) -> int:
        """A Boolean term variable."""
        return self.kernel.tm_fv(name, self.bool_ty)

    def literal(self, value: bool) -> int:
        """A Boolean literal."""
        return self.kernel.bool(self.bool_ty, value)


def basis(kernel: Kernel | None = None) -> Basis:
    """A fresh kernel carrying `kind.star` and `ty.bool`."""
    return Basis(Kernel() if kernel is None else kernel)


class Rows:
    """A refreshing cache over `Kernel.arena.definitions`.

    `Kernel.arena` clones the entire arena on every access, so a walk that
    reads it per node is quadratic. Rows created after a snapshot are picked
    up by one further clone, on the first miss.
    """

    __slots__ = ("_kernel", "_rows")

    def __init__(self, kernel: Kernel) -> None:
        self._kernel = kernel
        self._rows: dict[int, Definition] = {}
        self.refresh()

    def refresh(self) -> None:
        self._rows = {row.reference: row for row in self._kernel.arena.definitions}

    def __getitem__(self, reference: int) -> Definition:
        row = self._rows.get(reference)
        if row is None:
            self.refresh()
            row = self._rows[reference]
        return row

    def __len__(self) -> int:
        return len(self._rows)

    def __iter__(self) -> Iterator[Definition]:
        return iter(self._rows.values())

    def tag(self, reference: int) -> str:
        return self[reference].tag

    def children(self, reference: int) -> list[int]:
        return self[reference].children

    def mentions(self, root: int, name: int, sort: str) -> bool:
        """Whether a variable of `name` and `sort` occurs beneath `root`.

        Conservative in the same direction as the kernel: an import proxy
        counts as an occurrence, because nothing local can see inside it.
        """
        pending = [root]
        seen: set[int] = set()
        while pending:
            reference = pending.pop()
            if reference in seen:
                continue
            seen.add(reference)
            row = self[reference]
            if row.tag in PROXY_TAGS:
                return True
            if row.tag in VARIABLE_TAGS and row.name == name and _sort(row.tag) == sort:
                return True
            pending.extend(row.children)
        return False


def _sort(tag: str) -> str:
    return tag.split(".", 1)[0]


def prove_congruence(
    kernel: Kernel, left: int, right: int, rows: Rows | None = None
) -> SynFact:
    """Prove the direct fact `left =_syn right` by structural congruence.

    Two rows built by separate constructor calls are distinct references even
    when they spell the same expression, and the kernel compares classifiers
    by equality class rather than by reference. Recovering the class therefore
    means walking both rows and unioning the classifiers on the way up, which
    is what a client with a hash-consing index would do once instead.

    Raises `CannotProveError` when the two rows do not spell the same expression.
    """
    rows = Rows(kernel) if rows is None else rows
    if left == right:
        return kernel.syn_refl("syn", left)

    left_row, right_row = rows[left], rows[right]
    if left_row.tag != right_row.tag:
        raise CannotProveError(f"{left_row.tag} is not {right_row.tag}")
    if (left_row.name, left_row.value) != (right_row.name, right_row.value):
        raise CannotProveError(f"{left_row.tag} rows carry different payloads")
    if (left_row.source, left_row.foreign) != (right_row.source, right_row.foreign):
        raise CannotProveError("proxies address different imports")

    children = [
        prove_congruence(kernel, one, other, rows)
        for one, other in zip(left_row.children, right_row.children, strict=True)
    ]
    _unify_classifiers(kernel, left, right, rows)

    if left_row.tag in BINDER_TAGS:
        return kernel.syn_binder_congr("syn", left, right, children[0], children[1])
    if left_row.tag in IMPLICIT_BINDER_TAGS:
        witness = implicit_binder(kernel, left_row.name, rows)
        return kernel.syn_implicit_binder_congr(
            "syn", left, right, witness, children[0]
        )
    return kernel.syn_congr("syn", left, right, child_ids(children))


def unify(kernel: Kernel, left: int, right: int, rows: Rows | None = None) -> None:
    """Join two structurally equal rows into one equality class."""
    kernel.union_syn_fact(prove_congruence(kernel, left, right, rows))


def implicit_binder(kernel: Kernel, name: int | None, rows: Rows) -> int:
    """A `ty.fv` row of kind `kind.star` witnessing an implicit binder name.

    `Model` and `tm.ty_exists` store only the binder's numeric name, so every
    rule beneath them asks for an explicit row to stand in for it.
    """
    if name is None:
        raise CannotProveError("row has no binder name")
    star = next((row.reference for row in rows if row.tag == "kind.star"), None)
    if star is None:
        raise CannotProveError("kernel has no kind.star row")
    for row in rows:
        if row.tag == "ty.fv" and row.name == name and row.classifier == star:
            return row.reference
    reference = kernel.ty_fv(name, star)
    rows.refresh()
    return reference


def _unify_classifiers(kernel: Kernel, left: int, right: int, rows: Rows) -> None:
    """Make two rows classifier-compatible, as every rule's conclusion needs.

    Every mint rule ends in `compatible(input, output)`: same category, and
    union-find-equivalent classifiers for everything but a kind. Two rows that
    spell the same type are still two references until something unions them,
    so this proves and records that edge.

    A substitution that genuinely *changes* a term's type cannot satisfy the
    condition at all; that boundary surfaces here as a `CannotProveError`.
    """
    if kernel.category(left) == "kind":
        return
    left_classifier = kernel.classifier(left)
    right_classifier = kernel.classifier(right)
    if kernel.equivalent(left_classifier, right_classifier):
        return
    try:
        unify(kernel, left_classifier, right_classifier, rows)
    except CannotProveError as error:
        raise CannotProveError(
            f"rows {left} and {right} advertise unrelated classifiers "
            f"{left_classifier} and {right_classifier}"
        ) from error


def _same_variable(one: Definition, other: Definition) -> bool:
    """The kernel's notion of binder identity: name and classifier reference."""
    return (
        one.tag in VARIABLE_TAGS
        and one.tag == other.tag
        and one.name == other.name
        and one.classifier == other.classifier
    )


def _is_substitution_leaf(variable: Definition, row: Definition) -> bool:
    """Exactly the rows `Kernel.syn_sub_leaf` accepts, per the rule catalogue."""
    if row.tag in LEAF_TAGS:
        return True
    if row.tag not in VARIABLE_TAGS:
        return False
    if variable.tag == "ty.fv":
        return row.tag == "ty.fv" and row.name != variable.name
    return row.tag == "ty.fv" or row.name != variable.name


def substitute(
    kernel: Kernel,
    var: int,
    val: int,
    source: int,
    rows: Rows | None = None,
    memo: dict[int, tuple[int, SynFact]] | None = None,
) -> tuple[int, SynFact]:
    """Build `[val/var] source` and prove `[val/var] source =_syn output`.

    Returns the output row and the fact relating it to `source`. Rows that the
    substitution leaves alone are shared rather than rebuilt, so a closed
    subterm costs one leaf fact and no new definitions.

    Raises `CannotProveError` for the cases the kernel refuses on purpose: capture
    by a binder in `val`, two same-named variables that are not the same row,
    and descending into an import proxy.
    """
    rows = Rows(kernel) if rows is None else rows
    memo = {} if memo is None else memo
    if source in memo:
        return memo[source]

    result = _substitute(kernel, var, val, source, rows, memo)
    memo[source] = result
    return result


def _substitute(
    kernel: Kernel,
    var: int,
    val: int,
    source: int,
    rows: Rows,
    memo: dict[int, tuple[int, SynFact]],
) -> tuple[int, SynFact]:
    if source == var:
        return val, kernel.syn_sub_var(var, val)

    variable, row = rows[var], rows[source]
    if row.tag in PROXY_TAGS:
        raise CannotProveError("substitution cannot descend into an import proxy")
    if row.tag == variable.tag and row.name == variable.name:
        raise CannotProveError("two rows spell the same variable")
    if _is_substitution_leaf(variable, row):
        return source, kernel.syn_sub_leaf(var, val, source)
    if row.tag in BINDER_TAGS:
        return _substitute_binder(kernel, var, val, source, rows, memo)
    if row.tag in IMPLICIT_BINDER_TAGS:
        return _substitute_implicit_binder(kernel, var, val, source, rows, memo)

    children = [
        substitute(kernel, var, val, child, rows, memo) for child in row.children
    ]
    output = _rebuild(kernel, row, [reference for reference, _ in children], rows)
    if output != source:
        _unify_classifiers(kernel, source, output, rows)
    fact = kernel.syn_congr(
        "syn",
        source,
        output,
        child_ids(fact for _, fact in children),
        var=var,
        val=val,
    )
    return output, fact


def _substitute_binder(
    kernel: Kernel,
    var: int,
    val: int,
    source: int,
    rows: Rows,
    memo: dict[int, tuple[int, SynFact]],
) -> tuple[int, SynFact]:
    row = rows[source]
    binder, body = row.children
    binder_row, variable = rows[binder], rows[var]

    if _same_variable(binder_row, variable):
        # The binder shadows the substitution; both premises are direct.
        fact = kernel.syn_binder_congr(
            "syn",
            source,
            source,
            kernel.syn_refl("syn", binder),
            kernel.syn_refl("syn", body),
            var=var,
            val=val,
        )
        return source, fact
    if binder_row.tag == variable.tag and binder_row.name == variable.name:
        raise CannotProveError("binder and substitution variable are ambiguous")
    if rows.mentions(val, binder_row.name, _sort(binder_row.tag)):
        raise CannotProveError("replacement would be captured by the binder")

    crosses_binder = row.tag == "tm.lam" and variable.tag == "ty.fv"
    if crosses_binder:
        new_binder, binder_fact = substitute(kernel, var, val, binder, rows, memo)
    else:
        new_binder, binder_fact = binder, kernel.syn_refl("syn", binder)
    new_body, body_fact = substitute(kernel, var, val, body, rows, memo)

    output = _rebuild(kernel, row, [new_binder, new_body], rows)
    if output != source:
        _unify_classifiers(kernel, source, output, rows)
    fact = kernel.syn_binder_congr(
        "syn", source, output, binder_fact, body_fact, var=var, val=val
    )
    return output, fact


def _substitute_implicit_binder(
    kernel: Kernel,
    var: int,
    val: int,
    source: int,
    rows: Rows,
    memo: dict[int, tuple[int, SynFact]],
) -> tuple[int, SynFact]:
    row = rows[source]
    (body,) = row.children
    witness = implicit_binder(kernel, row.name, rows)
    witness_row, variable = rows[witness], rows[var]

    if _same_variable(witness_row, variable):
        fact = kernel.syn_implicit_binder_congr(
            "syn",
            source,
            source,
            witness,
            kernel.syn_refl("syn", body),
            var=var,
            val=val,
        )
        return source, fact
    if witness_row.tag == variable.tag and witness_row.name == variable.name:
        raise CannotProveError("binder and substitution variable are ambiguous")
    if rows.mentions(val, witness_row.name, "ty"):
        raise CannotProveError("replacement would be captured by the implicit binder")

    new_body, body_fact = substitute(kernel, var, val, body, rows, memo)
    output = _rebuild(kernel, row, [new_body], rows)
    if output != source:
        _unify_classifiers(kernel, source, output, rows)
    fact = kernel.syn_implicit_binder_congr(
        "syn", source, output, witness, body_fact, var=var, val=val
    )
    return output, fact


def _rebuild(kernel: Kernel, row: Definition, children: list[int], rows: Rows) -> int:
    """Rebuild one row over new children, sharing it when nothing moved."""
    if children == row.children:
        return row.reference
    reference = _construct(kernel, row, children)
    rows.refresh()
    return reference


def _construct(kernel: Kernel, row: Definition, children: list[int]) -> int:
    match row.tag:
        case "kind.star":
            return kernel.star()
        case "kind.arr":
            return kernel.kind_arr(*children)
        case "ty.bool":
            return kernel.bool_ty(row.classifier)
        case "ty.arr":
            return kernel.ty_arr(*children)
        case "ty.app":
            return kernel.ty_app(*children)
        case "ty.lam":
            return kernel.ty_lam(*children)
        case "ty.fv":
            return kernel.ty_fv(row.name, *children)
        case "ty.model":
            return kernel.model(row.name, *children)
        case "tm.ty_exists":
            return kernel.ty_exists(row.name, *children)
        case "tm.fv":
            return kernel.tm_fv(row.name, *children)
        case "tm.app":
            return kernel.app(*children)
        case "tm.lam":
            return kernel.lam(*children)
        case "tm.bool":
            return kernel.bool(row.classifier, row.value)
        case "tm.eq":
            return kernel.eq(row.classifier, *children)
        case "tm.eps":
            return kernel.eps(*children)
        case _:
            raise CannotProveError(f"cannot rebuild a {row.tag} row")


def beta(kernel: Kernel, redex: int, rows: Rows | None = None) -> tuple[int, SynFact]:
    """Contract one root beta redex, building the contractum if needed.

    Works for both `tm.app` over `tm.lam` and `ty.app` over `ty.lam`; the
    kernel's beta rules differ only in which category they check.
    """
    rows = Rows(kernel) if rows is None else rows
    row = rows[redex]
    if row.tag not in {"tm.app", "ty.app"}:
        raise CannotProveError(f"{row.tag} is not an application")
    function, argument = row.children
    function_row = rows[function]
    expected = "tm.lam" if row.tag == "tm.app" else "ty.lam"
    if function_row.tag != expected:
        raise CannotProveError(f"{function_row.tag} is not a {expected}")

    binder, body = function_row.children
    output, substitution = substitute(kernel, binder, argument, body, rows)
    _unify_classifiers(kernel, redex, output, rows)
    contract = kernel.tm_beta if row.tag == "tm.app" else kernel.ty_beta
    return output, contract(redex, substitution)
