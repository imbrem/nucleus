# Auditing Metamath axioms and definitions

Nucleus exposes two complementary views of a Metamath theorem's assumptions.
Neither moves parsing or naming conventions into the trusted kernel.

## Exact proof dependencies

`covalence_logic_metamath::trace::dependencies` walks the proof steps actually
used by an assertion and follows cited `$p` theorems transitively.
`trace::axioms` returns its sorted `$a` leaves. For a deterministic
whole-database artifact, `trace::AxiomIndex` computes every assertion's leaves
in one forward pass and returns them in source order. `trace::classify` assigns
each leaf one of four roles:

- `Axiom` and `Definition` follow caller-supplied naming conventions;
- `Syntax` is the structural class whose typecode is not the provable
  typecode;
- `Unclassified` retains provable `$a` assertions claimed by no convention.

The walk uses decoded compressed proof steps, so unused entries in a compressed
proof's label block do not appear. The result is syntactic metadata and may be
computed for an unverified database. Consumers making a claim about a valid
proof must separately require successful proof verification. In particular,
the `df-*` name is a useful report category, not evidence of conservativity.

## Theorems under an axiom set

`Nucleus.Metamath.TheoremsUnder` in
`lean/Nucleus/Nucleus/Metamath/Metatheory.lean` is the set of expressions
derivable when a predicate selects the usable database positions. The theorem
`theoremsUnder_mono` proves

```text
A ⊆ B  implies  TheoremsUnder(A) ⊆ TheoremsUnder(B).
```

This is a theorem about the Metamath derivability relation, including its
active hypotheses and distinct-variable obligations. It is not merely a fact
about the Rust dependency walker.

Eliminating `$p` citations altogether requires more than renaming inside the
current fixed-context relation. `VerifyTest.dummyDisjoint` is a checked
counterexample: a legal theorem proof can need a scope-local dummy floating
hypothesis that is intentionally absent from its mandatory frame. The corrected
direction is a binder-aware derivability relation with finite local dummy
floats and `$d` constraints, followed by alpha-renaming when proofs are spliced.
That work is tracked in [issue #1239](https://github.com/imbrem/nucleus/issues/1239).

## Propositional truth and explicit definitions

The same Lean module defines a small classical propositional calculus with
implication, falsity, the `K` and `S` schemes, classical contraposition, and
modus ponens. `Propositional.Derivable.sound` proves that derivability preserves
the ordinary truth semantics. Its closed-theorem corollary
`Propositional.theorem_true` says that a proposition proved from this axiom set
is true under every valuation.

`Propositional.DefinitionalDerivable` adds fresh proposition names together
with both directions of explicit definitions. Definition bodies are formulas
over the old atoms, so recursion is excluded by construction. Expanding every
fresh name translates an extended derivation to the base calculus;
`definitions_conservative` therefore proves that an extended proof of an old
formula yields a proof of that formula in the old calculus.

The module also defines proof-theoretic `Consistent A` as the impossibility of
deriving falsity. It proves:

- pure classical propositional logic is consistent, via its truth semantics;
- a theory postulating falsity is inconsistent;
- subsets of consistent theories are consistent;
- adjoining an already derivable proposition preserves and reflects
  consistency;
- explicit nonrecursive definitional extension preserves and reflects
  consistency.

`Independent A p` means both `A + p` and `A + not p` are consistent.
`independent_of_models` derives this from two models, and
`fresh_proposition_independent` is a concrete check for an unconstrained atom
over pure propositional logic. No ZFC independence claim is made without a
checked ZFC interpretation and models for both extensions.

Applying these results directly to a concrete `set.mm` formula still requires
a checked interpretation identifying its syntax and selected axiom labels with
this calculus. Certifying the `df-*` corpus under an appropriate explicit-
definition criterion is tracked in
[issue #1240](https://github.com/imbrem/nucleus/issues/1240) rather than inferred
from names.

## Arithmetic follow-up

The earlier `imbrem/covalence` repository contained a Peano arithmetic deep
embedding and a soundness projection. Porting it needs reconciliation with the
current HOL semantics and authority boundary, so it is tracked as follow-up
work in [issue #1241](https://github.com/imbrem/nucleus/issues/1241). The old
repository did not contain an equivalent completed second-order-arithmetic
soundness development; that new formalization is tracked in
[issue #1242](https://github.com/imbrem/nucleus/issues/1242).

The Rust `axiom_sets` module supplies deterministic named label sets for `PA`
(`peano.mm`), `HOL` (`hol.mm`), `IZF` (`iset.mm`), and `ZF`, `ZFC`, and `GT`
(`set.mm`). `resolve` checks every constant against a parsed database as a
logical `$a`; the opt-in corpus test resolves all sets against upstream files.
These constants identify assertions. They do not themselves prove consistency
or attach the intended semantics.
