# Ethane syntactic-fact rules

This is the rule catalogue for the checked methods in
[`Kernel`](../../crates/logic/hol/src/kernel/syn_facts.rs). It describes the
logical interface, not the cache-slot allocator. The denotation is formalized
in [`SynFacts.lean`](../../lean/Nucleus/Nucleus/Hol/Ethane/Arena/OneBased/SynFacts.lean).

## Judgments

Let `R` range over the refinement chain

```text
syn ⊑ alpha ⊑ conv.
```

The three fact shapes are:

```text
b =_R c           direct:    var = null,   val = null
[·/x]b =_R c      universal: var = x,      val = null
[a/x]b =_R c      concrete:  var = x,      val = a
```

`syn` is literal named syntax, `alpha` is named alpha-equivalence, and `conv`
is alpha-beta-eta conversion. A universal fact means that `[a/x]b =_R c` for
every well-formed `a` whose syntactic sort and classifier are compatible with
`x`. A payload with `var = null, val != null` is reserved and cannot be minted
by the checked API.

For `syn`, literal `b = c` together with the fact that substituting any
compatible value for `x` leaves `b` unchanged implies `[·/x]b =_syn c`. Lean
proves this as `Value.universal_syn_of_literal_and_substitution_free`, using
the observational predicate `Value.SubstitutionFree`. The converse finite-FV
characterization is not claimed yet: it needs determinism of the named
substitution relation and a bridge to `Expr.fvars` under `NoNameConfusion`.
This is semantic completeness work, not a soundness gap in the checked rules.

Every displayed expression is an existing, well-formed row. Equality of row
letters in a premise means equality of references, not merely a proved
relation. `compatible(b,c)` means equal syntactic categories and, for every
non-`Kind` row, union-find-equivalent advertised classifiers. Semantically,
types therefore have the same kind and terms have convertible advertised
types. These common conditions appear as `Value.WellFormed` and
`Value.Compatible` in
[`SynFacts.lean`](../../lean/Nucleus/Nucleus/Hol/Ethane/Arena/OneBased/SynFacts.lean).
The complete fact denotation is `SynMeaning`; `SynFact.Valid` adds resolution,
well-formedness, and endpoint compatibility.

Every mint method also accepts `target : Option<SynFactId>`. `null` reuses the
one-based free-list head or appends a slot. A non-null target overwrites only
an occupied slot; missing and free targets are errors. These IDs are ephemeral:
removal and truncation permit reuse. Lean specifies this with `SynArena.push`,
`SynArena.replace`, `FullKernel.push`, and `FullKernel.replace`.

## Relation rules

### Reflexivity: `Kernel::syn_refl`

```text
WF(b)
-------- refl(R)
b =_R b
```

Lean: `SynRel.holds_refl`, `Value.compatible_refl`,
`SynFact.Valid.refl`, and `SynFact.Checked.refl`. The last two construct the
exact payload returned by Rust before cache-slot allocation.

### Refinement: `Kernel::syn_refine`

```text
[a/x]b =_R c    R ⊑ S
--------------------- refine
[a/x]b =_S c
```

The notation also covers direct and universal facts; their endpoint fields
are copied unchanged. Lean: `SynInference.refine`, `SynRel.Holds.refine`,
`SynInference.meaningRefine`, `SynFact.Valid.refine`, and
`SynFact.Checked.refine`. The `Valid` theorem applies to direct, universal,
and concrete-substitution facts.

### Symmetry: `Kernel::syn_symm`

```text
b =_R c
---------- symm
c =_R b
```

Only a direct premise is accepted. Reversing a substitution judgment would
not in general describe a substitution. Lean: `SynRel.Holds.symm`,
`Value.Compatible.symm`, `SynFact.Valid.symm`, and `SynFact.Checked.symm`.

### Transitivity: `Kernel::syn_trans`

```text
[a/x]b =_R c    c =_S d    R ⊑ T    S ⊑ T
------------------------------------------------ trans
[a/x]b =_T d

b =_R c         c =_S d    R ⊑ T    S ⊑ T
------------------------------------------------ trans
b =_T d
```

The first schema also covers `[null/x]`, the universal judgment. The left
premise may therefore have any valid endpoint shape; the right premise must
be direct. Rust chooses the coarser of `R` and `S` for `T`. Lean:
`SynMeaning.trans_direct` is the semantic theorem and
`SynInference.transDirect` is its proof-relevant form.

## Substitution rules

### Variable: `Kernel::syn_sub_var`

```text
x is a free variable    compatible(x,a)
---------------------------------------- sub-var
[a/x]x =_syn a
```

Lean: `Value.Substitutes.varCase`, `NamedSubstitution.hit`, and
`SynInference.substitutionVariable`.

### Unchanged leaf: `Kernel::syn_sub_leaf`

```text
x is a free variable    compatible(x,a)
l is *, 2, true, false, or a free variable with a different name from x
------------------------------------------------------------------------ sub-leaf
[a/x]l =_syn l
```

The free-variable line abbreviates exactly these cases:

- type variable `x` and a differently named type variable `l`;
- term variable `x` and any type variable `l`;
- term variable `x` and a differently named term variable `l`.

A type variable `x` with a term-variable `l` is rejected because substitution
must descend into `l`'s type child. An imported proxy is not a leaf for this
rule. Lean: `detail.Expr.ActiveSubstitutionLeaf`,
`NamedSubstitution.leaf`, and `SynInference.substitutionUnchanged` once that
leaf derivation is resolved.

### Universally unchanged leaf: `Kernel::syn_sub_leaf_forall`

```text
x is a free variable
l is *, 2, true, false, or a free variable with a different name from x
----------------------------------------------------------------------- sub-leaf-∀
[·/x]l =_syn l
```

The accepted variable combinations are exactly the three cases listed for
`syn_sub_leaf` above.

Lean: `SynInference.universalSubstitutionUnchanged` quantifies over compatible
well-formed replacements; each instance uses `NamedSubstitution.leaf` (and
ultimately `NamedSubstitution.congr`) with an empty child derivation.

### Syntactic identity: `Kernel::syn_sub_identity`

```text
x =_syn a    b =_R c
-------------------- sub-id
[a/x]b =_R c
```

Both premises are direct. The first says that replacing `x` by `a` is
literally the identity. Lean: `Value.SyntaxEqual`,
`NamedSubstitution.hit`/`NamedSubstitution.congr`, and
`SynInference.substitution`.

## Congruence rules

### Non-binding constructor: `Kernel::syn_congr`

For a non-binding constructor `C` with identical non-child payload on both
sides:

```text
[a/x]b₁ =_R c₁  ...  [a/x]bₙ =_R cₙ
compatible(C(b₁,...,bₙ), C(c₁,...,cₙ))
------------------------------------------------ congr-C
[a/x]C(b₁,...,bₙ) =_R C(c₁,...,cₙ)
```

Child facts may refine `R`. The direct and universal forms use respectively
no endpoints and `[null/x]` on every premise and conclusion. A variable whose
name is `x` and every binder are rejected here. At a free-variable root,
child facts must refine `syn` even when the parent relation is `alpha` or
`conv`; this prevents a coarser classifier relation from changing variable
identity. Concrete and universal substitution reject proxy roots, while a
direct fact may relate matching proxies with the same import and foreign
index.
Lean: `NamedSubstitution.SameHead`, `NamedSubstitution.congr`,
`Value.Congruence`, and `SynInference.congr`.

### Explicit binder without renaming: `Kernel::syn_binder_congr`

For `B` equal to `ty.lam` or `tm.lam`:

```text
binder premise    body premise    freshness/shadowing obligations
compatible(B(x,b), B(x',c))
-------------------------------------------------------------- congr-B
[a/z]B(x,b) =_R B(x',c)
```

The exact child endpoints are determined as follows.

- If `z` is the binder, substitution is shadowed: both child premises are
  direct.
- A type substitution through `tm.lam` crosses the binder. The binders must
  have the same numeric name, and the binder child itself needs the same
  concrete or universal substitution evidence; its classifier may change.
- In every other case the two binder rows must be exactly the same typed
  variable and their evidence is direct.
- Same-category, same-name binders with different classifier references are
  rejected as ambiguous.
- If `z` and the binder have different categories, substitution crosses the
  body. This includes term substitution through `ty.lam`.
- For a concrete same-category substitution below a non-shadowing binder,
  `x` must not occur in `a`.
- A universal same-category substitution cannot cross a non-shadowing binder,
  because some replacement could contain the binder.

Binder and body evidence may use relations finer than `R`; their references
and selected endpoint modes must match exactly. The complete input/output
rows must be compatible. Freshness scanning treats an import proxy or fuel
exhaustion as a possible occurrence and rejects the rule.

Lean: the `tyLamShadow`, `tyLamCongr`, `lamTmShadow`, `lamTmCongr`, and
`lamTyCongr` constructors of `Value.NamedSubstitution`, plus
`Value.Congruence` and `SynInference.congr`.

### Implicit binder without renaming: `Kernel::syn_implicit_binder_congr`

This is the preceding rule for the implicit type binder of `tyExists` and
`Model`. An explicit `ty.fv` row witnesses the stored binder name.

```text
body premise    binder witness    freshness/shadowing obligations
compatible(B(x,b), B(x,c))
---------------------------------------------------------------- congr-implicit
[a/z]B(x,b) =_R B(x,c)
```

There is no `conv` instance for `Model`. Lean: the `tyExists*` and `model*`
constructors of `Value.NamedSubstitution`, `Value.Congruence`, and the theorem
`Value.no_conversion_congruence_under_model`.

Input and output must have the same constructor and stored name. The witness
must carry the literal `kind.star` classifier. Universal type substitution
cannot cross this type binder; concrete type substitution must prove
freshness. Term substitution crosses it. Body evidence may refine `R` and
must use the endpoint mode selected by shadowing. Proxies make the freshness
check fail conservatively.

## Alpha rules

### Explicit binder renaming: `Kernel::syn_alpha_binder`

```text
classifier(x) =_alpha classifier(y)    [y/x]b =_alpha c
y is fresh for b
---------------------------------------------------------------- alpha-B
B(x,b) =_alpha B(y,c)
```

The freshness premise is omitted when `x` and `y` are the same typed
variable. Each displayed alpha premise may in fact be a direct `syn` or
`alpha` fact, since either refines `alpha`; its references and substitution
endpoints must match exactly. A proxy in the scanned body conservatively
fails freshness. Lean: `Nucleus.Hol.Ethane.Expr.Alpha`, `Value.Alpha`,
`NamedSubstitution`, and `SynInference.direct`.

### Implicit binder renaming: `Kernel::syn_alpha_implicit_binder`

```text
x and y witness the stored binder names    [y/x]b =_alpha c
y is fresh for b
---------------------------------------------------------------- alpha-implicit
B(x,b) =_alpha B(y,c)
```

`B` is either `tyExists` or `Model`. This is alpha-equivalence, not conversion
congruence beneath `Model`. The body premise may be `syn` or `alpha`; both
binder witnesses must be literal `ty.fv` rows of kind `star`, and proxy
freshness is rejected conservatively. Lean: `Nucleus.Hol.Ethane.Expr.Alpha`,
`Value.Alpha`, `NamedSubstitution`, and `SynInference.direct`.

## Root conversion rules

### Type beta: `Kernel::ty_beta_fact`

```text
[A/x]b =_conv c
------------------------------ beta-ty
(ty.lam x. b) A =_conv c
```

The application shape is checked from rows and its result is required to be
classifier-compatible with `c`. The stored substitution premise may be
`syn`, `alpha`, or `conv`; each refines the displayed conversion premise.
Lean: `Nucleus.HolE.Named.FamBeta`,
`Value.equal_family_beta`, `SynInference.familyBeta`, and
`SynInference.familyBeta_sound`.

### Term beta: `Kernel::tm_beta_fact`

```text
[a/x]b =_conv c
-------------------------- beta-tm
(tm.lam x. b) a =_conv c
```

The stored substitution premise may be `syn`, `alpha`, or `conv`, and the
source/output rows must be classifier-compatible.

Lean: `Nucleus.HolE.Named.TmBeta`, `Value.equal_term_beta`,
`SynInference.termBeta`, and `SynInference.termBeta_sound`.

### Term eta: `Kernel::tm_eta_fact`

```text
x is not free in f
-------------------------- eta-tm
(tm.lam x. f x) =_conv f
```

This rule accepts the exact displayed shape. Alpha variants are compositions
of cached facts. Lean: `Nucleus.HolE.Named.TmEta`, `Value.equal_term_eta`,
`SynInference.termEta`, and `SynInference.termEta_sound`.

No beta or eta rule reduces beneath `Model`; see
`Value.no_conversion_congruence_under_model` and
`Nucleus.Hol.Ethane.OneBased.no_beta_from_model`.

## Equality union and cache operations

`Kernel::union_syn_fact` consumes only a direct fact `b =_R c`, for any of
`syn`, `alpha`, or `conv`, and joins the two row references in the arena
union-find. This is sound because both finer relations refine semantic
conversion. The kernel's semantic invariant states that every such edge is
true; its closure is formalized by
[`EqClass`](../../lean/Nucleus/Nucleus/Hol/Ethane/Arena/OneBased/UnionFind.lean)
and queried semantically by `Kernel.find_sound`.

`syn_fact`, `syn_fact_len`, `remove_syn_fact`, and `truncate_syn_facts` are
cache operations, not inference rules. `syn_fact_len` counts occupied and free
slots. `syn_fact` rejects a missing or free one-based slot. Removal replaces
an occupied slot with a link to the old free-list head; truncation retains a
prefix and rebuilds an ascending free chain over the retained holes. Neither
operation can add a claim. Their exact behavior and preservation of
`SynArena.Sound`, `SynArena.FreeListSafe`, and `FullKernelValid` are specified
by `SynArena.remove`, `SynArena.truncate`, `SynArena.Sound.remove`,
`SynArena.Sound.truncate`, `SynArena.FreeListSafe.remove`,
`SynArena.FreeListSafe.truncate`, `FullKernel.remove`, and
`FullKernel.truncate`.

Removal returns `false` without mutation for a missing or already-free slot.
Truncation is total; a length beyond the table size retains every slot and
still rebuilds the free chain.

## Imported proxies

`tm.ref`, `ty.ref`, and `kind.ref` are opaque edges to another table. A proxy
row does **not** itself assert that the imported expression is closed. Walking
through it during substitution would therefore silently assume that `x` is
not free in the imported expression. The current local leaf and congruence
rules conservatively reject that operation.

A future theorem-import interface may supply a checked universal fact
`[·/x]proxy =_R proxy`. Once supplied, the existing refinement and generalized
transitivity rules can consume it without inspecting the imported table. No
unchecked closedness assumption is part of the current kernel.

## Exact-checker correspondence still to prove

The cited Lean declarations prove the denotation of the rules and the safety
of the fact table. Reflexivity, refinement, and direct symmetry now construct
the exact valid and checked payload returned by their Rust methods. The leaf
helpers expose the corresponding proof-relevant substitution rules.

The remaining concrete row-checker bridges are generalized transitivity
(which first needs the fuel-bounded resolver's uniqueness theorem), the
non-binding and binder case splits, beta composition with cached
substitution, the eta occurrence scanner, and the `SynFact.Valid`-to-
`UnionResult` step for `union_syn_fact`. These are exact
implementation-correspondence obligations; they do not leave the semantic
meaning of a fact unspecified.
