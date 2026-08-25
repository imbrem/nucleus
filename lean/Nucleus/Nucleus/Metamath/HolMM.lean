import Nucleus.Metamath.HolMM.Interpretation
import Nucleus.Metamath.HolMM.Axioms

/-!
# Is `hol.mm` sound?

`hol.mm` is Metamath's own formalisation of higher-order logic (Mario Carneiro,
2014). `Nucleus.Hol` is a HOL kernel with a pointed-set semantics and a proved
soundness theorem. This development interprets the first into the second and
checks `hol.mm`'s axioms one at a time. It is a sanity check in both directions:
where the two line up, that is evidence for both; where they do not, that is the
interesting part.

The short version:

* **29 of `hol.mm`'s 71 `$a` statements are proved sound here**, with nothing
  left unproved anywhere in this development. That is the entire propositional
  and equality core, all the typing rules, and the whole explicit-substitution
  fragment except one axiom.
* **`ax-hbl1` is proved *unsound*** for the interpretation used — the standard
  one, in which a variable is a (name, type) pair. `ax_hbl1_counterexample` is a
  machine-checked countermodel.
* The mismatch is not an artefact of the choice of interpretation. `ax-beta` and
  `ax-hbl1` are jointly unsatisfiable on `hol.mm`'s raw syntax; see
  "The `ax-beta`/`ax-hbl1` tension" below.
* `ax-wabs`, `ax-wrep` and `ax-tdef` are **vacuous** in the distributed
  database: their shared `typedef` hypothesis has no introduction rule.
* Connecting any of this to `Nucleus.Metamath.verifyDatabase_sound` needs unique
  readability for `hol.mm`'s grammar, which is **not** proved here. See "The
  parsing gap".

## What the interpretation is

`Nucleus.Metamath.HolMM.Interpretation` fixes a `Nucleus.Hol` signature with one
primitive family, `ind`, modelled by the pointed set `(ℕ, 0)`. `Typ` and `Term`
are `hol.mm`'s ground type and term syntax; `elabTm` walks a `Term` under a list
of binders and returns the `hol.mm` type it synthesises together with a
`Nucleus.Hol` term of that type. `hol.mm`'s two judgment forms become

* `|- A : al` ↦ `Typed A al`, i.e. `elabTm [] A` succeeds at type `al`;
* `|- R |= A` ↦ `Seq R A`, i.e. both sides interpret at `bool` and the first
  semantically entails the second, in `Nucleus.Hol`'s own `Entails`.

The technical heart is `elabEval_transfer`: the value of an interpreted term
depends only on the logical environment, not on which binders were used to reach
it. Every `hol.mm` axiom that compares a term elaborated *under* a binder with
the same term elaborated *without* one — `ax-beta`, `ax-17`, `ax-distrc`,
`ax-distrl`, `ax-leq` — is discharged with it.

Three deliberate departures from the surface syntax, each of which weakens the
claim and is therefore stated explicitly:

1. **Metavariables are instantiated by abstract syntax.** A `hol.mm` axiom is a
   Metamath *schema* over flat symbol strings. Here it is a Lean theorem
   quantified over `Typ` and `Term`. That is the intended reading, but it is not
   the same statement until the parsing gap below is closed.
2. **`=` and `@` are annotated with the type they are used at.** `hol.mm`'s `ke`
   and `tat` are genuinely polymorphic constants (`ax-weq` gives
   `|- = : ( al -> ( al -> bool ) )` for *every* `al`), and `Nucleus.Hol` has no
   polymorphism. Equivalently: the interpretation is defined on typing
   derivations, not on raw terms. This matters for `ax-eqtypi`, which is proved
   here from `elabTm_type_unique`: on the *annotated* syntax a term determines
   its type. On raw `hol.mm` terms typing is not unique — `=` alone inhabits
   infinitely many types — so `ax-eqtypi` would need a different justification
   there, and the database's own comment that it is "unnecessary" is not
   obviously right.
3. **`$d x A` is weakened to "`x` does not occur free in `A`".** Metamath's `$d`
   is stronger (it forbids bound occurrences too), so the theorems proved here
   are stronger than `hol.mm` needs.

`hol.mm`'s context comma `( A , B )` is interpreted by the Church encoding
`(λ f. f A B) = (λ f. f ⊤ ⊤)`. That encoding is forced rather than chosen: over
`bool`, `Nucleus.Hol` supplies only equality and the constants without going to
a higher type, and those generate exactly the affine Boolean functions, which do
not include conjunction.

## Status of all 71 `$a` statements

**Syntax constructors (21), no semantic content.** `tv`, `ht`, `hb`, `hi`, `kc`,
`kl`, `ke`, `kt`, `kbr`, `kct`, `tfal`, `tan`, `tne`, `tim`, `tal`, `tex`,
`tor`, `teu`, `tf11`, `tfo`, `tat`. These build `term`/`type` expressions and
are absorbed into `Typ`/`Term`. `ke` and `tat` become `Term.eq`/`Term.choose`;
the ten defined constants (`tfal` … `tfo`) are *not* in `Term`, which is why
their `df-*` axioms are unformalised.

**`mmj2` helpers (3), inert.** `wffMMJ2`, `wffMMJ2t`, `wffMMJ2d`. They conclude
at typecode `wff`, which no `|-` rule consumes.

**Proved sound (29).** `ax-wv` (`ax_wv`), `ax-wl` (`ax_wl`), `ax-wc` (`ax_wc`),
`ax-wct` (`ax_wct`), `ax-wctl` (`ax_wctl`), `ax-wctr` (`ax_wctr`), `ax-wov`
(`ax_wov`), `ax-weq` (`ax_weq`), `ax-wat` (`ax_wat`), `df-ov` (`df_ov`),
`ax-cb1` (`ax_cb1`), `ax-cb2` (`ax_cb2`), `ax-id` (`ax_id`), `ax-trud`
(`ax_trud`), `ax-syl` (`ax_syl`), `ax-simpl` (`ax_simpl`), `ax-simpr`
(`ax_simpr`), `ax-jca` (`ax_jca`), `ax-refl` (`ax_refl`), `ax-eqmp` (`ax_eqmp`),
`ax-ded` (`ax_ded`), `ax-ceq` (`ax_ceq`), `ax-eqtypi` (`ax_eqtypi`),
`ax-eqtypri` (`ax_eqtypri`), `ax-beta` (`ax_beta`), `ax-17` (`ax_17`),
`ax-distrc` (`ax_distrc`), `ax-distrl` (`ax_distrl`), `ax-leq` (`ax_leq`).

`ax-cb1` and `ax-cb2` are sound because `Seq` carries typedness of both sides.
That is not a trick to make them go through: it is the reading `hol.mm`'s own
comment on `ax-cb1` argues for ("every axiom and inference rule that constructs
a theorem of the form `R |= A` … also ensures that `R : bool` and `A : bool`"),
and every other rule proved here does establish it.

**Refuted (1).** `ax-hbl1`, by `ax_hbl1_counterexample`.

**Vacuous in the distributed database (3).** `ax-wabs`, `ax-wrep`, `ax-tdef`.
All three take `|- typedef be ( A , R ) F` as a hypothesis. In revision
`b263d6e4` the token `typedef` occurs exactly four times outside the typesetting
block: the `$c` declaration, `wffMMJ2d` (typecode `wff`), and `ax-tdef.4`
itself. No `$a` or `$p` concludes a `|-` statement whose body starts with
`typedef`, so no instance of these axioms can ever be applied. They are an
interface for extensions, not axioms of `hol.mm`. This is a syntactic fact about
the database, independently checkable; it is *not* formalised here, because
doing so would require the database itself as a Lean value.

**Believed sound in this model, not formalised (14).**

* `ax-inst`. The substantial remaining rule. Its five hypotheses encode
  "effectively not free in" via the `( \ x : al . B  y : al ) = B` idiom plus
  two conditional equations `[ x : al = C ] |= [ A = B ]`. Under the
  (name, type) reading it is the ordinary substitution lemma, and `Nucleus.Hol`
  has the ingredients (`elabEval_transfer` is the same lemma in semantic form),
  but interpreting the conditional-equation hypotheses — which quantify over
  environments in which `x : al` takes the value of `C` — is a real addition.
  Not attempted.
* `ax-eta`. True in this model: `DenoteTy (.arr A B)` is the *full* function
  space and `Eval`'s lambda rule is pointwise, so `Nucleus.Hol`'s own
  `EqTm.eta` is validated by `EqTm.sound`. Unformalised only because the
  statement is phrased with `!`, which is a `df-al` definition.
* `ax-ac`. Also true in this model, and the initial worry that a pointed-set
  semantics might not support choice is unfounded: `Nucleus.Hol.chooseValue` is
  built from `Classical.choose`, `chooseValue_spec` is exactly the principle
  `ax-ac` states, and `Proves.choice` is the kernel rule with the same content.
  `@` is already interpreted here (`chooseFun`, `eval_chooseFun`). Unformalised
  only because the statement is phrased with `!` and `==>`.
* `ax-inf`. True in *this* model, because `ind` is interpreted as `ℕ`, which is
  Dedekind-infinite. Note this is a constraint on the model, not on the
  semantics: interpreting `ind` as a one-point pointed set gives a perfectly
  good `FamilyModel IndSig` that falsifies `ax-inf`. So "the pointed-set
  semantics validates `ax-inf`" is false as stated; "there is a pointed-set
  model validating it" is true, and that is what soundness needs.
* `df-al`, `df-fal`, `df-an`, `df-im`, `df-not`, `df-ex`, `df-or`, `df-eu`,
  `df-f11`, `df-fo`. Under a definitional interpretation — extend `Term` with
  each constant and elaborate it to its definiens — every one becomes an
  instance of reflexivity of equality, exactly as `df_ov` is proved here. Sound
  by construction; mechanical but bulky, so only `df-ov` is done.

## The `ax-beta`/`ax-hbl1` tension

This is the substantive finding, and it is not a defect of the interpretation.

`hol.mm` writes a type at every variable *occurrence* (`tv : term x : al`), but
its binder `kl : term \ x : al . T` is keyed only on the name `x`. Two axioms
pull in opposite directions on the fragment where one name is used at two types.

* `ax-hbl1` (`|- T. |= [ ( \ x : al . \ x : be . A  B ) = \ x : be . A ]`, with
  hypotheses `A : ga` and `B : al` and **no** `$d`) says that substituting for
  `x` at type `al` does not enter `\ x : be . A` — for an arbitrary `be`,
  including `be ≠ al`. That is only true if a binder captures every occurrence
  of the *name*, whatever type is written at it.
* `ax-beta` (`|- T. |= ( ( = ( \ x : al . A  x : al ) ) A )`, with hypothesis
  `A : be` and **no** `$d`) says that substituting `x : al` for itself in `A`
  returns `A` unchanged. If binders captured by name alone, then in
  `\ x : al . A` an occurrence of `x : be` with `be ≠ al` would be captured at
  the wrong type, and the axiom would equate that captured (junk) value with the
  free `x : be` of the right-hand side.

Take `al = bool`, `be = ind`, `A = x : bool`.

* Name-only binding validates `ax-hbl1` and refutes `ax-beta`: with
  `al = ind`, `A = x : bool`, `\ x : ind . x : bool` is a constant function, so
  `( \ x : ind . x : bool  x : ind )` cannot be the free variable `x : bool`.
* (Name, type) binding — the reading used here, and the one every standard
  presentation of HOL uses — validates `ax-beta` (`ax_beta`) and refutes
  `ax-hbl1` (`ax_hbl1_counterexample`).

The obvious third option does not repair both, though the argument for that is
informal and is *not* machine-checked. Suppose a name carried a single value in
some common domain `U`, coerced into each type by `coerce_al : U → ⟦al⟧`, with
`\ x : al . _` binding by name and rebinding through `inj_al : ⟦al⟧ → U`. Then
`ax-beta` at `A = x : be` forces `inj_al ∘ coerce_al = id`, so every `coerce_al`
is injective; taking `al = bool` bounds `U` to at most two elements, so a
variable of type `ind` could take at most two values — which the instantiation
rules (`ax-inst`, and `cl` derived from it) cannot reconcile with the infinitely
many closed `ind`-terms that `ax-inf` produces.

`hol.mm`'s rule set is, as far as we can tell, too weak to *derive* a
contradiction from the conflict: the only rule that reduces
`( \ x : al . \ x : be . A  B )` is `ax-hbl1` itself, and the only rule that
reduces `( \ x : ind . x : bool  x : ind )` is `ax-beta` itself, so the two
never meet inside a single proof. The honest statement is therefore not
"`hol.mm` is inconsistent" but:

> `hol.mm`'s axioms have no model on their raw syntax. Any model must first
> restrict to the fragment in which each variable name is used at a single type
> — a restriction the database states nowhere and enforces nowhere, though every
> proof in it respects it.

## The parsing gap

`Nucleus.Metamath.Provable` is a relation on *flat symbol strings*. Everything
here is about abstract syntax trees. Bridging them needs, in order:

1. printers `Typ → Metamath.Expr` and `Term → Metamath.Expr`;
2. that printing commutes with Metamath substitution, whenever the substitution
   sends each term metavariable to the print of a `Term` — this is routine, as
   `substBody` is a concatenation homomorphism and a metavariable prints as a
   single symbol;
3. **unique readability**: every expression derivable at typecode `term` is the
   print of exactly one `Term`, likewise `type`/`Typ`, and every expression
   derivable at typecode `|-` is the print of a `Typed` or `Seq` statement.

Step 3 is the real content, it is an induction over `Provable` that has to
enumerate the `term`-typecode assertions of the actual database, and it is not
attempted. Until it is, the results here say that `hol.mm`'s axioms are sound
*as schemas over its intended abstract syntax*, which is the mathematically
interesting statement but not yet a theorem about the `.mm` file.

## Unproved-placeholder inventory

None. `Nucleus.Metamath.HolMM.Interpretation` and
`Nucleus.Metamath.HolMM.Axioms` each contain zero unproved placeholders and
zero `axiom`s beyond Lean's own. Everything not proved is *absent*, not assumed:
there is no declaration in this development whose statement is asserted without
proof.
-/
