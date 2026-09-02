# Alethe proof component

This untrusted component parses solver output and drives the default
`nucleus:proof/alethe` checked-rule interface. The reusable command model,
strict parser, and native replay API live in `covalence-logic-alethe`; this
crate contains only component ABI and CAS/request glue.

The initial fixture is cvc5 QF_UF output. Unknown commands, attributes, sorts,
and rules are rejected. Solver identity, version, options, problem bytes,
proof bytes, and component identity are provenance, not proof authority.

`tests/fixtures/cvc5-qf-uflia` records one cvc5 QF_UFLIA proof, including its
`anchor`/`subproof` frames and rational literals. It is read-only evidence for
the frontend that lowers that fragment. The component ABI exposes only the
`QF_UF` refutation path.

## What QF_UFLIA support means today

Be blunt about it: **no QF_UFLIA problem can be refuted end to end, and this
build checks no arithmetic at all.** What exists is a faithful lowering and an
honest stop.

- Terms lower. `Int` and `Real` become uninterpreted type constants, numerals
  become uninterpreted term constants interned on their exact spelling, and
  `+ - * < <= > >= to_real to_int` become monomorphic uninterpreted function
  constants. Nothing is normalized: `-3` and `(- 3)` stay distinct rows, `5`
  and `5/1` stay distinct rows in distinct sorts, and `(> a b)` is not
  rewritten to `(< b a)`.
- Proofs parse, including `anchor`/`subproof` frames, `:discharge` lists,
  premises stated before `:args`, and rational literals.
- The propositional rules check, against ordinary HOL: `and_pos`, `and_neg`,
  `and_intro`, `or`, `or_neg`, `or_pos`, `not_and`, `not_or`, `not_not`,
  `contraction`, `reordering`, `equiv1`, `equiv2`, `equiv_pos1`, `equiv_pos2`,
  `implies_neg1`, `implies_neg2`, `implies`, `true`, `false`, `ite1`, `ite2`,
  `equiv_simplify`, `implies_simplify`, `or_simplify`, `subproof`, plus
  `resolution`, `th_resolution`, `refl`, `symm`, `trans`, `cong`, `xor1`,
  `xor2`, `xor_pos2`, `not_symm`, `distinct_elim`, `and`, a Boolean-only
  `evaluate`, and the `bool-double-not-elim`, `bool-eq-true`, `bool-eq-false`,
  `bool-xor-refl`, `distinct-binary-elim`, `eq-refl`, `eq-symm`,
  `ite-true-cond`, `ite-false-cond`, `ite-eq`, `ite-eq-branch` RARE rewrites.
  That is 51 accepted names, and every one has evidence: the live cvc5 corpus
  exercises 41 of them and hand-written proofs cover the 10 cvc5 1.3.4 never
  emits, with `replays_a_live_cvc5_qf_uf_rule_corpus` asserting the union is
  exactly the accepted set, so an accepting arm cannot ship untested.
- Every arithmetic rule fails closed with `ArithmeticTheoryMissing`, which is
  deliberately distinct from `Unsupported`. The classification is by rule
  family rather than by a list of individual names, so a family member this
  build has never seen is still refused by name instead of reaching a user
  rule handler: the `la_*` and `lia_*` linear-arithmetic rules, cvc5's
  `poly_simp*` extensions, `div_intro`, the numeric simplifiers
  (`comp_simplify`, `div_simplify`, `minus_simplify`, `mod_simplify`,
  `prod_simplify`, `sum_simplify`, `unary_minus_simplify`), every `arith-*`
  RARE name, `mod-elim`, `div-elim`, and `evaluate` on a numeric-sorted
  equation. `classifies_every_arithmetic_rule_by_family` asserts the whole
  inventory and that none of it reaches userspace. The residual is naming, not
  acceptance: a future RARE arithmetic rewrite spelled with neither the
  `arith-` prefix nor those two names would fail closed as `Unsupported`
  rather than by the arithmetic error.

`covalence_logic_alethe::lower_qf_uflia` is therefore not a checker. It
returns a `Lowering` with no theorem accessor, no `ThmId`, no kernel accessor,
no conversion into a `Refutation` and no rule-handler parameter, and it
reports the first arithmetic rule that stopped the proof. A proof that derives
the empty clause without needing arithmetic is refused rather than certified,
whether the arithmetic step it then states comes before the end of the proof
or the proof has no arithmetic step at all, because whether a QF_UFLIA
problem's unsatisfiability is purely propositional is not visible in its
input. Issue 1208 tracks the checked arithmetic, and issue 1210 tracks the
compact literal rows it would need; this frontend depends on neither and emits
no literal row.

The measured reach is a machine-checked table in
`covalence-logic-alethe`'s `lowers_live_cvc5_qf_uflia_proofs_to_a_named_arithmetic_gap`:
26 curated cvc5 1.3.4 problems, the propositional rules each one replays, and
the first arithmetic rule that stops it. All proofs are generated with
`--proof-granularity=dsl-rewrite`, which is hole-free on 143 of 143 measured
QF_UFLIA problems; `dsl-rewrite-strict` leaves a `hole` step on 6.3% of them,
and a `hole` is an unchecked solver step this replayer rejects outright.
