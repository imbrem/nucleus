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
  `resolution`, `refl`, `symm`, `trans`, `cong`, `xor1`, `xor2`, `xor_pos2`,
  `not_symm`, `distinct_elim`, `and`, a Boolean-only `evaluate`, and the
  `bool-double-not-elim`, `bool-eq-true`, `bool-eq-false`, `eq-refl`,
  `eq-symm`, `ite-true-cond`, `ite-false-cond`, `ite-eq`, `ite-eq-branch`
  RARE rewrites.
- Every arithmetic rule fails closed with `ArithmeticTheoryMissing`, which is
  deliberately distinct from `Unsupported`: `poly_simp`, `poly_simp_rel`,
  `la_generic`, `la_mult_pos`, `la_mult_neg`, `la_disequality`, `la_rw_eq`,
  `la_totality`, `la_tautology`, `comp_simplify`, `div_intro`, every `arith-*`
  RARE name, `mod-elim`, `div-elim`, and `evaluate` on a numeric-sorted
  equation.

`covalence_logic_alethe::lower_qf_uflia` is therefore not a checker. It
returns a `Lowering` with no theorem accessor, no `ThmId`, no conversion into
a `Refutation` and no rule-handler parameter, and it reports the first
arithmetic rule that stopped the proof. A proof that replays to its end
without needing arithmetic is refused rather than certified, because whether a
QF_UFLIA problem's unsatisfiability is purely propositional is not visible in
its input. Issue 1208 tracks the checked arithmetic, and issue 1210 tracks the
compact literal rows it would need; this frontend depends on neither and emits
no literal row.

The measured reach is a machine-checked table in
`covalence-logic-alethe`'s `lowers_live_cvc5_qf_uflia_proofs_to_a_named_arithmetic_gap`:
26 curated cvc5 1.3.4 problems, the propositional rules each one replays, and
the first arithmetic rule that stops it. All proofs are generated with
`--proof-granularity=dsl-rewrite`, which is hole-free on 143 of 143 measured
QF_UFLIA problems; `dsl-rewrite-strict` leaves a `hole` step on 6.3% of them,
and a `hole` is an unchecked solver step this replayer rejects outright.
