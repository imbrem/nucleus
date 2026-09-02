# An arithmetic layer over `nat`

This is a plan for writing `x * y + 5 - 3` and having it simplify, on top of
the compact literal rows and the `num1`/`num2` registry. It is a plan, not a
specification.

Everything here is untrusted userspace in `crates/logic/hol-derived`. It needs
no new kernel rule, no new axiom, and no new capability. The kernel already
exposes what it takes: `ap_term`, `ap_thm`, `eq_mp`, `forall_intro`,
`forall_elim`, `imp_right`, `convert_conclusions`, and `Naturals::induct`.

## Where this starts

The init slice already freezes `nat.zero`, `nat.succ`, `nat.rec`, `nat.add`,
`nat.mul`, and these laws:

    add.zero  add.successor  add.right_zero  add.right_successor
    add.commutative  mul.zero  mul.successor
    induction  succ.injective  zero_ne_succ

`nat` is a commutative _semiring_, not a ring: there is no additive inverse,
and `nat.sub` is truncated. So `x * y + 5 - 3` normalizes to `x * y + 2` only
because the subtraction is by a literal that a literal summand covers. A
normalizer over `nat` must treat any subtraction it cannot discharge as an
opaque atom.

## Laws to prove, in order

Each is an induction of the same shape as `prove_add_commutative` in
`natural_arithmetic.rs`. Two were prototyped against the real kernel:
`add.associative` took ~90 lines and added 242 arena rows in 64 ms;
`mul.right_zero` ~45 lines and 124 rows in 41 ms. Both worked on first run.

| law                      | statement               | proof                                            |
| ------------------------ | ----------------------- | ------------------------------------------------ |
| `add.associative`        | `(a+b)+c = a+(b+c)`     | induction on `a`                                 |
| `add.exchange`           | `(x+y)+z = (x+z)+y`     | equational, from associativity and commutativity |
| `mul.right_zero`         | `n*0 = 0`               | induction on `n`                                 |
| `mul.right_successor`    | `n*(succ m) = n*m + n`  | induction on `n`; the heaviest one               |
| `mul.one`                | `1*n = n` and `n*1 = n` | equational                                       |
| `mul.commutative`        | `a*b = b*a`             | induction on `a`                                 |
| `mul.right_distributive` | `(a+b)*c = a*c + b*c`   | induction on `a`                                 |
| `mul.left_distributive`  | `a*(b+c) = a*b + a*c`   | equational, from the above and commutativity     |
| `mul.associative`        | `(a*b)*c = a*(b*c)`     | induction on `a`, after distributivity           |

That completes the commutative semiring, which is all the normalizer needs.

`ap_term(theorem, add)` followed by `ap_thm(_, c)` gives binary congruence with
no lambda or beta plumbing. That is what keeps each law short.

## Subtraction, if wanted

`nat.pred` and `nat.sub` are new recursors, each around 1500 arena rows, plus
their equations. Then `sub.zero`, `sub.self`, `sub.succ_succ`,
`sub.add_cancel` (`(a+b) - b = a`, the one `x*y + 5 - 3` turns on),
`sub.sub_add`, and `sub.add_right_cancel`.

`c * (a - b) = c*a - c*b` is the hard one and needs an auxiliary lemma about
`c * pred a`. Leave it last; without it the normalizer treats a subtraction
under a product as an atom.

## The API

An expression builder over an arena, so callers never see rows or references:

```rust
let x = ctx.var("x");
let y = ctx.var("y");
let e = x * y + ctx.nat(5) - ctx.nat(3);   // std::ops on a Copy handle
let simplified = ctx.normalize(&e)?;       // Theorem: e = x * y + 2
```

`normalize` returns a theorem, not a term. The caller gets `e = normal_form`
proved by the kernel, so the normalizer needs no trust.

## The normalizer

Standard sum-of-monomials, reflected out and replayed back:

1. Read the term into `Vec<(coefficient, Vec<variable>)>`, sorting each
   monomial's factors and then the monomials.
2. Combine equal monomials and drop zero coefficients.
3. Emit the normal form.
4. Replay the rearrangement as a chain of checked equalities: commutativity
   and `add.exchange` for sorting sums, `mul.commutative` and associativity for
   sorting factors, distributivity for expanding products, and transitivity to
   join the chain.

Two terms are equal when their normal forms match, which is the usual
decision procedure for commutative semiring identities.

Cost is dominated by step 4: one checked equality per transposition. Sorting
with a bounded number of swaps keeps it linear in the number of monomials.

## Order of work

1. The `prove_by_induction` helper, factored out of the three near-identical
   proofs already in `natural_arithmetic.rs`.
2. The nine semiring laws.
3. The expression builder.
4. The normalizer.
5. Subtraction, if wanted.

Steps 1 and 2 are the bulk. Nothing after step 2 needs another induction.
