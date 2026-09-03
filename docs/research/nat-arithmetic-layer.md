# The arithmetic layer over `nat`

`x * y + 5 - 3` can be written, normalized, and the result proved. This note
says what exists, where it lives, and what it cannot do.

Everything here is untrusted userspace in `crates/logic/hol-derived`. It adds
no kernel rule, no axiom, and no capability, and it is not part of the init
slice. Each law is admitted through the same public checked operations any
caller may use.

## Modules

| module              | what it adds                                                                                        |
| ------------------- | --------------------------------------------------------------------------------------------------- |
| `natural_calc.rs`   | shared plumbing: instantiate a law, rewrite under an operation, chain the steps, prove by induction |
| `natural_ring.rs`   | the eleven commutative-semiring laws                                                                |
| `natural_sub.rs`    | `pred`, truncated `sub`, and their equations                                                        |
| `natural_expr.rs`   | `Expr`, written with the usual Rust operators                                                       |
| `natural_normal.rs` | the normalizer                                                                                      |

`natural_arithmetic.rs` already fixed `add` and `mul` and proved their
recursion equations; `prove_by_induction` was factored out of the three proofs
it already contained.

## The laws

`natural_ring.rs` restates the seven inherited equations so every statement
binds left to right, then proves:

| law                      | statement                     | proof            |
| ------------------------ | ----------------------------- | ---------------- |
| `add.associative`        | `(a + b) + c = a + (b + c)`   | induction on `a` |
| `add.exchange`           | `(a + b) + c = (a + c) + b`   | equational       |
| `mul.right_zero`         | `a * 0 = 0`                   | induction on `a` |
| `mul.right_successor`    | `a * succ b = a * b + a`      | induction on `a` |
| `mul.one`                | `1 * a = a`                   | equational       |
| `mul.right_one`          | `a * 1 = a`                   | equational       |
| `mul.commutative`        | `a * b = b * a`               | induction on `a` |
| `mul.right_distributive` | `(a + b) * c = a * c + b * c` | induction on `a` |
| `mul.left_distributive`  | `a * (b + c) = a * b + a * c` | equational       |
| `mul.associative`        | `(a * b) * c = a * (b * c)`   | induction on `a` |
| `mul.exchange`           | `(a * b) * c = (a * c) * b`   | equational       |

That is a commutative semiring: `nat` has no additive inverse, so there is no
ring to complete.

`natural_sub.rs` adds `pred` and `sub` as primitive recursions, then
`sub.successor_both` (`succ a - succ b = a - b`) and `sub.add_cancel`
(`(a + b) - b = a`). The second is what makes `x * y + 5 - 3` work.

Recursion runs on the subtrahend, so the recursor is `minus b a = a - b` and
`sub` wraps it as `λa b. minus b a`. Only the two equations mention `minus`;
nothing later unfolds `sub`.

## The API

```rust
let ring = kernel.natural_ring(&naturals, &arithmetic)?;
let subtraction = kernel.natural_subtraction(&naturals, &arithmetic, &ring, schemas)?;
let normalizer = NaturalNormalizer::with_subtraction(&naturals, ring, subtraction);

let x = Expr::atom(x_term);
let y = Expr::atom(y_term);
let proof = normalizer.normalize(&mut kernel, &(x * y + 5 - 3))?;
// proof.theorem : ⊢ (x * y + 5) - 3 = x * y + 2
```

`normalize` returns a theorem, not a term, so the normalizer needs no trust.
`prove_equal` proves two expressions equal through their normal forms, and
`evaluate` reads a closed expression's value off its normal form.

## The normal form

A sum of monomials. Each monomial is a coefficient times a sorted product of
atoms; the monomials are sorted too, with the constant last. Two expressions
are equal in every commutative semiring exactly when their normal forms match,
which is the usual decision procedure.

Sums and products are both commutative monoids with the same law shapes, so
insertion and merging are written once and instantiated twice: once over
monomials with `add`, once over factors with `mul`. Combining two monomials
with the same atoms uses distributivity; combining two coefficients multiplies
numerals.

Every rewrite is a checked kernel operation. A bug in the normalizer produces a
failure, never a false theorem.

## Limits

- **Literals are unary.** `nat.zero` and `nat.succ` are the only numerals the
  init slice provides, so a literal is a `succ` tower and is capped at
  `MAX_LITERAL` (4096). Compact literal rows exist as syntax but have no
  lowering yet; when they do, numerals become cheap.
- **Subtraction is truncated and only partly decided.** `a - b` normalizes when
  `b` is a literal no larger than the constant term of `a`. Anything else stays
  an opaque atom, which is sound but incomplete: `5 - 7` is left alone rather
  than folded to `0`.
- **Cost is linear in rewrites, and each rewrite copies the arena.** The kernel
  stages every rule application, so normalizing a large expression or a large
  literal is slow. Keep literals small.
- **A normalizer is bound to one kernel.** It holds kernel-local theorem
  handles and caches the terms it builds.

## What is not here

Order (`le`, `lt`), division, and the integers. The `num1`/`num2` builtin
registry reserves opcodes for all of them; none has a lowering yet, so none has
a law to normalize with.
