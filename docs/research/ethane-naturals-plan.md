# From the axiom of infinity to `1 + 1 = 2`

This is the route from what the kernel has today to a full object-language
theory of the natural numbers: literals, accelerated arithmetic, the abstract
algebraic hierarchy, and the classic Principia target. It is a plan, not a
specification; each phase names the artifacts it must produce in Rust, in Lean,
and in the init slice, and the property that decides whether the phase is done.

## Where we actually are

The distinction that matters is between the _semantic_ naturals and the
_object-language_ naturals.

`lean/Nucleus/Nucleus/HolE/ClassicalNaturals.lean` already carries the semantic
side in full: `CNatModel`, the carving of a model out of any infinite type
(`natModelOfInjectiveNotSurjective`), `natrec` with its uniqueness theorem,
`add` and `mul` with commutativity and associativity, and `transport` between
any two models. That is a theorem _about the meaning_ of `ax.inf`.

Nothing of that exists as Ethane syntax. There is no `nat` row, no `nat.rec`
definition in the executable init slice, and no object-language theorem whose
statement mentions a natural number. `theories/init-boolean.checked.json`
stops at `imp` — ten declarations, the Boolean fragment. `theories/init.json`
is a design sketch (`"status": "design-sketch"`) that already names `ind`,
`nat`, `nat.rec`, `nat.add`, `nat.mul`, `nat.le`, `nat.lt` with the intended
bodies. The sketch is the target; the checked slice is the floor.

So the work is to close the gap between a Lean theorem about models and an
Ethane arena that proves things.

## Phase 1 — `ind` and the carving of `nat`

The sketch's construction is the standard HOL one and it is the right one,
because the carving is the content. `ind` is the infinite type delivered by
`ax.inf`; `nat` is the subtype of `ind` cut out by the induction predicate:

    nat := { x : ind // ∀ P : ind → bool.
              (P ind.zero ∧ closed-under P ind.succ) → P x }

Deliverables:

- Kernel: `ind`, `ind.zero`, `ind.succ` derived from `Kernel::inf_exists`, with
  `ind.succ.injective` and `ind.zero ≠ ind.succ n` as proved theorems, not
  assumptions. The existing `InfinityAxiom` binder already yields the injective
  non-surjective map; `ind.zero` is the missed point.
- Userspace: `nat` as a `Subtype` package over `ind` (the untrusted
  `SubtypeExt` in `crates/nucleus/src/subtype.rs`), so the carving stays out of
  the TCB. `ax.sub` is the only extra capability.
- Lean: the object-level `nat` must be shown to denote a `CNatModel`. This is
  the bridge theorem and it is the phase's real deliverable — everything later
  reads its conclusion rather than re-deriving it.

Done when: `nat.zero`, `nat.succ` and `nat.induction` are object-language
theorems in an arena whose `axs` is exactly `{ax.inf, ax.sub}`.

Implementation checkpoint: `covalence-logic-hol-derived::NaturalExt` now
constructs the chosen `ind`, the induction-closure predicate, the guarded
`nat` subtype, `nat.zero`, `nat.succ`, and the exact induction statement with
those two capabilities. The init S-expression source lives in the separate
untrusted `covalence-logic-hol-script` crate. The remaining distinction is
intentional: `nat.induction` is currently a well-typed statement, not yet a
projected theorem. Issue #997 tracks the minimal standard HOL equality and
instantiation calculus needed to turn the package theorem into that result;
the API must not label the row proved before that bridge exists.

Open universals land here. `nat`'s defining predicate quantifies over
`P : ind → bool`, a _term_ quantifier, so it does not need `ty.forall`. But the
algebraic hierarchy in phase 5 does, and the coproduct rule that motivated
`ty.forall` is the same shape. The quantifier is now open — its predicate
carries the ambient term depth — so a `ty.forall` may appear under `tm.lam`,
which is what the hierarchy needs.

## Phase 2 — `nat.rec` and its three laws

`nat.rec` is where the induction principle becomes a definition. The sketch
writes it as `["graph.recursor", "nat.induction", "epsilon"]`: define the
recursor by choosing, with `eps`, the unique function whose graph satisfies the
recursion equations, and use induction to prove that choice total and unique.

Deliverables: `nat.rec.zero`, `nat.rec.succ`, `nat.rec.unique` as object-language
theorems. Lean already has the semantic counterpart (`natrec_unique`), so the
Lean obligation is that the object-level recursor denotes it.

Done when: `nat.rec` reduces on `nat.zero` and on `nat.succ n` by kernel
conversion, not by an axiom.

This is the phase most likely to be painful, because `eps` at a function type
plus a uniqueness argument is a lot of object-language plumbing. Budget for it.

## Phase 3 — `add`, `mul`, and their laws

Mechanical once phase 2 lands, following the sketch bodies exactly:

    nat.add := nat.rec nat (λ n. n) (λ _ f m. nat.succ (f m))
    nat.mul := nat.rec nat nat.zero (λ n f m. nat.add m (f m))

Then `add.zero`, `add.succ`, `add.assoc`, `add.comm`, `mul.zero`, `mul.succ`,
`mul.assoc`, `mul.comm`, and `distrib`. Each is an induction, so each is an
application of `nat.induction` to a predicate built from `nat.rec`'s laws.

Done when: `1 + 1 = 2` is provable — the Principia target — where `1` and `2`
are `nat.succ nat.zero` and `nat.succ (nat.succ nat.zero)`. Note that at this
point the proof uses no literals and no acceleration: it is the unary proof,
and it is the one that certifies everything after it.

## Phase 4 — `tm.nat` literals and accelerated builtins

Only now do literals make sense, because only now is there something for a
literal to _mean_.

**Representation.** `Node::Nat(u64)`, an inline unsigned literal in `Expr`, tag
`tm.nat`. Inline rather than a reference because the value is not syntax with
children; `row.rs` already has the shape for this in `Node::Bool`. u64 is the
deliberate first cut: bignat and then bigint are follow-ups, and the wire tag
must be versioned (`tm.nat.v1`) so widening the domain is a new tag rather than
a reinterpretation of an old one. `crates/logic/hol/src/init.rs` already has a
test asserting the checked manifest _rejects_ `tm.nat`; that test encodes the
current invariant and must be updated deliberately, not deleted.

**Acceleration.** `tm.succ`, `tm.pred`, `tm.add`, `tm.sub`, `tm.mul`, `tm.div`,
`tm.mod` as builtins in the existing `Op1`/`Op2` families in
`crates/logic/hol/src/builtin.rs`. That file's contract already says what a
builtin is: _a macro whose sole meaning is canonical recursive expansion to the
opcode-free init definitions_. Arithmetic builtins keep that contract — `tm.add`
on two `tm.nat` literals lowers to the phase-3 `nat.add` applied to the unary
expansions, and the accelerated evaluator must agree with that lowering. The
acceleration is a fast path for a meaning that is already fixed, never a new
meaning. `pred`, `sub`, `div` and `mod` need their total-fallback conventions
pinned in the registry (truncated subtraction, `div` and `mod` by zero) since
Ethane has no partiality.

**Trust.** Literals and arithmetic opcodes do not add an axiom. They are compact
syntax for the opcode-free definitions already present in the init slice. A
checked operation must either lower the compact row to that canonical syntax or
produce a syntactic certificate relating it to the lowering. An accelerated
evaluator may compute the same result more cheaply, but its answer is not proof
authority by itself.

This keeps the phase-3 unary proof and the accelerated spelling in the same
logic: neither depends on trusting a host u64 implementation. The agreement
test remains essential as an implementation regression test, while soundness
comes from checking the lowering rather than from a capability that blesses the
fast path.

Done when: `tm.nat 1 + tm.nat 1 = tm.nat 2` lowers to the phase-3 definitions,
the lowered proof checks in an opcode-free kernel, and differential tests assert
that accelerated construction agrees with lowering on a range of inputs
including the u64 boundary.

## Phase 5 — the algebraic hierarchy

Define, in the init slice, what it means to be a monoid, a commutative monoid,
a group, a group with zero, a semiring, a commutative semiring — each as a
predicate on a type together with its operations. Then prove `nat` satisfies
them, discharging each obligation from the phase-3 laws.

This is where `ty.forall` earns its place. An algebraic property is a statement
about _some_ carrier, and the natural encoding quantifies over the carrier:

    IsMonoid := λ op. λ unit. ∀ᵗ α. …

with the operations as term arguments under the type quantifier — which is
exactly the open form, a `ty.forall` standing under `tm.lam` and mentioning the
lambda's variables. The same shape gives the coproduct rule that motivated the
quantifier in the first place.

Done when: `nat` is a commutative semiring by an object-language proof, and the
proof of, say, `add.comm` is _reused_ rather than restated.

## Ordering and risk

Phases 1–3 are strictly sequential; each needs the previous phase's theorems.
Phase 4 depends only on phase 3's `nat.add`/`nat.mul` (it needs something to
lower _to_), and phase 5 depends only on phase 3's laws. So 4 and 5 are
independent of each other and can proceed in parallel once 3 lands.

The two places to expect trouble: phase 2, because `eps` at a function type
with a uniqueness side condition is genuinely intricate in object language; and
phase 4's agreement property, because a fast path that disagrees with its
lowering on one input is a soundness bug that a bitflag cannot catch. The
differential test is not optional there.

The init slice grows monotonically across all five phases, so the manifest hash
changes at every step. That is expected — `Manifest::addr` covers names and
migration metadata precisely so a slice revision is visible.
