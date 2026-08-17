# v0 MVP: the host language is the shell

**Scope-down.** No Scheme, no Forsp, no effects, no handlers, no parser. The
interactive shell is a **Python prompt natively and a JavaScript prompt in the
browser** — including the browser's own dev console. CBOR is the proof format.
The only thing being designed is the HOL API.

Supersedes the surface-layer half of `2026-08-17-eight-hour-mvp.md`; that plan's
kernel lanes stand unchanged. The language work in `notes/design/` is unaffected
and unscheduled — it resumes on top of this, not instead of it.

---

## 1. Why this is the right cut

Three reasons hold up, and there is a fourth that is bigger than the others.

- **Two hosts means no rewrite either way.** Python is the better bet for AI and
  application work; JS is the only one that runs in a browser, and a static
  browser demo matters. Committing to one now is a bet that has to be paid off
  later; supporting both is cheap *because both bindings already exist*.
- **Both are already implemented.** `crates/ffi/python` has a working pyo3
  module with three registered submodules and typed stubs;
  `crates/browser` + `packages/nucleus` has a working wasm-bindgen surface with
  node and browser tests. Adding HOL to each follows an established pattern
  rather than inventing one.
- **Simple imperative hosts force a simple API.** There is no way to hide a
  baroque interface behind syntax when the interface *is* the syntax.

And the fourth, which is the real prize:

> **There is no parser anywhere in v0.** Terms are built by calling constructors,
> so the API *is* the term language. That removes a reader, a printer's inverse,
> a grammar, an error-position story, and their fixtures — and it removes the
> single largest source of "is this thing I typed the thing I proved" ambiguity.

It also shrinks the TCB. CBOR decoding becomes untrusted (§4), so the trusted
crate is only the five rule files: **≈ 970 lines, unchanged from the eight-hour
plan, now with the whole surface layer outside it.**

---

## 2. The demo

Native:

```python
>>> import covalence as cv
>>> s = cv.hol.Session()
>>> f  = s.lam(s.bool_ty(), s.bound(0))
>>> a  = s.app(f, s.true())
>>> s.type_of(a)
bool
>>> th = s.eq_of_eq_tm(s.beta(a))
>>> th
|- (= bool (app (lam bool #0) #t) #t)
>>> s.to_cbor(th).hex()[:12]
'a2016f74686d'
>>> s.type_of(s.app(s.true(), s.true()))
TypeError: not a function type at argument 0
```

Browser, in the dev console with no build step:

```js
> const s = new nucleus.Session()
> const f = s.lam(s.boolTy(), s.bound(0))
> const th = s.eqOfEqTm(s.beta(s.app(f, s.true())))
> th.toString()
"|- (= bool (app (lam bool #0) #t) #t)"
> await nucleus.fromCbor(s.toCbor(th))   // re-checked, not trusted
```

Four things demonstrated: it type-checks, it beta-reduces, it mints theorems
that cannot be forged, and it rejects garbage without panicking. Same transcript,
two hosts, one kernel.

---

## 3. The API

About 35 operations. Handles are session-scoped opaque integers, kind-checked
and bounds-checked on **every** use.

```
Session()

  types      bool_ty · nat_ty · base_ty(name) · arr(a,b) · sub(carrier, pred)
  terms      bound(i) · free(name,ty) · app(f,x) · lam(dom,body) · bool(b)
             zero · succ(x) · eq(ty,l,r) · eps(ty,p) · abs(c,p,v) · rep(c,p,v)
  checking   type_of(t) -> Ty                    raises; never panics

  EqTm       refl · symm · trans · cong_app · cong_succ · cong_lam · beta · eta
  Proves     hyp · truth · eq_refl · eq_mp · choice · convert · eq_of_eq_tm
             antisymm · abs_rep · rep_abs · succ_injective · zero_not_succ

  inspect    hyps(thm) -> [Tm] · concl(thm) -> Tm · show(h) -> str
  codec      to_cbor(h) -> bytes · from_cbor(bytes) -> handle        replay
  signing    sign(thm, key) -> bytes
             admit_signed(bytes, keys: [PublicKey]) -> Thm           trusted
             trusted_keys() -> [PublicKey]     which keys this session relied on
```

Each host wraps handles in a thin class for `repr`/`toString` — perhaps fifty
lines, userspace, no logic.

### One thing agents will get wrong

`Proves Γ H p` carries its hypotheses as a **`List`**, and the API stores them
the same way. Do **not** use a set, do not deduplicate, do not sort. `antisymm`
takes derivations whose hypothesis lists are literally `p :: H` and `q :: H` and
checks that structurally.

An ergonomic hypothesis *set* would be the ordinary LCF choice and would silently
break the correspondence to the Lean, which is the whole reason the corpus
comparison in §5 means anything. Faithful beats comfortable here.

---

## 4. CBOR, signing, and where the trust boundary sits

There are **two decode paths with different trust levels**, and conflating them
is a soundness hole. Name them separately in the API and in the code.

### (a) Replay — untrusted

CBOR carries raw syntax plus a rule tape. Decode, then re-run every rule through
the same methods a caller would use. No privileged path, so a wrong decode
yields a rejected or different theorem, never an unjustified one. This codec is
userspace; its only hard requirement is not panicking on adversarial bytes.

### (b) Signed admission — trusted, and it is a different thing entirely

The point of signing is that the recipient **does not re-check the proof** —
otherwise there would be no reason to sign. So the path is: verify a signature,
decode a statement, admit it. And that makes the decoder trusted, because *what
was signed is a meaning, and a decoder is the thing that assigns meaning to
bytes*. A decoder that turns the signer's `|- true` into `|- false` converts an
honest signature into a forged theorem. This is the classic
signature-wrapping/canonicalization failure, and it has bitten XML-DSig, JWT,
and several others.

**But the decoder does not have to be the trusted component.** Invert it:

```
1.  untrusted decoder            bytes B  ──▶  candidate statement in the arena
2.  TRUSTED canonical encoder    statement ──▶  B′
3.  TRUSTED                      verify(key, sig, hash(B′))
4.  admit only if step 3 passes
```

If the decoder is wrong, `B′ ≠ B`, the hash differs, and the signature fails.
**A decoder bug can only cause false rejection, never false acceptance.**

This is strictly better than trusting the decoder, because parsing adversarial
bytes into meaning is hard and serializing a known in-memory value is easy. It
also means **`to_cbor` is TCB and `from_cbor` is not** — the opposite of the
first draft of this plan, and a much smaller thing to audit. Perhaps 150 lines.

It also preserves the standing rule intact: nothing is ever deserialized *into* a
checked object. Bytes become a raw candidate; the candidate is then verified.

### What the trusted encoder must satisfy

1. **Deterministic** — one statement, one byte string, always. Lean's
   `Cbor.deterministic` with `deterministic_unique` is exactly this property, and
   the Rust encoder is transcribed from it.
2. **Injective** — distinct statements never share bytes. This is the actual
   soundness property: a collision means a signature over one statement admits
   the other. `HolLN.Json.encode_injective` is the shape of the theorem wanted.
3. **Domain-separated** — a statement's bytes must not be readable as a term, a
   proof, a snapshot, or any other signed object. Tag the preimage.
4. **Total** — no panics on any arena-well-formed input.

### Pin the theory in the signed object, from the first signature

A signed `|- P` is only meaningful relative to the signature it was proved
under: `base "foo"` in the signer's theory and `base "foo"` in the recipient's
are different types that print identically. Without a theory identifier in the
signed preimage, a signature transfers between incompatible theories.

v0 declares no base types, so this is vacuous today — which is exactly why the
field must be there anyway. **Adding it later invalidates every signature ever
issued.** One `O256` of the theory's canonical description, in the preimage,
now.

### Signed admission is this kernel's `#print axioms`

Admitting under a key accepts a theorem the session did not check. That is a
different trust mode from everything else in the kernel and should be visible:

- the trusted key set is an **explicit argument**, never ambient;
- the session records which keys were actually relied upon;
- `session.trusted_keys()` reports them.

A result that depended on no key is checked outright; one that depended on `K`
is checked *modulo* trusting `K`. That is precisely the distinction
`#print axioms` draws in Lean, it costs almost nothing, and without it signing
is a hole rather than a feature.

---

## 5. Keeping three surfaces honest

Three bindings — Rust, Python, JS — is three chances to drift. One mechanism
catches all of it:

> **`conformance/v0.cbor`: one transcript of operations and expected results,
> replayed by a Rust test, a Python test, and a node test.**

Any divergence between hosts is a binding bug. Divergence from the expected
results is a kernel bug. The file is generated from the Lean corpus where
`HolLN` covers the case, and hand-written where it does not.

This is the same shape as the Lean/Rust differential test in the fortnight plan,
one level up, and it costs a day.

---

## 6. Work plan

| Lane | File | TCB? | Notes |
| --- | --- | --- | --- |
| L1 | `kernel/src/syntax.rs` | **TCB** | the 15-constructor enum, arena, handles |
| L2 | `kernel/src/subst.rs` | **TCB** | open/weaken/instantiate + naive reference |
| L3 | `kernel/src/check.rs` | **TCB** | `Kinded` + `HasType`, 17 rules |
| L4 | `kernel/src/eq.rs` | **TCB** | `EqTm`, 8 rules |
| L5 | `kernel/src/proves.rs` | **TCB** | `Proves`, 12 rules |
| L6 | `kernel/src/show.rs` | semi | printing. Not soundness-critical, but a wrong printer displays a true theorem as a false one — hold it to the corpus |
| L7a | `kernel/src/canon.rs` | **TCB** | canonical statement encoder: deterministic, injective, domain-separated, total. ~150 lines |
| L7b | `codec/src/cbor.rs` | user | replay encode + decode; fuzz for panics |
| L7c | `codec/src/signed.rs` | user | decode candidate, re-encode via L7a, verify. Untrusted by construction |
| L8 | `ffi/python/src/hol.rs` + `python/covalence/hol.py` | user | follow the `hash`/`sat`/`lrat` pattern exactly, including `.pyi` |
| L9 | `browser/src/hol.rs` + `packages/nucleus/src` | user | follow the `Repl` pattern; put `Session` on `window.nucleus` |
| L10 | `conformance/` + three drivers | test | §5 |

L1–L5 are unchanged from the eight-hour plan and keep their model assignment.
L7a joins them in the TCB, taking the read budget to ≈ 1120 lines.
L8 and L9 are mechanical against an existing pattern — good cheap-model lanes,
and their oracle is L10.

### Order

1. **L1–L5** to a Rust test proving `|- true` and one beta equality. Nothing else starts before this passes.
2. **L6 + L10** — printer and transcript together, since the transcript is what the printer is checked against.
3. **L8 and L9 in parallel** — both are one line per operation over a finished core.
4. **L7a** whenever L1 lands — it depends only on the syntax, and it is TCB, so it wants your reading time early rather than at the end.
5. **L7b, L7c** last. Replay needs the rule methods finished to re-check through them, and signed admission needs L7a.

### Static browser demo

`packages/nucleus/demo.html` and `demo.caddyfile` already exist for the SQLite
REPL. Extend rather than replace: the same page gains a `nucleus.Session`, and
the demo instruction is "open the console". No build step for whoever is looking.

---

## 7. Out of scope for v0

Scheme and Forsp · effect handlers, capabilities, revocation · the CEK machine ·
content-addressed links · key management, rotation, and revocation — v0 takes a key set as an argument and does nothing else with it · CAS integration beyond what `to_cbor` hands back ·
SQLite · flat arrays and arenas as an interchange format ·
e-graphs · OpenTheory, Metamath, Alethe · tactics · `run_sound` and all new Lean.

The Lean gate for v0 is the existing `empty_not_proves_false` plus the corpus.
No new Lean is written.

---

## 8. What v0 is for

Same as always: to find out whether the API is any good, cheaply, before anything
is committed to.

Specifically it answers questions the design notes cannot: whether ~35 flat
operations are enough to be pleasant, whether handles want to be integers or
objects, whether `Proves`' hypothesis list is bearable in an imperative host,
and whether building terms by constructor call is tolerable or maddening at a
real prompt.

**Write the answers into `notes/spikes/hol-kernel-rust.md` as you find them.**
That file is the input to the fortnight, and the third Rust kernel spike is
worth more for what it records than for what it runs.

### Forward pointer

When the Scheme arrives, it arrives as a *guest* of the host language, scripted
from Python and JS rather than replacing them — so it will be implemented
against this same flat API. That makes v0 a genuine test of whether the API is
complete enough to host an interpreter, which is a much harder bar than being
complete enough to type at. If something is missing, it will show up there
first.
