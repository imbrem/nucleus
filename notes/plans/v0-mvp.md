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

There are **two codecs with different trust levels**. Conflating them is a
soundness hole; failing to separate them makes the TCB much larger than it needs
to be.

### (a) The statement codec — TCB, both directions

Signing means the recipient does **not** re-check the proof. So both ends of the
wire are trusted, symmetrically:

```
signer      P  ──encode──▶  B,  sign(key, B)      encoder trusted:
                                                  a signer whose encoder emits Q
                                                  has attested to Q, not to P

recipient   B  ──decode──▶  P,  verify(key, B)    decoder trusted:
                                                  a recipient whose decoder reads Q
                                                  admits Q under a signature for P
```

Both directions carry the meaning, so both are in the TCB. This is the whole of
the correction to the previous draft of this plan.

### The single theorem that covers both

```
decode (encode S) = S            for every well-formed statement S
```

Round-trip is sufficient *and* it implies what is separately needed: if
`encode P = encode Q` for `P ≠ Q`, round-trip fails at one of them, so
injectivity is a corollary rather than an extra obligation. One theorem, both
components.

It is also the *right* theorem for this threat model. Bytes on the signed path
are always in the image of `encode`, because an attacker who could present bytes
outside it would have to forge a signature. So the general "decoder must
withstand arbitrary adversarial input" burden does not apply to *soundness*
here — only to totality.

`HolLN.Json` already establishes this shape, with `encode_injective` proved and
the decode side present; the Rust codec is transcribed from it and the corpus
carries byte-exact expected encodings.

### Requirements

1. **Round-trip**, as above. The property test is the corpus; the proof is Lean's.
2. **Deterministic encoding** — one statement, one byte string. `Cbor.deterministic`
   with `deterministic_unique` is exactly this.
3. **Domain-separated** — statement bytes must not be readable as a term, a proof,
   a snapshot, or any other signed object. Tag the preimage.
4. **Total, both directions** — no panics on any input, adversarial included.
   Soundness does not depend on this; availability and the no-panic rule do.

### Rejected: verify-by-re-encoding

An earlier draft proposed keeping the decoder untrusted by re-encoding the
decoded candidate and verifying the signature over *that*. It is sound, and it
does confine decoder bugs to false rejections.

It was rejected because it makes every signature depend on the recipient
reproducing the signer's bytes exactly, so **any change to the encoder
invalidates every signature ever issued** — trading a bounded correctness
obligation for unbounded operational brittleness. Recorded here because it is an
appealing idea that someone will propose again.

### (b) The proof/replay codec — userspace

CBOR carrying raw syntax plus a rule tape, decoded and re-run through the same
rule methods a caller would use. No privileged path, so a wrong decode yields a
rejected or different theorem, never an unjustified one. Fuzz it for panics;
do not read it.

**Keeping (b) out of (a) is what keeps this small.** Only statements —
hypotheses and a conclusion — need the trusted codec. Proofs, which are far
larger and more complex, never do.

### Pin the theory in the signed preimage, from the first signature

A signed `|- P` is meaningful only relative to the signature it was proved
under: `base "foo"` in the signer's theory and in the recipient's are different
types that print identically. Without a theory identifier in the preimage, a
signature transfers between incompatible theories.

v0 declares no base types, so this is vacuous today — which is exactly why the
field must be there anyway. **Adding it later invalidates every signature ever
issued.** One `O256` of the theory's canonical description, in the preimage, now.

### Signed admission is this kernel's `#print axioms`

Admitting under a key accepts a theorem the session did not check — a different
trust mode from everything else here, and it should be visible:

- the trusted key set is an **explicit argument**, never ambient;
- the session records which keys were actually relied upon;
- `session.trusted_keys()` reports them.

A result that depended on no key is checked outright; one that depended on `K` is
checked *modulo* trusting `K`. That is the distinction `#print axioms` draws in
Lean, it costs almost nothing, and without it signing is a hole rather than a
feature.

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
| L7a | `kernel/src/statement.rs` | **TCB** | statement codec, **both directions**: deterministic, round-tripping, domain-separated, total. ~300 lines |
| L7b | `kernel/src/signed.rs` | **TCB** | sign / verify / admit over L7a's preimage; key set explicit; record reliance. ~120 lines |
| L7c | `codec/src/replay.rs` | user | proof tape encode + decode-then-recheck; fuzz for panics |
| L8 | `ffi/python/src/hol.rs` + `python/covalence/hol.py` | user | follow the `hash`/`sat`/`lrat` pattern exactly, including `.pyi` |
| L9 | `browser/src/hol.rs` + `packages/nucleus/src` | user | follow the `Repl` pattern; put `Session` on `window.nucleus` |
| L10 | `conformance/` + three drivers | test | §5 |

L1–L5 are unchanged from the eight-hour plan and keep their model assignment.
L7a and L7b join them in the TCB, taking the read budget to ≈ 1390 lines. That
is the cost of signing, and it is worth paying deliberately rather than
discovering.
L8 and L9 are mechanical against an existing pattern — good cheap-model lanes,
and their oracle is L10.

### Order

1. **L1–L5** to a Rust test proving `|- true` and one beta equality. Nothing else starts before this passes.
2. **L6 + L10** — printer and transcript together, since the transcript is what the printer is checked against.
3. **L8 and L9 in parallel** — both are one line per operation over a finished core.
4. **L7a** as soon as L1 lands — it depends only on the syntax, and it is TCB, so it wants reading time early rather than at the end. Its round-trip property test is written before it is.
5. **L7b** after L7a. **L7c** last; replay needs the rule methods finished to re-check through them.

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
