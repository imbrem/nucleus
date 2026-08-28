import Nucleus.Bytes
import Nucleus.Cas.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Blob expressions and the models that interpret them

A `BlobExpr` is syntax for a byte string built from content addresses, literal
octets, zero fill, concatenation and checked slicing.  It is interpreted in a
`Nucleus.Model`: a **total, injective** function `σ : O256 → Bytes` that
*extends* a given `Nucleus.Cas`, so `σ h = b` for every checked pair `(h, b)`
the store holds.  `BlobExpr.denote` is then an ordinary partial function of the
model, not a relation over an unknown fibre.

## Why injectivity is part of the definition

`σ h` is *the* blob that `h` names, and distinct addresses cannot name one blob:
`Nucleus.Name.name` is a function, so `name b` determines a single address for
`b`.  Injectivity is therefore not an extra assumption bolted onto the semantics
but a restatement of what content addressing means, and it is load-bearing —
it is the whole of the digest-disequality rule, see `Model.sigma_ne`.

Requiring it costs nothing.  The part of `σ` the store pins is automatically
injective for exactly the same reason: no blob is pinned to two addresses.  What
*can* fail is one address pinned to two different blobs, which is precisely a
collision; and a finite injective partial map always extends to a total
injection, because there are infinitely many byte strings to spend on the
addresses the store says nothing about.  `Cas.nonempty_model_iff_collisionFree`
is that argument, and `Cas.blobBound` is the room it spends.

## The standing assumption

Every refutation downstream of this file is sound **relative to the existence
of at least one model**, and `Cas.nonempty_model_iff_collisionFree` says that
existence is *exactly* collision-freedom.  Under a collision there are no
models, every proposition is vacuously valid, and the calculus is unsound.  The
hypothesis is stated here once, and the refutation rules in `Nucleus.Blob.Eq`
carry it as a single section variable; no individual rule restates it.

## A considered strengthening: the section property

`Model.IsSection` asks for `name (σ h) = h`, which says `σ h` really *is* a blob
named `h`.  It implies injectivity — see `Model.injective_of_isSection` — and it
would buy the two range-fact theorems at the end of `Nucleus.Blob.Eq`, which
without it have to assume it outright: an unpinned address is otherwise sent
somewhere the naming function knows nothing about, so a bare naming equation
`name whole = h` says nothing at all about `σ h`.

It is deliberately *not* adopted.  Existence would then be tied to `name` being
surjective, since every address would have to be named by some blob, and
`Cas.nonempty_model_iff_collisionFree` would stop being an equivalence — the
standing assumption would no longer be collision-freedom, which is the one
hypothesis the rest of the system already tracks.  Injectivity is everything the
calculus needs and it is free.

## A digest is always defined

`blake3 h` denotes `σ h`, whatever the store knows: there is no empty fibre and
no "this digest names nothing" case.  What varies from model to model is *which*
byte string, which is why `BlobExpr.length?` still answers `none` at a digest —
the value is certainly defined, its length is not determined.  Undefinedness has
exactly two sources: a slice that runs out of range, and a concatenation with an
undefined side.

Two observations approximate the denotation from inside, and both are partial
for a reason.  `BlobExpr.length?` answers `some n` only after bounds-checking
every slice against its subject, so `some n` certifies that the expression is
defined in *every* model with a value of `n` octets; that certificate is what
makes disagreeing lengths a sound disequality.  `BlobExpr.eval?` answers
`some v` only when the expression denotes `v` in every model.  A digest carries
neither, so both are `none` there — `none` means "unknown", never zero and
never an error.

Out-of-range slices are undefined rather than clamped, uniformly in `denote`,
`length?` and `eval?`; see `Nucleus.Bytes.slice?`.  And `blake3 hash` is the
blob *named* by `hash`, never the 32 octets of the digest itself, which are
`bytes hash.encode`.
-/

namespace Nucleus

/-!
## Models

A model is the semantic parameter of the whole blob theory.  It is not part of
any runtime representation: nothing constructs one outside this file, and the
Rust side has no counterpart.
-/

/--
A total, injective reading of content addresses as byte strings that agrees
with `cas`.

`sigma` is total, so *every* address denotes a byte string; `injective` says
distinct addresses name distinct blobs, which is what content addressing means
and what licenses digest disequality; `extendsCas` pins exactly the addresses
the store has checked.  An address the store says nothing about is free to vary
from model to model, which is precisely what makes an unknown blob unknown
rather than absent.
-/
structure Model [Name Bytes O256] (cas : Cas) where
  /-- The total interpretation of content addresses. -/
  sigma : O256 → Bytes
  /-- Distinct addresses name distinct blobs.  A name is a function, so no blob
  answers to two addresses. -/
  injective : Function.Injective sigma
  /-- Every checked pair in the store is respected. -/
  extendsCas : ∀ pair ∈ cas, sigma pair.hash = pair.blob

namespace Cas

variable [Name Bytes O256]

/--
The greatest length of any blob the store pins, and `0` when it pins none.

This exists only to give the canonical model somewhere safe to send the
addresses the store says nothing about: a run of more than `blobBound` zero
octets cannot be a stored blob, so the two halves of that model never collide.
-/
def blobBound (cas : Cas) : Nat := cas.pairs.sup fun pair ↦ pair.blob.length

/-- Every blob the store holds fits inside `Cas.blobBound`. -/
theorem length_le_blobBound {cas : Cas} {hash : O256} {blob : Bytes}
    (found : cas.Lookup hash blob) : blob.length ≤ cas.blobBound := by
  obtain ⟨pair, member, _, blobEqual⟩ := found
  rw [← blobEqual]
  exact Finset.le_sup (f := fun pair : CasPair ↦ pair.blob.length) (mem_iff_mem_pairs.mp member)

/--
A collision-free store has a model.

The model reads a stored address back to its blob and sends every other address
to a run of zero octets one longer than `Cas.blobBound` plus the address itself,
read as a number.  Both halves are injective and they cannot meet: the stored
half is injective because `Nucleus.Name.name` is a function, the fresh half
because the length records the address, and no stored blob is that long.
`Cas.lookup_functional` is what makes the stored half a definition rather than a
choice: collision-freedom is exactly the statement that the relational lookup of
`Nucleus.Cas` is a partial function.
-/
theorem nonempty_model_of_collisionFree {cas : Cas} (collisionFree : cas.CollisionFree) :
    Nonempty (Model cas) := by
  classical
  obtain ⟨sigma, stored, fresh⟩ :
      ∃ sigma : O256 → Bytes,
        (∀ hash blob, cas.Lookup hash blob → sigma hash = blob) ∧
          ∀ hash, ¬ (∃ blob, cas.Lookup hash blob) →
            sigma hash = Bytes.replicate (cas.blobBound + 1 + hash.toNat) 0 := by
    refine ⟨fun hash ↦ if found : ∃ blob, cas.Lookup hash blob then found.choose
      else Bytes.replicate (cas.blobBound + 1 + hash.toNat) 0, ?_, ?_⟩
    · intro hash blob found
      have known : ∃ other, cas.Lookup hash other := ⟨blob, found⟩
      change (if found : ∃ other, cas.Lookup hash other then found.choose
        else Bytes.replicate (cas.blobBound + 1 + hash.toNat) 0) = blob
      rw [dif_pos known]
      exact lookup_functional collisionFree known.choose_spec found
    · intro hash missing
      change (if found : ∃ other, cas.Lookup hash other then found.choose
        else Bytes.replicate (cas.blobBound + 1 + hash.toNat) 0) = _
      rw [dif_neg missing]
  refine ⟨⟨sigma, ?_, ?_⟩⟩
  · intro left right equal
    by_cases leftFound : ∃ blob, cas.Lookup left blob
    · obtain ⟨leftBlob, leftLookup⟩ := leftFound
      by_cases rightFound : ∃ blob, cas.Lookup right blob
      · obtain ⟨rightBlob, rightLookup⟩ := rightFound
        rw [stored left leftBlob leftLookup, stored right rightBlob rightLookup] at equal
        rw [← lookup_valid leftLookup, ← lookup_valid rightLookup, equal]
      · have bounded : leftBlob.length ≤ cas.blobBound := length_le_blobBound leftLookup
        rw [stored left leftBlob leftLookup, fresh right rightFound] at equal
        have lengths := congrArg Bytes.length equal
        rw [Bytes.length_replicate] at lengths
        exact absurd lengths (by omega)
    · by_cases rightFound : ∃ blob, cas.Lookup right blob
      · obtain ⟨rightBlob, rightLookup⟩ := rightFound
        have bounded : rightBlob.length ≤ cas.blobBound := length_le_blobBound rightLookup
        rw [fresh left leftFound, stored right rightBlob rightLookup] at equal
        have lengths := congrArg Bytes.length equal
        rw [Bytes.length_replicate] at lengths
        exact absurd lengths (by omega)
      · rw [fresh left leftFound, fresh right rightFound] at equal
        have lengths := congrArg Bytes.length equal
        rw [Bytes.length_replicate, Bytes.length_replicate] at lengths
        exact BitVec.toNat_inj.mp (by omega)
  · intro pair member
    exact stored pair.hash pair.blob (lookup_of_mem member)

/-- A store with a model is collision-free: `sigma` is a function, so the two
sides of a collision would have to be the same blob. -/
theorem collisionFree_of_nonempty_model {cas : Cas} (model : Nonempty (Model cas)) :
    cas.CollisionFree := by
  obtain ⟨model⟩ := model
  rw [collisionFree_iff_pairwise]
  intro left right leftMember rightMember hashEqual
  rw [← model.extendsCas left leftMember, ← model.extendsCas right rightMember, hashEqual]

/--
THE STANDING ASSUMPTION: a store is interpretable exactly when it is
collision-free.

Everything the equality calculus refutes is refuted in a model, so every
refutation rule is sound only under this hypothesis.  Under a collision the
right-hand side fails, there are no models, and `BlobEq.Valid` holds vacuously
of every equation — which is unsoundness, not a curiosity.
-/
theorem nonempty_model_iff_collisionFree (cas : Cas) :
    Nonempty (Model cas) ↔ cas.CollisionFree :=
  ⟨collisionFree_of_nonempty_model, nonempty_model_of_collisionFree⟩

end Cas

namespace Model

variable [Name Bytes O256] {cas : Cas}

/--
Distinct content addresses denote distinct blobs, in *every* model.

This is the fact that licenses digest disequality, and the whole of it is the
`injective` field: `sigma` picks *the* blob an address names, and a name
determines its blob, so two addresses that differ cannot be sent to one blob.
No separating model has to be constructed, because the separation is uniform:
the two sides differ *everywhere* rather than merely somewhere.  Collision
freedom is needed only to have a model at all; it is the standing assumption of
the calculus, not an extra premise of this rule.
-/
theorem sigma_ne (model : Model cas) {left right : O256} (different : left ≠ right) :
    model.sigma left ≠ model.sigma right :=
  model.injective.ne different

/--
The considered strengthening: `sigma` returns a blob actually *named* by its
argument.

Recorded, and deliberately not adopted; the file header says why, and
`Nucleus.BlobEq.valid_ofCasRange` and `Nucleus.CasRange.of_valid` are what it
would buy.
-/
def IsSection (model : Model cas) : Prop := ∀ hash, Name.name (model.sigma hash) = hash

/-- The section property is strictly stronger than injectivity: it *derives* the
`injective` field rather than assuming it. -/
theorem injective_of_isSection {model : Model cas} (isSection : model.IsSection) :
    Function.Injective model.sigma := by
  intro left right equal
  rw [← isSection left, ← isSection right, equal]

end Model

/--
A half-open sub-range of a byte string.

`stop` is exclusive, and `none` runs to the end of the subject, which is how a
span pins a whole byte string without naming its length.  There is deliberately
no `start ≤ stop` field: the Rust `BlobSpan::new` rejects a backwards span but
`BlobRange::span()` bypasses that guard, so the laxer type is the faithful
mirror.  Both are undefined.
-/
@[ext]
structure BlobSpan where
  start : Nat
  stop : Option Nat
  deriving DecidableEq

namespace BlobSpan

/-- The span selecting an entire byte string. -/
def whole : BlobSpan := ⟨0, none⟩

@[simp] theorem whole_start : whole.start = 0 := rfl

@[simp] theorem whole_stop : whole.stop = none := rfl

end BlobSpan

/--
An expression denoting a byte string.

Variants are named for the hash *algorithm* rather than for "the CAS", so a
`sha256` sibling can be added without any arm claiming to be the only digest.
`cat` is binary; an n-ary generalisation is deliberately deferred, since a
nested inductive would force `List.Forall₂` motives on every clause below.
-/
inductive BlobExpr where
  /-- The blob whose unkeyed BLAKE3 content address is `hash` — not the 32
  octets of the digest, which are `BlobExpr.bytes hash.encode`. -/
  | blake3 (hash : O256)
  /-- A checked sub-range of another expression.  Out of range is undefined. -/
  | slice (blob : BlobExpr) (span : BlobSpan)
  /-- The concatenation of two expressions, in order. -/
  | cat (left right : BlobExpr)
  /-- A literal byte string. -/
  | bytes (value : Bytes)
  /-- `count` zero octets. -/
  | zero (count : Nat)
  deriving DecidableEq

namespace BlobExpr

/--
Slice an expression, normalising the whole-byte-string span away.

`sliceOf blob BlobSpan.whole = blob` is sound because every byte string is its
own whole slice, so the two denote the same thing in every model.  It earns its
`if` on the Rust side, where a whole-blob range and a bare hash would otherwise
reify to different expressions for the same claim.
-/
def sliceOf (blob : BlobExpr) (span : BlobSpan) : BlobExpr :=
  if span = BlobSpan.whole then blob else .slice blob span

@[simp] theorem sliceOf_whole (blob : BlobExpr) : blob.sliceOf BlobSpan.whole = blob :=
  if_pos rfl

theorem sliceOf_of_ne {blob : BlobExpr} {span : BlobSpan} (different : span ≠ BlobSpan.whole) :
    blob.sliceOf span = .slice blob span :=
  if_neg different

/-- Whether this expression is a bare content address.  The decision procedure
reads it to reach the digest-separation branch. -/
def isDigest : BlobExpr → Bool
  | .blake3 _ => true
  | _ => false

theorem isDigest_iff {expr : BlobExpr} : expr.isDigest = true ↔ ∃ hash, expr = .blake3 hash := by
  cases expr with
  | blake3 hash => exact ⟨fun _ ↦ ⟨hash, rfl⟩, fun _ ↦ rfl⟩
  | _ => exact ⟨fun absurdity ↦ by simp [isDigest] at absurdity, fun ⟨_, wrong⟩ ↦ by
      simp at wrong⟩

/--
The byte string this expression denotes in `model`.

`blake3 hash` is always defined: it is `model.sigma hash`, and no clause can
fail there.  `none` therefore means one of exactly two things — a slice ran out
of range, or a concatenation had an undefined side — and it propagates outwards
through `cat` and `slice` rather than escaping.
-/
def denote [Name Bytes O256] {cas : Cas} : BlobExpr → Model cas → Option Bytes
  | .blake3 hash, model => some (model.sigma hash)
  | .slice blob span, model =>
      (blob.denote model).bind fun subject ↦ subject.slice? span.start span.stop
  | .cat left right, model =>
      (left.denote model).bind fun head ↦ (right.denote model).map fun tail ↦ head.append tail
  | .bytes value, _ => some value
  | .zero count, _ => some (Bytes.replicate count 0)

section Denotation

variable [Name Bytes O256] {cas : Cas}

@[simp] theorem denote_blake3 (hash : O256) (model : Model cas) :
    (blake3 hash).denote model = some (model.sigma hash) := rfl

@[simp] theorem denote_bytes (value : Bytes) (model : Model cas) :
    (bytes value).denote model = some value := rfl

@[simp] theorem denote_zero (count : Nat) (model : Model cas) :
    (zero count).denote model = some (Bytes.replicate count 0) := rfl

theorem denote_cat (left right : BlobExpr) (model : Model cas) :
    (cat left right).denote model =
      (left.denote model).bind fun head ↦
        (right.denote model).map fun tail ↦ head.append tail := rfl

theorem denote_slice (blob : BlobExpr) (span : BlobSpan) (model : Model cas) :
    (slice blob span).denote model =
      (blob.denote model).bind fun subject ↦ subject.slice? span.start span.stop := rfl

/-- A digest is defined in every model.  This is the clause that changed: there
is no empty fibre and no unresolvable address. -/
theorem denote_blake3_isSome (hash : O256) (model : Model cas) :
    ((blake3 hash).denote model).isSome := rfl

/--
Distinct digests denote *different* byte strings, in every model.

Two lines from `Model.injective`, with no model construction anywhere: this is
the whole justification of the digest-disequality branch of
`Nucleus.BlobEq.decide?`.
-/
theorem denote_blake3_ne (model : Model cas) {left right : O256} (different : left ≠ right) :
    (blake3 left).denote model ≠ (blake3 right).denote model := fun equal ↦
  model.sigma_ne different (Option.some.inj equal)

/-- Normalising the whole-byte-string span away preserves the denotation. -/
@[simp] theorem denote_sliceOf (blob : BlobExpr) (span : BlobSpan) (model : Model cas) :
    (blob.sliceOf span).denote model = (slice blob span).denote model := by
  by_cases entire : span = BlobSpan.whole
  · subst entire
    rw [sliceOf_whole, denote_slice]
    cases denoted : blob.denote model with
    | none => rfl
    | some subject => simp
  · rw [sliceOf_of_ne entire]

/-- A store pins the addresses it holds: every model reads a checked pair back
to its own blob. -/
theorem denote_blake3_of_mem {pair : CasPair} {model : Model cas} (member : pair ∈ cas) :
    (blake3 pair.hash).denote model = some pair.blob := by
  rw [denote_blake3, model.extendsCas pair member]

/--
An out-of-range slice is undefined, rather than clamped or truncated.  A
truncating slice would make false facts derivable, so "out of range" means
"undefined" uniformly in `denote`, `length?` and `eval?`.
-/
theorem denote_slice_eq_none {blob : BlobExpr} {span : BlobSpan} {model : Model cas}
    (unbounded : ∀ subject : Bytes, blob.denote model = some subject →
      subject.slice? span.start span.stop = none) :
    (slice blob span).denote model = none := by
  rw [denote_slice]
  cases denoted : blob.denote model with
  | none => rfl
  | some subject => rw [Option.bind_some, unbounded subject denoted]

end Denotation

/--
The length of the byte string this expression denotes, when it is structurally
determined.

`some n` is a definedness certificate: in *every* model the expression is
defined, with a value of `n` octets.  That is what makes a length disagreement
a sound disequality, and it is why the `slice` clause bounds-checks against its
subject rather than reporting a bare span width — two out-of-range slices of
differing widths are both undefined, so they are equal.

`none` is neither an error nor zero.  It means "no answer here": a digest is
always defined but its length varies from model to model, and an out-of-range
slice is not defined at all.  Both collapse to `none`, and the SQL-null reading
of that `none` is what `cmpLength?` enforces.  The Rust counterpart is
additionally partial, answering `none` once a sum leaves `u64`.
-/
def length? : BlobExpr → Option Nat
  | .blake3 _ => none
  | .slice blob span =>
      blob.length?.bind fun subject ↦
        if span.start ≤ span.stop.getD subject ∧ span.stop.getD subject ≤ subject then
          some (span.stop.getD subject - span.start)
        else
          none
  | .cat left right =>
      left.length?.bind fun leftLength ↦
        right.length?.bind fun rightLength ↦ some (leftLength + rightLength)
  | .bytes value => some value.length
  | .zero count => some count

@[simp] theorem length?_blake3 (hash : O256) : (blake3 hash).length? = none := rfl

@[simp] theorem length?_bytes (value : Bytes) : (bytes value).length? = some value.length := rfl

@[simp] theorem length?_zero (count : Nat) : (zero count).length? = some count := rfl

theorem length?_cat (left right : BlobExpr) :
    (cat left right).length? =
      left.length?.bind fun leftLength ↦
        right.length?.bind fun rightLength ↦ some (leftLength + rightLength) := rfl

theorem length?_slice (blob : BlobExpr) (span : BlobSpan) :
    (slice blob span).length? =
      blob.length?.bind fun subject ↦
        if span.start ≤ span.stop.getD subject ∧ span.stop.getD subject ≤ subject then
          some (span.stop.getD subject - span.start)
        else
          none := rfl

/--
Compare two expressions' lengths, or `none` when either length is unknown.

This is the single place two lengths are ever compared, and the `bind` is the
point of it: an unknown length must agree with nothing, not even with itself,
so that no cancellation or disequality rule can be satisfied by two expressions
that merely both hide their lengths.  Comparing the two `Option`s directly would
make `none = none` an agreement, which is the SQL-null bug.
-/
def cmpLength? (left right : BlobExpr) : Option Ordering :=
  left.length?.bind fun leftLength ↦ right.length?.map fun rightLength ↦
    compare leftLength rightLength

theorem cmpLength?_of_length? {left right : BlobExpr} {leftLength rightLength : Nat}
    (leftKnown : left.length? = some leftLength)
    (rightKnown : right.length? = some rightLength) :
    left.cmpLength? right = some (compare leftLength rightLength) := by
  simp [cmpLength?, leftKnown, rightKnown]

theorem cmpLength?_of_unknown_left {left : BlobExpr} (right : BlobExpr)
    (unknown : left.length? = none) : left.cmpLength? right = none := by
  simp [cmpLength?, unknown]

theorem cmpLength?_of_unknown_right (left : BlobExpr) {right : BlobExpr}
    (unknown : right.length? = none) : left.cmpLength? right = none := by
  cases known : left.length? <;> simp [cmpLength?, known, unknown]

/-- An unknown length does not even agree with itself. -/
theorem cmpLength?_self_of_unknown {expr : BlobExpr} (unknown : expr.length? = none) :
    expr.cmpLength? expr = none :=
  cmpLength?_of_unknown_left expr unknown

/--
The converse of `cmpLength?_of_length?` at `eq`: an agreeing comparison is
exactly a pair of *known*, equal lengths.

This is the bridge from the shape the cancellation rules test — one `Ordering`
answer — to the shape their proofs consume, and it is where the SQL-null reading
pays off: because `cmpLength?` short-circuits on an unknown length, `some .eq`
can only have come from two `some` lengths, so no rule firing on `some .eq` can
be satisfied by two expressions that merely both hide their lengths.
-/
theorem exists_length?_of_cmpLength?_eq {left right : BlobExpr}
    (agree : left.cmpLength? right = some .eq) :
    ∃ count, left.length? = some count ∧ right.length? = some count := by
  rcases Option.eq_none_or_eq_some left.length? with leftNone | ⟨leftLength, leftKnown⟩
  · rw [cmpLength?_of_unknown_left right leftNone] at agree
    simp at agree
  · rcases Option.eq_none_or_eq_some right.length? with rightNone | ⟨rightLength, rightKnown⟩
    · rw [cmpLength?_of_unknown_right left rightNone] at agree
      simp at agree
    · rw [cmpLength?_of_length? leftKnown rightKnown] at agree
      refine ⟨leftLength, leftKnown, ?_⟩
      rw [Nat.compare_eq_eq.mp (Option.some.inj agree)]
      exact rightKnown

/--
The byte string this expression denotes, when one byte string answers in every
model.

`none` for every `blake3` node, because the model is free there, and `none` for
an out-of-range slice, because such an expression is undefined.  The Rust
counterpart is additionally partial, refusing to materialise past a byte budget;
a smaller budget only ever loses answers, never adds wrong ones.
-/
def eval? : BlobExpr → Option Bytes
  | .blake3 _ => none
  | .slice blob span => blob.eval?.bind fun subject ↦ subject.slice? span.start span.stop
  | .cat left right =>
      left.eval?.bind fun head ↦ right.eval?.map fun tail ↦ head.append tail
  | .bytes value => some value
  | .zero count => some (Bytes.replicate count 0)

@[simp] theorem eval?_blake3 (hash : O256) : (blake3 hash).eval? = none := rfl

@[simp] theorem eval?_bytes (value : Bytes) : (bytes value).eval? = some value := rfl

@[simp] theorem eval?_zero (count : Nat) :
    (zero count).eval? = some (Bytes.replicate count 0) := rfl

theorem eval?_cat (left right : BlobExpr) :
    (cat left right).eval? =
      left.eval?.bind fun head ↦ right.eval?.map fun tail ↦ head.append tail := rfl

theorem eval?_slice (blob : BlobExpr) (span : BlobSpan) :
    (slice blob span).eval? =
      blob.eval?.bind fun subject ↦ subject.slice? span.start span.stop := rfl

/--
A canonical family of undefined expressions: a slice starting one octet past the
end of the empty byte string, of naive width `width`.

The family is indexed by width on purpose.  The *span* widths differ, yet every
member is undefined in every model and so they are all equal to each other; that
is exactly why `length?` bounds-checks a slice against its subject instead of
reporting the bare span width, and why an unchecked width would be an unsound
source of disequalities.
-/
def voidSlice (width : Nat) : BlobExpr :=
  .slice (.bytes Bytes.empty) ⟨1, some (1 + width)⟩

@[simp] theorem length?_voidSlice (width : Nat) : (voidSlice width).length? = none := by
  rw [voidSlice, length?_slice]
  simp only [length?_bytes, Option.bind_some, Bytes.length_empty]
  rw [if_neg]
  omega

@[simp] theorem eval?_voidSlice (width : Nat) : (voidSlice width).eval? = none := by
  rw [voidSlice, eval?_slice]
  simp only [eval?_bytes, Option.bind_some]
  exact Bytes.slice?_eq_none (by simp only [Option.getD_some, Bytes.length_empty]; omega)

@[simp] theorem denote_voidSlice [Name Bytes O256] {cas : Cas} (width : Nat) (model : Model cas) :
    (voidSlice width).denote model = none := by
  rw [voidSlice, denote_slice, denote_bytes, Option.bind_some]
  exact Bytes.slice?_eq_none (by simp only [Option.getD_some, Bytes.length_empty]; omega)

section Soundness

variable [Name Bytes O256] {cas : Cas}

/--
A known length is a definedness certificate valid in every model.

`some n` says the expression is defined everywhere with an `n`-octet value, and
both halves are load-bearing: the value is what makes a length disagreement a
sound disequality, and the definedness is what makes cancellation possible at
all, since the rule needs a witness on the other side of the concatenation.
-/
theorem length?_sound : ∀ {expr : BlobExpr} {count : Nat},
    expr.length? = some count → ∀ model : Model cas,
      ∃ blob, expr.denote model = some blob ∧ blob.length = count := by
  intro expr
  induction expr with
  | blake3 hash =>
      intro count known
      simp at known
  | slice subject span subjectSound =>
      intro count known model
      rw [length?_slice] at known
      cases subjectKnown : subject.length? with
      | none => rw [subjectKnown] at known; simp at known
      | some subjectLength =>
          rw [subjectKnown, Option.bind_some] at known
          split at known
          · rename_i bounded
            obtain ⟨whole, wholeDenote, wholeLength⟩ := subjectSound subjectKnown model
            have lower : span.start ≤ span.stop.getD whole.length := by
              rw [wholeLength]; exact bounded.1
            have upper : span.stop.getD whole.length ≤ whole.length := by
              rw [wholeLength]; exact bounded.2
            have sliced := Bytes.slice?_of_le lower upper
            refine ⟨Bytes.ofList ((whole.toList.drop span.start).take
              (span.stop.getD whole.length - span.start)), ?_, ?_⟩
            · rw [denote_slice, wholeDenote, Option.bind_some, sliced]
            · rw [Bytes.length_of_slice? sliced, wholeLength, ← Option.some.inj known]
          · simp at known
  | cat left right leftSound rightSound =>
      intro count known model
      rw [length?_cat] at known
      cases leftKnown : left.length? with
      | none => rw [leftKnown] at known; simp at known
      | some leftLength =>
          cases rightKnown : right.length? with
          | none => rw [leftKnown, rightKnown] at known; simp at known
          | some rightLength =>
              rw [leftKnown, rightKnown] at known
              simp only [Option.bind_some] at known
              obtain ⟨head, headDenote, headLength⟩ := leftSound leftKnown model
              obtain ⟨tail, tailDenote, tailLength⟩ := rightSound rightKnown model
              refine ⟨head.append tail, ?_, ?_⟩
              · rw [denote_cat, headDenote, Option.bind_some, tailDenote, Option.map_some]
              · rw [Bytes.length_append, headLength, tailLength, ← Option.some.inj known]
  | bytes value =>
      intro count known model
      rw [length?_bytes] at known
      exact ⟨value, rfl, Option.some.inj known⟩
  | zero repeats =>
      intro count known model
      rw [length?_zero] at known
      exact ⟨_, rfl, by rw [Bytes.length_replicate, Option.some.inj known]⟩

/-- A known length is the length of the denotation in any given model. -/
theorem length_of_length? {expr : BlobExpr} {count : Nat} {blob : Bytes} {model : Model cas}
    (known : expr.length? = some count) (denoted : expr.denote model = some blob) :
    blob.length = count := by
  obtain ⟨other, otherDenote, otherLength⟩ := length?_sound known model
  rw [Option.some.inj (denoted.symm.trans otherDenote)]
  exact otherLength

/-- A known length certifies definedness in any given model. -/
theorem denote_isSome_of_length? {expr : BlobExpr} {count : Nat} (known : expr.length? = some count)
    (model : Model cas) : ∃ blob, expr.denote model = some blob := by
  obtain ⟨blob, denoted, _⟩ := length?_sound known model
  exact ⟨blob, denoted⟩

/-- An expression undefined in even one model has no known length.  The
contrapositive of `denote_isSome_of_length?`, and the reason two undefined
expressions never compare. -/
theorem length?_eq_none_of_denote_eq_none {expr : BlobExpr} {model : Model cas}
    (undefined : expr.denote model = none) : expr.length? = none := by
  cases known : expr.length? with
  | none => rfl
  | some count =>
      obtain ⟨blob, denoted⟩ := denote_isSome_of_length? known model
      rw [undefined] at denoted
      simp at denoted

/--
Evaluation pins the denotation in every model.

`eval? = some value` is therefore strictly stronger than a length certificate:
it settles equality in *both* directions, which is what lets the decision
procedure answer `some false` from two successful evaluations that disagree.
-/
theorem eval?_sound : ∀ {expr : BlobExpr} {value : Bytes},
    expr.eval? = some value → ∀ model : Model cas, expr.denote model = some value := by
  intro expr
  induction expr with
  | blake3 hash =>
      intro value evaluated
      simp at evaluated
  | slice subject span subjectSound =>
      intro value evaluated model
      rw [eval?_slice] at evaluated
      cases subjectEval : subject.eval? with
      | none => rw [subjectEval] at evaluated; simp at evaluated
      | some whole =>
          rw [subjectEval, Option.bind_some] at evaluated
          rw [denote_slice, subjectSound subjectEval model, Option.bind_some, evaluated]
  | cat left right leftSound rightSound =>
      intro value evaluated model
      rw [eval?_cat] at evaluated
      cases leftEval : left.eval? with
      | none => rw [leftEval] at evaluated; simp at evaluated
      | some head =>
          cases rightEval : right.eval? with
          | none => rw [leftEval, rightEval] at evaluated; simp at evaluated
          | some tail =>
              rw [leftEval, rightEval] at evaluated
              simp only [Option.bind_some, Option.map_some] at evaluated
              rw [denote_cat, leftSound leftEval model, Option.bind_some,
                rightSound rightEval model, Option.map_some, evaluated]
  | bytes literal =>
      intro value evaluated model
      rw [eval?_bytes] at evaluated
      rw [denote_bytes, evaluated]
  | zero repeats =>
      intro value evaluated model
      rw [eval?_zero] at evaluated
      rw [denote_zero, evaluated]

end Soundness

end BlobExpr

end Nucleus
