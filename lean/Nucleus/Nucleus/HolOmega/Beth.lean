import Nucleus.HolOmega.PowerTower
import Nucleus.HolOmega.TotalSubtype

/-!
# The beth tower, and codes

`Block n` is tower level `n`, of size `ℶ_(ω * n)`: `Block 0` is countable, and
each next level is the whole power tower over the one below.

## Why a tower at all

Lean's universes are already a cumulative hierarchy and reach well past `ℶ_ω`,
so a model at any *fixed* rank needs none of this. But our ranks are terms, and
`Code : (n : Nat) → Type (n + 1)` is not writable — universe polymorphism
quantifies over level variables, not over `Nat`. So a rank has to be
interpreted by an ordinary function out of `Nat`, and that is what `Block` is.

## What a level buys

A level absorbs any *fixed* number of further powersets, because it is an
ω-union of them. So `Fits b` — "embeds into some level of block `b`" — is
closed under function spaces and subtypes, which is every type former HOL has.

What it does *not* absorb is a product indexed by the whole block: that would
need one more powerset than the block has, uniformly. Ranks are the
compensation. `Fits.pi` takes an index and fibres that each fit at `b` and
lands the product back at `b`, and the model spends one rank getting there.

## Codes

A `Code` is a nonempty bounded subset of a block, and `rank` is which block.
The level *inside* the block is bookkeeping that `rank` does not see — which is
exactly why rank survives `→` and `Sub` untouched, and only `∀` costs one.
-/

namespace Nucleus.HolOmega.Beth

/-- Tower level `n`, of size `ℶ_(ω * n)`. The same recursion as `PowerLevel`,
one scale up: the step is a whole power tower rather than a single
powerset. -/
abbrev Block := Level PowerTower Nat

namespace Block

/-- The tower is cumulative. -/
abbrev raise {m n : Nat} (h : m ≤ n) : Block m ↪ Block n := Level.raise h

/-- Every level is infinite, and countably so at the bottom. -/
abbrev ofNat (n : Nat) : Nat ↪ Block n := raise (Nat.zero_le n)

end Block

/-- `X` fits at block `b` when it embeds into one of the levels making that
block up. Since the block is an ω-union, "some level" is genuinely weaker than
"the block itself", and that gap is what the closure operations live in. -/
structure Fits (b : Nat) (X : Type) where
  level : Nat
  emb : X ↪ PowerLevel (Block b) level

namespace Fits

variable {b : Nat} {X Y : Type}

def ofEmbedding (e : X ↪ Y) (f : Fits b Y) : Fits b X := ⟨f.level, e.trans f.emb⟩

/-- Blocks are cumulative, so fitting is monotone in the block. -/
def mono (h : b ≤ b') (f : Fits b X) : Fits b' X :=
  ⟨f.level, f.emb.trans (Level.mapBase (Block.raise h) f.level)⟩

def atLevel (f : Fits b X) {m : Nat} (h : f.level ≤ m) :
    X ↪ PowerLevel (Block b) m :=
  f.emb.trans (Level.raise h)

/-- Anything fitting at a block fits *into* the next one, all at once. This is
what makes the fibres of a product uniformly bounded. -/
def toBlock (f : Fits b X) : X ↪ Block (b + 1) :=
  f.emb.trans (Tower.ofLevel f.level)

/-- A block absorbs function spaces: four more powersets, and it has ω of them
to spare. -/
def arrow (f : Fits b X) (g : Fits b Y) : Fits b (X → Y) :=
  ⟨max f.level g.level + 4,
    graphEmb (f.atLevel (le_max_left _ _)) (g.atLevel (le_max_right _ _))⟩

/-- A product whose index fits at `b` and whose fibres all embed into `b`
itself fits at `b`. The fibres have to be bounded *uniformly*, which is the
whole difference between this and a product indexed by the block. -/
def pi {I : Type} {G : I → Type} (f : Fits b I)
    (g : ∀ i, G i ↪ Block b) : Fits b ((i : I) → G i) :=
  let e : ((i : I) → G i) ↪ (I → Block b) :=
    ⟨fun h i => g i (h i),
      fun _ _ hh => funext fun i => (g i).injective (congrFun hh i)⟩
  ⟨f.level + 4, e.trans (graphEmb f.emb (Level.raise (Nat.zero_le f.level)))⟩

/-- A dependent sum whose index fits at `b` and whose fibres all embed into `b`
fits at `b`. Cheaper than the product: a pair costs three levels where a graph
costs four, and the index needs no bound relative to the fibres. -/
def sigma {I : Type} {G : I → Type} (f : Fits b I)
    (g : ∀ i, G i ↪ Block b) : Fits b ((i : I) × G i) :=
  let e : ((i : I) × G i) ↪ (I × Block b) :=
    ⟨fun p => (p.1, g p.1 p.2), by
      rintro ⟨i, x⟩ ⟨j, y⟩ hij
      simp only [Prod.mk.injEq] at hij
      obtain ⟨rfl, hij⟩ := hij
      exact congrArg _ ((g i).injective hij)⟩
  ⟨f.level + 3,
    e.trans ((f.emb.prodMap (Level.raise (Nat.zero_le f.level))).trans
      Pairing.pairEmb)⟩

end Fits

/-- A code: a nonempty bounded subset of a block. `rank` is which block; the
level inside it is bookkeeping the rank does not see. -/
structure Code where
  rank : Nat
  level : Nat
  carrier : Set (PowerLevel (Block rank) level)
  nonempty : carrier.Nonempty

/-- What a code denotes. -/
def El (A : Code) : Type := A.carrier

noncomputable instance (A : Code) : Inhabited (El A) :=
  Classical.inhabited_of_nonempty A.nonempty.to_subtype

namespace Code

theorem ext {A B : Code} (hr : A.rank = B.rank) (hl : A.level = B.level)
    (hc : HEq A.carrier B.carrier) : A = B := by
  obtain ⟨r, l, S, _⟩ := A
  obtain ⟨r', l', S', _⟩ := B
  cases hr
  cases hl
  cases hc
  rfl

def fits (A : Code) : Fits A.rank (El A) :=
  ⟨A.level, Function.Embedding.subtype _⟩

/-- Turn a type that fits at a block into a code for it. -/
noncomputable def of {b : Nat} {X : Type} (f : Fits b X) (hne : Nonempty X) :
    Code :=
  ⟨b, f.level, Set.range f.emb,
    ⟨f.emb (Classical.arbitrary X), Classical.arbitrary X, rfl⟩⟩

@[simp] theorem rank_of {b : Nat} {X : Type} (f : Fits b X) (hne : Nonempty X) :
    (of f hne).rank = b := rfl

/-- A code built from a type denotes that type. -/
noncomputable def ofEquiv {b : Nat} {X : Type} (f : Fits b X)
    (hne : Nonempty X) : El (of f hne) ≃ X :=
  (rangeEquiv f.emb).symm

end Code

/-! ## Codes below a rank

`allCode` quantifies over the codes of a bounded rank, so that collection has
to be bounded too. It is: a code of rank at most `r` is a bounded subset of
block `r` once raised, and all of those together are exactly block `r + 1`. -/

/-- The codes of rank at most `r`. -/
def CodeLE (r : Nat) := {A : Code // A.rank ≤ r}

namespace CodeLE

private def toBlock (r : Nat) (A : CodeLE r) : Nat × Block (r + 1) :=
  (A.val.rank,
    Tower.ofLevel (A.val.level + 1)
      (Level.mapBase (Block.raise A.property) (A.val.level + 1) A.val.carrier))

private theorem toBlock_injective (r : Nat) :
    Function.Injective (toBlock r) := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ h
  simp only [toBlock] at h
  obtain ⟨hrank, h⟩ := Prod.mk.injEq .. ▸ h
  obtain ⟨b, k, S, hS⟩ := A
  obtain ⟨b', k', S', hS'⟩ := B
  cases hrank
  injection h with hk h
  cases Nat.succ.inj hk
  have hSS : S = S' :=
    (Level.mapBase (Block.raise hA) (k + 1)).injective (eq_of_heq h)
  subst hSS
  rfl

/-- Codes of bounded rank are themselves bounded. -/
def fits (r : Nat) : Fits (r + 1) (CodeLE r) :=
  Fits.ofEmbedding ⟨toBlock r, toBlock_injective r⟩
    ⟨3, (Function.Embedding.prodMap (Block.ofNat (r + 1))
      (Function.Embedding.refl _)).trans Pairing.pairEmb⟩

end CodeLE

/-! ## The closures a HOL universe needs -/

private def boolEmb : Bool ↪ Block 0 where
  toFun b := (cond b 1 0 : Nat)
  inj' a b h := by
    have h : (cond a 1 0 : Nat) = cond b 1 0 := h
    cases a <;> cases b <;> simp_all

/-- Booleans need no tower at all, so they sit at the bottom rank. -/
noncomputable def boolCode : Code := Code.of (b := 0) ⟨0, boolEmb⟩ ⟨true⟩

noncomputable def boolEquiv : El boolCode ≃ Bool := Code.ofEquiv _ _

/-- Function spaces stay at the same rank: the block absorbs the four extra
powersets a graph costs. -/
noncomputable def arr (A B : Code) : Code :=
  Code.of ((A.fits.mono (le_max_left _ _)).arrow (B.fits.mono (le_max_right _ _)))
    ⟨fun _ => default⟩

noncomputable def arrEquiv (A B : Code) : El (arr A B) ≃ (El A → El B) :=
  Code.ofEquiv _ _

@[simp] theorem rank_arr (A B : Code) :
    (arr A B).rank = max A.rank B.rank := rfl

/-- Subtypes stay at the same rank too: they only shrink. -/
noncomputable def subCode (A : Code) (P : El A → Prop) : Code :=
  Code.of (A.fits.ofEmbedding (Function.Embedding.subtype _))
    (TotalSubtype.nonempty P)

noncomputable def subEquiv (A : Code) (P : El A → Prop) :
    El (subCode A P) ≃ TotalSubtype (El A) P := Code.ofEquiv _ _

@[simp] theorem rank_subCode (A : Code) (P : El A → Prop) :
    (subCode A P).rank = A.rank := rfl

/-- A product over an index fitting at `r`, with fibres of rank at most `s`,
costs exactly one rank. This is the only former that costs anything, and it is
what the whole tower exists for. -/
noncomputable def piCode {r s : Nat} {I : Type} (hI : Fits r I)
    (F : I → Code) (hF : ∀ X, (F X).rank ≤ s) : Code :=
  Code.of (b := max r s + 1)
    (Fits.pi (hI.mono (by omega))
      (fun X => ((F X).fits.mono (le_trans (hF X) (by omega))).toBlock))
    ⟨fun _ => default⟩

noncomputable def piEquiv {r s : Nat} {I : Type} (hI : Fits r I)
    (F : I → Code) (hF : ∀ X, (F X).rank ≤ s) :
    El (piCode hI F hF) ≃ ((X : I) → El (F X)) := Code.ofEquiv _ _

@[simp] theorem rank_piCode {r s : Nat} {I : Type} (hI : Fits r I)
    (F : I → Code) (hF : ∀ X, (F X).rank ≤ s) :
    (piCode hI F hF).rank = max r s + 1 := rfl

/-- A dependent sum over an index fitting at `r` with fibres of rank at most
`s`, at the same rank as the corresponding product. This is what an existential
type denotes: a pair of a witness and an element of the fibre over it. -/
noncomputable def sigmaCode {r s : Nat} {I : Type} (hI : Fits r I)
    (hne : Nonempty I) (F : I → Code) (hF : ∀ X, (F X).rank ≤ s) : Code :=
  Code.of (b := max r s + 1)
    (Fits.sigma (hI.mono (by omega))
      (fun X => ((F X).fits.mono (le_trans (hF X) (by omega))).toBlock))
    ⟨⟨Classical.arbitrary I, default⟩⟩

noncomputable def sigmaEquiv {r s : Nat} {I : Type} (hI : Fits r I)
    (hne : Nonempty I) (F : I → Code) (hF : ∀ X, (F X).rank ≤ s) :
    El (sigmaCode hI hne F hF) ≃ ((X : I) × El (F X)) := Code.ofEquiv _ _

@[simp] theorem rank_sigmaCode {r s : Nat} {I : Type} (hI : Fits r I)
    (hne : Nonempty I) (F : I → Code) (hF : ∀ X, (F X).rank ≤ s) :
    (sigmaCode hI hne F hF).rank = max r s + 1 := rfl

end Nucleus.HolOmega.Beth
