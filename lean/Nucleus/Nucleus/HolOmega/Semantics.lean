import Mathlib.Data.Set.Basic
import Nucleus.HolOmega.Env
import Nucleus.HolOmega.Typing

/-!
# Semantic scaffolding

Kind denotations, and the three ways one can give this language a meaning.
Only the third carries the soundness proof; the other two are recorded because
which one you pick determines what soundness can even say, and the choice is
easy to make silently.

## `DirectModel` — interpret the derivation

The interpretation functions take the *derivation* as an argument, so the
meaning of `Δ ⊢ A : K` may depend on how it was derived. This is the most
permissive interface, and the one closest to how a naive reading of the rules
works: recurse on the derivation tree, and interpret each rule.

It is also the one that does not quite work here. `Judgement` lands in `Prop`,
so it is proof-irrelevant: two derivations of the same judgement are equal, and
Lean will not let a `Type`-valued function distinguish them. So a `DirectModel`
can only be built by choosing data from a proof, which needs classical choice
and is exactly the dependency the soundness proof below avoids by going
relational. Recorded as the design point it is, not used.

## `ShapeModel` — interpret types as types

Each syntactic type denotes a Lean type (`ty : Ty Base → Type v`), and a
well-typed term denotes an *element of its own type's denotation*. This is
intrinsically-typed semantics: ill-typed terms are not merely unsound, they are
unwritable, and the type of the interpretation function states preservation
rather than proving it.

The cost is that every structural operation becomes a transport. Weakening a
context changes the type of the environment; substitution changes the type of
the result; and each of those needs an explicit coercion that has to be proved
coherent. For a language whose whole point is that terms are content-addressed
trees passed around freely, that is a lot of friction.

## `SoundModel` — one carrier, plus membership

Everything lands in a single untyped carrier `Ω`, with `carrier : Ty Base → Set Ω`
saying which elements inhabit which type, and closure laws saying the
operations respect it. Typing soundness then reads: a well-typed term denotes
*something*, and that something is in the carrier of its type.

This is the one used, for two reasons. Substitution and weakening are trivial,
since nothing changes type. And the carrier is defined on *raw* types, so open
contexts have a semantics before any well-kindedness judgement is imposed —
which matters because the later layers deliberately admit terms that are not
yet known to be well-formed. It lives in `Soundness.lean`, next to the proof
it exists for.
-/

universe u v

namespace Nucleus.HolOmega

/-- Kinds denote type-level functions over sets of the carrier. -/
def Kind.denote (Ω : Type v) : Kind → Type v
  | .star => Set Ω
  | .arr K L => Kind.denote Ω K → Kind.denote Ω L

/-- An assignment for the kind context. -/
def KindEnv (Ω : Type v) : KindCtx → Type v
  | [] => PUnit
  | K :: Δ => Kind.denote Ω K × KindEnv Ω Δ

/-- Interpretation that reads its content off a derivation. See the module
docstring: proof irrelevance makes this unusable without choice. -/
structure DirectModel (Base : Type u) (Ω : Type v) where
  ty : ∀ {Δ : KindCtx} {A : Ty Base} {K : Kind},
    Kinded Δ A K → KindEnv Ω Δ → Kind.denote Ω K
  tm : ∀ {Δ : KindCtx} {Γ : TmCtx Base} {t : Tm Base} {A : Ty Base},
    HasType Δ Γ t A → KindEnv Ω Δ → Env (fun _ => Ω) Γ → Ω

/-- Intrinsically-typed interpretation: a term denotes an element of its own
type's denotation, so preservation is stated by the types rather than proved.
See the module docstring for why the transports this forces are not worth it
here. -/
structure ShapeModel (Base : Type u) (Ω : Type v) where
  ty : Ty Base → Type v
  tm : ∀ {Δ : KindCtx} {Γ : TmCtx Base} {t : Tm Base} {A : Ty Base},
    HasType Δ Γ t A → KindEnv Ω Δ → Env ty Γ → ty A

end Nucleus.HolOmega
