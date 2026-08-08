import Mathlib
import Nucleus.HolOmega.RankedKinds
import Nucleus.HolOmega.Semantics

universe u v

namespace Nucleus.HolOmega.FullRanking

open Kernel RankedKinds

/-- Experimental formation calculus in which application joins independently
ranked operands at their maximum.  Quantifier `+2` remains unchanged and is
orthogonal to this experiment. -/
inductive Kinded {Base : Type u} : KindCtx → Ty Base → RKind → Prop
  | base : Kinded Δ (.base c) ⟨.star, 0⟩
  | tyVar : Δ[n]? = some RK → Kinded Δ (.tyVar n) RK
  | tyLam : Kinded (RK :: Δ) A ⟨L, r⟩ →
      Kinded Δ (.tyLam RK A) ⟨.arr RK.kind L, max RK.rank r⟩
  | tyApp : Kinded Δ F ⟨.arr K L, r₁⟩ → Kinded Δ X ⟨K, r₂⟩ →
      Kinded Δ (.tyApp F X) ⟨L, max r₁ r₂⟩
  | tyAll : Kinded (RK :: Δ) A ⟨.star, s⟩ →
      Kinded Δ (.tyAll RK A) ⟨.star, max RK.rank s + 2⟩
  | tyBool : Kinded Δ .tyBool ⟨.star, 0⟩
  | tyArr : Kinded Δ A ⟨.star, r₁⟩ → Kinded Δ B ⟨.star, r₂⟩ →
      Kinded Δ (.tyArr A B) ⟨.star, max r₁ r₂⟩
  | tySub : Kinded Δ A ⟨.star, r⟩ → HolOmega.HasType Δ [A] p .tyBool →
      Kinded Δ (.tySub A p) ⟨.star, r⟩
  | subsume : Kinded Δ A ⟨.star, r⟩ → r ≤ s → Kinded Δ A ⟨.star, s⟩

structure BaseSemantics (Base : Type u) (U : Universe.{v}) where
  code : Base → U.Code
  rank_code : ∀ c, U.rank (code c) = 0

/-!
The earlier `CoherentVal` slice prototype is not conformance evidence.  Its
extension law excludes the identity function: extending a low-rank identity
acts as `extend ∘ restrict` on a genuinely new higher-rank argument.  Whole
functions with a tail-quantified stability predicate are the correct carrier.
-/

/-- A whole value is available from rank `r` onward.  At arrow kinds it must
preserve every later slice, which makes the predicate monotone at all kinds. -/
def StableAt (U : Universe.{v}) (r : Nat) : (K : Kind) → WholeVal U K → Prop
  | .star, c => U.rank c ≤ r
  | .arr K L, f => ∀ s, r ≤ s → ∀ x, StableAt U s K x → StableAt U s L (f x)

theorem StableAt.mono (hrs : r ≤ s) :
    ∀ {K : Kind} {x : WholeVal U K}, StableAt U r K x → StableAt U s K x := by
  intro K x hx
  cases K with
  | star => exact hx.trans hrs
  | arr K L =>
    intro t hst y hy
    exact hx t (hrs.trans hst) y hy

def RankedVal (U : Universe.{v}) (r : Nat) (K : Kind) :=
  {x : WholeVal U K // StableAt U r K x}

def RankedVal.subsume (hrs : r ≤ s) (x : RankedVal U r K) : RankedVal U s K :=
  ⟨x.val, x.property.mono hrs⟩

def RankedVal.appMax (f : RankedVal U r₁ (.arr K L)) (x : RankedVal U r₂ K) :
    RankedVal U (max r₁ r₂) L :=
  ⟨f.val x.val, f.property _ (Nat.le_max_left _ _) x.val
    (x.property.mono (Nat.le_max_right _ _))⟩

def stableId : RankedVal U r (.arr K K) :=
  ⟨id, fun _ _ _ hx => hx⟩

@[simp] theorem stableId_app (x : RankedVal U s K) :
    (stableId (U := U) (r := r) (K := K)).appMax x |>.val = x.val := rfl

/-- The precise failure of the old slice extension on identity.  Equality to
`x` is unavailable when `x` contains genuinely rank-`s` data. -/
theorem slice_extend_id_apply (hrs : r ≤ s) (x : Slice U s K) :
    RankedKinds.extend U hrs (.arr K K) (fun y : Slice U r K => y) x =
      RankedKinds.extend U hrs K (RankedKinds.restrict U hrs K x) := rfl

def WholeEnv (U : Universe.{v}) : KindCtx → Type v
  | [] => PUnit
  | RK :: Δ => WholeVal U RK.kind × WholeEnv U Δ

def EnvStable (U : Universe.{v}) (r : Nat) : {Δ : KindCtx} → WholeEnv U Δ → Prop
  | [], _ => True
  | RK :: Δ, ρ => StableAt U r RK.kind ρ.1 ∧ EnvStable U r ρ.2

theorem EnvStable.mono (hrs : r ≤ s) :
    ∀ {Δ : KindCtx} {ρ : WholeEnv U Δ}, EnvStable U r ρ → EnvStable U s ρ := by
  intro Δ
  induction Δ with
  | nil => simp [EnvStable]
  | cons RK Δ ih =>
    intro ρ h
    exact ⟨h.1.mono hrs, ih h.2⟩

def WholeEnv.lookup {Δ : KindCtx} {n : Nat} {RK : RKind} (h : Δ[n]? = some RK) :
    WholeEnv U Δ → WholeVal U RK.kind := by
  induction Δ generalizing n RK with
  | nil => simp at h
  | cons J Δ ih =>
    intro ρ
    cases n with
    | zero => simp at h; subst J; exact ρ.1
    | succ n => exact ih (by simpa using h) ρ.2

theorem EnvStable.lookup {Δ : KindCtx} {n : Nat} {RK : RKind}
    (h : Δ[n]? = some RK) {ρ : WholeEnv U Δ} (hρ : EnvStable U r ρ) :
    StableAt U r RK.kind (ρ.lookup h) := by
  induction Δ generalizing n RK with
  | nil => simp at h
  | cons J Δ ih =>
    cases n with
    | zero => simp at h; subst J; exact hρ.1
    | succ n => exact ih (by simpa using h) hρ.2

/-- Elaborated semantic evidence, not the final surface formation judgement.
It is a Kripke logical relation over all ranks above `minRank`. -/
structure Kripke (U : Universe.{v}) (Δ : KindCtx) (minRank : Nat) (K : Kind) where
  run : WholeEnv U Δ → WholeVal U K
  stable : ∀ s, minRank ≤ s → ∀ ρ, EnvStable U s ρ → StableAt U s K (run ρ)

def Kripke.raise (x : Kripke U Δ r K) (hrs : r ≤ s) : Kripke U Δ s K where
  run := x.run
  stable t h := x.stable t (hrs.trans h)

def Kripke.var (h : Δ[n]? = some RK) : Kripke U Δ 0 RK.kind where
  run ρ := ρ.lookup h
  stable s _ ρ hρ := hρ.lookup h

def Kripke.code (c : U.Code) (hc : U.rank c ≤ m) : Kripke U Δ m .star where
  run _ := c
  stable s h _ _ := hc.trans h

def Kripke.bool : Kripke U Δ 0 .star :=
  .code U.boolCode (by simp [U.rank_boolCode])

def Kripke.arr (a : Kripke U Δ r₁ .star) (c : Kripke U Δ r₂ .star) :
    Kripke U Δ (max r₁ r₂) .star where
  run ρ := U.arr (a.run ρ) (c.run ρ)
  stable s h ρ hρ := (U.rank_arr _ _).trans <| Nat.max_le
    (a.stable s ((Nat.le_max_left _ _).trans h) ρ hρ)
    (c.stable s ((Nat.le_max_right _ _).trans h) ρ hρ)

def Kripke.app (f : Kripke U Δ r₁ (.arr K L)) (x : Kripke U Δ r₂ K) :
    Kripke U Δ (max r₁ r₂) L where
  run ρ := f.run ρ (x.run ρ)
  stable s h ρ hρ := f.stable s ((Nat.le_max_left _ _).trans h) ρ hρ
    s le_rfl (x.run ρ) (x.stable s ((Nat.le_max_right _ _).trans h) ρ hρ)

/-- Type lambda stability is derived compositionally from body stability. -/
def Kripke.lam (body : Kripke U (RK :: Δ) m L) : Kripke U Δ m (.arr RK.kind L) where
  run ρ x := body.run (x, ρ)
  stable s h ρ hρ := by
    intro t hst x hx
    exact body.stable t (h.trans hst) (x, ρ) ⟨hx, hρ.mono hst⟩

@[simp] theorem Kripke.app_lam (body : Kripke U (RK :: Δ) r₁ L)
    (x : Kripke U Δ r₂ RK.kind) (ρ : WholeEnv U Δ) :
    ((body.lam).app x).run ρ = body.run (x.run ρ, ρ) := rfl

/-- A compositional elaboration of the higher-kind fragment into Kripke
evidence.  Unlike `Kinded`, this relation records the semantic object needed
for sound max-rank application.  It is intentionally not yet the surface
checker: rank-polymorphic formation must generate this evidence. -/
inductive Elaborates {Base : Type u} {U : Universe.{v}} (B : BaseSemantics Base U) :
    {Δ : KindCtx} → (A : Ty Base) → (RK : RKind) →
      Kripke U Δ RK.rank RK.kind → Prop
  | base {Δ c} : Elaborates B (Δ := Δ) (.base c) ⟨.star, 0⟩
      (.code (B.code c) (by simp [B.rank_code]))
  | tyVar {Δ n RK} (h : Δ[n]? = some RK) : Elaborates B (.tyVar n) RK
      ((.var h).raise (Nat.zero_le _))
  | tyLam {Δ RK A L r} {a : Kripke U (RK :: Δ) r L}
      (ha : Elaborates B A ⟨L, r⟩ a) :
      Elaborates B (.tyLam RK A) ⟨.arr RK.kind L, max RK.rank r⟩
        (a.lam.raise (Nat.le_max_right _ _))
  | tyApp {Δ F X K L r₁ r₂} {f : Kripke U Δ r₁ (.arr K L)}
      {x : Kripke U Δ r₂ K} (hf : Elaborates B F ⟨.arr K L, r₁⟩ f)
      (hx : Elaborates B X ⟨K, r₂⟩ x) :
      Elaborates B (.tyApp F X) ⟨L, max r₁ r₂⟩ (f.app x)
  | tyBool {Δ} : Elaborates B (Δ := Δ) .tyBool ⟨.star, 0⟩ .bool
  | tyArr {Δ A C r₁ r₂} {a : Kripke U Δ r₁ .star} {c : Kripke U Δ r₂ .star}
      (ha : Elaborates B A ⟨.star, r₁⟩ a) (hc : Elaborates B C ⟨.star, r₂⟩ c) :
      Elaborates B (.tyArr A C) ⟨.star, max r₁ r₂⟩ (a.arr c)
  | subsume {Δ A r s} {a : Kripke U Δ r .star}
      (ha : Elaborates B A ⟨.star, r⟩ a) (hrs : r ≤ s) :
      Elaborates B A ⟨.star, s⟩ (a.raise hrs)

theorem Elaborates.kinded {B : BaseSemantics Base U}
    (h : Elaborates B (Δ := Δ) A RK a) : Kinded Δ A RK := by
  induction h with
  | base => exact .base
  | tyVar h => exact .tyVar h
  | tyLam _ ih => exact .tyLam ih
  | tyApp _ _ ihF ihX => exact .tyApp ihF ihX
  | tyBool => exact .tyBool
  | tyArr _ _ ihA ihC => exact .tyArr ihA ihC
  | subsume _ hrs ih => exact .subsume ih hrs

/-!
## Rank expressions and instantiation

Surface HOL-omega ranks contain the affine form `z + n`; `max` and successor
are retained internally so formation results remain representable.  This is
the first, deliberately syntax-independent layer of `INST_RANK`.
-/

inductive RankExpr where
  | fixed (n : Nat)
  | varAdd (z offset : Nat)
  | add (a : RankExpr) (offset : Nat)
  | max (a b : RankExpr)
  | succ (a : RankExpr)
  deriving DecidableEq, Repr

def RankExpr.eval (ξ : Nat → Nat) : RankExpr → Nat
  | .fixed n => n
  | .varAdd z n => ξ z + n
  | .add a n => a.eval ξ + n
  | .max a b => max (a.eval ξ) (b.eval ξ)
  | .succ a => a.eval ξ + 1

def RankExpr.subst (σ : Nat → RankExpr) : RankExpr → RankExpr
  | .fixed n => .fixed n
  | .varAdd z n => .add (σ z) n
  | .add a n => .add (a.subst σ) n
  | .max a b => .max (a.subst σ) (b.subst σ)
  | .succ a => .succ (a.subst σ)

/- `varAdd` substitution is most useful for numeric assignments.  General
symbolic normalization will be supplied with the final rank AST. -/
def RankExpr.instantiate (ξ : Nat → Nat) : RankExpr → RankExpr :=
  RankExpr.subst (fun z => .fixed (ξ z))

theorem RankExpr.eval_instantiate (e : RankExpr) (ξ ζ : Nat → Nat) :
    (e.instantiate ξ).eval ζ = e.eval ξ := by
  induction e with
  | fixed n => rfl
  | varAdd z n => simp [instantiate, subst, eval]
  | add a n ih => simp [instantiate, subst, eval, ih]
  | max a b ihA ihB => simp [instantiate, subst, eval, ihA, ihB]
  | succ a ih => simp [instantiate, subst, eval, ih]

/-- An elaborated rank-polymorphic formation family.  Its syntax and context
may contain rank annotations instantiated by `ξ`; one derivation therefore
supplies every concrete instance. -/
structure RankScheme (Base : Type u) where
  context : (Nat → Nat) → KindCtx
  type : (Nat → Nat) → Ty Base
  kind : Kind
  rank : RankExpr
  formed : ∀ ξ, Kinded (context ξ) (type ξ) ⟨kind, rank.eval ξ⟩

theorem RankScheme.instantiate (S : RankScheme Base) (ξ : Nat → Nat) :
    Kinded (S.context ξ) (S.type ξ) ⟨S.kind, S.rank.eval ξ⟩ := S.formed ξ

/-- A concrete rank-polymorphic higher-kind identity.  One formation object
instantiates to the expected lambda at every assignment, including affine
`z+n` ranks. -/
def rankIdentityScheme (Base : Type u) (K : Kind) (r : RankExpr) : RankScheme Base where
  context _ := []
  type ξ := .tyLam ⟨K, r.eval ξ⟩ (.tyVar 0)
  kind := .arr K K
  rank := r
  formed ξ := by
    simpa using Kinded.tyLam (Kinded.tyVar (Δ := []) (RK := ⟨K, r.eval ξ⟩) (by simp))

example (ξ : Nat → Nat) :
    Kinded [] ((rankIdentityScheme Base K (.varAdd z n)).type ξ)
      ⟨.arr K K, ξ z + n⟩ :=
  (rankIdentityScheme Base K (.varAdd z n)).instantiate ξ

/-- Current equal-rank formation embeds in the max-rank calculus, after
normalizing base/Boolean ranks by subsumption. -/
theorem ofCore {Base : Type u} (h : HolOmega.Kinded Δ A RK) : Kinded Δ A RK := by
  induction h with
  | base => exact .subsume .base (Nat.zero_le _)
  | tyVar h => exact .tyVar h
  | tyLam h ih => simpa using Kinded.tyLam ih
  | tyApp _ _ ihF ihX => simpa using Kinded.tyApp ihF ihX
  | tyAll _ ih => exact .tyAll ih
  | tyBool => exact .subsume .tyBool (Nat.zero_le _)
  | tyArr _ _ ihA ihB => simpa using Kinded.tyArr ihA ihB
  | tySub _ hp ihA _ => exact .tySub ihA hp
  | subsume _ hrs ih => exact .subsume ih hrs

/-!
`Kripke` proves compositional stability through type lambda and max-rank
application.  Connecting `Kinded.tyLam` to it requires the final surface rank
syntax to elaborate one derivation uniformly at every assignment, rather than
only at the binder's single concrete slice.  `RankScheme` states that bridge.

For `tyAll`, the new carrier `{x : WholeVal U K // StableAt U r K x}` must be
shown small enough for the Beth universe and used as the quantifier domain.
That cardinal fitting theorem is the next semantic obligation.  The separate
exact `+1` improvement remains the cardinal blocker recorded in
`RankedKinds.lean`; the existing universe still validates `+2`.
-/

end Nucleus.HolOmega.FullRanking
