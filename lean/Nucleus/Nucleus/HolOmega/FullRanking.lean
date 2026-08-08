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

def Env (U : Universe.{v}) : KindCtx → Type v
  | [] => PUnit
  | RK :: Δ => AtRank U RK.rank RK.kind × Env U Δ

def Env.lookup {U : Universe.{v}} {Δ : KindCtx} {n : Nat} {RK : RKind}
    (h : Δ[n]? = some RK) : Env U Δ → AtRank U RK.rank RK.kind := by
  induction Δ generalizing n RK with
  | nil => simp at h
  | cons J Δ ih =>
    intro ρ
    cases n with
    | zero => simp at h; subst J; exact ρ.1
    | succ n => exact ih (by simpa using h) ρ.2

structure BaseSemantics (Base : Type u) (U : Universe.{v}) where
  code : Base → U.Code
  rank_code : ∀ c, U.rank (code c) = 0

/-- Every base atom has a coherent rank-zero interpretation. -/
def denoteBase (B : BaseSemantics Base U) (c : Base) :
    AtRank U 0 .star :=
  down U 0 (coherentCode U (B.code c)) (by simp [B.rank_code])

noncomputable def denoteBool (U : Universe.{v}) : AtRank U 0 .star :=
  down U 0 (coherentCode U U.boolCode) (by simp [U.rank_boolCode])

/-- Arrow formation joins the independently ranked domain and codomain. -/
noncomputable def denoteArr (A : AtRank U r₁ .star) (C : AtRank U r₂ .star) :
    AtRank U (max r₁ r₂) .star :=
  let a := A.observe
  let c := C.observe
  down U _ (coherentCode U (U.arr a.val c.val)) <| by
    exact (U.rank_arr a.val c.val).trans
      (Nat.max_le (a.property.trans (Nat.le_max_left _ _))
        (c.property.trans (Nat.le_max_right _ _)))

/-- The max-rank semantic operation required by `Kinded.tyApp`. -/
def applyAtMax (F : AtRank U r₁ (.arr K L)) (X : AtRank U r₂ K) :
    AtRank U (max r₁ r₂) L := coherentAppAt U F X

/-- The compositional semantic fragment whose constructors need no additional
naturality premise.  In particular `tyApp` really interprets unequal operand
ranks at their maximum; this is stronger than the current equal-rank kernel.
`tyLam` is deliberately absent and isolated below as the remaining obligation. -/
inductive Denotes {Base : Type u} {U : Universe.{v}} (B : BaseSemantics Base U) :
    {Δ : KindCtx} → (ρ : Env U Δ) → (A : Ty Base) → (RK : RKind) →
      AtRank U RK.rank RK.kind → Prop
  | base {Δ ρ c} : Denotes B (Δ := Δ) ρ (.base c) ⟨.star, 0⟩ (denoteBase B c)
  | tyVar {Δ ρ n RK} (h : Δ[n]? = some RK) :
      Denotes B ρ (.tyVar n) RK (ρ.lookup h)
  | tyApp {Δ ρ F X K L r₁ r₂} {f : AtRank U r₁ (.arr K L)}
      {x : AtRank U r₂ K} (hf : Denotes B ρ F ⟨.arr K L, r₁⟩ f)
      (hx : Denotes B ρ X ⟨K, r₂⟩ x) :
      Denotes B ρ (.tyApp F X) ⟨L, max r₁ r₂⟩ (applyAtMax f x)
  | tyBool {Δ ρ} :
      Denotes B (Δ := Δ) ρ .tyBool ⟨.star, 0⟩ (denoteBool U)
  | tyArr {Δ ρ A C r₁ r₂} {a : AtRank U r₁ .star} {c : AtRank U r₂ .star}
      (hA : Denotes B ρ A ⟨.star, r₁⟩ a)
      (hC : Denotes B ρ C ⟨.star, r₂⟩ c) :
      Denotes B ρ (.tyArr A C) ⟨.star, max r₁ r₂⟩ (denoteArr a c)
  | subsume {Δ ρ A r s} {a : AtRank U r .star}
      (hA : Denotes B (Δ := Δ) ρ A ⟨.star, r⟩ a) (hrs : r ≤ s) :
      Denotes B ρ A ⟨.star, s⟩ (subsume U hrs a)

/-- Exact certificate needed to turn a family of slice-level body
interpretations into a coherent semantic type lambda.  A future soundness
proof for `Kinded.tyLam` must construct this certificate from weakening and
substitution/naturality of the body; it cannot be recovered from a single
fixed-rank denotation. -/
structure LambdaNaturality (U : Universe.{v}) (m : Nat) (K L : Kind) where
  body : ∀ r, m ≤ r → Slice U r K → Slice U r L
  restrict_body : ∀ {r s} (hr : m ≤ r) (hrs : r ≤ s) (x : Slice U r K),
    restrict U hrs L (body s (hr.trans hrs) (extend U hrs K x)) = body r hr x
  extend_body : ∀ {r s} (hr : m ≤ r) (hrs : r ≤ s) (x : Slice U s K),
    extend U hrs L (body r hr (restrict U hrs K x)) = body s (hr.trans hrs) x

noncomputable def LambdaNaturality.denote (h : LambdaNaturality U m K L) :
    CoherentVal U (.arr K L) :=
  coherentLam U m h.body h.restrict_body h.extend_body

noncomputable def atRankDefault (U : Universe.{v}) (r : Nat) (K : Kind) :
    AtRank U r K := down U r (coherentConst U K) (by simp)

theorem atRank_nonempty (U : Universe.{v}) (r : Nat) (K : Kind) :
    Nonempty (AtRank U r K) := ⟨atRankDefault U r K⟩

noncomputable def envDefault (U : Universe.{v}) : (Δ : KindCtx) → Env U Δ
  | [] => PUnit.unit
  | RK :: Δ => (atRankDefault U RK.rank RK.kind, envDefault U Δ)

theorem env_nonempty (U : Universe.{v}) (Δ : KindCtx) : Nonempty (Env U Δ) :=
  ⟨envDefault U Δ⟩

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
The remaining formation-soundness obligation is specifically type lambda.
A derivation of its body at one rank does not yet provide the natural family
of body interpretations required by `coherentLam`.  The full judgement must
therefore carry (or derive via a Kripke logical relation) weakening/naturality
for every larger observation rank.  Application, variables, environments,
nonemptiness, and equal-rank core lowering above are already independent of
that choice.  Quantifier `+1` remains the separate cardinal blocker recorded
in `RankedKinds.lean`.
-/

end Nucleus.HolOmega.FullRanking
