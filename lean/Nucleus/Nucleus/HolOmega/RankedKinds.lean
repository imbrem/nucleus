import Mathlib
import Nucleus.HolOmega.Model

/-!
# Whole higher-kind values and rank slices

An isolated prototype for ranking *all* kinds.  It does not change the current
kernel.  `WholeVal` gives the unrestricted simple-kind hierarchy; `AtRank`
states preservation of a rank slice.  `Slice` is the executable presentation
used by the current kernel, with variance-correct restriction and extension.
-/

universe u

namespace Nucleus.HolOmega.RankedKinds

open Kernel

def WholeVal (U : Universe.{u}) : Kind → Type u
  | .star => U.Code
  | .arr K L => WholeVal U K → WholeVal U L

def PreservesSlice (U : Universe.{u}) (r : Nat) : (K : Kind) → WholeVal U K → Prop
  | .star, c => U.rank c ≤ r
  | .arr K L, f => ∀ x, PreservesSlice U r K x → PreservesSlice U r L (f x)

theorem PreservesSlice.star_mono (hrs : r ≤ s) {c : WholeVal U .star}
    (hc : PreservesSlice U r .star c) : PreservesSlice U s .star c := hc.trans hrs

variable (U : Universe.{u})

/-- Rank slices are exactly the current kernel's `KindVal`. -/
abbrev Slice (r : Nat) (K : Kind) : Type u := KindVal U.rank r K

theorem slice_eq_kernel : Slice U r K = KindVal U.rank r K := rfl

def defaultSlice (U : Universe.{u}) : (r : Nat) → (K : Kind) → Slice U r K
  | r, .star => ⟨U.boolCode, by simp [U.rank_boolCode]⟩
  | r, .arr K L => fun _ => defaultSlice U r L

mutual
  noncomputable def extend (hrs : r ≤ s) : (K : Kind) → Slice U r K → Slice U s K
    | .star, c => ⟨c.val, c.property.trans hrs⟩
    | .arr K L, f => fun x => extend hrs L (f (restrict hrs K x))

  noncomputable def restrict (hrs : r ≤ s) : (K : Kind) → Slice U s K → Slice U r K
    | .star, c => by
        classical
        exact if h : U.rank c.val ≤ r then ⟨c.val, h⟩ else defaultSlice U r .star
    | .arr K L, f => fun x => restrict hrs L (f (extend hrs K x))
end

@[simp] theorem restrict_extend (hrs : r ≤ s) :
    ∀ (K : Kind) (x : Slice U r K), restrict U hrs K (extend U hrs K x) = x := by
  intro K
  induction K with
  | star =>
    intro x
    apply Subtype.ext
    simp [extend, restrict, x.property]
  | arr K L ihK ihL =>
    intro f
    funext x
    simp only [extend, restrict]
    rw [ihK, ihL]

theorem extend_restrict_comp (hrs : r ≤ s) (hst : s ≤ t) (K : Kind) :
    (∀ x : Slice U r K,
      extend U hst K (extend U hrs K x) = extend U (hrs.trans hst) K x) ∧
    (∀ x : Slice U t K,
      restrict U hrs K (restrict U hst K x) = restrict U (hrs.trans hst) K x) := by
  induction K with
  | star =>
    constructor
    · intro x
      rfl
    · intro x
      apply Subtype.ext
      by_cases hs : U.rank x.val ≤ s
      · by_cases hr : U.rank x.val ≤ r
        · simp [restrict, hs, hr]
        · simp [restrict, hs, hr, defaultSlice]
      · have hr : ¬ U.rank x.val ≤ r := fun h => hs (h.trans hrs)
        simp [restrict, hs, hr, defaultSlice, U.rank_boolCode]
  | arr K L ihK ihL =>
    constructor
    · intro f
      funext x
      simp only [extend]
      rw [ihK.2]
      exact ihL.1 _
    · intro f
      funext x
      simp only [restrict]
      rw [ihK.1]
      exact ihL.2 _

theorem extend_comp (hrs : r ≤ s) (hst : s ≤ t) (K : Kind) (x : Slice U r K) :
    extend U hst K (extend U hrs K x) = extend U (hrs.trans hst) K x :=
  (extend_restrict_comp U hrs hst K).1 x

theorem restrict_comp (hrs : r ≤ s) (hst : s ≤ t) (K : Kind) (x : Slice U t K) :
    restrict U hrs K (restrict U hst K x) = restrict U (hrs.trans hst) K x :=
  (extend_restrict_comp U hrs hst K).2 x

theorem restrict_extend_between (hrq : r ≤ q) (hqs : q ≤ s) (x : Slice U r K) :
    restrict U hqs K (extend U (hrq.trans hqs) K x) = extend U hrq K x := by
  rw [← extend_comp U hrq hqs K x]
  exact restrict_extend U hqs K (extend U hrq K x)

/-- Application after aligning both ranks at their maximum. -/
noncomputable def appMax (F : Slice U r₁ (.arr K L)) (X : Slice U r₂ K) :
    Slice U (max r₁ r₂) L :=
  extend U (Nat.le_max_left _ _) (.arr K L) F
    (extend U (Nat.le_max_right _ _) K X)

/-- Base slices embed in whole values and satisfy `AtRank`. -/
def Slice.toWholeStar (x : Slice U r .star) : WholeVal U .star := x.val

theorem Slice.toWholeStar_atRank (x : Slice U r .star) :
    PreservesSlice U r .star (Slice.toWholeStar U x) := x.property

/-- At base kind, the whole-value predicate and the existing kernel slice are
literally the same subtype data. -/
def wholeStarEquiv : {c : WholeVal U .star // PreservesSlice U r .star c} ≃ Slice U r .star :=
  Equiv.refl _

/-!
`PreservesSlice` alone is intentionally not called `AtRank`: at arrow kinds it
is not monotone, since a larger rank admits new inputs.  The corrected whole
domain is a coherent family of slices with both restriction and canonical
extension laws. -/

structure CoherentVal (K : Kind) where
  minRank : Nat
  slice : ∀ r, minRank ≤ r → Slice U r K
  restrict_natural : ∀ {r s} (hr : minRank ≤ r) (hrs : r ≤ s),
    restrict U hrs K (slice s (hr.trans hrs)) = slice r hr
  extend_natural : ∀ {r s} (hr : minRank ≤ r) (hrs : r ≤ s),
    extend U hrs K (slice r hr) = slice s (hr.trans hrs)

/-- Every individual slice has a canonical coherent extension whose tail
starts at that slice's rank. -/
noncomputable def fromSlice (r : Nat) (K : Kind) (x : Slice U r K) : CoherentVal U K where
  minRank := r
  slice s hrs := extend U hrs K x
  restrict_natural := by
    intro q s hrq hqs
    exact restrict_extend_between U hrq hqs x
  extend_natural := by
    intro q s hrq hqs
    exact extend_comp U hrq hqs K x

/-- A rank view retains the coherent whole value; only its observation level
changes.  This is the restricted-graph presentation needed for higher-kind
subsumption. -/
structure AtRank (r : Nat) (K : Kind) where
  whole : CoherentVal U K
  within : whole.minRank ≤ r

def AtRank.observe (x : AtRank U r K) : Slice U r K := x.whole.slice r x.within

def down (r : Nat) (x : CoherentVal U K) (h : x.minRank ≤ r) : AtRank U r K := ⟨x, h⟩
def up (x : AtRank U r K) : CoherentVal U K := x.whole

@[simp] theorem up_down (r : Nat) (x : CoherentVal U K) (h : x.minRank ≤ r) :
    up U (down U r x h) = x := rfl
@[simp] theorem down_up (x : AtRank U r K) : down U r (up U x) x.within = x := by
  cases x; rfl

/-- All-kind rank subsumption is monotone because both views share the same
coherent whole value. -/
def subsume (hrs : r ≤ s) (x : AtRank U r K) : AtRank U s K :=
  ⟨x.whole, x.within.trans hrs⟩

@[simp] theorem subsume_observe (hrs : r ≤ s) (x : AtRank U r K) :
    (subsume U hrs x).observe = extend U hrs K x.observe := by
  exact (x.whole.extend_natural x.within hrs).symm

/-- Coherent application is pointwise on every slice. -/
noncomputable def coherentApp (F : CoherentVal U (.arr K L))
    (X : CoherentVal U K) : CoherentVal U L where
  minRank := max F.minRank X.minRank
  slice r hr := F.slice r ((Nat.le_max_left _ _).trans hr)
    (X.slice r ((Nat.le_max_right _ _).trans hr))
  restrict_natural := by
    intro r s hr hrs
    have hFr := (Nat.le_max_left F.minRank X.minRank).trans hr
    have hXr := (Nat.le_max_right F.minRank X.minRank).trans hr
    have hF := F.restrict_natural hFr hrs
    have hX := X.extend_natural hXr hrs
    change restrict U hrs L (F.slice s _ (X.slice s _)) = F.slice r _ (X.slice r _)
    rw [← hX]
    have happ := congrFun hF (X.slice r hXr)
    simpa [restrict, restrict_extend] using happ
  extend_natural := by
    intro r s hr hrs
    have hFr := (Nat.le_max_left F.minRank X.minRank).trans hr
    have hXr := (Nat.le_max_right F.minRank X.minRank).trans hr
    have hF := F.extend_natural hFr hrs
    have hX := X.restrict_natural hXr hrs
    change extend U hrs L (F.slice r _ (X.slice r _)) = F.slice s _ (X.slice s _)
    rw [← hX]
    have happ := congrFun hF (X.slice s (hXr.trans hrs))
    simpa [extend, restrict_extend] using happ

/-- Semantic type lambda.  Its premises are precisely the two naturality laws
that a body interpretation must prove; application then consumes the result
without further transports. -/
noncomputable def coherentLam (m : Nat)
    (body : ∀ r, m ≤ r → Slice U r K → Slice U r L)
    (hrestrict : ∀ {r s} (hr : m ≤ r) (hrs : r ≤ s) (x : Slice U r K),
      restrict U hrs L (body s (hr.trans hrs) (extend U hrs K x)) = body r hr x)
    (hextend : ∀ {r s} (hr : m ≤ r) (hrs : r ≤ s) (x : Slice U s K),
      extend U hrs L (body r hr (restrict U hrs K x)) = body s (hr.trans hrs) x) :
    CoherentVal U (.arr K L) where
  minRank := m
  slice r hr := body r hr
  restrict_natural := by
    intro r s hr hrs
    funext x
    exact hrestrict hr hrs x
  extend_natural := by
    intro r s hr hrs
    funext x
    exact hextend hr hrs x

@[simp] theorem coherentLam_observe (m : Nat)
    (body : ∀ r, m ≤ r → Slice U r K → Slice U r L) hr hres hext :
    (down U r (coherentLam U m body hres hext) hr).observe = body r hr := rfl

noncomputable def coherentAppAt (F : AtRank U r₁ (.arr K L)) (X : AtRank U r₂ K) :
    AtRank U (max r₁ r₂) L :=
  down U _ (coherentApp U F.whole X.whole)
    (max_le_max F.within X.within)

theorem coherentAppAt_observe (F : AtRank U r₁ (.arr K L)) (X : AtRank U r₂ K) :
    (coherentAppAt U F X).observe = appMax U F.observe X.observe := by
  change F.whole.slice (max r₁ r₂) _ (X.whole.slice (max r₁ r₂) _) = _
  rw [← F.whole.extend_natural F.within (Nat.le_max_left r₁ r₂)]
  rw [← X.whole.extend_natural X.within (Nat.le_max_right r₁ r₂)]
  rfl

/-- Every universe code yields a nonempty coherent base value, beginning at
exactly its own rank. -/
noncomputable def coherentCode (c : U.Code) : CoherentVal U .star where
  minRank := U.rank c
  slice r h := ⟨c, h⟩
  restrict_natural := by
    intro r s hr hrs
    apply Subtype.ext
    simp [restrict, hr]
  extend_natural := by
    intro r s hr hrs
    rfl

@[simp] theorem coherentCode_observe (c : U.Code) (h : U.rank c ≤ r) :
    (down U r (coherentCode U c) h).observe = (⟨c, h⟩ : Slice U r .star) := rfl

/-- Constant higher-kind values show that the coherent domain is inhabited at
every kind, not merely an interface whose laws might have no witnesses. -/
noncomputable def coherentConst (U : Universe.{u}) : (K : Kind) → CoherentVal U K
  | .star => coherentCode U U.boolCode
  | .arr K L =>
      let out := coherentConst U L
      { minRank := out.minRank
        slice := fun r h _ => out.slice r h
        restrict_natural := by
          intro r s hr hrs
          funext x
          simp only [restrict]
          exact out.restrict_natural hr hrs
        extend_natural := by
          intro r s hr hrs
          funext x
          simp only [extend]
          exact out.extend_natural hr hrs }

noncomputable instance coherentValInhabited (K : Kind) : Inhabited (CoherentVal U K) :=
  ⟨coherentConst U K⟩

theorem coherentVal_nonempty (K : Kind) : Nonempty (CoherentVal U K) :=
  ⟨coherentConst U K⟩

@[simp] theorem coherentConst_minRank (K : Kind) : (coherentConst U K).minRank = 0 := by
  induction K with
  | star => exact U.rank_boolCode
  | arr K L _ ih => simpa [coherentConst] using ih

/-- Coherent environments retain one whole value for every ranked binder,
together with evidence that it is available at the binder's declared rank. -/
def CoherentEnv (U : Universe.{u}) : KindCtx → Type u
  | [] => PUnit
  | RK :: Δ => AtRank U RK.rank RK.kind × CoherentEnv U Δ

def CoherentEnv.lookup {Δ : KindCtx} {n : Nat} {RK : RKind}
    (h : Δ[n]? = some RK) : CoherentEnv U Δ → AtRank U RK.rank RK.kind := by
  induction Δ generalizing n RK with
  | nil => simp at h
  | cons J Δ ih =>
    intro ρ
    cases n with
    | zero =>
      simp at h
      subst J
      exact ρ.1
    | succ n => exact ih (by simpa using h) ρ.2

noncomputable def coherentEnvDefault (U : Universe.{u}) : (Δ : KindCtx) → CoherentEnv U Δ
  | [] => PUnit.unit
  | RK :: Δ =>
      let x := coherentConst U RK.kind
      (down U RK.rank x (by simp [x]), coherentEnvDefault U Δ)

/-- Beth's existing model supplies the prototype maps directly. -/
example : Slice Beth.model r K = KindVal Beth.model.rank r K := rfl

/-!
## Exact `+1` quantifier ranks

The slice redesign itself does not prove an exact `max r s + 1` bound.
`Beth.piCode`/`sigmaCode` place their carrier in block `max r s + 1`, while a
`Code`'s rank is the successor of its block, yielding the existing `+2`.
Closing the gap requires a new cardinal-closure theorem constructing the
dependent product/sum in a block at most `max r s`, or a changed code/rank
convention.  Restriction/extension laws cannot alter that cardinal fact.
-/

end Nucleus.HolOmega.RankedKinds
