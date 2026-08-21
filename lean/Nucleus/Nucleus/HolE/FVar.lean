import Nucleus.Dict
import Nucleus.HolE
import Mathlib.Data.Finset.Image

/-!
# Typed free variables

A free variable is identified by its index together with its syntactic sort.
Type conversion therefore does not change variable identity.  The index type
is a parameter so that arenas can later use source-qualified names without
changing the support API.
-/

namespace Nucleus.HolE

universe u v

/-- The syntactic sort carried by a free variable. -/
inductive FVarSort (Ty : Type v) where
  | ty (kind : Kind)
  | tm (type : Ty)
  deriving DecidableEq

/-- A typed free-variable name.  Both fields participate in identity. -/
structure FVar (Ix : Type u) (Ty : Type v) where
  ix : Ix
  sort : FVarSort Ty
  deriving DecidableEq

namespace FVar

variable {Ix : Type u} {Ty : Type v} [DecidableEq Ix] [DecidableEq Ty]

def isTy : FVar Ix Ty → Bool
  | ⟨_, .ty _⟩ => true
  | _ => false

def isTm : FVar Ix Ty → Bool
  | ⟨_, .tm _⟩ => true
  | _ => false

/-- Type-variable part of a support. -/
def tyvars (support : Finset (FVar Ix Ty)) : Finset (FVar Ix Ty) :=
  support.filter fun item => isTy item = true

/-- Term-variable part of a support. -/
def tmvars (support : Finset (FVar Ix Ty)) : Finset (FVar Ix Ty) :=
  support.filter fun item => isTm item = true

/-- Erase sorts and retain every index used in a support. -/
def indices (support : Finset (FVar Ix Ty)) : Finset Ix :=
  support.image ix

def tyIndices (support : Finset (FVar Ix Ty)) : Finset Ix :=
  (tyvars support).image ix

def tmIndices (support : Finset (FVar Ix Ty)) : Finset Ix :=
  (tmvars support).image ix

/-- All syntactic sorts paired with a particular index. -/
def sortsAt (support : Finset (FVar Ix Ty)) (name : Ix) : Finset (FVarSort Ty) :=
  (support.filter fun item => item.ix = name).image sort

/-- The dictionary view of a support, grouped by index. -/
def byIndex (support : Finset (FVar Ix Ty)) : Nucleus.Dict Ix (Finset (FVarSort Ty)) where
  lookup name := if name ∈ indices support then some (sortsAt support name) else none
  keys := indices support
  mem_keys := by simp

omit [DecidableEq Ty] in
@[simp] theorem mem_indices {support : Finset (FVar Ix Ty)} {name : Ix} :
    name ∈ indices support ↔ ∃ item ∈ support, item.ix = name := by
  simp [indices]

@[simp] theorem mem_sortsAt {support : Finset (FVar Ix Ty)} {name : Ix}
    {variableSort : FVarSort Ty} :
    variableSort ∈ sortsAt support name ↔ ⟨name, variableSort⟩ ∈ support := by
  constructor
  · intro membership
    simp only [sortsAt, Finset.mem_image, Finset.mem_filter] at membership
    obtain ⟨item, ⟨inSupport, sameName⟩, sameSort⟩ := membership
    cases item
    simp_all
  · intro membership
    simp only [sortsAt, Finset.mem_image, Finset.mem_filter]
    exact ⟨⟨name, variableSort⟩, ⟨membership, rfl⟩, rfl⟩

@[simp] theorem lookup_byIndex {support : Finset (FVar Ix Ty)} {name : Ix} :
    (byIndex support).lookup name =
      if name ∈ indices support then some (sortsAt support name) else none := rfl

@[simp] theorem mem_getD_byIndex {support : Finset (FVar Ix Ty)} {name : Ix}
    {variableSort : FVarSort Ty} :
    variableSort ∈ (byIndex support).getD name ∅ ↔
      ⟨name, variableSort⟩ ∈ support := by
  by_cases used : name ∈ indices support
  · change variableSort ∈
        (if name ∈ indices support then some (sortsAt support name) else none).getD ∅ ↔ _
    rw [if_pos used]
    exact mem_sortsAt
  · have absent : ⟨name, variableSort⟩ ∉ support := by
      intro membership
      apply used
      exact (mem_indices.mpr ⟨⟨name, variableSort⟩, membership, rfl⟩)
    change variableSort ∈
        (if name ∈ indices support then some (sortsAt support name) else none).getD ∅ ↔ _
    rw [if_neg used]
    simp [absent]

/-- No index is used at two distinct syntactic sorts. -/
def NoNameConfusion (support : Finset (FVar Ix Ty)) : Prop :=
  ∀ ⦃name left right⦄,
    ⟨name, left⟩ ∈ support → ⟨name, right⟩ ∈ support → left = right

/-- Conversion-equivalent term types cannot give the same index two names. -/
def NoConvConfusion (conv : Ty → Ty → Prop)
    (support : Finset (FVar Ix Ty)) : Prop :=
  ∀ ⦃name left right⦄,
    ⟨name, .tm left⟩ ∈ support → ⟨name, .tm right⟩ ∈ support →
      conv left right → left = right

omit [DecidableEq Ix] [DecidableEq Ty] in
theorem noNameConfusion_noConvConfusion
    {support : Finset (FVar Ix Ty)} (clear : NoNameConfusion support)
    (conv : Ty → Ty → Prop) : NoConvConfusion conv support := by
  intro name left right inLeft inRight _
  have equality := clear inLeft inRight
  cases equality
  rfl

end FVar

end Nucleus.HolE
