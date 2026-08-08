import Nucleus.HolOmega.Model

/-!
# Worked derivations

What the kernel actually is, checked rather than described. Everything here is
built in the shallow-intrinsic syntax of `Kernel.lean` and holds for every
`Universe`, so `Beth.model` makes all of it non-vacuous.

* `polyId` — the polymorphic identity at `∀α:⋆@r. α → α`, and the theorem that
  instantiating and applying it returns its argument. This is the whole point
  of `TY_ALL`: quantification over the types of a kind at a rank.
* `Exists`/`Forall` — the HOL definitions, `P (ε P)` and `P = λ_. ⊤`.
* `existsIntro`, `forallElim`, `equalSymm` — derivations in `Derives`,
  including the fact that symmetry of `equal` is *derivable* even though
  `EqTm.symm` is primitive.

`Forall` and `Exists` are the term-level quantifiers over a type. They are
built *under* a `TY_ALL`, so `forallAll` below is genuinely `∀α. (α → bool) →
bool` — a polymorphic constant, which the rank-zero encoding could not state.
-/

namespace Nucleus.HolOmega.Kernel.Examples

variable (U : Universe)

/-! ## The polymorphic identity -/

/-- `α → α`, in a kind context binding `α` at kind `⋆` and rank `r`. -/
def selfArrow (r : Nat) : STy U [⟨.star, r⟩] := fun ρ => U.arr ρ.1.val ρ.1.val

theorem rank_selfArrow (r : Nat) (ρ : Kind.Env U [⟨.star, r⟩]) :
    U.rank (selfArrow U r ρ) ≤ r :=
  le_trans (U.rank_arr _ _) (by simpa using ρ.1.property)

/-- `∀α:⋆@r. α → α`. -/
def polyIdTy (r : Nat) : STy U [] :=
  Ty.all U r r (selfArrow U r) (rank_selfArrow U r)

/-- `Λα:⋆@r. λx:α. x`. -/
def polyId (r : Nat) : Tm U (Γ := ([] : Ctx U [])) (polyIdTy U r) :=
  Tm.tyLam U .star r r (rank_selfArrow U r) (Tm.lam U (Tm.vz U))

/-- Instantiating the polymorphic identity at a type and applying it returns
the argument. The type-level beta rule is doing the work. -/
theorem polyId_app (r : Nat) (X : Ty U [] ⟨.star, r⟩)
    (x : Tm U ([] : Ctx U []) (fun ρ => (X ρ).val)) :
    Tm.app U (Tm.tyApp U (h := rank_selfArrow U r) (polyId U r) X) x = x := by
  have hbeta := Tm.tyBeta U (Γ := ([] : Ctx U []))
    (h := rank_selfArrow U r) (Tm.lam U (Tm.vz U)) X
  rw [polyId, hbeta]
  funext ρ γ
  simp only [Tm.app, Tm.instantiateBody, Tm.lam, Tm.vz, Equiv.apply_symm_apply]

/-! ## The quantifiers over a type -/

variable {Δ : List RKind} {Γ : Ctx U Δ} {A : STy U Δ}

/-- `∃x:A. P x`, as HOL defines it: `P (ε P)`. -/
noncomputable def Exists (P : Tm U Γ (Ty.arr U A (Ty.boolCode U))) :
    Tm U Γ (Ty.boolCode U) := Tm.app U P (Tm.epsilon U P)

/-- `∀x:A. P x`, as HOL defines it: `P = λ_. ⊤`. -/
noncomputable def Forall (P : Tm U Γ (Ty.arr U A (Ty.boolCode U))) :
    Tm U Γ (Ty.boolCode U) :=
  Tm.equal U P (Tm.lam U (Tm.boolCode U true))

/-- A witness proves an existential. This is exactly the choice rule. -/
theorem existsIntro {H : List (Tm U Γ (Ty.boolCode U))}
    (P : Tm U Γ (Ty.arr U A (Ty.boolCode U))) (x : Tm U Γ A)
    (h : Derives U H (Tm.app U P x)) : Derives U H (Exists U P) :=
  Derives.choice P x h

/-- Symmetry of `equal` is derivable, though `EqTm.symm` is primitive: rewrite
along `x = y` inside `fun z => equal z x`, starting from reflexivity. -/
theorem equalSymm {H : List (Tm U Γ (Ty.boolCode U))} (x y : Tm U Γ A)
    (h : Derives U H (Tm.equal U x y)) : Derives U H (Tm.equal U y x) := by
  -- `p := λz. equal z x`
  let p : Tm U Γ (Ty.arr U A (Ty.boolCode U)) :=
    Tm.lam U (Tm.equal U (Tm.vz U) (Tm.vs U x))
  have hx : Derives U H (Tm.app U p x) :=
    Derives.convert (EqTm.symm (EqTm.beta _ _)) (Derives.eqRefl x)
  exact Derives.convert (EqTm.beta _ _) (Derives.eqMp p x y h hx)

/-- A universal can be instantiated: rewrite along `P = λ_. ⊤` inside
`fun Q => Q x`, starting from truth. -/
theorem forallElim {H : List (Tm U Γ (Ty.boolCode U))}
    (P : Tm U Γ (Ty.arr U A (Ty.boolCode U))) (x : Tm U Γ A)
    (h : Derives U H (Forall U P)) : Derives U H (Tm.app U P x) := by
  -- `q := λQ. Q x`
  let q : Tm U Γ (Ty.arr U (Ty.arr U A (Ty.boolCode U)) (Ty.boolCode U)) :=
    Tm.lam U (Tm.app U (Tm.vz U) (Tm.vs U x))
  have htrue : Derives U H (Tm.app U q (Tm.lam U (Tm.boolCode U true))) :=
    Derives.convert (EqTm.symm (EqTm.trans (EqTm.beta _ _) (EqTm.beta _ _)))
      Derives.truth
  have hsymm : Derives U H (Tm.equal U (Tm.lam U (Tm.boolCode U true)) P) :=
    equalSymm U _ _ h
  exact Derives.convert (EqTm.beta _ _)
    (Derives.eqMp q (Tm.lam U (Tm.boolCode U true)) P hsymm htrue)

/-! ## A polymorphic constant

`Forall` above lives at a fixed type. Under a `TY_ALL` it becomes a genuine
polymorphic constant, which is what having a real universal type former buys
over the rank-zero encoding. -/

/-- `(α → bool) → bool`, with `α` bound at kind `⋆` and rank `r`. -/
def predArrow (r : Nat) : STy U [⟨.star, r⟩] :=
  fun ρ => U.arr (U.arr ρ.1.val U.boolCode) U.boolCode

theorem rank_predArrow (r : Nat) (ρ : Kind.Env U [⟨.star, r⟩]) :
    U.rank (predArrow U r ρ) ≤ r := by
  refine le_trans (U.rank_arr _ _) (max_le (le_trans (U.rank_arr _ _) ?_) ?_)
  · exact max_le ρ.1.property (by simp [U.rank_boolCode])
  · simp [U.rank_boolCode]

/-- `∀α:⋆@r. (α → bool) → bool` — the type of a polymorphic quantifier. -/
def forallAllTy (r : Nat) : STy U [] :=
  Ty.all U r r (predArrow U r) (rank_predArrow U r)

/-- `Λα:⋆@r. λP:α → bool. (P = λ_. ⊤)`: the universal quantifier as one
polymorphic constant rather than one constant per type. -/
noncomputable def forallAll (r : Nat) :
    Tm U (Γ := ([] : Ctx U [])) (forallAllTy U r) :=
  Tm.tyLam U .star r r (rank_predArrow U r)
    (Tm.lam U (Tm.equal U (Tm.vz U) (Tm.lam U (Tm.boolCode U true))))

/-! ## Consistency, restated for the record -/

/-- None of the above lets `false` be derived. -/
theorem consistent :
    ¬ Derives Beth.model (Δ := []) (Γ := []) [] (Tm.boolCode Beth.model false) :=
  Beth.consistent

end Nucleus.HolOmega.Kernel.Examples
