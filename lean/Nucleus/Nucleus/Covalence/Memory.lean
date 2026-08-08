import Mathlib
import Nucleus.Covalence

universe u

namespace Nucleus.Covalence.Memory

open HolOmega Nucleus.Covalence

/-- Row tags currently understood by the recursive Covalence term layer. -/
inductive HolTag
  | hole | boolTrue | boolFalse | app | lam | eq | eps | cast
  deriving DecidableEq, Repr

abbrev Row (Index : Type u) :=
  HolTag × Option Index × Option Index × Option Index

/-- Content-addressed storage is deliberately only a partial row lookup. -/
abbrev Memory (Index : Type u) := Index → Option (Row Index)

theorem kinded_arr_parts (h : Kinded Δ (.tyArr A B) ⟨.star, r⟩) :
    Kinded Δ A ⟨.star, r⟩ ∧ Kinded Δ B ⟨.star, r⟩ := by
  induction h with
  | tyArr hA hB => exact ⟨hA, hB⟩
  | subsume _ hrs ih => exact ⟨.subsume ih.1 hrs, .subsume ih.2 hrs⟩

def cutoff (name : Index → Nat) (i : Index) (hA : Kinded Δ A ⟨.star, r⟩) :
    Hol Base Δ Γ A := .hole (name i) hA

/-- Spend at most `fuel` row dereferences.  There is no visited set: cycles,
sharing, and long acyclic paths are treated identically.  Zero never reads
memory.  A missing row, missing required coordinate, incompatible tag, or
exhausted child budget becomes the hole named by the index being unfolded. -/
def unfold [DecidableEq Base] (name : Index → Nat) (mem : Memory Index) :
    (fuel : Nat) → (i : Index) → (A : Ty Base) →
      Kinded Δ A ⟨.star, r⟩ → Hol Base Δ Γ A
  | 0, i, _, hA => cutoff name i hA
  | fuel + 1, i, A, hA =>
    match mem i with
    | none => cutoff name i hA
    | some (.hole, _, _, _) => cutoff name i hA
    | some (.boolTrue, _, _, _) =>
        if h : A = .tyBool then h ▸ Hol.bool true else cutoff name i hA
    | some (.boolFalse, _, _, _) =>
        if h : A = .tyBool then h ▸ Hol.bool false else cutoff name i hA
    | some (.app, some fi, some xi, _) =>
        let hBool : Kinded Δ (.tyBool : Ty Base) ⟨.star, r⟩ := .tyBool
        let hFun : Kinded Δ (.tyArr .tyBool A) ⟨.star, r⟩ := .tyArr hBool hA
        .app (unfold name mem fuel fi (.tyArr .tyBool A) hFun)
          (unfold name mem fuel xi .tyBool hBool)
    | some (.lam, some bi, _, _) =>
        match A, hA with
        | .tyArr D C, hArr =>
          let parts := kinded_arr_parts hArr
          .lam parts.1 (unfold name mem fuel bi C parts.2)
        | _, _ => cutoff name i hA
    | some (.eq, some xi, some yi, _) =>
        if h : A = .tyBool then
          h ▸ Hol.eq (Judgement.tyBool (r := r))
            (unfold name mem fuel xi .tyBool (.tyBool))
            (unfold name mem fuel yi .tyBool (.tyBool))
        else cutoff name i hA
    | some (.eps, some pi, _, _) =>
        let hBool : Kinded Δ (.tyBool : Ty Base) ⟨.star, r⟩ := .tyBool
        let hPred : Kinded Δ (.tyArr A .tyBool) ⟨.star, r⟩ := .tyArr hA hBool
        .eps hA (unfold name mem fuel pi (.tyArr A .tyBool) hPred)
    | some (.cast, some ti, _, _) =>
        .cast (unfold name mem fuel ti A hA) A hA (.inl (.alpha rfl))
    | some _ => cutoff name i hA

@[simp] theorem unfold_zero [DecidableEq Base] (name : Index → Nat)
    (mem : Memory Index) (i : Index) (hA : Kinded Δ A ⟨.star, r⟩) :
    unfold name mem 0 i A hA = cutoff name i hA := rfl

/-- Typed information order: a named hole may be filled by any sorted tree;
matching constructors refine componentwise. -/
inductive Refines : Hol Base Δ Γ A → Hol Base Δ Γ A → Prop
  | hole : Refines (.hole name hA) t
  | bool : Refines (.bool b) (.bool b)
  | app : Refines f g → Refines x y → Refines (.app f x) (.app g y)
  | lam : Refines t u → Refines (.lam hA t) (.lam hA u)
  | eq : Refines x x' → Refines y y' → Refines (.eq hA x y) (.eq hA x' y')
  | eps : Refines p q → Refines (.eps hA p) (.eps hA q)
  | cast : Refines t u → Refines (.cast t A hA d) (.cast u A hA d)

notation:50 x " ⊑ " y => Refines x y

theorem Refines.refl (t : Hol Base Δ Γ A) : t ⊑ t := by
  induction t <;> aesop (add safe constructors Refines)

theorem Refines.trans {a b c : Hol Base Δ Γ A} : a ⊑ b → b ⊑ c → a ⊑ c := by
  intro hab hbc
  induction hab generalizing c <;> cases hbc <;> aesop (add safe constructors Refines)

set_option maxHeartbeats 3200000 in
theorem unfold_step [DecidableEq Base] (name : Index → Nat) (mem : Memory Index)
    (d : Nat) (i : Index) (hA : Kinded Δ A ⟨.star, r⟩) :
    unfold name mem d i A hA ⊑ unfold name mem (d + 1) i A hA := by
  induction d generalizing i A Γ r with
  | zero => exact .hole
  | succ d ih =>
    simp only [unfold]
    split <;> aesop (add safe constructors Refines)

theorem unfold_mono [DecidableEq Base] (name : Index → Nat) (mem : Memory Index)
    {d e : Nat} (hde : d ≤ e) (i : Index) (hA : Kinded Δ A ⟨.star, r⟩) :
    unfold name mem d i A hA ⊑ unfold name mem e i A hA := by
  induction hde with
  | refl => exact .refl _
  | @step e _ ih => exact Refines.trans ih (unfold_step name mem e i hA)

/-- Totality and sortedness are intrinsic in the unfolding result. -/
theorem unfold_lower_typed [DecidableEq Base] (name : Index → Nat)
    (mem : Memory Index) (d : Nat) (i : Index) (hA : Kinded Δ A ⟨.star, r⟩) :
    HasType Δ Γ (unfold name mem d i A hA).repair.1 A :=
  (unfold name mem d i A hA).repair.2

def unfoldedNode [DecidableEq Base] (name : Index → Nat) (mem : Memory Index)
    (d : Nat) (i : Index) (hA : Kinded Δ A ⟨.star, r⟩) : TermNode Base Δ Γ A :=
  .valid (unfold name mem d i A hA).repair.1
    (unfold name mem d i A hA).repair.2

/-- Uniform memory derivability: every deeper dereference budget has a
genuine Covalence derivation of its unfolded, sorted conclusion.  Quantifying
over all extensions is exactly what makes shallow-to-deep monotonicity valid;
a proof cannot depend on a particular canonical cutoff filling. -/
def Derives (name : Index → Nat) (mem : Memory Index) (d : Nat) (i : Index) : Prop :=
  ∀ e, d ≤ e → Nonempty (CovProves ([] : KindCtx) ([] : TmCtx Empty) []
    (unfoldedNode name mem e i (Judgement.tyBool (r := 0))))

theorem Derives.mono (h : Derives name mem d i) (hde : d ≤ e) :
    Derives name mem e i := by
  intro q heq
  exact h q (hde.trans heq)

/-- Lowering is uniform at every budget in a memory derivation. -/
theorem Derives.lower (h : Derives name mem d i) (e : Nat) (hde : d ≤ e) :
    ∃ (p : Proves ([] : KindCtx) ([] : TmCtx Empty) []
        (unfoldedNode name mem e i (Judgement.tyBool (r := 0))).repair.1), True := by
  obtain ⟨cov⟩ := h e hde
  exact ⟨cov.lower cov.canonicalFilling, trivial⟩

theorem validFalse_not_covProves :
    ¬CovProves ([] : KindCtx) ([] : TmCtx Empty) []
      (.valid (.tmBool false) (.tmBool)) := by
  apply empty_not_proves_false
  intro d
  cases d <;> rfl

/-- No uniformly derivable memory row may unfold to Boolean false at its
starting budget.  This is the memory-indexed consistency theorem, discharged
through Covalence consistency rather than by inspecting row tags. -/
theorem not_derives_false (name : Index → Nat) (mem : Memory Index)
    (d : Nat) (i : Index)
    (hfalse : (unfold name mem d i (.tyBool : Ty Empty)
      (Judgement.tyBool (r := 0))).repair.1 = .tmBool false) :
    ¬Derives name mem d i := by
  intro h
  obtain ⟨cov⟩ := h d le_rfl
  rw [hfalse] at cov
  exact validFalse_not_covProves cov

end Nucleus.Covalence.Memory
