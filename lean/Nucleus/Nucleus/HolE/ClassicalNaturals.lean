import Nucleus.HolE.Infinity

/-!
# A model of the naturals, from the axiom of infinity

`Nucleus.HolE.Infinity` gives a Dedekind-infinite carrier: an equality-
reflecting endomap that misses a point.  That is strictly weaker than the
naturals — the carrier may contain elements the map never reaches from the
missed point, and nothing so far rules them out.  Induction is exactly the
statement that there are none.

So the naturals are carved out rather than assumed: `Reachable` is the
intersection of every subset containing the point and closed under the map,
and the subtype it cuts satisfies Peano *by construction*, induction included.
This is the classical half of the bootstrap — the object-language half carves
the same subtype with `ax.sub`.
-/

namespace Nucleus.HolE.Infinity

set_option relaxedAutoImplicit true

/-- A model of the naturals: a carrier with zero and successor satisfying the
Peano axioms.

Induction is a field rather than a consequence, because it is the one Peano
axiom a Dedekind-infinite carrier does not already give. -/
structure CNatModel where
  carrier : Type
  zero : carrier
  succ : carrier → carrier
  succ_injective : ∀ x y, succ x = succ y → x = y
  succ_ne_zero : ∀ x, succ x ≠ zero
  induction : ∀ P : carrier → Prop, P zero → (∀ x, P x → P (succ x)) → ∀ x, P x

namespace CInfinityStructure

variable {A : CPointed}

/-- The part of the carrier the map actually reaches from the missed point:
the intersection of every subset containing it and closed under the map.

Impredicative, and deliberately so — quantifying over *all* subsets is what
makes the resulting induction principle hold for all of them. -/
def Reachable (s : CInfinityStructure A) (a : A.carrier) : Prop :=
  ∀ S : A.carrier → Prop, S s.missed → (∀ x, S x → S (s.next x)) → S a

theorem reachable_missed (s : CInfinityStructure A) : s.Reachable s.missed :=
  fun _ base _ => base

theorem reachable_next (s : CInfinityStructure A) {a : A.carrier}
    (reachable : s.Reachable a) : s.Reachable (s.next a) :=
  fun S base step => step a (reachable S base step)

/-- The naturals carved out of a Dedekind-infinite carrier. -/
def natModel (s : CInfinityStructure A) : CNatModel where
  carrier := {a : A.carrier // s.Reachable a}
  zero := ⟨s.missed, s.reachable_missed⟩
  succ := fun x => ⟨s.next x.1, s.reachable_next x.2⟩
  succ_injective := by
    intro x y equality
    have carriers : s.next x.1 = s.next y.1 := congrArg Subtype.val equality
    exact Subtype.ext ((s.reflectsEquality x.1 y.1).mp carriers)
  succ_ne_zero := by
    intro x equality
    exact s.misses x.1 (congrArg Subtype.val equality)
  induction := by
    intro P base step x
    -- Instantiate `Reachable` at "some proof of reachability makes `P` hold".
    -- Pairing the proof with the property is what lets the closure step apply
    -- `step`: a bare `∀ h, P ⟨a, h⟩` gives nothing to feed it.
    let S : A.carrier → Prop := fun a => ∃ reachable : s.Reachable a, P ⟨a, reachable⟩
    have baseS : S s.missed := ⟨s.reachable_missed, base⟩
    have stepS : ∀ a, S a → S (s.next a) := by
      rintro a ⟨reachable, holds⟩
      exact ⟨s.reachable_next reachable, step ⟨a, reachable⟩ holds⟩
    obtain ⟨reachable, holds⟩ := x.2 S baseS stepS
    -- `Reachable` is a `Prop`, so the recovered proof and `x`'s own agree.
    exact (Subtype.ext rfl : (⟨x.1, reachable⟩ : {a // s.Reachable a}) = x) ▸ holds

end CInfinityStructure

/-- **A model of the naturals exists, given the axiom of infinity.**

The classical witness for the infinity sentence is `natInfinity`, so this is
not vacuous; but the construction takes an arbitrary Dedekind-infinite carrier,
which is what makes it a consequence of the axiom rather than of the witness. -/
theorem natModel_exists_of_infinity
    (witness : Σ carrier : CPointed, CInfinityStructure carrier) :
    Nonempty CNatModel :=
  ⟨witness.2.natModel⟩

/-- Discharged against the axiom's own witness. -/
theorem natModel_exists : Nonempty CNatModel :=
  natModel_exists_of_infinity ⟨natPointed, natInfinity⟩

namespace CNatModel

variable (M : CNatModel)

/-- The numeral map: `ofNat n` is `succ` applied `n` times to `zero`.

Lean's own `Nat` is doing the recursion, which is exactly what a *model* is
entitled to — the point of this section is to show the carved-out carrier is
the naturals, not to reconstruct arithmetic from nothing. -/
def ofNat (M : CNatModel) : Nat → M.carrier
  | 0 => M.zero
  | n + 1 => M.succ (ofNat M n)

@[simp] theorem ofNat_zero : M.ofNat 0 = M.zero := rfl

@[simp] theorem ofNat_succ (n : Nat) : M.ofNat (n + 1) = M.succ (M.ofNat n) := rfl

theorem ofNat_injective : Function.Injective M.ofNat := by
  intro m
  induction m with
  | zero =>
      intro n equality
      cases n with
      | zero => rfl
      | succ n => exact absurd equality.symm (M.succ_ne_zero (M.ofNat n))
  | succ m ih =>
      intro n equality
      cases n with
      | zero => exact absurd equality (M.succ_ne_zero (M.ofNat m))
      | succ n =>
          exact congrArg Nat.succ (ih (M.succ_injective _ _ equality))

theorem ofNat_surjective : Function.Surjective M.ofNat := by
  refine M.induction (fun x => ∃ n, M.ofNat n = x) ⟨0, rfl⟩ ?_
  rintro x ⟨n, rfl⟩
  exact ⟨n + 1, rfl⟩

/-- The index of an element: the number of successors it stands for.

Chosen rather than computed — the model's carrier is abstract, so there is
nothing to compute with. `ofNat_toNat` and `toNat_ofNat` below pin it down
completely regardless. -/
noncomputable def toNat (M : CNatModel) (x : M.carrier) : Nat :=
  Classical.choose (M.ofNat_surjective x)

@[simp] theorem ofNat_toNat (x : M.carrier) : M.ofNat (M.toNat x) = x :=
  Classical.choose_spec (M.ofNat_surjective x)

@[simp] theorem toNat_ofNat (n : Nat) : M.toNat (M.ofNat n) = n :=
  M.ofNat_injective (M.ofNat_toNat (M.ofNat n))

/-- **The carved-out carrier is the naturals**, not merely a carrier that
happens to satisfy the axioms.

`ofNat` and `toNat` are mutually inverse, so the model is isomorphic to `Nat`
— and any two models are therefore isomorphic to each other. Categoricity is
what earns the name. -/
theorem ofNat_toNat_inverse :
    (∀ x : M.carrier, M.ofNat (M.toNat x) = x) ∧ (∀ n : Nat, M.toNat (M.ofNat n) = n) :=
  ⟨M.ofNat_toNat, M.toNat_ofNat⟩

@[simp] theorem toNat_zero : M.toNat M.zero = 0 := M.toNat_ofNat 0

@[simp] theorem toNat_succ (x : M.carrier) : M.toNat (M.succ x) = M.toNat x + 1 := by
  have step : M.ofNat (M.toNat x + 1) = M.succ x := by
    show M.succ (M.ofNat (M.toNat x)) = M.succ x
    rw [M.ofNat_toNat]
  rw [← step, M.toNat_ofNat]

/-! ## Primitive recursion

Induction alone gives the *uniqueness* of a recursor but not its existence;
categoricity supplies both at once, by transporting `Nat`'s. -/

/-- Recursion over the index, where the equations are definitional. -/
def natrecAux (M : CNatModel) {C : Type} (base : C)
    (step : M.carrier → C → C) : Nat → C
  | 0 => base
  | n + 1 => step (M.ofNat n) (natrecAux M base step n)

/-- Primitive recursion over the model. -/
noncomputable def natrec (M : CNatModel) {C : Type} (base : C)
    (step : M.carrier → C → C) (x : M.carrier) : C :=
  M.natrecAux base step (M.toNat x)

@[simp] theorem natrec_zero {C : Type} (base : C) (step : M.carrier → C → C) :
    M.natrec base step M.zero = base := by
  simp [natrec, natrecAux]

@[simp] theorem natrec_succ {C : Type} (base : C) (step : M.carrier → C → C)
    (x : M.carrier) :
    M.natrec base step (M.succ x) = step x (M.natrec base step x) := by
  simp [natrec, natrecAux]

/-- Recursion is determined by its two equations, which is what makes a
definition by `natrec` a definition rather than a choice. -/
theorem natrec_unique {C : Type} (base : C) (step : M.carrier → C → C)
    (candidate : M.carrier → C) (at_zero : candidate M.zero = base)
    (at_succ : ∀ x, candidate (M.succ x) = step x (candidate x)) :
    candidate = M.natrec base step := by
  funext x
  refine M.induction (fun x => candidate x = M.natrec base step x) ?_ ?_ x
  · simpa using at_zero
  · intro y ih
    simp [at_succ y, ih]

/-! ## Addition

Defined by recursion on the *second* argument, which is the convention that
makes `add_succ` the definitional equation and `succ_add` the one needing
induction.  Commutativity then costs two inductions rather than one, and the
asymmetry is the whole content of the proof. -/

/-- `add x y` recurses on `y`. -/
noncomputable def add (M : CNatModel) (x y : M.carrier) : M.carrier :=
  M.natrec x (fun _ accumulator => M.succ accumulator) y

@[simp] theorem add_zero (x : M.carrier) : M.add x M.zero = x := by
  simp [add]

@[simp] theorem add_succ (x y : M.carrier) :
    M.add x (M.succ y) = M.succ (M.add x y) := by
  simp [add]

@[simp] theorem zero_add (x : M.carrier) : M.add M.zero x = x := by
  refine M.induction (fun x => M.add M.zero x = x) ?_ ?_ x
  · simp
  · intro y ih
    simp [ih]

theorem succ_add (x y : M.carrier) :
    M.add (M.succ x) y = M.succ (M.add x y) := by
  refine M.induction (fun y => M.add (M.succ x) y = M.succ (M.add x y)) ?_ ?_ y
  · simp
  · intro z ih
    simp [ih]

theorem add_comm (x y : M.carrier) : M.add x y = M.add y x := by
  refine M.induction (fun y => M.add x y = M.add y x) ?_ ?_ y
  · simp
  · intro z ih
    simp [ih, M.succ_add]

theorem add_assoc (x y z : M.carrier) :
    M.add (M.add x y) z = M.add x (M.add y z) := by
  refine M.induction (fun z => M.add (M.add x y) z = M.add x (M.add y z)) ?_ ?_ z
  · simp
  · intro w ih
    simp [ih]

theorem add_right_comm (x y z : M.carrier) :
    M.add (M.add x y) z = M.add (M.add x z) y := by
  rw [M.add_assoc, M.add_comm y z, ← M.add_assoc]

/-- Addition agrees with `Nat`'s under the numeral map, which is the sanity
check that the definition means what it says. -/
theorem ofNat_add (m n : Nat) : M.add (M.ofNat m) (M.ofNat n) = M.ofNat (m + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      show M.add (M.ofNat m) (M.succ (M.ofNat n)) = M.succ (M.ofNat (m + n))
      rw [M.add_succ, ih]

/-! ## Multiplication -/

/-- `mul x y` recurses on `y`, accumulating a copy of `x` per successor. -/
noncomputable def mul (M : CNatModel) (x y : M.carrier) : M.carrier :=
  M.natrec M.zero (fun _ accumulator => M.add accumulator x) y

@[simp] theorem mul_zero (x : M.carrier) : M.mul x M.zero = M.zero := by
  simp [mul]

@[simp] theorem mul_succ (x y : M.carrier) :
    M.mul x (M.succ y) = M.add (M.mul x y) x := by
  simp [mul]

@[simp] theorem zero_mul (x : M.carrier) : M.mul M.zero x = M.zero := by
  refine M.induction (fun x => M.mul M.zero x = M.zero) ?_ ?_ x
  · simp
  · intro y ih
    simp [ih]

theorem succ_mul (x y : M.carrier) :
    M.mul (M.succ x) y = M.add (M.mul x y) y := by
  refine M.induction (fun y => M.mul (M.succ x) y = M.add (M.mul x y) y) ?_ ?_ y
  · simp
  · intro z ih
    simp only [M.mul_succ, ih, M.add_succ]
    exact congrArg M.succ (M.add_right_comm (M.mul x z) z x)

theorem mul_comm (x y : M.carrier) : M.mul x y = M.mul y x := by
  refine M.induction (fun y => M.mul x y = M.mul y x) ?_ ?_ y
  · simp
  · intro z ih
    simp only [M.mul_succ, M.succ_mul, ih]

end CNatModel

end Nucleus.HolE.Infinity
