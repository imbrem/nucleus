import Nucleus.HolE.Infinity

/-!
# A model of the naturals, from the axiom of infinity

`Nucleus.HolE.Infinity` gives a Dedekind-infinite carrier: an equality-
reflecting endomap that misses a point.  That is strictly weaker than the
naturals — the carrier may contain elements the map never reaches from the
missed point, and nothing so far rules them out.  Induction is exactly the
statement that there are none.

So the naturals are carved out rather than assumed, and the carving is the
content: `natModelOfInjectiveNotSurjective` is a *theorem* that a model can be
extracted from any injective, non-surjective endomap.  `Reachable` is the
intersection of every subset containing the missed point and closed under the
map, and the subtype it cuts satisfies Peano by construction — induction
included, which is exactly what the intersection buys.

The starting point cannot be chosen freely.  It has to be one the map misses,
which is what non-surjectivity supplies; `ArbitraryPoint` exhibits an injective
non-surjective map on which any other choice lands in a cycle.  The missed
point is load-bearing, not a convenience.

Categoricity then makes "the naturals" well defined rather than merely
inhabited: `ofNat`/`toNat` are mutually inverse, `transport` carries any model
to any other, and it commutes with zero, successor and addition.

This is the classical half of the bootstrap.  The object-language half carves
the same subtype with `ax.sub`, and stops short of naming the carrier until
`ty.exists` elimination exists.
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

/-! ## Declaration/proof phase separation

The userspace init builder freezes public syntax before replaying proofs.  The
following semantic factorization records the corresponding trust boundary:
the declaration is data, while `CNatProof` is the evidence required to turn
that data into a model.  Neither structure says anything about the untrusted
source language which happened to construct the declaration. -/

/-- The data of a natural-number candidate, without any laws. -/
structure CNatDecl where
  carrier : Type
  zero : carrier
  succ : carrier → carrier

/-- The Peano evidence certifying one fixed natural-number declaration. -/
structure CNatProof (D : CNatDecl) : Prop where
  succ_injective : ∀ x y, D.succ x = D.succ y → x = y
  succ_ne_zero : ∀ x, D.succ x ≠ D.zero
  induction : ∀ P : D.carrier → Prop,
    P D.zero → (∀ x, P x → P (D.succ x)) → ∀ x, P x

/-- Forget the proofs while retaining exactly the declared data. -/
def CNatModel.declaration (M : CNatModel) : CNatDecl where
  carrier := M.carrier
  zero := M.zero
  succ := M.succ

/-- Project a model's evidence as a proof of its exact declaration. -/
theorem CNatModel.proof (M : CNatModel) : CNatProof M.declaration := by
  exact {
    succ_injective := M.succ_injective
    succ_ne_zero := M.succ_ne_zero
    induction := M.induction
  }

/-- Checked evidence reconstructs a model; declaration data alone does not. -/
def CNatDecl.certify (D : CNatDecl) (proof : CNatProof D) : CNatModel where
  carrier := D.carrier
  zero := D.zero
  succ := D.succ
  succ_injective := proof.succ_injective
  succ_ne_zero := proof.succ_ne_zero
  induction := proof.induction

@[simp] theorem CNatModel.certify_declaration (M : CNatModel) :
    M.declaration.certify M.proof = M := by
  cases M
  rfl

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

/-- Non-surjectivity *supplies* a missed point; it does not merely assert one
exists somewhere. -/
theorem exists_missed_of_not_surjective {A : CPointed} {next : A.carrier → A.carrier}
    (nonsurjective : ¬ Function.Surjective next) : ∃ z, ∀ x, next x ≠ z :=
  Classical.byContradiction fun none_missed =>
    nonsurjective fun target =>
      Classical.byContradiction fun unhit =>
        none_missed ⟨target, fun x hit => unhit ⟨x, hit⟩⟩

/-- An injective endomap that is not surjective is a Dedekind-infinite
structure, with the missed point chosen from the failure of surjectivity. -/
noncomputable def CInfinityStructure.ofInjectiveNotSurjective {A : CPointed}
    (next : A.carrier → A.carrier) (injective : Function.Injective next)
    (nonsurjective : ¬ Function.Surjective next) : CInfinityStructure A where
  next := next
  missed := Classical.choose (exists_missed_of_not_surjective nonsurjective)
  reflectsEquality := fun _ _ => ⟨fun images => injective images, fun equal => equal ▸ rfl⟩
  misses := Classical.choose_spec (exists_missed_of_not_surjective nonsurjective)

/-- **A model of the naturals can be extracted from any injective endomap that
is not surjective.**

Not merely "exists": `natModel` is the extraction, and this is it applied to
the structure non-surjectivity hands over.  The carving is the whole content —
Dedekind-infinity says the carrier has room, and the theorem says the naturals
are the part of that room the map actually reaches. -/
noncomputable def natModelOfInjectiveNotSurjective {A : CPointed}
    (next : A.carrier → A.carrier) (injective : Function.Injective next)
    (nonsurjective : ¬ Function.Surjective next) : CNatModel :=
  (CInfinityStructure.ofInjectiveNotSurjective next injective nonsurjective).natModel

/-! ## The starting point has to be one the map misses

An injective non-surjective map and *some* distinguished point is not enough:
the point must be outside the map's image, which is what `misses` says and what
non-surjectivity supplies.  Starting anywhere else can land in a cycle, and
then the carved-out part is finite and `succ_ne_zero` fails. -/

namespace ArbitraryPoint

/-- Injective, not surjective, and carrying a two-element cycle. -/
def next : Nat ⊕ Bool → Nat ⊕ Bool
  | .inl index => .inl (index + 1)
  | .inr flag => .inr (!flag)

theorem next_injective : Function.Injective next := by
  rintro (m | a) (n | b) equality <;> simp_all [next]

theorem next_not_surjective : ¬ Function.Surjective next := by
  intro surjective
  obtain ⟨preimage, hit⟩ := surjective (.inl 0)
  cases preimage <;> simp [next] at hit

/-- Two steps from `inr true` returns to it.  So had the construction been
allowed to start there, `zero` would be the successor of something reachable —
no argument from injectivity or non-surjectivity can rescue it, because both
hold here. -/
theorem cycle : next (next (.inr true)) = .inr true := by decide

end ArbitraryPoint

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

/-! ## The impredicative recursion graph

This is the semantic counterpart of the opcode-free `NatRecGraph` schema.
It is the intersection of every relation containing the base pair and closed
under the recursive step.  The equivalence below is the model argument behind
the userspace graph construction and its Hilbert-choice selection. -/

def RecGraph {C : Type} (base : C) (step : M.carrier → C → C)
    (n : M.carrier) (value : C) : Prop :=
  ∀ relation : M.carrier → C → Prop,
    relation M.zero base →
    (∀ k z, relation k z → relation (M.succ k) (step k z)) →
    relation n value

theorem recGraph_base {C : Type} (base : C) (step : M.carrier → C → C) :
    M.RecGraph base step M.zero base := by
  intro relation atZero _
  exact atZero

theorem recGraph_step {C : Type} (base : C) (step : M.carrier → C → C)
    {n : M.carrier} {value : C} (holds : M.RecGraph base step n value) :
    M.RecGraph base step (M.succ n) (step n value) := by
  intro relation atZero atSucc
  exact atSucc n value (holds relation atZero atSucc)

theorem recGraph_natrec {C : Type} (base : C) (step : M.carrier → C → C)
    (n : M.carrier) : M.RecGraph base step n (M.natrec base step n) := by
  refine M.induction (fun n => M.RecGraph base step n (M.natrec base step n)) ?_ ?_ n
  · simpa using M.recGraph_base base step
  · intro k holds
    simpa using M.recGraph_step base step holds

theorem recGraph_iff {C : Type} (base : C) (step : M.carrier → C → C)
    (n : M.carrier) (value : C) :
    M.RecGraph base step n value ↔ value = M.natrec base step n := by
  constructor
  · intro holds
    exact holds (fun k z => z = M.natrec base step k) (by simp)
      (by intro k z equality; simp [equality])
  · rintro rfl
    exact M.recGraph_natrec base step n

theorem recGraph_total {C : Type} (base : C) (step : M.carrier → C → C)
    (n : M.carrier) : ∃ value, M.RecGraph base step n value :=
  ⟨M.natrec base step n, M.recGraph_natrec base step n⟩

theorem recGraph_functional {C : Type} (base : C) (step : M.carrier → C → C)
    {n : M.carrier} {left right : C}
    (leftHolds : M.RecGraph base step n left)
    (rightHolds : M.RecGraph base step n right) : left = right := by
  rw [M.recGraph_iff base step n left] at leftHolds
  rw [M.recGraph_iff base step n right] at rightHolds
  exact leftHolds.trans rightHolds.symm

noncomputable def graphRecursor {C : Type} (base : C)
    (step : M.carrier → C → C) (n : M.carrier) : C :=
  Classical.choose (M.recGraph_total base step n)

theorem graphRecursor_graph {C : Type} (base : C) (step : M.carrier → C → C)
    (n : M.carrier) : M.RecGraph base step n (M.graphRecursor base step n) :=
  Classical.choose_spec (M.recGraph_total base step n)

theorem graphRecursor_eq_natrec {C : Type} (base : C)
    (step : M.carrier → C → C) :
    M.graphRecursor base step = M.natrec base step := by
  funext n
  exact (M.recGraph_iff base step n (M.graphRecursor base step n)).mp
    (M.graphRecursor_graph base step n)

@[simp] theorem graphRecursor_zero {C : Type} (base : C)
    (step : M.carrier → C → C) :
    M.graphRecursor base step M.zero = base := by
  rw [M.graphRecursor_eq_natrec base step]
  exact M.natrec_zero base step

@[simp] theorem graphRecursor_succ {C : Type} (base : C)
    (step : M.carrier → C → C) (n : M.carrier) :
    M.graphRecursor base step (M.succ n) =
      step n (M.graphRecursor base step n) := by
  rw [M.graphRecursor_eq_natrec base step]
  exact M.natrec_succ base step n

theorem graphRecursor_unique {C : Type} (base : C)
    (step : M.carrier → C → C) (candidate : M.carrier → C)
    (atZero : candidate M.zero = base)
    (atSucc : ∀ n, candidate (M.succ n) = step n (candidate n)) :
    candidate = M.graphRecursor base step := by
  rw [M.graphRecursor_eq_natrec base step]
  exact M.natrec_unique base step candidate atZero atSucc

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

/-! ## The userspace init arithmetic package

The Rust package uses closed function-valued graph recursors, with the
recursive argument first.  These definitions mirror that construction rather
than merely restating the conventional operations above. -/

noncomputable def graphAdd (M : CNatModel) (n m : M.carrier) : M.carrier :=
  M.graphRecursor (fun value => value)
    (fun _ previous value => M.succ (previous value)) n m

@[simp] theorem graphAdd_zero (m : M.carrier) :
    M.graphAdd M.zero m = m := by
  simp [graphAdd]

@[simp] theorem graphAdd_succ (n m : M.carrier) :
    M.graphAdd (M.succ n) m = M.succ (M.graphAdd n m) := by
  simp [graphAdd]

theorem graphAdd_eq_add (n m : M.carrier) :
    M.graphAdd n m = M.add m n := by
  refine M.induction (fun n => M.graphAdd n m = M.add m n) ?_ ?_ n
  · simp
  · intro k ih
    simp [ih]

noncomputable def graphMul (M : CNatModel) (n m : M.carrier) : M.carrier :=
  M.graphRecursor (fun _ => M.zero)
    (fun _ previous value => M.graphAdd (previous value) value) n m

@[simp] theorem graphMul_zero (m : M.carrier) :
    M.graphMul M.zero m = M.zero := by
  simp [graphMul]

@[simp] theorem graphMul_succ (n m : M.carrier) :
    M.graphMul (M.succ n) m = M.graphAdd (M.graphMul n m) m := by
  simp [graphMul]

theorem graphMul_eq_mul (n m : M.carrier) :
    M.graphMul n m = M.mul m n := by
  refine M.induction (fun n => M.graphMul n m = M.mul m n) ?_ ?_ n
  · simp
  · intro k ih
    rw [M.graphMul_succ, M.graphAdd_eq_add, ih, M.mul_succ]
    exact M.add_comm m (M.mul m k)

def one (M : CNatModel) : M.carrier := M.succ M.zero

def two (M : CNatModel) : M.carrier := M.succ M.one

theorem graphAdd_one_one : M.graphAdd M.one M.one = M.two := by
  simp [one, two]

/-! ## Any two models are the same model

Categoricity within a model (`ofNat_toNat_inverse`) immediately gives it
between models, which is what licenses the definite article: *the* naturals. -/

/-- Read an element of one model as an element of another. -/
noncomputable def transport (M N : CNatModel) (x : M.carrier) : N.carrier :=
  N.ofNat (M.toNat x)

@[simp] theorem transport_zero (M N : CNatModel) :
    transport M N M.zero = N.zero := by
  simp [transport]

@[simp] theorem transport_succ (M N : CNatModel) (x : M.carrier) :
    transport M N (M.succ x) = N.succ (transport M N x) := by
  simp [transport]

@[simp] theorem transport_transport (M N : CNatModel) (x : M.carrier) :
    transport N M (transport M N x) = x := by
  simp [transport]

/-- Transport is a homomorphism for addition, so the arithmetic does not depend
on which model it was done in. -/
theorem transport_add (M N : CNatModel) (x y : M.carrier) :
    transport M N (M.add x y) = N.add (transport M N x) (transport M N y) := by
  refine M.induction
    (fun y => transport M N (M.add x y) = N.add (transport M N x) (transport M N y)) ?_ ?_ y
  · simp
  · intro z ih
    simp [ih]

end CNatModel

end Nucleus.HolE.Infinity
