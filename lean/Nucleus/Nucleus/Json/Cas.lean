import Nucleus.Json.Extensional

/-!
# Gas-bounded dereferencing of JSON content-addressed stores

A `JsonCas Scalar Name` is a finite partial map from names to JSON trees whose
scalar positions contain either an ordinary scalar or a link to another name.
Dereferencing is bounded by gas: each store lookup consumes one unit, while
walking the JSON container structure is free.
-/

namespace Nucleus

universe u

/-- A scalar value or a link to another object in a store. -/
abbrev Link (Scalar : Type u) (Name : Type) := Scalar ⊕ Name

/-- Epistemically partial information. `unknown` is a bottom element and is
deliberately distinct from `Option`, which remains available for data-level
nullability (including JSON `null`). -/
inductive Unknown (α : Type u) where
  | unknown
  | known (value : α)
  deriving DecidableEq, Repr

namespace Unknown

def isKnown : Unknown α → Bool
  | .unknown => false
  | .known _ => true

def get : (x : Unknown α) → x.isKnown → α
  | .known value, _ => value

def bind (x : Unknown α) (f : α → Unknown β) : Unknown β :=
  match x with
  | .unknown => .unknown
  | .known value => f value

end Unknown

/-- A more fine-grained alternative result type, retaining known container
structure and marking unknown scalar positions with `.unknown`. -/
abbrev PartialJson (Scalar : Type u) := Json (Unknown Scalar)

namespace PartialJson

/-- The convention for a wholly unknown subtree in the partial-tree variant. -/
def unknown {Scalar : Type u} : PartialJson Scalar := .scalar .unknown

end PartialJson

namespace Unknown

/-- The flat information order: `.unknown` is unknown and hence below every value;
known values are comparable only when equal. -/
def Le {α : Type u} (x y : Unknown α) : Prop := x = .unknown ∨ x = y

@[refl] theorem le_refl {α : Type u} (x : Unknown α) : Le x x := Or.inr rfl

theorem unknown_le {α : Type u} (x : Unknown α) : Le .unknown x := Or.inl rfl

theorem known_le_iff {α : Type u} {x : α} {y : Unknown α} :
    Le (.known x) y ↔ y = .known x := by
  simp [Le, eq_comm]

theorem le_trans {α : Type u} {x y z : Unknown α} : Le x y → Le y z → Le x z := by
  rintro (rfl | rfl) h
  · exact unknown_le z
  · exact h

theorem le_antisymm {α : Type u} {x y : Unknown α} : Le x y → Le y x → x = y := by
  rintro (rfl | rfl) h
  · rcases h with h | h
    · exact h.symm
    · exact h.symm
  · rfl

theorem isKnown_of_le {α : Type u} {x y : Unknown α} (hxy : Le x y)
    (hx : x.isKnown) : y.isKnown := by
  rcases hxy with rfl | rfl
  · simp [isKnown] at hx
  · exact hx

theorem get_eq_get_of_le {α : Type u} {x y : Unknown α} (hxy : Le x y)
    (hx : x.isKnown) (hy : y.isKnown) : x.get hx = y.get hy := by
  rcases hxy with rfl | rfl
  · simp [isKnown] at hx
  · rfl

end Unknown

/-- A finite content-addressed store. The `Finset` presentation gives a
proof-friendly finite domain while `get?` exposes the usual partial-map API. -/
structure JsonCas (Scalar : Type u) (Name : Type) where
  names : Finset Name
  values : {name // name ∈ names} → Json (Link Scalar Name)

namespace JsonCas

variable {Scalar : Type u} {Name : Type} [DecidableEq Name]

/-- Look up an encoded object by name. -/
def get? (cas : JsonCas Scalar Name) (name : Name) :
    Unknown (Json (Link Scalar Name)) :=
  if h : name ∈ cas.names then .known (cas.values ⟨name, h⟩) else .unknown

/-- Dereference every link in a JSON tree using `resolve`. Container shape and
object keys are preserved; failure of any scalar position makes the result
unknown. -/
def derefWith (resolve : Name → Unknown (Json Scalar)) :
    Json (Link Scalar Name) → Unknown (Json Scalar)
  | .scalar (.inl value) => .known (.scalar value)
  | .scalar (.inr name) => resolve name
  | .list n elems =>
      if h : ∀ i, (derefWith resolve (elems i)).isKnown then
        .known (.list n fun i => (derefWith resolve (elems i)).get (h i))
      else .unknown
  | .map keys vals =>
      if h : ∀ k, (derefWith resolve (vals k)).isKnown then
        .known (.map keys fun k => (derefWith resolve (vals k)).get (h k))
      else .unknown

/-- Fetch and fully dereference a named object, consuming one unit of gas for
each followed store entry. -/
def fetch (cas : JsonCas Scalar Name) : Nat → Name → Unknown (Json Scalar)
  | 0, _ => .unknown
  | gas + 1, name => (cas.get? name).bind (derefWith (cas.fetch gas))

/-- The induced partial dereference function at a fixed gas bound. -/
def dereference (cas : JsonCas Scalar Name) (gas : Nat) :
    Name → Unknown (Json Scalar) := cas.fetch gas

/-! ## Partial-tree variant

`fetchPartial` explores the alternative `Json (Unknown Scalar)` encoding. It
preserves container structure even when one link cannot be resolved, using
`.scalar .unknown` for an unknown subtree. This is strictly more fine-grained than
the primary all-or-nothing `Unknown (Json Scalar)` result, so it is exposed as
a separate operation rather than silently changing `fetch` semantics.
-/

/-- Dereference into a partially known JSON tree. -/
def derefPartialWith (resolve : Name → PartialJson Scalar) :
    Json (Link Scalar Name) → PartialJson Scalar
  | .scalar (.inl value) => .scalar (.known value)
  | .scalar (.inr name) => resolve name
  | .list n elems => .list n fun i => derefPartialWith resolve (elems i)
  | .map keys vals => .map keys fun k => derefPartialWith resolve (vals k)

/-- Gas-bounded fetching that retains partial container information. -/
def fetchPartial (cas : JsonCas Scalar Name) : Nat → Name → PartialJson Scalar
  | 0, _ => PartialJson.unknown
  | gas + 1, name =>
      match cas.get? name with
      | .unknown => PartialJson.unknown
      | .known value => derefPartialWith (cas.fetchPartial gas) value

/-- Pointwise extension in the flat information order. Existing entries may
not change, but previously absent names may become known. -/
def InformationLe (a b : JsonCas Scalar Name) : Prop :=
  ∀ name, Unknown.Le (a.get? name) (b.get? name)

instance : LE (JsonCas Scalar Name) := ⟨InformationLe⟩

theorem informationLe_def {a b : JsonCas Scalar Name} :
    a ≤ b ↔ ∀ name, Unknown.Le (a.get? name) (b.get? name) := Iff.rfl

/-- A finite store is determined extensionally by lookup. -/
theorem ext_get? {a b : JsonCas Scalar Name}
    (h : ∀ name, a.get? name = b.get? name) : a = b := by
  have hnames : a.names = b.names := Finset.ext fun name => by
    constructor
    · intro ha
      by_contra hb
      simpa [get?, ha, hb] using h name
    · intro hb
      by_contra ha
      simpa [get?, ha, hb] using h name
  cases a with
  | mk namesA valuesA =>
      cases b with
      | mk namesB valuesB =>
          simp only at hnames
          subst namesB
          congr 1
          funext name
          have heq := h name.1
          simpa [get?, name.2] using heq

instance : PartialOrder (JsonCas Scalar Name) where
  le_refl _ _ := Unknown.le_refl _
  le_trans _ _ _ hab hbc name := Unknown.le_trans (hab name) (hbc name)
  le_antisymm a b hab hba := ext_get? fun name =>
    Unknown.le_antisymm (hab name) (hba name)

omit [DecidableEq Name] in
theorem derefWith_mono {resolve₁ resolve₂ : Name → Unknown (Json Scalar)}
    (hresolve : ∀ name, Unknown.Le (resolve₁ name) (resolve₂ name)) :
    ∀ j, Unknown.Le (derefWith resolve₁ j) (derefWith resolve₂ j) := by
  intro j
  induction j with
  | scalar link =>
      cases link with
      | inl value => exact Unknown.le_refl _
      | inr name => exact hresolve name
  | list n elems ih =>
      unfold derefWith
      split <;> rename_i h₁
      · have h₂ : ∀ i, (derefWith resolve₂ (elems i)).isKnown := by
          intro i
          exact Unknown.isKnown_of_le (ih i) (h₁ i)
        rw [dif_pos h₂, Unknown.known_le_iff]
        congr 2
        funext i
        exact (Unknown.get_eq_get_of_le (ih i) (h₁ i) (h₂ i)).symm
      · exact Unknown.unknown_le _
  | map keys vals ih =>
      unfold derefWith
      split <;> rename_i h₁
      · have h₂ : ∀ k, (derefWith resolve₂ (vals k)).isKnown := by
          intro k
          exact Unknown.isKnown_of_le (ih k) (h₁ k)
        rw [dif_pos h₂, Unknown.known_le_iff]
        congr 2
        funext k
        exact (Unknown.get_eq_get_of_le (ih k) (h₁ k) (h₂ k)).symm
      · exact Unknown.unknown_le _

/-- Fetching is monotone in the store information order. -/
theorem fetch_mono {a b : JsonCas Scalar Name} (hab : a ≤ b) :
    ∀ gas name, Unknown.Le (a.fetch gas name) (b.fetch gas name) := by
  intro gas
  induction gas with
  | zero => intro name; exact Unknown.unknown_le _
  | succ gas ih =>
      intro name
      unfold fetch
      rcases hab name with hnone | heq
      · simp [hnone, Unknown.Le, Unknown.bind]
      · rw [heq]
        cases h : b.get? name with
        | unknown => simp [Unknown.Le, Unknown.bind]
        | known value =>
            simp only [Unknown.bind]
            exact derefWith_mono ih value

/-- Consequently, the induced functions are pointwise monotone. -/
theorem dereference_mono {a b : JsonCas Scalar Name} (hab : a ≤ b) (gas : Nat) :
    ∀ name, Unknown.Le (a.dereference gas name) (b.dereference gas name) :=
  fetch_mono hab gas

/-- Increasing the gas bound can only reveal more information. -/
theorem fetch_succ_mono (cas : JsonCas Scalar Name) :
    ∀ gas name, Unknown.Le (cas.fetch gas name) (cas.fetch (gas + 1) name) := by
  intro gas
  induction gas with
  | zero => intro name; exact Unknown.unknown_le _
  | succ gas ih =>
      intro name
      unfold fetch
      cases h : cas.get? name with
      | unknown => simp [Unknown.Le, Unknown.bind]
      | known value =>
          simp only [Unknown.bind]
          exact derefWith_mono ih value

/-- Fetching is monotone as a function of gas. -/
theorem fetch_gas_mono (cas : JsonCas Scalar Name) {gas₁ gas₂ : Nat}
    (hgas : gas₁ ≤ gas₂) (name : Name) :
    Unknown.Le (cas.fetch gas₁ name) (cas.fetch gas₂ name) := by
  induction gas₂, hgas using Nat.le_induction with
  | base => exact Unknown.le_refl _
  | succ gas₂ _ ih =>
      exact Unknown.le_trans ih (fetch_succ_mono cas gas₂ name)

/-- The induced dereference functions are pointwise monotone in gas. -/
theorem dereference_gas_mono (cas : JsonCas Scalar Name) {gas₁ gas₂ : Nat}
    (hgas : gas₁ ≤ gas₂) :
    ∀ name, Unknown.Le (cas.dereference gas₁ name) (cas.dereference gas₂ name) :=
  fun name => fetch_gas_mono cas hgas name

omit [DecidableEq Name] in
/-- Dereferencing depends only on the resolver values for links that actually
occur in the input tree. -/
theorem derefWith_congr {resolve₁ resolve₂ : Name → Unknown (Json Scalar)} :
    ∀ j : Json (Link Scalar Name),
      (∀ name, Sum.inr name ∈ j.scalars → resolve₁ name = resolve₂ name) →
      derefWith resolve₁ j = derefWith resolve₂ j := by
  intro j
  induction j with
  | scalar link =>
      cases link with
      | inl value => simp [derefWith]
      | inr name => intro h; exact h name (by simp [Json.scalars])
  | list n elems ih =>
      intro h
      have heq : ∀ i, derefWith resolve₁ (elems i) = derefWith resolve₂ (elems i) := by
        intro i
        apply ih i
        intro name hname
        apply h name
        simp only [Json.scalars, Multiset.mem_sum]
        exact ⟨i, by simp, hname⟩
      simp only [derefWith]
      simp_rw [heq]
  | map keys vals ih =>
      intro h
      have heq : ∀ k, derefWith resolve₁ (vals k) = derefWith resolve₂ (vals k) := by
        intro k
        apply ih k
        intro name hname
        apply h name
        simp only [Json.scalars, Multiset.mem_sum]
        exact ⟨k, by simp, hname⟩
      simp only [derefWith]
      simp_rw [heq]

/-- A linked name occurring in the stored value at `parent`. -/
def DependsOn (cas : JsonCas Scalar Name) (child parent : Name) : Prop :=
  ∃ value, cas.get? parent = .known value ∧ Sum.inr child ∈ value.scalars

/-- A finite CAS equipped with a decreasing rank for every link. This is a
constructive acyclicity certificate and records a dereference-depth bound. -/
structure Acyclic extends JsonCas Scalar Name where
  rank : Name → Nat
  decreases : ∀ {child parent}, toJsonCas.DependsOn child parent → rank child < rank parent

namespace Acyclic

variable (cas : JsonCas.Acyclic (Scalar := Scalar) (Name := Name))

/-- A finite acyclic store has a global maximum dereference depth. -/
theorem exists_maximumDereferenceDepth :
    ∃ depth, ∀ name ∈ cas.names, cas.rank name < depth := by
  refine ⟨cas.names.sup cas.rank + 1, ?_⟩
  intro name hname
  exact Nat.lt_succ_of_le (Finset.le_sup (f := cas.rank) hname)

/-- Once the gas exceeds a name's acyclic rank, adding more gas cannot change
the dereferenced result. -/
theorem fetch_stable_of_rank : ∀ name gas extra,
    cas.rank name < gas →
    cas.toJsonCas.fetch gas name = cas.toJsonCas.fetch (gas + extra) name := by
  intro name
  induction hrank : cas.rank name using Nat.strong_induction_on generalizing name with
  | h _rank ih =>
      intro gas extra hgas
      subst hrank
      cases gas with
      | zero => omega
      | succ fuel =>
          rw [Nat.succ_add]
          simp only [fetch]
          cases hlookup : cas.toJsonCas.get? name with
          | unknown => simp [Unknown.bind]
          | known value =>
              simp only [Unknown.bind]
              apply derefWith_congr
              intro child hchild
              have hdep : cas.toJsonCas.DependsOn child name :=
                ⟨value, hlookup, hchild⟩
              have hdecrease : cas.rank child < cas.rank name := cas.decreases hdep
              have hchildFuel : cas.rank child < fuel := by omega
              simpa [Nat.succ_add] using
                ih (cas.rank child) hdecrease child rfl fuel extra hchildFuel

/-- The maximum rank is a global gas bound after which the entire induced
dereference function is stable. -/
theorem dereference_stable_at_maximum :
    ∃ depth, ∀ extra name,
      cas.toJsonCas.dereference depth name =
        cas.toJsonCas.dereference (depth + extra) name := by
  refine ⟨cas.names.sup cas.rank + 1, ?_⟩
  intro extra name
  by_cases hname : name ∈ cas.names
  · apply fetch_stable_of_rank cas
    exact Nat.lt_succ_of_le (Finset.le_sup (f := cas.rank) hname)
  · rw [Nat.succ_add]
    simp [dereference, fetch, get?, hname, Unknown.bind]

end Acyclic

end JsonCas

end Nucleus
