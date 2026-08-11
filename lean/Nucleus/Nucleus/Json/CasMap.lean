import Nucleus.Json.Cas

/-!
# Partial mapping of dereferenced CAS values

A partial scalar map returns `Unknown.unknown` when it cannot interpret an
input. For parsing, this deliberately identifies invalid input with absent
knowledge: failure means only “I do not know how to parse that”.
-/

namespace Nucleus

universe u

namespace Unknown

theorem bind_mono {α β : Type u} {x y : Unknown α}
    {f g : α → Unknown β} (hxy : Le x y) (hfg : ∀ value, Le (f value) (g value)) :
    Le (x.bind f) (y.bind g) := by
  rcases hxy with hx | hxy
  · subst x
    exact unknown_le _
  · subst y
    cases x with
    | unknown => exact unknown_le _
    | known value => exact hfg value

@[simp] theorem bind_unknown {α β : Type u} (f : α → Unknown β) :
    (Unknown.unknown : Unknown α).bind f = .unknown := rfl

@[simp] theorem bind_known {α β : Type u} (value : α) (f : α → Unknown β) :
    (Unknown.known value).bind f = f value := rfl

theorem bind_assoc {α β γ : Type u} (x : Unknown α)
    (f : α → Unknown β) (g : β → Unknown γ) :
    (x.bind f).bind g = x.bind fun value => (f value).bind g := by
  cases x <;> rfl

@[simp] theorem get_known {α : Type u} (value : α)
    (h : (Unknown.known value).isKnown) : (Unknown.known value).get h = value := rfl

end Unknown

namespace Json

/-- Map scalar leaves with a partial function. Failure at any leaf makes the
whole result unknown, matching `JsonCas.fetch`'s all-or-nothing result. -/
def mapScalarPartial {Scalar Target : Type u}
    (f : Scalar → Unknown Target) : Json Scalar → Unknown (Json Target)
  | .scalar value => (f value).bind fun mapped => .known (.scalar mapped)
  | .list n elems =>
      if h : ∀ i, (mapScalarPartial f (elems i)).isKnown then
        .known (.list n fun i => (mapScalarPartial f (elems i)).get (h i))
      else .unknown
  | .map keys vals =>
      if h : ∀ k, (mapScalarPartial f (vals k)).isKnown then
        .known (.map keys fun k => (mapScalarPartial f (vals k)).get (h k))
      else .unknown

/-- Partial scalar mapping is monotone in the information supplied by the
scalar function. -/
theorem mapScalarPartial_mono {Scalar Target : Type u}
    {f g : Scalar → Unknown Target} (hfg : ∀ value, Unknown.Le (f value) (g value)) :
    ∀ j, Unknown.Le (mapScalarPartial f j) (mapScalarPartial g j) := by
  intro j
  induction j with
  | scalar value =>
      exact Unknown.bind_mono (hfg value) fun mapped => Unknown.le_refl _
  | list n elems ih =>
      unfold mapScalarPartial
      split <;> rename_i h₁
      · have h₂ : ∀ i, (mapScalarPartial g (elems i)).isKnown := fun i =>
          Unknown.isKnown_of_le (ih i) (h₁ i)
        rw [dif_pos h₂, Unknown.known_le_iff]
        congr 2
        funext i
        exact (Unknown.get_eq_get_of_le (ih i) (h₁ i) (h₂ i)).symm
      · exact Unknown.unknown_le _
  | map keys vals ih =>
      unfold mapScalarPartial
      split <;> rename_i h₁
      · have h₂ : ∀ k, (mapScalarPartial g (vals k)).isKnown := fun k =>
          Unknown.isKnown_of_le (ih k) (h₁ k)
        rw [dif_pos h₂, Unknown.known_le_iff]
        congr 2
        funext k
        exact (Unknown.get_eq_get_of_le (ih k) (h₁ k) (h₂ k)).symm
      · exact Unknown.unknown_le _

/-- A total scalar map is the ordinary `Json.mapScalar`, wrapped as known. -/
theorem mapScalarPartial_total {Scalar Target : Type u} (f : Scalar → Target) :
    ∀ j, mapScalarPartial (fun value => .known (f value)) j = .known (j.mapScalar f) := by
  intro j
  induction j with
  | scalar value => rfl
  | list n elems ih =>
      simp only [mapScalarPartial]
      rw [dif_pos fun i => by simp [ih i, Unknown.isKnown]]
      congr 2
      funext i
      simp [ih i]
  | map keys vals ih =>
      simp only [mapScalarPartial]
      rw [dif_pos fun k => by simp [ih k, Unknown.isKnown]]
      congr 2
      funext k
      simp [ih k]

end Json

namespace JsonCas

variable {Scalar Target : Type u} {Name : Type} [DecidableEq Name]

/-- Fetch a value and partially interpret each scalar. Invalid input is
reported as unknown information. -/
def mapFetch (cas : JsonCas Scalar Name) (parse : Scalar → Unknown Target)
    (gas : Nat) (name : Name) : Unknown (Json Target) :=
  (cas.fetch gas name).bind (Json.mapScalarPartial parse)

/-- The induced partially mapped dereference function. -/
def mapDereference (cas : JsonCas Scalar Name) (parse : Scalar → Unknown Target)
    (gas : Nat) : Name → Unknown (Json Target) := cas.mapFetch parse gas

theorem mapFetch_mono {a b : JsonCas Scalar Name} {parse₁ parse₂ : Scalar → Unknown Target}
    (hab : a ≤ b) (hparse : ∀ value, Unknown.Le (parse₁ value) (parse₂ value)) :
    ∀ gas name, Unknown.Le (a.mapFetch parse₁ gas name) (b.mapFetch parse₂ gas name) := by
  intro gas name
  exact Unknown.bind_mono (fetch_mono hab gas name)
    (fun value => Json.mapScalarPartial_mono hparse value)

theorem mapDereference_mono {a b : JsonCas Scalar Name}
    {parse₁ parse₂ : Scalar → Unknown Target} (hab : a ≤ b)
    (hparse : ∀ value, Unknown.Le (parse₁ value) (parse₂ value)) (gas : Nat) :
    ∀ name, Unknown.Le (a.mapDereference parse₁ gas name)
      (b.mapDereference parse₂ gas name) :=
  mapFetch_mono hab hparse gas

theorem mapFetch_gas_mono (cas : JsonCas Scalar Name)
    (parse : Scalar → Unknown Target) {gas₁ gas₂ : Nat} (hgas : gas₁ ≤ gas₂) (name : Name) :
    Unknown.Le (cas.mapFetch parse gas₁ name) (cas.mapFetch parse gas₂ name) :=
  Unknown.bind_mono (fetch_gas_mono cas hgas name)
    (fun value => Unknown.le_refl (Json.mapScalarPartial parse value))

end JsonCas

end Nucleus
