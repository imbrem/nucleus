import Nucleus.Json.CasMap

/-!
# CAS entries with non-JSON targets

A heterogeneous store entry is either linked JSON or an opaque value `α`.
Opaque entries become scalar leaves in the resolved tree, so the two result
surfaces are exactly `Unknown (Json (Link Scalar α))` and
`Json (Unknown (Link Scalar α))`.  The existing gas, information-order, and
acyclic theory is reused by compiling this store to `JsonCas`.
-/

namespace Nucleus

universe u

/-- A finite CAS whose entries can be linked JSON blocks or opaque values. -/
structure HeterogeneousJsonCas (Scalar : Type u) (Name : Type) (α : Type) where
  names : Finset Name
  values : {name // name ∈ names} → Json (Link Scalar Name) ⊕ α

namespace HeterogeneousJsonCas

variable {Scalar : Type u} {Name : Type} {α : Type} [DecidableEq Name]

private def widenLink : Link Scalar Name → Link (Link Scalar α) Name
  | .inl scalar => .inl (.inl scalar)
  | .inr name => .inr name

/-- Compile heterogeneous entries to an ordinary JSON CAS. An opaque entry is
represented by a one-leaf JSON tree containing the right injection. -/
def toJsonCas (cas : HeterogeneousJsonCas Scalar Name α) :
    JsonCas (Link Scalar α) Name where
  names := cas.names
  values name := match cas.values name with
    | .inl json => json.mapScalar widenLink
    | .inr other => .scalar (.inl (.inr other))

/-- All-or-nothing gas-bounded resolution. A successfully resolved leaf is
either an ordinary JSON scalar or an opaque non-JSON target. -/
def fetch (cas : HeterogeneousJsonCas Scalar Name α) (gas : Nat) (name : Name) :
    Unknown (Json (Link Scalar α)) := cas.toJsonCas.fetch gas name

/-- The induced name-indexed resolver at fixed gas. -/
def dereference (cas : HeterogeneousJsonCas Scalar Name α) (gas : Nat) :
    Name → Unknown (Json (Link Scalar α)) := cas.fetch gas

/-- Fine-grained resolution retaining known container structure around
unknown leaves. -/
def fetchPartial (cas : HeterogeneousJsonCas Scalar Name α) (gas : Nat) (name : Name) :
    Json (Unknown (Link Scalar α)) := cas.toJsonCas.fetchPartial gas name

/-- Information order inherited from the compiled ordinary JSON CAS. -/
def InformationLe (a b : HeterogeneousJsonCas Scalar Name α) : Prop :=
  a.toJsonCas ≤ b.toJsonCas

instance : LE (HeterogeneousJsonCas Scalar Name α) := ⟨InformationLe⟩

/-- Heterogeneous resolution is monotone as store information grows. -/
theorem fetch_mono {a b : HeterogeneousJsonCas Scalar Name α} (hab : a ≤ b)
    (gas : Nat) (name : Name) :
    Unknown.Le (a.fetch gas name) (b.fetch gas name) :=
  JsonCas.fetch_mono hab gas name

/-- Heterogeneous resolution is monotone in the gas bound. -/
theorem fetch_gas_mono (cas : HeterogeneousJsonCas Scalar Name α)
    {gas₁ gas₂ : Nat} (hgas : gas₁ ≤ gas₂) (name : Name) :
    Unknown.Le (cas.fetch gas₁ name) (cas.fetch gas₂ name) :=
  JsonCas.fetch_gas_mono cas.toJsonCas hgas name

/-! ## Composition

Composition exposes two gas caps because they measure different traversals:
`outerGas` bounds names in the first store and `innerGas` bounds each opaque
name handed to the second store. A shared cap is also provided. Treating a
single *additive* budget by choosing a split is intentionally left explicit:
moving gas from one side to the other is not monotone in general.
-/

/-- Resolve an outer `Name → JSON-or-β` store and then resolve every resulting
`β` leaf through an inner `β → JSON-or-γ` store. -/
private def liftIntermediate {β γ : Type} : Link Scalar β → Link (Link Scalar γ) β
  | .inl scalar => .inl (.inl scalar)
  | .inr target => .inr target

def composeFetch {β γ : Type} [DecidableEq β]
    (outer : HeterogeneousJsonCas Scalar Name β)
    (inner : HeterogeneousJsonCas Scalar β γ)
  (outerGas innerGas : Nat) (name : Name) :
    Unknown (Json (Link Scalar γ)) :=
  (outer.fetch outerGas name).bind
    (fun json => JsonCas.derefWith (inner.fetch innerGas)
      (json.mapScalar liftIntermediate))

/-- Pointwise composition at fixed independent caps. -/
def composeDereference {β γ : Type} [DecidableEq β]
    (outer : HeterogeneousJsonCas Scalar Name β)
    (inner : HeterogeneousJsonCas Scalar β γ)
    (outerGas innerGas : Nat) : Name → Unknown (Json (Link Scalar γ)) :=
  composeFetch outer inner outerGas innerGas

/-- The common policy giving both stages the same maximum depth. This is a
per-stage cap, not an additive global resource bound. -/
def composeFetchShared {β γ : Type} [DecidableEq β]
    (outer : HeterogeneousJsonCas Scalar Name β)
    (inner : HeterogeneousJsonCas Scalar β γ)
    (gas : Nat) (name : Name) : Unknown (Json (Link Scalar γ)) :=
  composeFetch outer inner gas gas name

/-- Increasing the outer cap can only reveal more composed information. -/
theorem composeFetch_mono_outerGas {β γ : Type} [DecidableEq β]
    (outer : HeterogeneousJsonCas Scalar Name β)
    (inner : HeterogeneousJsonCas Scalar β γ)
    {gas₁ gas₂ innerGas : Nat} (hgas : gas₁ ≤ gas₂) (name : Name) :
    Unknown.Le (composeFetch outer inner gas₁ innerGas name)
      (composeFetch outer inner gas₂ innerGas name) :=
  Unknown.bind_mono (fetch_gas_mono outer hgas name)
    (fun _ => Unknown.le_refl _)

/-- Increasing the inner cap can only reveal more composed information. -/
theorem composeFetch_mono_innerGas {β γ : Type} [DecidableEq β]
    (outer : HeterogeneousJsonCas Scalar Name β)
    (inner : HeterogeneousJsonCas Scalar β γ)
    {outerGas gas₁ gas₂ : Nat} (hgas : gas₁ ≤ gas₂) (name : Name) :
    Unknown.Le (composeFetch outer inner outerGas gas₁ name)
      (composeFetch outer inner outerGas gas₂ name) :=
  Unknown.bind_mono (Unknown.le_refl _) fun json =>
    JsonCas.derefWith_mono (fun target => fetch_gas_mono inner hgas target)
      (json.mapScalar liftIntermediate)

/-- Independent caps bounded by a shared cap reveal no more information than
giving that shared cap to both stages. -/
theorem composeFetch_le_shared {β γ : Type} [DecidableEq β]
    (outer : HeterogeneousJsonCas Scalar Name β)
    (inner : HeterogeneousJsonCas Scalar β γ)
    {outerGas innerGas sharedGas : Nat}
    (houter : outerGas ≤ sharedGas) (hinner : innerGas ≤ sharedGas)
    (name : Name) :
    Unknown.Le (composeFetch outer inner outerGas innerGas name)
      (composeFetchShared outer inner sharedGas name) :=
  Unknown.le_trans
    (composeFetch_mono_outerGas outer inner houter name)
    (composeFetch_mono_innerGas outer inner hinner name)

private def composePartialWith {β γ : Type}
    (resolve : β → Json (Unknown (Link Scalar γ))) :
    Json (Unknown (Link Scalar β)) → Json (Unknown (Link Scalar γ))
  | .scalar .unknown => .scalar .unknown
  | .scalar (.known (.inl scalar)) => .scalar (.known (.inl scalar))
  | .scalar (.known (.inr target)) => resolve target
  | .list n elems => .list n fun i => composePartialWith resolve (elems i)
  | .map keys vals => .map keys fun k => composePartialWith resolve (vals k)

/-- Fine-grained composition preserves outer container structure and delegates
known `β` leaves to the inner partial resolver. -/
def composeFetchPartial {β γ : Type} [DecidableEq β]
    (outer : HeterogeneousJsonCas Scalar Name β)
    (inner : HeterogeneousJsonCas Scalar β γ)
    (outerGas innerGas : Nat) (name : Name) :
    Json (Unknown (Link Scalar γ)) :=
  composePartialWith (inner.fetchPartial innerGas) (outer.fetchPartial outerGas name)

/-- Embed an ordinary JSON-only CAS as a heterogeneous store with no opaque
entries. -/
def ofJsonCas (cas : JsonCas Scalar Name) : HeterogeneousJsonCas Scalar Name α where
  names := cas.names
  values name := .inl (cas.values name)

/-- Eliminate the impossible alternative from a result whose opaque type is
empty. -/
def eliminateEmpty : Json (Link Scalar Empty) → Json Scalar :=
  Json.mapScalar (Sum.elim id Empty.elim)

/-- Eliminate an impossible opaque alternative under epistemic partiality. -/
def eliminateEmptyUnknown : Unknown (Json (Link Scalar Empty)) → Unknown (Json Scalar)
  | .unknown => .unknown
  | .known json => .known (eliminateEmpty json)

@[simp] theorem eliminateEmpty_scalar_left (scalar : Scalar) :
    eliminateEmpty (.scalar (.inl scalar)) = .scalar scalar := rfl

@[simp] theorem eliminateEmptyUnknown_isKnown
    (value : Unknown (Json (Link Scalar Empty))) :
    (eliminateEmptyUnknown value).isKnown = value.isKnown := by
  cases value <;> rfl

theorem eliminateEmptyUnknown_get
    (value : Unknown (Json (Link Scalar Empty))) (h : value.isKnown) :
    (eliminateEmptyUnknown value).get (by simpa using h) =
      eliminateEmpty (value.get h) := by
  cases value with
  | unknown => simp [Unknown.isKnown] at h
  | known value => rfl

omit [DecidableEq Name] in
private theorem eliminateEmptyUnknown_derefWith
    {mixed : Name → Unknown (Json (Link Scalar Empty))}
    {plain : Name → Unknown (Json Scalar)}
    (hresolve : ∀ name, eliminateEmptyUnknown (mixed name) = plain name) :
    ∀ json : Json (Link Scalar Name),
      eliminateEmptyUnknown
          (JsonCas.derefWith mixed (json.mapScalar widenLink)) =
        JsonCas.derefWith plain json := by
  intro json
  induction json with
  | scalar link =>
      cases link with
      | inl scalar => rfl
      | inr name => exact hresolve name
  | list n elems ih =>
      simp only [Json.mapScalar, JsonCas.derefWith]
      by_cases hm : ∀ i, (JsonCas.derefWith mixed ((elems i).mapScalar widenLink)).isKnown
      · have hp : ∀ i, (JsonCas.derefWith plain (elems i)).isKnown := by
          intro i
          rw [← ih i, eliminateEmptyUnknown_isKnown]
          exact hm i
        rw [dif_pos hm, dif_pos hp]
        simp only [eliminateEmptyUnknown, eliminateEmpty, Json.mapScalar]
        congr 2
        funext i
        have heq := ih i
        have hc : (eliminateEmptyUnknown
            (JsonCas.derefWith mixed ((elems i).mapScalar widenLink))).isKnown := by
          simpa using hm i
        rw [← eliminateEmptyUnknown_get _ (hm i)]
        exact Unknown.get_eq_get_of_le (Or.inr heq) hc (hp i)
      · have hp : ¬∀ i, (JsonCas.derefWith plain (elems i)).isKnown := by
          intro hp
          apply hm
          intro i
          rw [← eliminateEmptyUnknown_isKnown
            (value := JsonCas.derefWith mixed ((elems i).mapScalar widenLink)), ih i]
          exact hp i
        rw [dif_neg hm, dif_neg hp]
        rfl
  | map keys vals ih =>
      simp only [Json.mapScalar, JsonCas.derefWith]
      by_cases hm : ∀ k, (JsonCas.derefWith mixed ((vals k).mapScalar widenLink)).isKnown
      · have hp : ∀ k, (JsonCas.derefWith plain (vals k)).isKnown := by
          intro k
          rw [← ih k, eliminateEmptyUnknown_isKnown]
          exact hm k
        rw [dif_pos hm, dif_pos hp]
        simp only [eliminateEmptyUnknown, eliminateEmpty, Json.mapScalar]
        congr 2
        funext k
        have heq := ih k
        have hc : (eliminateEmptyUnknown
            (JsonCas.derefWith mixed ((vals k).mapScalar widenLink))).isKnown := by
          simpa using hm k
        rw [← eliminateEmptyUnknown_get _ (hm k)]
        exact Unknown.get_eq_get_of_le (Or.inr heq) hc (hp k)
      · have hp : ¬∀ k, (JsonCas.derefWith plain (vals k)).isKnown := by
          intro hp
          apply hm
          intro k
          rw [← eliminateEmptyUnknown_isKnown
            (value := JsonCas.derefWith mixed ((vals k).mapScalar widenLink)), ih k]
          exact hp k
        rw [dif_neg hm, dif_neg hp]
        rfl

/-- Choosing no opaque target type recovers the original all-or-nothing JSON
resolver, up to elimination of the impossible sum alternative. -/
theorem fetch_ofJsonCas_empty (cas : JsonCas Scalar Name) : ∀ gas name,
    eliminateEmptyUnknown ((ofJsonCas (α := Empty) cas).fetch gas name) =
      cas.fetch gas name := by
  intro gas
  induction gas with
  | zero => intro name; rfl
  | succ gas ih =>
      intro name
      simp only [fetch, JsonCas.fetch]
      by_cases h : name ∈ cas.names
      · have hget : (ofJsonCas (α := Empty) cas).toJsonCas.get? name =
            .known ((cas.values ⟨name, h⟩).mapScalar widenLink) := by
          simp [JsonCas.get?, toJsonCas, ofJsonCas, h]
        have hplain : cas.get? name = .known (cas.values ⟨name, h⟩) := by
          simp [JsonCas.get?, h]
        rw [hget, hplain]
        simp only [Unknown.bind]
        exact eliminateEmptyUnknown_derefWith ih (cas.values ⟨name, h⟩)
      · simp [toJsonCas, ofJsonCas, JsonCas.get?, h, Unknown.bind,
          eliminateEmptyUnknown]

/-- The induced resolver function also specializes to the old resolver when
the opaque target type is empty. -/
theorem dereference_ofJsonCas_empty (cas : JsonCas Scalar Name) (gas : Nat) :
    ∀ name,
      eliminateEmptyUnknown
          ((ofJsonCas (α := Empty) cas).dereference gas name) =
        cas.dereference gas name :=
  fetch_ofJsonCas_empty cas gas

end HeterogeneousJsonCas

end Nucleus
