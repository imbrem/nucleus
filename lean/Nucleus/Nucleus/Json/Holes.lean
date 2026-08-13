import Nucleus.Json.Patch
import Nucleus.Json.CasMap

/-!
# JSON with holes

A template is JSON whose scalar leaves are either ordinary scalars or named
holes. A hole stands for an arbitrary JSON subtree, not merely another scalar.
This is exactly scalar substitution (`Json.bind`), giving useful identity and
associativity laws for free. Epistemically partial filling uses `Unknown`, so a
missing hole assignment is distinct from JSON null.
-/

namespace Nucleus

universe u

/-- JSON containing ordinary scalar leaves or named holes. -/
abbrev JsonWithHoles (Scalar : Type u) (Hole : Type u) (Key : Type := String) :=
  Json (Scalar ⊕ Hole) Key

namespace JsonWithHoles

variable {Scalar Hole Hole₂ Hole₃ : Type u} {Key : Type}

/-- Regard ordinary JSON as a template containing no holes. -/
def embed (json : Json Scalar Key) : JsonWithHoles Scalar Hole Key :=
  json.mapScalar Sum.inl

/-- A template consisting of one hole. Filling may replace it by an arbitrary
subtree. -/
def hole (name : Hole) : JsonWithHoles Scalar Hole Key := .scalar (.inr name)

/-- Substitute templates for holes while preserving ordinary scalar leaves. -/
def substitute (template : JsonWithHoles Scalar Hole Key)
    (assignment : Hole → JsonWithHoles Scalar Hole₂ Key) :
    JsonWithHoles Scalar Hole₂ Key :=
  template.bind (Sum.elim (fun scalar => .scalar (.inl scalar)) assignment)

/-- Fill every hole with an ordinary JSON subtree. -/
def fill (template : JsonWithHoles Scalar Hole Key)
    (assignment : Hole → Json Scalar Key) : Json Scalar Key :=
  template.bind (Sum.elim Json.scalar assignment)

/-- Fill holes with epistemically partial assignments. Any unavailable hole
makes the all-or-nothing result unknown. -/
def fillUnknown (template : JsonWithHoles Scalar Hole Key)
    (assignment : Hole → Unknown (Json Scalar Key)) : Unknown (Json Scalar Key) :=
  match template with
  | .scalar (.inl scalar) => .known (.scalar scalar)
  | .scalar (.inr name) => assignment name
  | .list n elems =>
      if h : ∀ i, (fillUnknown (elems i) assignment).isKnown then
        .known (.list n fun i => (fillUnknown (elems i) assignment).get (h i))
      else .unknown
  | .map keys vals =>
      if h : ∀ k, (fillUnknown (vals k) assignment).isKnown then
        .known (.map keys fun k => (fillUnknown (vals k) assignment).get (h k))
      else .unknown

@[simp] theorem substitute_hole (name : Hole)
    (assignment : Hole → JsonWithHoles Scalar Hole₂ Key) :
    substitute (hole name) assignment = assignment name := rfl

@[simp] theorem fill_hole (name : Hole) (assignment : Hole → Json Scalar Key) :
    fill (hole name) assignment = assignment name := rfl

/-- Embedding then filling is the identity, independently of the assignment. -/
@[simp] theorem fill_embed (json : Json Scalar Key) (assignment : Hole → Json Scalar Key) :
    fill (embed json) assignment = json := by
  induction json with
  | scalar value => rfl
  | list n elems ih =>
      simp only [embed, Json.mapScalar, fill, Json.bind_list]
      congr 1
      exact funext ih
  | map keys vals ih =>
      simp only [embed, Json.mapScalar, fill, Json.bind_map]
      congr 1
      exact funext ih

/-- Substitution by the corresponding hole is the identity template. -/
@[simp] theorem substitute_id (template : JsonWithHoles Scalar Hole Key) :
    substitute template hole = template := by
  induction template with
  | scalar value => cases value <;> rfl
  | list n elems ih =>
      simp only [substitute, Json.bind_list]
      congr 1
      exact funext ih
  | map keys vals ih =>
      simp only [substitute, Json.bind_map]
      congr 1
      exact funext ih

/-- Template substitution is associative. -/
theorem substitute_assoc (template : JsonWithHoles Scalar Hole Key)
    (first : Hole → JsonWithHoles Scalar Hole₂ Key)
    (second : Hole₂ → JsonWithHoles Scalar Hole₃ Key) :
    substitute (substitute template first) second =
      substitute template (fun name => substitute (first name) second) := by
  rw [substitute, substitute, Json.bind_assoc]
  apply congrArg (Json.bind template)
  funext value
  cases value with
  | inl scalar => rfl
  | inr name => rfl

/-- Filling after substitution equals filling each substituted template first. -/
theorem fill_substitute (template : JsonWithHoles Scalar Hole Key)
    (first : Hole → JsonWithHoles Scalar Hole₂ Key)
    (second : Hole₂ → Json Scalar Key) :
    fill (substitute template first) second =
      fill template (fun name => fill (first name) second) := by
  rw [substitute, fill, Json.bind_assoc]
  apply congrArg (Json.bind template)
  funext value
  cases value with
  | inl scalar => rfl
  | inr name => rfl

/-- Known assignments make partial filling agree with total filling. -/
theorem fillUnknown_known (template : JsonWithHoles Scalar Hole Key)
    (assignment : Hole → Json Scalar Key) :
    fillUnknown template (fun name => .known (assignment name)) =
      .known (fill template assignment) := by
  induction template with
  | scalar value => cases value <;> rfl
  | list n elems ih =>
      simp only [fillUnknown, fill, Json.bind_list]
      rw [dif_pos fun i => by simp [ih i, Unknown.isKnown]]
      congr 2
      funext i
      have h := ih i
      apply Unknown.get_eq_get_of_le (Or.inr h)
      simp [Unknown.isKnown]
  | map keys vals ih =>
      simp only [fillUnknown, fill, Json.bind_map]
      rw [dif_pos fun k => by simp [ih k, Unknown.isKnown]]
      congr 2
      funext k
      have h := ih k
      apply Unknown.get_eq_get_of_le (Or.inr h)
      simp [Unknown.isKnown]

/-- Information refinement between templates: the right template can be
obtained by substituting (possibly still-holed) templates into the left. -/
def Refines (less more : JsonWithHoles Scalar Hole Key) : Prop :=
  ∃ assignment : Hole → JsonWithHoles Scalar Hole Key,
    substitute less assignment = more

instance : LE (JsonWithHoles Scalar Hole Key) := ⟨Refines⟩

theorem le_refl (template : JsonWithHoles Scalar Hole Key) : template ≤ template :=
  ⟨hole, substitute_id template⟩

theorem le_trans {a b c : JsonWithHoles Scalar Hole Key} :
    a ≤ b → b ≤ c → a ≤ c := by
  rintro ⟨first, rfl⟩ ⟨second, rfl⟩
  exact ⟨fun name => substitute (first name) second, (substitute_assoc _ _ _).symm⟩

instance : Preorder (JsonWithHoles Scalar Hole Key) where
  le_refl := le_refl
  le_trans _ _ _ := le_trans

end JsonWithHoles

end Nucleus
