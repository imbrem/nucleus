import Nucleus.Hol.Ethane.Kernel.TypedFreeVariable

/-!
# Implementation-derived checked classifications

This is the first semantic state layered over the raw dense arena.  A checked
entry contains an Ethane typing certificate, and `RowsDerived` requires every
entry to be the result of classifying the corresponding raw row against the
previous checked entries.  Thus a type handle is evidence derived from the
operation history, not an external assertion.

The initial classifier intentionally recognizes only Boolean types, Boolean
terms, and typed free variables.  Unsupported rows cannot be added through
this checked layer yet.
-/

namespace Nucleus.Hol.Ethane.Kernel

open Nucleus.Hol.Ethane

set_option relaxedAutoImplicit true

/-- Exact representability predicate for a signed Rust `i64`. -/
def I64Valid (value : Int) : Prop :=
  -(2 ^ 63 : Int) ≤ value ∧ value < (2 ^ 63 : Int)

/-- A signed arena reference proved representable by the Rust boundary type. -/
structure I64Ref where
  value : Int
  valid : I64Valid value

theorem boolTy_kinded {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types) :
    Nucleus.Hol.Ethane.Kinded typeScope (.boolTy : Ty Sig) := by
  refine ⟨.boolTy, .kind, ?_, rfl, .boolTy⟩
  simp [Nucleus.Hol.Ethane.Expr.lower, Nucleus.Hol.Ethane.Expr.toHolE,
    Nucleus.HolE.Named.lower, Nucleus.HolE.Named.lowerFam]
  rfl

theorem bool_hasType {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types) (value : Bool) :
    Nucleus.Hol.Ethane.HasType typeScope .nil Nucleus.HolE.emptyBound
      (.bool value) (.boolTy : Ty Sig) := by
  refine ⟨.bool value, .tm .boolTy, ?_, ?_, .bool value⟩
  · change Nucleus.HolE.Named.lowerTm typeScope .nil (.bool value) =
      some (.bool value)
    rw [Nucleus.HolE.Named.lowerTm]
  · simp [Nucleus.Hol.Ethane.Classification.lower,
      Nucleus.Hol.Ethane.Expr.lowerTy, Nucleus.Hol.Ethane.Expr.lowerFam,
      Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lowerFam]

/-- A checked semantic value retained by the implementation-facing classifier. -/
inductive Checked {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types) where
  | type (value : Ty Sig) (kinded : Nucleus.Hol.Ethane.Kinded typeScope value)
  | term (value : Tm Sig) (type : Ty Sig)
      (typed : Nucleus.Hol.Ethane.HasType typeScope .nil
        Nucleus.HolE.emptyBound value type)

namespace Checked

/-- Forget typing evidence while retaining the exact elaborated syntax. -/
def expression {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {typeScope : TyScope types} :
    Checked (Sig := Sig) typeScope → Syn Sig
  | .type value _ => value.erase
  | .term value _ _ => value.erase

end Checked

abbrev CheckedView {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types) :=
  Int → Option (Checked (Sig := Sig) typeScope)

/-- Extend a checked view at the next absolute signed index. -/
def CheckedView.set {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {typeScope : TyScope types}
    (view : CheckedView (Sig := Sig) typeScope) (index : Int)
    (value : Checked (Sig := Sig) typeScope) : CheckedView (Sig := Sig) typeScope :=
  fun wanted => if wanted = index then some value else view wanted

/-- View after all checked values in a local prefix have been installed. -/
def CheckedView.extend {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {typeScope : TyScope types} :
    CheckedView (Sig := Sig) typeScope → Int →
    List (Checked (Sig := Sig) typeScope) → CheckedView (Sig := Sig) typeScope
  | view, _, [] => view
  | view, next, value :: values =>
      CheckedView.extend (view.set next value) (next + 1) values

theorem CheckedView.extend_append {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {typeScope : TyScope types}
    (view : CheckedView (Sig := Sig) typeScope) (next : Int)
    (values : List (Checked (Sig := Sig) typeScope))
    (value : Checked (Sig := Sig) typeScope) :
    view.extend next (values ++ [value]) =
      (view.extend next values).set (next + values.length) value := by
  induction values generalizing view next with
  | nil => simp [extend]
  | cons head values ih =>
      change (view.set next head).extend (next + 1) (values ++ [value]) =
        ((view.set next head).extend (next + 1) values).set
          (next + ((values.length : Int) + 1)) value
      rw [ih]
      congr 1
      omega

/-- Classify one raw row using only previously checked values. -/
noncomputable def classify {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types)
    (view : CheckedView (Sig := Sig) typeScope) :
    Nucleus.Hol.Ethane.Arena.Row Sig Nat Int →
      Option (Checked (Sig := Sig) typeScope)
  | .boolTy => some (.type .boolTy (boolTy_kinded typeScope))
  | .bool value => some (.term (.bool value) .boolTy (bool_hasType typeScope value))
  | .tmFv name typeReference =>
      match view typeReference with
      | some (.type type typeKinded) =>
          some (.term (.tmFv name type) type (tmFv_hasType name typeKinded))
      | some (.term ..) | none => none
  | _ => none

/-- Every checked value is derived from its raw row and the preceding checked
view.  The two lists must have exactly the same shape. -/
def RowsDerived {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types) :
    CheckedView (Sig := Sig) typeScope → Int →
    List (Nucleus.Hol.Ethane.Arena.Row Sig Nat Int) →
    List (Checked (Sig := Sig) typeScope) → Prop
  | _, _, [], [] => True
  | view, next, row :: rows, value :: values =>
      classify typeScope view row = some value ∧
        RowsDerived typeScope (view.set next value) (next + 1) rows values
  | _, _, _, _ => False

theorem RowsDerived.length_eq {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {typeScope : TyScope types}
    {view : CheckedView (Sig := Sig) typeScope} {next : Int}
    {rows : List (Nucleus.Hol.Ethane.Arena.Row Sig Nat Int)}
    {values : List (Checked (Sig := Sig) typeScope)}
    (derived : RowsDerived (Sig := Sig) typeScope view next rows values) :
    rows.length = values.length := by
  induction rows generalizing view next values with
  | nil => cases values <;> simp_all [RowsDerived]
  | cons row rows ih =>
      cases values with
      | nil => contradiction
      | cons value values =>
          simp only [List.length_cons]
          exact congrArg (fun length => length + 1) (ih derived.2)

theorem RowsDerived.append {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {typeScope : TyScope types}
    {rows : List (Nucleus.Hol.Ethane.Arena.Row Sig Nat Int)}
    {values : List (Checked (Sig := Sig) typeScope)}
    {view : CheckedView (Sig := Sig) typeScope} {next : Int}
    {row : Nucleus.Hol.Ethane.Arena.Row Sig Nat Int}
    {value : Checked (Sig := Sig) typeScope}
    (derived : RowsDerived (Sig := Sig) typeScope view next rows values)
    (classified : classify (Sig := Sig) typeScope (view.extend next values) row = some value) :
    RowsDerived (Sig := Sig) typeScope view next (rows ++ [row])
      (values ++ [value]) := by
  induction rows generalizing view next values with
  | nil =>
      cases values with
      | nil => exact ⟨classified, trivial⟩
      | cons => contradiction
  | cons head rows ih =>
      cases values with
      | nil => contradiction
      | cons first values =>
          exact ⟨derived.1, ih derived.2 classified⟩

/- A representation capability for an arena of the shared Ethane row
vocabulary.  Dense storage and a future verified arena can implement the same
interface. -/
class RowArena (Raw : Type) (Sig : Signature) where
  rows : Raw → List (Nucleus.Hol.Ethane.Arena.Row Sig Nat Int)
  offset : Raw → Int
  next : Raw → Int
  push : Raw → Nucleus.Hol.Ethane.Arena.Row Sig Nat Int → Raw
  next_eq (raw) : next raw = offset raw + (rows raw).length
  rows_push (raw row) : rows (push raw row) = rows raw ++ [row]
  offset_push (raw row) : offset (push raw row) = offset raw
  next_push (raw row) : next (push raw row) = next raw + 1

/-- A semantically checked persistent arena.  `base` is the already checked
parent/CAS view, while local classifications are derived from shared raw rows.
`Sound` may close over the shared ghost CAS and its fact interpretation. -/
structure ClassifiedArena (Sig : Signature) [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types) (Raw : Type)
    [RowArena Raw Sig] (Sound : Raw → Prop) where
  raw : Raw
  base : CheckedView (Sig := Sig) typeScope
  checked : List (Checked (Sig := Sig) typeScope)
  derived : RowsDerived (Sig := Sig) typeScope base (RowArena.offset (Sig := Sig) raw)
    (RowArena.rows (Sig := Sig) raw) checked
  offsetValid : I64Valid (RowArena.offset (Sig := Sig) raw)
  nextBound : RowArena.next (Sig := Sig) raw ≤ (2 ^ 63 : Int)
  sound : Sound raw

namespace ClassifiedArena

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
  {types : List Kind} {typeScope : TyScope types}
  {Raw : Type} [RowArena Raw Sig] {Sound : Raw → Prop}

/-- The complete checked view, including all local classifications. -/
def view (state : ClassifiedArena Sig typeScope Raw Sound) :
    CheckedView (Sig := Sig) typeScope :=
  state.base.extend (RowArena.offset (Sig := Sig) state.raw) state.checked

/-- Elaborated syntax projection of the implementation-derived checked view. -/
def valueView (state : ClassifiedArena Sig typeScope Raw Sound) :
    Int → Option (Nucleus.Hol.Ethane.Arena.Value Sig Nat) :=
  fun reference => (state.view reference).map fun checked =>
    .syntax checked.expression

/-- A handle proves that a reference denotes a checked type in this arena. -/
structure TypeHandle (state : ClassifiedArena Sig typeScope Raw Sound) where
  reference : I64Ref
  type : Ty Sig
  kinded : Nucleus.Hol.Ethane.Kinded typeScope type
  checked : state.view reference.value = some (.type type kinded)
  backward : reference.value < RowArena.next (Sig := Sig) state.raw

/-- A checked type handle discharges the semantic `TmFvReady` premise without
an external ghost classification assertion. -/
def TypeHandle.tmFvReady {state : ClassifiedArena Sig typeScope Raw Sound}
    (handle : TypeHandle state) :
    TmFvReady typeScope (RowArena.next (Sig := Sig) state.raw) state.valueView
      handle.reference.value where
  backward := handle.backward
  typeWitness :=
    { type := handle.type
      resolves := by simp [valueView, handle.checked, Checked.expression]
      kinded := handle.kinded }

/-- Persistent Boolean-type transition, extending both the raw arena and the
implementation-derived classification list. -/
def boolTy (state : ClassifiedArena Sig typeScope Raw Sound)
    (nextValid : I64Valid (RowArena.next (Sig := Sig) state.raw))
    (preserves : Sound state.raw →
      Sound (RowArena.push (Sig := Sig) state.raw .boolTy)) :
    Σ next : ClassifiedArena Sig typeScope Raw Sound, TypeHandle next := by
  let checked : Checked (Sig := Sig) typeScope :=
    .type .boolTy (boolTy_kinded typeScope)
  let next : ClassifiedArena Sig typeScope Raw Sound :=
    { raw := RowArena.push (Sig := Sig) state.raw .boolTy
      base := state.base
      checked := state.checked ++ [checked]
      derived := by
        rw [RowArena.rows_push, RowArena.offset_push]
        simpa [checked] using
          state.derived.append (row := .boolTy) (value := checked) rfl
      offsetValid := by
        rw [RowArena.offset_push]
        exact state.offsetValid
      nextBound := by
        rw [RowArena.next_push]
        have upper := nextValid.2
        omega
      sound := preserves state.sound }
  refine ⟨next, {
    reference := ⟨RowArena.next (Sig := Sig) state.raw, nextValid⟩
    type := .boolTy
    kinded := boolTy_kinded typeScope
    checked := ?_
    backward := ?_ }⟩
  · have lengths := state.derived.length_eq
    dsimp [next, view]
    rw [RowArena.offset_push]
    change state.base.extend (RowArena.offset (Sig := Sig) state.raw)
      (state.checked ++ [checked]) (RowArena.next (Sig := Sig) state.raw) =
        some checked
    rw [CheckedView.extend_append, RowArena.next_eq, lengths]
    simp [CheckedView.set]
  · change RowArena.next (Sig := Sig) state.raw <
      RowArena.next (Sig := Sig) (RowArena.push state.raw .boolTy)
    rw [RowArena.next_push]
    omega

/-- Persistent Boolean-term transition with a derived term classification. -/
def bool (state : ClassifiedArena Sig typeScope Raw Sound) (value : Bool)
    (nextValid : I64Valid (RowArena.next (Sig := Sig) state.raw))
    (preserves : Sound state.raw →
      Sound (RowArena.push (Sig := Sig) state.raw (.bool value))) :
    ClassifiedArena Sig typeScope Raw Sound := by
  let checked : Checked (Sig := Sig) typeScope :=
    .term (.bool value) .boolTy (bool_hasType typeScope value)
  exact
    { raw := RowArena.push (Sig := Sig) state.raw (.bool value)
      base := state.base
      checked := state.checked ++ [checked]
      derived := by
        rw [RowArena.rows_push, RowArena.offset_push]
        simpa [checked] using
          state.derived.append (row := .bool value) (value := checked) rfl
      offsetValid := by
        rw [RowArena.offset_push]
        exact state.offsetValid
      nextBound := by
        rw [RowArena.next_push]
        have upper := nextValid.2
        omega
      sound := preserves state.sound }

end ClassifiedArena

end Nucleus.Hol.Ethane.Kernel
