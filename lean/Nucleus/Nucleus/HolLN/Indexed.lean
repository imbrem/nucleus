import Nucleus.HolLN.Array
import Nucleus.HolLN.Kernel

/-!
# Indexed HOL LN collections and proof-producing equivalence classes

This module is the bridge from serialized arenas to index-oriented kernels.
It deliberately distinguishes three layers:

* `Collection Base ι` is any indexed collection of packed HOL LN entries.
* `ShapeEquiv` is untrusted/e-graph-style equivalence data which may only
  relate entries with the same syntax sort and binder depth.
* `ProvenEquiv` is a homogeneous term equivalence whose edges carry ordinary
  HOL `EqTm` derivations.

`TypedIndex` turns an index into a typed variable for the indexed rules: it
records the represented term, the fact that the collection stores that term,
and its existing HOL typing derivation.  The rules below therefore reuse the
ordinary kernel rather than defining a second notion of HOL validity.
-/

namespace Nucleus.HolLN.Indexed

universe u v

/-- A collection of packed HOL LN values indexed by an arbitrary type. -/
structure Collection (Base : Type u) (ι : Type v) where
  entry : ι → Array.Packed Base

instance {Base : Type u} {ι : Type v} : CoeFun (Collection Base ι)
    (fun _ => ι → Array.Packed Base) where
  coe := Collection.entry

/-- A finite collection with its length in the type. -/
structure FiniteCollection (Base : Type u) (length : Nat) where
  entry : Fin length → Array.Packed Base

instance {Base : Type u} {length : Nat} : CoeFun (FiniteCollection Base length)
    (fun _ => Fin length → Array.Packed Base) where
  coe := FiniteCollection.entry

def FiniteCollection.asCollection {Base : Type u} {length : Nat}
    (collection : FiniteCollection Base length) : Collection Base (Fin length) :=
  ⟨collection.entry⟩

/-- Convert a runtime array to its exact-length functional view. -/
def FiniteCollection.ofArray {Base : Type u} (entries : Array (Array.Packed Base)) :
    FiniteCollection Base entries.size :=
  ⟨fun index => entries[index]⟩

/-- A finite collection whose length is discovered dynamically. -/
structure SomeFiniteCollection (Base : Type u) where
  length : Nat
  collection : FiniteCollection Base length

/-- Parse and elaborate JSON, then expose the result as `Fin length → Packed`. -/
def Array.Json.elaborateFinite {Base : Type u} (json : Array.Json.Tree Base) :
    Option (SomeFiniteCollection Base) := do
  let entries ← Array.Json.elaborate json
  some ⟨entries.size, FiniteCollection.ofArray entries⟩

/-- A shape-compatible equivalence relation for an indexed packed collection.
This is structural e-graph data, not yet a claim of HOL equality. -/
structure ShapeEquiv {Base : Type u} {ι : Type v} (collection : Collection Base ι) where
  rel : ι → ι → Prop
  refl : ∀ index, rel index index
  symm : ∀ {left right}, rel left right → rel right left
  trans : ∀ {left middle right}, rel left middle → rel middle right → rel left right
  sort_eq : ∀ {left right}, rel left right → (collection left).sort = (collection right).sort
  depth_eq : ∀ {left right}, rel left right → (collection left).depth = (collection right).depth

def ShapeEquiv.setoid {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    (equivalence : ShapeEquiv collection) : Setoid ι where
  r := equivalence.rel
  iseqv := ⟨equivalence.refl, equivalence.symm, equivalence.trans⟩

/-- Equivalence classes of indices for shape-compatible raw e-graph data. -/
abbrev ShapeEquiv.Class {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    (equivalence : ShapeEquiv collection) := Quotient equivalence.setoid

def ShapeEquiv.classOf {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    (equivalence : ShapeEquiv collection) (index : ι) : equivalence.Class :=
  Quotient.mk equivalence.setoid index

/-- An index certified to store a term of one particular HOL type. This is the
basic variable used by the index-oriented rules below. -/
structure TypedIndex {Base : Type u} {ι : Type v} (collection : Collection Base ι)
    (Δ : FreeCtx Base) {depth : Nat} (Γ : BoundCtx Base depth) (type : Ty Base) where
  index : ι
  term : Tm Base depth
  stored : collection index = Array.Packed.ofTm term
  typing : HasType Δ Γ term type

def TypedIndex.checked {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {type : Ty Base}
    (index : TypedIndex collection Δ Γ type) : Checked Δ Γ type :=
  ⟨index.term, index.typing⟩

/-- A natural-number free-variable index together with its type lookup. -/
structure TypedFreeIndex {Base : Type u} (Δ : FreeCtx Base) (type : Ty Base) where
  name : Nat
  kinded : Kinded type
  lookup : Δ name = some type

def TypedFreeIndex.term {Base : Type u} {Δ : FreeCtx Base} {type : Ty Base}
    (freeIndex : TypedFreeIndex Δ type) (depth : Nat) : Tm Base depth :=
  .free freeIndex.name

theorem TypedFreeIndex.typing {Base : Type u} {Δ : FreeCtx Base} {type : Ty Base}
    (freeIndex : TypedFreeIndex Δ type) {depth : Nat} (Γ : BoundCtx Base depth) :
    HasType Δ Γ (freeIndex.term depth) type :=
  .free freeIndex.name freeIndex.kinded freeIndex.lookup

/-- Locate a typed free variable in an indexed collection. -/
def TypedIndex.free {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {type : Ty Base} (freeIndex : TypedFreeIndex Δ type)
    {depth : Nat} (Γ : BoundCtx Base depth) (index : ι)
    (stored : collection index = Array.Packed.ofTm (freeIndex.term depth)) :
    TypedIndex collection Δ Γ type :=
  ⟨index, freeIndex.term depth, stored, freeIndex.typing Γ⟩

/-- Locate an application node, deriving its type from typed child indices. -/
def TypedIndex.app {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A B : Ty Base}
    (function : TypedIndex collection Δ Γ (.arr A B))
    (argument : TypedIndex collection Δ Γ A) (index : ι)
    (stored : collection index = Array.Packed.ofTm (.app function.term argument.term)) :
    TypedIndex collection Δ Γ B :=
  ⟨index, .app function.term argument.term, stored, .app function.typing argument.typing⟩

/-- Locate a successor node. -/
def TypedIndex.succ {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth}
    (value : TypedIndex collection Δ Γ .natTy) (index : ι)
    (stored : collection index = Array.Packed.ofTm (.succ value.term)) :
    TypedIndex collection Δ Γ .natTy :=
  ⟨index, .succ value.term, stored, .succ value.typing⟩

/-- Locate an equality proposition built from two typed child indices. -/
def TypedIndex.eq {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base}
    (hA : Kinded A) (left right : TypedIndex collection Δ Γ A) (index : ι)
    (stored : collection index = Array.Packed.ofTm (.eq A left.term right.term)) :
    TypedIndex collection Δ Γ .boolTy :=
  ⟨index, .eq A left.term right.term, stored, .eq hA left.typing right.typing⟩

/-- An ordinary HOL equality derivation whose endpoints are collection indices. -/
structure EqAt {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base}
    (left right : TypedIndex collection Δ Γ A) where
  proof : EqTm Δ Γ left.term right.term A

def EqAt.refl {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base}
    (index : TypedIndex collection Δ Γ A) : EqAt index index :=
  ⟨.refl index.typing⟩

def EqAt.symm {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base}
    {left right : TypedIndex collection Δ Γ A} (equality : EqAt left right) :
    EqAt right left :=
  ⟨.symm equality.proof⟩

def EqAt.trans {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base}
    {left middle right : TypedIndex collection Δ Γ A}
    (first : EqAt left middle) (second : EqAt middle right) : EqAt left right :=
  ⟨.trans first.proof second.proof⟩

def EqAt.app {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A B : Ty Base}
    {leftFunction rightFunction : TypedIndex collection Δ Γ (.arr A B)}
    {leftArgument rightArgument : TypedIndex collection Δ Γ A}
    (functions : EqAt leftFunction rightFunction) (arguments : EqAt leftArgument rightArgument)
    (leftIndex rightIndex : ι)
    (leftStored : collection leftIndex =
      Array.Packed.ofTm (.app leftFunction.term leftArgument.term))
    (rightStored : collection rightIndex =
      Array.Packed.ofTm (.app rightFunction.term rightArgument.term)) :
    EqAt (leftFunction.app leftArgument leftIndex leftStored)
      (rightFunction.app rightArgument rightIndex rightStored) :=
  ⟨.app functions.proof arguments.proof⟩

def EqAt.succ {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth}
    {left right : TypedIndex collection Δ Γ .natTy} (equality : EqAt left right)
    (leftIndex rightIndex : ι)
    (leftStored : collection leftIndex = Array.Packed.ofTm (.succ left.term))
    (rightStored : collection rightIndex = Array.Packed.ofTm (.succ right.term)) :
    EqAt (left.succ leftIndex leftStored) (right.succ rightIndex rightStored) :=
  ⟨.succ equality.proof⟩

/-- A homogeneous, proof-producing equivalence relation over typed indices. -/
structure ProvenEquiv {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base}
    (family : ι → TypedIndex collection Δ Γ A) where
  rel : ι → ι → Prop
  refl : ∀ index, rel index index
  symm : ∀ {left right}, rel left right → rel right left
  trans : ∀ {left middle right}, rel left middle → rel middle right → rel left right
  sound : ∀ {left right}, rel left right → EqAt (family left) (family right)

def ProvenEquiv.setoid {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base}
    {family : ι → TypedIndex collection Δ Γ A} (equivalence : ProvenEquiv family) : Setoid ι where
  r := equivalence.rel
  iseqv := ⟨equivalence.refl, equivalence.symm, equivalence.trans⟩

/-- A HOL-justified equivalence class of typed term indices. -/
abbrev ProvenEquiv.Class {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base}
    {family : ι → TypedIndex collection Δ Γ A} (equivalence : ProvenEquiv family) :=
  Quotient equivalence.setoid

def ProvenEquiv.classOf {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base}
    {family : ι → TypedIndex collection Δ Γ A} (equivalence : ProvenEquiv family)
    (index : ι) : equivalence.Class :=
  Quotient.mk equivalence.setoid index

/-- Indexed Boolean hypotheses, each carrying its own storage and typing proof. -/
abbrev Hypotheses {Base : Type u} {ι : Type v} (collection : Collection Base ι)
    (Δ : FreeCtx Base) {depth : Nat} (Γ : BoundCtx Base depth) :=
  List (TypedIndex collection Δ Γ .boolTy)

def Hypotheses.terms {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth}
    (hypotheses : Hypotheses collection Δ Γ) : List (Tm Base depth) :=
  hypotheses.map TypedIndex.term

theorem Hypotheses.typed {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth}
    (hypotheses : Hypotheses collection Δ Γ) : TypedHyps Δ Γ hypotheses.terms := by
  intro proposition member
  simp only [terms, List.mem_map] at member
  obtain ⟨index, _, rfl⟩ := member
  exact index.typing

/-- An ordinary HOL theorem whose conclusion and hypotheses are addressed by
typed collection indices. -/
structure ProvesAt {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth}
    (hypotheses : Hypotheses collection Δ Γ)
    (conclusion : TypedIndex collection Δ Γ .boolTy) where
  proof : Proves Δ Γ hypotheses.terms conclusion.term

def ProvesAt.hyp {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth}
    {hypotheses : Hypotheses collection Δ Γ}
    (conclusion : TypedIndex collection Δ Γ .boolTy) (member : conclusion ∈ hypotheses) :
    ProvesAt hypotheses conclusion :=
  ⟨.hyp hypotheses.typed (List.mem_map.mpr ⟨conclusion, member, rfl⟩)⟩

def ProvesAt.truth {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth}
    (hypotheses : Hypotheses collection Δ Γ) (index : ι)
    (stored : collection index = Array.Packed.ofTm (.bool true : Tm Base depth)) :
    ProvesAt hypotheses ⟨index, .bool true, stored, .bool true⟩ :=
  ⟨.truth hypotheses.typed⟩

def ProvesAt.eqOfEqAt {Base : Type u} {ι : Type v} {collection : Collection Base ι}
    {Δ : FreeCtx Base} {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base}
    (hypotheses : Hypotheses collection Δ Γ) (hA : Kinded A)
    {left right : TypedIndex collection Δ Γ A} (equality : EqAt left right)
    (index : ι)
    (stored : collection index = Array.Packed.ofTm (.eq A left.term right.term)) :
    ProvesAt hypotheses (TypedIndex.eq hA left right index stored) :=
  ⟨.eqOfEqTm hypotheses.typed hA equality.proof⟩

end Nucleus.HolLN.Indexed
