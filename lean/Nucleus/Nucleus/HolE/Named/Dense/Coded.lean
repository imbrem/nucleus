import Nucleus.HolE.Named.Dense.Encoding
import Nucleus.SimpTy

/-!
# Forests indexed by denoted codes

The raw arena API is parameterized by an index type.  This layer instead
bundles a code whose canonical denotation is that index type.  Operations on
codes therefore induce operations on forests and public encodings: in
particular, a concrete coproduct combines two disjoint forests.
-/

namespace Nucleus.HolE.Named.Unsorted.Dense

open Nucleus

universe u v w

variable {N : Type u → Type v} {Code : Type w} [Denotes.{w, u} Code]
variable {ι κ : Type u}

/-- Change every index in a public encoding along an equivalence. -/
def PublicEncoding.reindexEquiv [MapIndices N] (equiv : ι ≃ κ)
    (encoding : PublicEncoding N ι) : PublicEncoding N κ where
  forest index :=
    (encoding.forest (equiv.symm index)).map (MapIndices.mapIndices equiv)
  exports := encoding.exports.map equiv

@[simp] theorem PublicEncoding.reindexEquiv_exports_length [MapIndices N]
    (equiv : ι ≃ κ) (encoding : PublicEncoding N ι) :
    (encoding.reindexEquiv equiv).exports.length = encoding.exports.length := by
  simp [PublicEncoding.reindexEquiv]

/-- Change every index in a rooted encoding along an equivalence. -/
def RootedEncoding.reindexEquiv [MapIndices N] (equiv : ι ≃ κ)
    (encoding : RootedEncoding N ι) : RootedEncoding N κ where
  forest index :=
    (encoding.forest (equiv.symm index)).map (MapIndices.mapIndices equiv)
  root := equiv encoding.root

@[simp] theorem RootedEncoding.reindexEquiv_toPublic [MapIndices N]
    (equiv : ι ≃ κ) (encoding : RootedEncoding N ι) :
    (encoding.reindexEquiv equiv).toPublic = encoding.toPublic.reindexEquiv equiv := by
  cases encoding
  rfl

/-- A node forest whose index type is the canonical denotation of a bundled
code. -/
structure CodeForest (N : Type u → Type v) (Code : Type w) [Denotes.{w, u} Code] where
  code : Code
  forest : code → Option (N code)

/-- A code-indexed forest with an ordered list of public indices. -/
structure CodePublicEncoding (N : Type u → Type v) (Code : Type w)
    [Denotes.{w, u} Code] where
  code : Code
  encoding : PublicEncoding N code

/-- A code-indexed forest with one distinguished public index. -/
structure CodeRootedEncoding (N : Type u → Type v) (Code : Type w)
    [Denotes.{w, u} Code] where
  code : Code
  encoding : RootedEncoding N code

def CodePublicEncoding.toForest (encoding : CodePublicEncoding N Code) :
    CodeForest N Code :=
  ⟨encoding.code, encoding.encoding.forest⟩

def CodeRootedEncoding.toForest (encoding : CodeRootedEncoding N Code) :
    CodeForest N Code :=
  ⟨encoding.code, encoding.encoding.forest⟩

def CodeRootedEncoding.toPublic (encoding : CodeRootedEncoding N Code) :
    CodePublicEncoding N Code :=
  ⟨encoding.code, encoding.encoding.toPublic⟩

/-- Reinterpret a code-indexed forest at another code with an equivalent
carrier. -/
def CodeForest.reindex [MapIndices N] (forest : CodeForest N Code)
    (target : Code) (equiv : forest.code ≃ target) : CodeForest N Code where
  code := target
  forest index :=
    (forest.forest (equiv.symm index)).map (MapIndices.mapIndices equiv)

def CodePublicEncoding.reindex [MapIndices N]
    (encoding : CodePublicEncoding N Code) (target : Code)
    (equiv : encoding.code ≃ target) : CodePublicEncoding N Code :=
  ⟨target, encoding.encoding.reindexEquiv equiv⟩

def CodeRootedEncoding.reindex [MapIndices N]
    (encoding : CodeRootedEncoding N Code) (target : Code)
    (equiv : encoding.code ≃ target) : CodeRootedEncoding N Code :=
  ⟨target, encoding.encoding.reindexEquiv equiv⟩

/-- Concatenate two public encodings. Their index code is the concrete
coproduct of the input codes, while its distinguished equivalence transports
the raw `Sum` indices produced by `PublicEncoding.sum`. -/
def CodePublicEncoding.concat [MapIndices N] [HasCoproduct Code]
    (left right : CodePublicEncoding N Code) : CodePublicEncoding N Code :=
  let code := HasCoproduct.coproduct left.code right.code
  let split : code ≃ (left.code ⊕ right.code) :=
    Nucleus.TypeFormers.coproductEquiv left.code right.code
  let includeLeft : left.code → code := Nucleus.TypeFormers.inl
  let includeRight : right.code → code := Nucleus.TypeFormers.inr
  { code
    encoding :=
      { forest := fun index => match split index with
          | .inl source =>
              (left.encoding.forest source).map (MapIndices.mapIndices includeLeft)
          | .inr source =>
              (right.encoding.forest source).map (MapIndices.mapIndices includeRight)
        exports := left.encoding.exports.map includeLeft ++
          right.encoding.exports.map includeRight } }

@[simp] theorem CodePublicEncoding.concat_code [MapIndices N] [HasCoproduct Code]
    (left right : CodePublicEncoding N Code) :
    (left.concat right).code = HasCoproduct.coproduct left.code right.code := rfl

theorem CodePublicEncoding.concat_exports [MapIndices N] [HasCoproduct Code]
    (left right : CodePublicEncoding N Code) :
    (left.concat right).encoding.exports =
      left.encoding.exports.map
        (Nucleus.TypeFormers.inl (Code := Code) (right := right.code)) ++
      right.encoding.exports.map
        (Nucleus.TypeFormers.inr (Code := Code) (left := left.code)) := by
  rfl

/-- Coproduct is the algebraic name for code-indexed concatenation. -/
abbrev CodePublicEncoding.coproduct [MapIndices N] [HasCoproduct Code]
    (left right : CodePublicEncoding N Code) : CodePublicEncoding N Code :=
  left.concat right

@[simp] theorem CodePublicEncoding.concat_exports_length [MapIndices N]
    [HasCoproduct Code] (left right : CodePublicEncoding N Code) :
    (left.concat right).encoding.exports.length =
      left.encoding.exports.length + right.encoding.exports.length := by
  calc
    _ = (left.encoding.exports.map
          (Nucleus.TypeFormers.inl (Code := Code) (right := right.code)) ++
        right.encoding.exports.map
          (Nucleus.TypeFormers.inr (Code := Code) (left := left.code))).length :=
      congrArg List.length (CodePublicEncoding.concat_exports left right)
    _ = _ := by simp

/-- Concatenate two forests without manufacturing public indices. -/
def CodeForest.concat [MapIndices N] [HasCoproduct Code]
    (left right : CodeForest N Code) : CodeForest N Code :=
  let leftPublic : CodePublicEncoding N Code :=
    ⟨left.code, ⟨left.forest, []⟩⟩
  let rightPublic : CodePublicEncoding N Code :=
    ⟨right.code, ⟨right.forest, []⟩⟩
  (leftPublic.concat rightPublic).toForest

@[simp] theorem CodeForest.concat_code [MapIndices N] [HasCoproduct Code]
    (left right : CodeForest N Code) :
    (left.concat right).code = HasCoproduct.coproduct left.code right.code := rfl

abbrev CodeForest.coproduct [MapIndices N] [HasCoproduct Code]
    (left right : CodeForest N Code) : CodeForest N Code :=
  left.concat right

/-- Concatenating rooted encodings exposes both roots in order. -/
def CodeRootedEncoding.concat [MapIndices N] [HasCoproduct Code]
    (left right : CodeRootedEncoding N Code) : CodePublicEncoding N Code :=
  left.toPublic.concat right.toPublic

@[simp] theorem CodeRootedEncoding.concat_exports_length [MapIndices N]
    [HasCoproduct Code] (left right : CodeRootedEncoding N Code) :
    (left.concat right).encoding.exports.length = 2 := by
  change (left.toPublic.concat right.toPublic).encoding.exports.length = 2
  rw [CodePublicEncoding.concat_exports_length]
  rfl

/-! Common bundled code families. -/

abbrev TypeCodeForest (N : Type u → Type v) := CodeForest N (Type u)
abbrev TypeCodePublicEncoding (N : Type u → Type v) :=
  CodePublicEncoding N (Type u)
abbrev TypeCodeRootedEncoding (N : Type u → Type v) :=
  CodeRootedEncoding N (Type u)

abbrev SimpTy0Forest (N : Type u → Type v) (Base : Type w) [Denotes.{w, u} Base] :=
  CodeForest N (SimpTy0 Base)
abbrev SimpTy0PublicEncoding (N : Type u → Type v) (Base : Type w)
    [Denotes.{w, u} Base] :=
  CodePublicEncoding N (SimpTy0 Base)
abbrev SimpTy0RootedEncoding (N : Type u → Type v) (Base : Type w)
    [Denotes.{w, u} Base] :=
  CodeRootedEncoding N (SimpTy0 Base)

end Nucleus.HolE.Named.Unsorted.Dense
