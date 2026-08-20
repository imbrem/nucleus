import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Countable.Defs
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Concrete denoted type formers

A code coerces to its canonical Lean carrier through `CoeSort`. The type-former
capabilities below package both an operation on codes and a distinguished
equivalence from the result's carrier to the corresponding Lean construction.
They are concrete semantic structure, rather than bare categorical universal
properties.
-/

namespace Nucleus

universe u v w

/-- A code with a canonical interpretation as a Lean type. -/
class Denotes (Code : Type u) where
  denote : Code → Type v

/-- Every denotation may be used directly in type position. -/
instance {Code : Type u} [Denotes Code] : CoeSort Code (Type v) where
  coe := Denotes.denote

/-- Every carrier in a denoted family is finite. -/
class FiniteDen (Code : Type u) [Denotes Code] : Prop where
  finite (code : Code) : Finite code

/-- Every carrier in a denoted family is countable. -/
class CountableDen (Code : Type u) [Denotes Code] : Prop where
  countable (code : Code) : Countable code

instance {Code : Type u} [Denotes Code] [FiniteDen Code] (code : Code) : Finite code :=
  FiniteDen.finite code

instance {Code : Type u} [Denotes Code] [CountableDen Code] (code : Code) : Countable code :=
  CountableDen.countable code

instance {Code : Type u} [Denotes Code] [FiniteDen Code] : CountableDen Code where
  countable code := by
    letI := FiniteDen.finite code
    infer_instance

/-- Natural numbers are the canonical codes for the finite carriers `Fin n`. -/
instance : Denotes Nat where
  denote := Fin

instance : FiniteDen Nat where
  finite n := by
    change Finite (Fin n)
    infer_instance

/-- A distinguished embedding of a code's carrier into a type. -/
class Embeds {Code : Type u} [Denotes Code] (code : Code) (target : Type w) where
  embedding : code ↪ target

/-- A distinguished equivalence from a code's carrier to a type. -/
class Encodes {Code : Type u} [Denotes Code] (code : Code) (target : Type w) where
  equiv : code ≃ target

/-- Merely having a canonical equivalence also supplies its canonical embedding. -/
instance (priority := 100) {Code : Type u} [Denotes Code] (code : Code) (target : Type w)
    [encoding : Encodes code target] : Embeds code target where
  embedding := encoding.equiv.toEmbedding

/-- The property that some equivalence exists; unlike `Encodes`, it chooses no canonical one. -/
def IsEncoded {Code : Type u} [Denotes Code] (code : Code) (target : Type w) : Prop :=
  Nonempty (code ≃ target)

/-- Typeclass form of `IsEncoded`, for APIs that need proof search but no chosen equivalence. -/
class HasEncoding {Code : Type u} [Denotes Code]
    (code : Code) (target : Type w) : Prop where
  exists_equiv : IsEncoded code target

instance {Code : Type u} [Denotes Code] (code : Code) (target : Type w)
    [encoding : Encodes code target] : HasEncoding code target where
  exists_equiv := ⟨encoding.equiv⟩

/-- The property that some embedding exists; unlike `Embeds`, it chooses no canonical one. -/
def IsEmbeddable {Code : Type u} [Denotes Code] (code : Code) (target : Type w) : Prop :=
  Nonempty (code ↪ target)

/-- Typeclass form of `IsEmbeddable`. -/
class HasEmbedding {Code : Type u} [Denotes Code]
    (code : Code) (target : Type w) : Prop where
  exists_embedding : IsEmbeddable code target

instance {Code : Type u} [Denotes Code] (code : Code) (target : Type w)
    [embedding : Embeds code target] : HasEmbedding code target where
  exists_embedding := ⟨embedding.embedding⟩

theorem IsEncoded.isEmbeddable {Code : Type u} [Denotes Code] {code : Code}
    {target : Type w} : IsEncoded code target → IsEmbeddable code target := by
  rintro ⟨equiv⟩
  exact ⟨equiv.toEmbedding⟩

/-- A code is empty exactly when its carrier is equivalent to `Empty`. -/
def IsEmptyCode {Code : Type u} [Denotes Code] (code : Code) : Prop := IsEncoded code Empty

abbrev EncodesEmpty {Code : Type u} [Denotes Code] (code : Code) := Encodes code Empty
abbrev EmbedsEmpty {Code : Type u} [Denotes Code] (code : Code) := Embeds code Empty
abbrev HasEmptyEncoding {Code : Type u} [Denotes Code] (code : Code) :=
  HasEncoding code Empty
abbrev IsEmptyEmbeddable {Code : Type u} [Denotes Code] (code : Code) :=
  IsEmbeddable code Empty
abbrev HasEmptyEmbedding {Code : Type u} [Denotes Code] (code : Code) :=
  HasEmbedding code Empty

/-- Codes with a distinguished empty type. -/
class HasEmpty (Code : Type u) [Denotes Code] where
  empty : Code
  encodes : Encodes empty Empty

/-- Codes with a distinguished unit type. -/
class HasUnit (Code : Type u) [Denotes Code] where
  unit : Code
  encodes : Encodes unit Unit

/-- Codes with a distinguished natural-number type. -/
class HasNat (Code : Type u) [Denotes Code] where
  nat : Code
  encodes : Encodes nat Nat

/-- Codes with a distinguished Boolean type. -/
class HasBool (Code : Type u) [Denotes Code] where
  bool : Code
  encodes : Encodes bool Bool

/-- Codes with concrete binary coproducts. -/
class HasCoproduct (Code : Type u) [Denotes Code] where
  coproduct : Code → Code → Code
  encodes (left right : Code) : Encodes (coproduct left right) (left ⊕ right)

/-- Codes with concrete binary products. -/
class HasProduct (Code : Type u) [Denotes Code] where
  product : Code → Code → Code
  encodes (left right : Code) : Encodes (product left right) (left × right)

/-- Codes with concrete exponentials. -/
class HasExponential (Code : Type u) [Denotes Code] where
  exponential : Code → Code → Code
  encodes (domain codomain : Code) : Encodes (exponential domain codomain) (domain → codomain)

/-! The concrete type formers preserve canonical equivalences. -/

instance {Code : Type u} [Denotes Code] [HasCoproduct Code]
    (left right : Code) (X : Type v) (Y : Type w) [Encodes left X] [Encodes right Y] :
    Encodes (HasCoproduct.coproduct left right) (X ⊕ Y) where
  equiv := (HasCoproduct.encodes left right).equiv.trans <|
    Equiv.sumCongr Encodes.equiv Encodes.equiv

instance {Code : Type u} [Denotes Code] [HasProduct Code]
    (left right : Code) (X : Type v) (Y : Type w) [Encodes left X] [Encodes right Y] :
    Encodes (HasProduct.product left right) (X × Y) where
  equiv := (HasProduct.encodes left right).equiv.trans <|
    Equiv.prodCongr Encodes.equiv Encodes.equiv

instance {Code : Type u} [Denotes Code] [HasExponential Code]
    (domain codomain : Code) (X : Type v) (Y : Type w)
    [Encodes domain X] [Encodes codomain Y] :
    Encodes (HasExponential.exponential domain codomain) (X → Y) where
  equiv := (HasExponential.encodes domain codomain).equiv.trans <|
    Equiv.arrowCongr Encodes.equiv Encodes.equiv

/-! Coproducts and products also preserve embeddings. There is deliberately
no analogous exponential instance: an embedding of domains has the wrong
variance for transporting arbitrary functions. -/

instance {Code : Type u} [Denotes Code] [HasCoproduct Code]
    (left right : Code) (X : Type v) (Y : Type w) [Embeds left X] [Embeds right Y] :
    Embeds (HasCoproduct.coproduct left right) (X ⊕ Y) where
  embedding := (HasCoproduct.encodes left right).equiv.toEmbedding.trans <|
    Function.Embedding.sumMap Embeds.embedding Embeds.embedding

instance {Code : Type u} [Denotes Code] [HasProduct Code]
    (left right : Code) (X : Type v) (Y : Type w) [Embeds left X] [Embeds right Y] :
    Embeds (HasProduct.product left right) (X × Y) where
  embedding := (HasProduct.encodes left right).equiv.toEmbedding.trans <|
    Function.Embedding.prodMap Embeds.embedding Embeds.embedding

section ClosureExamples

variable {Code : Type u} [Denotes Code] {A B : Code} {X : Type v} {Y : Type w}

example [HasCoproduct Code] [Encodes A X] [Encodes B Y] :
    Encodes (HasCoproduct.coproduct A B) (X ⊕ Y) := inferInstance

example [HasProduct Code] [Embeds A X] [Embeds B Y] :
    Embeds (HasProduct.product A B) (X × Y) := inferInstance

example [HasExponential Code] [Encodes A X] [Encodes B Y] :
    Encodes (HasExponential.exponential A B) (X → Y) := inferInstance

end ClosureExamples

namespace TypeFormers

def coproduct {Code : Type u} [Denotes Code] [HasCoproduct Code]
    (left right : Code) : Code := HasCoproduct.coproduct left right

def product {Code : Type u} [Denotes Code] [HasProduct Code]
    (left right : Code) : Code := HasProduct.product left right

def exponential {Code : Type u} [Denotes Code] [HasExponential Code]
    (domain codomain : Code) : Code := HasExponential.exponential domain codomain

end TypeFormers

scoped[SimpTypeFormers] infixr:65 " ⊕ₛ " => Nucleus.TypeFormers.coproduct
scoped[SimpTypeFormers] infixr:70 " ⊗ₛ " => Nucleus.TypeFormers.product
scoped[SimpTypeFormers] infixr:60 " ⇨ₛ " => Nucleus.TypeFormers.exponential

namespace TypeFormers

variable {Code : Type u} [Denotes Code]

local infixr:65 " ⊕ₛ " => coproduct (Code := Code)
local infixr:70 " ⊗ₛ " => product (Code := Code)
local infixr:60 " ⇨ₛ " => exponential (Code := Code)

def emptyEquiv [HasEmpty Code] : (HasEmpty.empty : Code) ≃ Empty := HasEmpty.encodes.equiv
def unitEquiv [HasUnit Code] : (HasUnit.unit : Code) ≃ Unit := HasUnit.encodes.equiv
def natEquiv [HasNat Code] : (HasNat.nat : Code) ≃ Nat := HasNat.encodes.equiv
def boolEquiv [HasBool Code] : (HasBool.bool : Code) ≃ Bool := HasBool.encodes.equiv

def coproductEquiv [HasCoproduct Code] (left right : Code) :
    (left ⊕ₛ right) ≃ (left ⊕ right) := (HasCoproduct.encodes left right).equiv

def productEquiv [HasProduct Code] (left right : Code) :
    (left ⊗ₛ right) ≃ (left × right) := (HasProduct.encodes left right).equiv

def exponentialEquiv [HasExponential Code] (domain codomain : Code) :
    (domain ⇨ₛ codomain) ≃ (domain → codomain) :=
  (HasExponential.encodes domain codomain).equiv

def inl [HasCoproduct Code] {left right : Code} : left → (left ⊕ₛ right) :=
  fun value => (coproductEquiv left right).symm (.inl value)

def inr [HasCoproduct Code] {left right : Code} : right → (left ⊕ₛ right) :=
  fun value => (coproductEquiv left right).symm (.inr value)

def copair [HasCoproduct Code] {left right : Code} {target : Type w}
    (onLeft : left → target) (onRight : right → target) : (left ⊕ₛ right) → target :=
  fun value => Sum.elim onLeft onRight (coproductEquiv left right value)

def pair [HasProduct Code] {left right : Code} (leftValue : left) (rightValue : right) :
    left ⊗ₛ right := (productEquiv left right).symm (leftValue, rightValue)

def fst [HasProduct Code] {left right : Code} : (left ⊗ₛ right) → left :=
  fun value => (productEquiv left right value).1

def snd [HasProduct Code] {left right : Code} : (left ⊗ₛ right) → right :=
  fun value => (productEquiv left right value).2

def curry [HasExponential Code] {domain codomain : Code}
    (function : domain → codomain) : domain ⇨ₛ codomain :=
  (exponentialEquiv domain codomain).symm function

def apply [HasExponential Code] {domain codomain : Code}
    (function : domain ⇨ₛ codomain) (argument : domain) : codomain :=
  exponentialEquiv domain codomain function argument

/-- Additive symmetry transported through the distinguished coproduct equivalences. -/
def coproductComm [HasCoproduct Code] (A B : Code) : (A ⊕ₛ B) ≃ (B ⊕ₛ A) :=
  (coproductEquiv A B).trans ((Equiv.sumComm A B).trans (coproductEquiv B A).symm)

def coproductAssoc [HasCoproduct Code] (A B C : Code) :
    ((A ⊕ₛ B) ⊕ₛ C) ≃ (A ⊕ₛ (B ⊕ₛ C)) :=
  (coproductEquiv (A ⊕ₛ B) C).trans <|
    (Equiv.sumCongr (coproductEquiv A B) (Equiv.refl C)).trans <|
    (Equiv.sumAssoc A B C).trans <|
    (Equiv.sumCongr (Equiv.refl A) (coproductEquiv B C).symm).trans <|
    (coproductEquiv A (B ⊕ₛ C)).symm

def productComm [HasProduct Code] (A B : Code) : (A ⊗ₛ B) ≃ (B ⊗ₛ A) :=
  (productEquiv A B).trans ((Equiv.prodComm A B).trans (productEquiv B A).symm)

def productAssoc [HasProduct Code] (A B C : Code) :
    ((A ⊗ₛ B) ⊗ₛ C) ≃ (A ⊗ₛ (B ⊗ₛ C)) :=
  (productEquiv (A ⊗ₛ B) C).trans <|
    (Equiv.prodCongr (productEquiv A B) (Equiv.refl C)).trans <|
    (Equiv.prodAssoc A B C).trans <|
    (Equiv.prodCongr (Equiv.refl A) (productEquiv B C).symm).trans <|
    (productEquiv A (B ⊗ₛ C)).symm

def coproductRightUnitor [HasCoproduct Code] [HasEmpty Code] (A : Code) :
    (A ⊕ₛ HasEmpty.empty) ≃ A :=
  (coproductEquiv A HasEmpty.empty).trans <|
    (Equiv.sumCongr (Equiv.refl A) emptyEquiv).trans (Equiv.sumEmpty A Empty)

def coproductLeftUnitor [HasCoproduct Code] [HasEmpty Code] (A : Code) :
    (HasEmpty.empty ⊕ₛ A) ≃ A :=
  (coproductComm _ A).trans (coproductRightUnitor A)

def productRightUnitor [HasProduct Code] [HasUnit Code] (A : Code) :
    (A ⊗ₛ HasUnit.unit) ≃ A :=
  (productEquiv A HasUnit.unit).trans <|
    (Equiv.prodCongr (Equiv.refl A) unitEquiv).trans (Equiv.prodUnique A Unit)

def productLeftUnitor [HasProduct Code] [HasUnit Code] (A : Code) :
    (HasUnit.unit ⊗ₛ A) ≃ A :=
  (productComm _ A).trans (productRightUnitor A)

def productEmptyRight [HasProduct Code] [HasEmpty Code] (A : Code) :
    (A ⊗ₛ HasEmpty.empty) ≃ (HasEmpty.empty : Code) :=
  (productEquiv A HasEmpty.empty).trans <|
    (Equiv.prodCongr (Equiv.refl A) emptyEquiv).trans <|
    (Equiv.prodEmpty A).trans emptyEquiv.symm

def productEmptyLeft [HasProduct Code] [HasEmpty Code] (A : Code) :
    (HasEmpty.empty ⊗ₛ A) ≃ (HasEmpty.empty : Code) :=
  (productComm _ A).trans (productEmptyRight A)

def productCoproductDistrib [HasProduct Code] [HasCoproduct Code] (A B C : Code) :
    (A ⊗ₛ (B ⊕ₛ C)) ≃ ((A ⊗ₛ B) ⊕ₛ (A ⊗ₛ C)) :=
  (productEquiv A (B ⊕ₛ C)).trans <|
    (Equiv.prodCongr (Equiv.refl A) (coproductEquiv B C)).trans <|
    (Equiv.prodSumDistrib A B C).trans <|
    (Equiv.sumCongr (productEquiv A B).symm (productEquiv A C).symm).trans <|
    (coproductEquiv (A ⊗ₛ B) (A ⊗ₛ C)).symm

def coproductProductDistrib [HasProduct Code] [HasCoproduct Code] (A B C : Code) :
    ((A ⊕ₛ B) ⊗ₛ C) ≃ ((A ⊗ₛ C) ⊕ₛ (B ⊗ₛ C)) :=
  (productEquiv (A ⊕ₛ B) C).trans <|
    (Equiv.prodCongr (coproductEquiv A B) (Equiv.refl C)).trans <|
    (Equiv.sumProdDistrib A B C).trans <|
    (Equiv.sumCongr (productEquiv A C).symm (productEquiv B C).symm).trans <|
    (coproductEquiv (A ⊗ₛ C) (B ⊗ₛ C)).symm

def exponentialCurry [HasProduct Code] [HasExponential Code] (A B C : Code) :
    ((A ⊗ₛ B) ⇨ₛ C) ≃ (A ⇨ₛ (B ⇨ₛ C)) :=
  (exponentialEquiv (A ⊗ₛ B) C).trans <|
    (Equiv.arrowCongr (productEquiv A B) (Equiv.refl C)).trans <|
    (Equiv.curry A B C).trans <|
    (Equiv.arrowCongr (Equiv.refl A) (exponentialEquiv B C).symm).trans <|
    (exponentialEquiv A (B ⇨ₛ C)).symm

def coproductExponential [HasCoproduct Code] [HasProduct Code] [HasExponential Code]
    (A B C : Code) : ((A ⊕ₛ B) ⇨ₛ C) ≃ ((A ⇨ₛ C) ⊗ₛ (B ⇨ₛ C)) :=
  (exponentialEquiv (A ⊕ₛ B) C).trans <|
    (Equiv.arrowCongr (coproductEquiv A B) (Equiv.refl C)).trans <|
    (Equiv.sumArrowEquivProdArrow A B C).trans <|
    (Equiv.prodCongr (exponentialEquiv A C).symm (exponentialEquiv B C).symm).trans <|
    (productEquiv (A ⇨ₛ C) (B ⇨ₛ C)).symm

private def boolUnitSum : Bool ≃ (Unit ⊕ Unit) where
  toFun
    | false => .inl ()
    | true => .inr ()
  invFun
    | .inl _ => false
    | .inr _ => true
  left_inv value := by cases value <;> rfl
  right_inv value := by cases value <;> rfl

def boolEquivUnitCoproduct [HasBool Code] [HasUnit Code] [HasCoproduct Code] :
    (HasBool.bool : Code) ≃ (HasUnit.unit ⊕ₛ HasUnit.unit) :=
  boolEquiv.trans <| boolUnitSum.trans <|
    (Equiv.sumCongr unitEquiv.symm unitEquiv.symm).trans
      (coproductEquiv HasUnit.unit HasUnit.unit).symm

private def natUnitSum : Nat ≃ (Unit ⊕ Nat) where
  toFun
    | 0 => .inl ()
    | n + 1 => .inr n
  invFun
    | .inl _ => 0
    | .inr n => n + 1
  left_inv value := by cases value <;> rfl
  right_inv value := by cases value <;> rfl

def natEquivUnitCoproduct [HasNat Code] [HasUnit Code] [HasCoproduct Code] :
    (HasNat.nat : Code) ≃ (HasUnit.unit ⊕ₛ HasNat.nat) :=
  natEquiv.trans <| natUnitSum.trans <|
    (Equiv.sumCongr unitEquiv.symm natEquiv.symm).trans
      (coproductEquiv HasUnit.unit HasNat.nat).symm

end TypeFormers

/-! `Type u` is the tautological concrete model. -/

instance : Denotes (Type u) where denote type := type

instance : HasEmpty (Type u) where
  empty := ULift.{u} Empty
  encodes := ⟨Equiv.ulift⟩

instance : HasUnit (Type u) where
  unit := ULift.{u} Unit
  encodes := ⟨Equiv.ulift⟩

instance : HasNat (Type u) where
  nat := ULift.{u} Nat
  encodes := ⟨Equiv.ulift⟩

instance : HasBool (Type u) where
  bool := ULift.{u} Bool
  encodes := ⟨Equiv.ulift⟩

instance : HasCoproduct (Type u) where
  coproduct := Sum
  encodes _ _ := ⟨Equiv.refl _⟩

instance : HasProduct (Type u) where
  product := Prod
  encodes _ _ := ⟨Equiv.refl _⟩

instance : HasExponential (Type u) where
  exponential domain codomain := domain → codomain
  encodes _ _ := ⟨Equiv.refl _⟩

end Nucleus
