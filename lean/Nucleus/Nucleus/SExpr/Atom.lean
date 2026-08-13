import Nucleus.Cbor.Bytes
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Disjoint
import Mathlib.Logic.Embedding.Basic

/-!
# S-expression atom capabilities

Small, orthogonal typeclasses describe which literal domains an atom type can
represent losslessly.  Symbols are literally a subtype of the atom carrier;
their optional string and natural-number spellings land in that subtype.

Disjointness is separate from representability.  This permits both tagged atom
types, whose literal classes are disjoint, and intentionally overlapping atom
types such as `String`.
-/

namespace Nucleus

universe u

/-- Atoms with a lossless string-literal injection. -/
class StringAtoms (Atom : Type u) where
  ofString : String ↪ Atom

/-- Atoms with a lossless byte-literal injection. -/
class ByteAtoms (Atom : Type u) where
  ofBytes : Bytes ↪ Atom

/-- Atoms with a lossless mathematical-integer injection. -/
class IntegerAtoms (Atom : Type u) where
  ofInteger : Int ↪ Atom

/-- A distinguished subtype of atoms regarded as symbols. -/
class SymbolAtoms (Atom : Type u) where
  symbols : Set Atom

/-- Symbols with a lossless injection from strings. -/
class StringSymbols (Atom : Type u) extends SymbolAtoms Atom where
  symbolOfString : String ↪ symbols

/-- Symbols with a lossless injection from natural numbers. -/
class NatSymbols (Atom : Type u) extends SymbolAtoms Atom where
  symbolOfNat : Nat ↪ symbols

/-- A runtime type name for each atom.  This is intentionally independent of
the available injections: applications may classify additional atom kinds. -/
class AtomTypeNames (Atom : Type u) where
  typeName : Atom → String

namespace Atom

variable {Atom : Type u}

/-- The symbol subtype selected for an atom carrier. -/
abbrev Symbol [SymbolAtoms Atom] := ↥(SymbolAtoms.symbols (Atom := Atom))

def ofString [StringAtoms Atom] : String ↪ Atom := StringAtoms.ofString
def ofBytes [ByteAtoms Atom] : Bytes ↪ Atom := ByteAtoms.ofBytes
def ofInteger [IntegerAtoms Atom] : Int ↪ Atom := IntegerAtoms.ofInteger
def symbolOfString [StringSymbols Atom] : String ↪ Symbol (Atom := Atom) :=
  StringSymbols.symbolOfString
def symbolOfNat [NatSymbols Atom] : Nat ↪ Symbol (Atom := Atom) :=
  NatSymbols.symbolOfNat
def typeName [AtomTypeNames Atom] (value : Atom) : String := AtomTypeNames.typeName value

end Atom

namespace AtomTypeName

def string : String := "string"
def bytes : String := "bytes"
def integer : String := "int"
def symbol : String := "symbol"

end AtomTypeName

/-- Injected string literals are classified as `"string"`. -/
class StringAtomsTypeName (α : Type u) [StringAtoms α] [AtomTypeNames α] : Prop where
  typeName_ofString : ∀ value,
    Atom.typeName (Atom.ofString (Atom := α) value) = AtomTypeName.string

/-- Injected byte literals are classified as `"bytes"`. -/
class ByteAtomsTypeName (α : Type u) [ByteAtoms α] [AtomTypeNames α] : Prop where
  typeName_ofBytes : ∀ value,
    Atom.typeName (Atom.ofBytes (Atom := α) value) = AtomTypeName.bytes

/-- Injected mathematical integers are classified as `"int"`. -/
class IntegerAtomsTypeName (α : Type u) [IntegerAtoms α]
    [AtomTypeNames α] : Prop where
  typeName_ofInteger : ∀ value,
    Atom.typeName (Atom.ofInteger (Atom := α) value) = AtomTypeName.integer

/-- Every member of the distinguished symbol subtype is classified as
`"symbol"`, independently of whether it has string or natural syntax. -/
class SymbolAtomsTypeName (α : Type u) [SymbolAtoms α]
    [AtomTypeNames α] : Prop where
  typeName_symbol : ∀ value : Atom.Symbol (Atom := α),
    Atom.typeName value.1 = AtomTypeName.symbol

/-- Standard type-name laws for all four common atom categories. -/
class StandardAtomTypeNames (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom]
    [IntegerAtoms Atom] [SymbolAtoms Atom] [AtomTypeNames Atom] : Prop extends
    StringAtomsTypeName Atom, ByteAtomsTypeName Atom,
    IntegerAtomsTypeName Atom, SymbolAtomsTypeName Atom where

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [SymbolAtoms Atom] [AtomTypeNames Atom] [h : StandardAtomTypeNames Atom] :
    StringAtomsTypeName Atom := h.toStringAtomsTypeName

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [SymbolAtoms Atom] [AtomTypeNames Atom] [h : StandardAtomTypeNames Atom] :
    ByteAtomsTypeName Atom := h.toByteAtomsTypeName

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [SymbolAtoms Atom] [AtomTypeNames Atom] [h : StandardAtomTypeNames Atom] :
    IntegerAtomsTypeName Atom := h.toIntegerAtomsTypeName

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [SymbolAtoms Atom] [AtomTypeNames Atom] [h : StandardAtomTypeNames Atom] :
    SymbolAtomsTypeName Atom := h.toSymbolAtomsTypeName

/-- The images of two embeddings into the same carrier do not overlap. -/
class DisjointEmbeddings {Left : Type*} {Right : Type*} {Target : Type*}
    (left : Left ↪ Target) (right : Right ↪ Target) : Prop where
  ne : ∀ (a : Left) (b : Right), left a ≠ right b

namespace DisjointEmbeddings

variable {Left Right Target : Type*} {left : Left ↪ Target} {right : Right ↪ Target}

theorem symmetric [DisjointEmbeddings left right] : DisjointEmbeddings right left :=
  ⟨fun b a h => DisjointEmbeddings.ne a b h.symm⟩

theorem ranges [DisjointEmbeddings left right] :
    Disjoint (Set.range left) (Set.range right) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, h⟩
  exact DisjointEmbeddings.ne a b h.symm

theorem of_ranges
    (h : Disjoint (Set.range left) (Set.range right)) :
    DisjointEmbeddings left right := by
  constructor
  intro a b hab
  exact Set.disjoint_left.mp h ⟨a, rfl⟩ ⟨b, hab.symm⟩

end DisjointEmbeddings

/-- String and byte literals are distinct atom constructors. -/
abbrev StringBytesDisjoint (α : Type u) [StringAtoms α] [ByteAtoms α] :=
  DisjointEmbeddings (Atom.ofString (Atom := α)) (Atom.ofBytes (Atom := α))

/-- String and integer literals are distinct atom constructors. -/
abbrev StringIntegersDisjoint (α : Type u) [StringAtoms α] [IntegerAtoms α] :=
  DisjointEmbeddings (Atom.ofString (Atom := α)) (Atom.ofInteger (Atom := α))

/-- Byte and integer literals are distinct atom constructors. -/
abbrev BytesIntegersDisjoint (α : Type u) [ByteAtoms α] [IntegerAtoms α] :=
  DisjointEmbeddings (Atom.ofBytes (Atom := α)) (Atom.ofInteger (Atom := α))

/-- The three common literal injections have pairwise-disjoint images. -/
class LiteralAtomsDisjoint (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom]
    [IntegerAtoms Atom] : Prop where
  stringsBytes : StringBytesDisjoint Atom
  stringsIntegers : StringIntegersDisjoint Atom
  bytesIntegers : BytesIntegersDisjoint Atom

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [h : LiteralAtomsDisjoint Atom] : StringBytesDisjoint Atom := h.stringsBytes

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [h : LiteralAtomsDisjoint Atom] : StringIntegersDisjoint Atom := h.stringsIntegers

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [h : LiteralAtomsDisjoint Atom] : BytesIntegersDisjoint Atom := h.bytesIntegers

namespace SymbolAtoms

variable {α : Type u} [SymbolAtoms α]

/-- Inclusion of the distinguished symbol subtype into its atom carrier. -/
def embedding : Atom.Symbol (Atom := α) ↪ α := Function.Embedding.subtype _

end SymbolAtoms

/-- String literals and symbols are distinct atom constructors. -/
abbrev StringsSymbolsDisjoint (α : Type u) [StringAtoms α] [SymbolAtoms α] :=
  DisjointEmbeddings (Atom.ofString (Atom := α))
    (SymbolAtoms.embedding (α := α))

/-- Byte literals and symbols are distinct atom constructors. -/
abbrev BytesSymbolsDisjoint (α : Type u) [ByteAtoms α] [SymbolAtoms α] :=
  DisjointEmbeddings (Atom.ofBytes (Atom := α))
    (SymbolAtoms.embedding (α := α))

/-- Integer literals and symbols are distinct atom constructors. -/
abbrev IntegersSymbolsDisjoint (α : Type u) [IntegerAtoms α]
    [SymbolAtoms α] :=
  DisjointEmbeddings (Atom.ofInteger (Atom := α))
    (SymbolAtoms.embedding (α := α))

/-- All common literal categories and the symbol subtype are pairwise disjoint. -/
class AtomKindsDisjoint (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom]
    [IntegerAtoms Atom] [SymbolAtoms Atom] : Prop extends LiteralAtomsDisjoint Atom where
  stringsSymbols : StringsSymbolsDisjoint Atom
  bytesSymbols : BytesSymbolsDisjoint Atom
  integersSymbols : IntegersSymbolsDisjoint Atom

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [SymbolAtoms Atom]
    [h : AtomKindsDisjoint Atom] : LiteralAtomsDisjoint Atom := h.toLiteralAtomsDisjoint

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [SymbolAtoms Atom]
    [h : AtomKindsDisjoint Atom] : StringsSymbolsDisjoint Atom := h.stringsSymbols

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [SymbolAtoms Atom]
    [h : AtomKindsDisjoint Atom] : BytesSymbolsDisjoint Atom := h.bytesSymbols

instance (Atom : Type u) [StringAtoms Atom] [ByteAtoms Atom] [IntegerAtoms Atom]
    [SymbolAtoms Atom]
    [h : AtomKindsDisjoint Atom] : IntegersSymbolsDisjoint Atom := h.integersSymbols

end Nucleus
