import Nucleus.HolE.Named.Dense.Representation

/-!
# Publicly rooted encodings

The definitions here do not assume finiteness, well-foundedness, or even that
decoding terminates structurally.  A decoder may target an independently
defined cotree type, so cyclic and infinite representations fit the same API.
-/

namespace Nucleus.HolE.Named.Unsorted.Dense

universe u v w x
set_option linter.checkUnivs false

/-- Node families which permit their child index type to be changed. -/
class MapIndices (N : Type u → Type v) where
  mapIndices : (ι → κ) → N ι → N κ

instance {Sig : Signature.{u}} {Name : Type} : MapIndices (Node Sig Name) where
  mapIndices f node := ⟨node.tag, node.children.map f⟩

/-- A forest bundled with the ordered list of indices visible to clients. -/
structure PublicEncoding (N : Type u → Type v) (ι : Type u) where
  forest : ι → Option (N ι)
  exports : List ι

/-- The single-export form of `PublicEncoding`. -/
structure RootedEncoding (N : Type u → Type v) (ι : Type u) where
  forest : ι → Option (N ι)
  root : ι

/-- View a concrete single-tree encoder result as an absolutely numbered,
single-export encoding. -/
def EncodingResult.toRooted {Sig : Signature.{u}} {Name : Type}
    (result : EncodingResult Sig Name) :
    RootedEncoding (Node Sig Name) Nat where
  forest index := if result.offset ≤ index then result.nodes[index - result.offset]? else none
  root := result.root

/-- View a concrete list encoder result as an absolutely numbered public
encoding.  Its public indices retain the input order. -/
def ListEncodingResult.toPublic {Sig : Signature.{u}} {Name : Type}
    (result : ListEncodingResult Sig Name) :
    PublicEncoding (Node Sig Name) Nat where
  forest index := if result.offset ≤ index then result.nodes[index - result.offset]? else none
  exports := result.roots

def RootedEncoding.toPublic (encoding : RootedEncoding N ι) : PublicEncoding N ι :=
  ⟨encoding.forest, [encoding.root]⟩

def PublicEncoding.rooted? (encoding : PublicEncoding N ι) : Option (RootedEncoding N ι) :=
  match encoding.exports with
  | [root] => some ⟨encoding.forest, root⟩
  | _ => none

@[simp] theorem RootedEncoding.rooted?_toPublic (encoding : RootedEncoding N ι) :
    encoding.toPublic.rooted? = some encoding := by cases encoding <;> rfl

/-- If the partial projection succeeds, converting back loses no data. -/
theorem PublicEncoding.toPublic_of_rooted?_eq_some
    (encoding : PublicEncoding N ι) (rooted : RootedEncoding N ι)
    (success : encoding.rooted? = some rooted) : rooted.toPublic = encoding := by
  rcases encoding with ⟨forest, exports⟩
  simp only [PublicEncoding.rooted?] at success
  cases exports with
  | nil => contradiction
  | cons root rest =>
      cases rest with
      | nil => simp only [Option.some.injEq] at success; cases success; rfl
      | cons next rest => contradiction

/-- Observable decoding of all public roots. -/
def PublicEncoding.decode
    (decoder : (ι → Option (N ι)) → ι → D) (encoding : PublicEncoding N ι) : List D :=
  encoding.exports.map (decoder encoding.forest)

/-- Observable decoding of the sole public root. -/
def RootedEncoding.decode
    (decoder : (ι → Option (N ι)) → ι → D) (encoding : RootedEncoding N ι) : D :=
  decoder encoding.forest encoding.root

@[simp] theorem RootedEncoding.decode_toPublic
    (decoder : (ι → Option (N ι)) → ι → D) (encoding : RootedEncoding N ι) :
    encoding.toPublic.decode decoder = [encoding.decode decoder] := rfl

/-- Two encodings are equivalent precisely when their public decodings agree.
Private garbage, sharing, cycles, and choice of indices are unobservable. -/
def PublicEncoding.Equivalent
    (decoder : (ι → Option (N ι)) → ι → D) (left right : PublicEncoding N ι) : Prop :=
  left.decode decoder = right.decode decoder

def PublicEncoding.decodingSetoid
    (decoder : (ι → Option (N ι)) → ι → D) : Setoid (PublicEncoding N ι) where
  r := PublicEncoding.Equivalent decoder
  iseqv := ⟨fun _ => rfl, fun equality => equality.symm,
    fun left middle => left.trans middle⟩

/-- Decoding equivalence for the one-root presentation. -/
def RootedEncoding.Equivalent
    (decoder : (ι → Option (N ι)) → ι → D) (left right : RootedEncoding N ι) : Prop :=
  left.decode decoder = right.decode decoder

def RootedEncoding.decodingSetoid
    (decoder : (ι → Option (N ι)) → ι → D) : Setoid (RootedEncoding N ι) where
  r := RootedEncoding.Equivalent decoder
  iseqv := ⟨fun _ => rfl, fun equality => equality.symm,
    fun left middle => left.trans middle⟩

theorem RootedEncoding.equivalent_toPublic_iff
    (decoder : (ι → Option (N ι)) → ι → D) (left right : RootedEncoding N ι) :
    PublicEncoding.Equivalent decoder left.toPublic right.toPublic ↔
      RootedEncoding.Equivalent decoder left right := by
  simp [PublicEncoding.Equivalent, RootedEncoding.Equivalent]

/-- Disjoint concatenation preserves both forests without imposing decidable
equality or renumbering either input. -/
def PublicEncoding.sum [MapIndices N]
    (left : PublicEncoding N ι) (right : PublicEncoding N κ) :
    PublicEncoding N (ι ⊕ κ) where
  forest
    | .inl index => (left.forest index).map (MapIndices.mapIndices Sum.inl)
    | .inr index => (right.forest index).map (MapIndices.mapIndices Sum.inr)
  exports := left.exports.map Sum.inl ++ right.exports.map Sum.inr

@[simp] theorem PublicEncoding.sum_exports_length [MapIndices N]
    (left : PublicEncoding N ι) (right : PublicEncoding N κ) :
    (left.sum right).exports.length = left.exports.length + right.exports.length := by
  simp [PublicEncoding.sum]

def PublicEncoding.map [MapIndices N] (f : ι → κ)
    (merge : κ → Option (N κ)) (encoding : PublicEncoding N ι) : PublicEncoding N κ where
  forest := merge
  exports := encoding.exports.map f

@[simp] theorem PublicEncoding.map_exports_length [MapIndices N] (f : ι → κ)
    (merge : κ → Option (N κ)) (encoding : PublicEncoding N ι) :
    (encoding.map f merge).exports.length = encoding.exports.length := by
  simp [PublicEncoding.map]

/-- Reindexing is observationally sound whenever the chosen target forest and
decoder preserve decoding at every public root.  Injectivity on the live
dependency closure is one useful, node-specific way to establish `preserves`;
the generic wrapper needs only the exact semantic condition. -/
theorem PublicEncoding.decode_map
    [MapIndices N] (sourceDecoder : (ι → Option (N ι)) → ι → D)
    (targetDecoder : (κ → Option (N κ)) → κ → D) (f : ι → κ)
    (merge : κ → Option (N κ)) (encoding : PublicEncoding N ι)
    (preserves : ∀ index ∈ encoding.exports,
      targetDecoder merge (f index) = sourceDecoder encoding.forest index) :
    (encoding.map f merge).decode targetDecoder = encoding.decode sourceDecoder := by
  simp only [PublicEncoding.decode, PublicEncoding.map, List.map_map]
  apply List.map_congr_left
  intro index member
  exact preserves index member

/-- A partial reindexing need only be defined on the exposed live roots at
this raw level.  Dependency closure and decoder preservation are properties
which can be imposed by a particular node theory. -/
structure PublicEncoding.PartialMap (encoding : PublicEncoding N ι) (κ : Type w) where
  map : ι → Option κ
  exportsDefined : ∀ index, index ∈ encoding.exports → ∃ target, map index = some target

/-- The quotient of raw encodings by their observable decodings.  Its target
`D` may itself be a coinductive or quotient cotree type. -/
abbrev PublicEncoding.Quotient
    {N : Type u → Type v} {ι : Type u} {D : Type x}
    (decoder : (ι → Option (N ι)) → ι → D) :=
  _root_.Quotient (PublicEncoding.decodingSetoid decoder)

/-- A raw operation descends to decoding quotients exactly when it respects
decoding equivalence.  This is the common foundation for quotient-level sum,
reindexing, and later node-specific operations. -/
def PublicEncoding.Quotient.map
    {N : Type u → Type v} {ι : Type u} {D : Type x}
    {N' : Type u → Type v} {κ : Type u} {D' : Type x}
    (sourceDecoder : (ι → Option (N ι)) → ι → D)
    (targetDecoder : (κ → Option (N' κ)) → κ → D')
    (operation : PublicEncoding N ι → PublicEncoding N' κ)
    (congruent : ∀ {left right}, PublicEncoding.Equivalent sourceDecoder left right →
      PublicEncoding.Equivalent targetDecoder (operation left) (operation right)) :
    PublicEncoding.Quotient sourceDecoder → PublicEncoding.Quotient targetDecoder :=
  _root_.Quotient.lift
    (fun encoding => _root_.Quotient.mk _ (operation encoding))
    (fun _ _ equivalent => _root_.Quotient.sound (congruent equivalent))

namespace NoncanonicalIntegerExample

/-- Deliberately redundant integer representation. -/
structure Encoding where
  value : Int
  padding : Nat
  deriving DecidableEq

def decode (encoding : Encoding) : Int := encoding.value

def sevenA : Encoding := ⟨7, 0⟩
def sevenB : Encoding := ⟨7, 12⟩

example : sevenA ≠ sevenB := by decide
example : decode sevenA = decode sevenB := rfl

def decodingSetoid : Setoid Encoding where
  r left right := decode left = decode right
  iseqv := ⟨fun _ => rfl, fun equality => equality.symm,
    fun left middle => left.trans middle⟩

/-- Distinct integer encodings become the same value after quotienting by
canonical decoding. -/
example : Quotient.mk decodingSetoid sevenA = Quotient.mk decodingSetoid sevenB := by
  apply Quotient.sound
  rfl

end NoncanonicalIntegerExample

end Nucleus.HolE.Named.Unsorted.Dense
