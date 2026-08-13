import Nucleus.Cbor.Dag
import Nucleus.Json.CasMap

/-!
# Codec-aware CBOR views of byte CASes

Storage returns bytes plus a codec discriminator. A registry interprets those
bytes as a linked, string-key CBOR tree. Native DAG-CBOR and JSON codecs can
decode into that common tree; raw blocks become one CBOR byte-string leaf.
After interpretation, every link in the resulting tree is recursively fetched
and interpreted. One unit of gas is consumed per fetched block.
-/

namespace Nucleus

/-- Built-in formats plus an open numeric codec space. -/
inductive CborBlockFormat where
  | dagCbor
  | dagJson
  | raw
  | other (code : Nat)
  deriving DecidableEq

/-- Bytes stored under a name, accompanied by their intended interpretation. -/
structure CborBlock where
  format : CborBlockFormat
  bytes : Bytes
  deriving DecidableEq

/-- The common output of every non-opaque codec. Links remain visible for the
recursive CAS phase. -/
abbrev LinkedCborBlock (Name : Type) := Json (Link StringKeyCborScalar Name)

/-- A codec registry. Failure means only that this registry cannot interpret
the block. A JSON decoder embeds JSON scalars into `StringKeyCborScalar`; a
native decoder recognizes DAG-CBOR tag-42 links. -/
structure CborCodecRegistry (Name : Type) where
  decode : CborBlockFormat → Bytes → Unknown (LinkedCborBlock Name)
  raw_decode : ∀ bytes, decode .raw bytes = .known (.scalar (.inl (.bytes bytes)))

/-- A finite CAS of uninterpreted blocks. -/
structure CborBlockCas (Name : Type) where
  names : Finset Name
  blocks : {name // name ∈ names} → CborBlock

namespace CborBlockCas

variable {Name : Type} [DecidableEq Name]

def get? (cas : CborBlockCas Name) (name : Name) : Unknown CborBlock :=
  if h : name ∈ cas.names then .known (cas.blocks ⟨name, h⟩) else .unknown

/-- Decode one fetched block, retaining its links for recursive traversal. -/
def decodeBlock (registry : CborCodecRegistry Name) (block : CborBlock) :
    Unknown (LinkedCborBlock Name) := registry.decode block.format block.bytes

/-- Fetch bytes, decode according to their codec, then recursively traverse all
links exposed by that decoded value. Parsing is free; each block lookup costs
one unit of gas. -/
def fetch (cas : CborBlockCas Name) (registry : CborCodecRegistry Name) :
    Nat → Name → Unknown StringKeyCbor
  | 0, _ => .unknown
  | gas + 1, name =>
      (cas.get? name).bind fun block =>
        (decodeBlock registry block).bind (JsonCas.derefWith (cas.fetch registry gas))

def dereference (cas : CborBlockCas Name) (registry : CborCodecRegistry Name)
    (gas : Nat) : Name → Unknown StringKeyCbor := cas.fetch registry gas

@[simp] theorem fetch_zero (cas : CborBlockCas Name)
    (registry : CborCodecRegistry Name) (name : Name) :
    cas.fetch registry 0 name = .unknown := rfl

omit [DecidableEq Name] in
/-- Raw blocks are terminal CBOR byte strings; they expose no recursive links. -/
theorem decodeBlock_raw (registry : CborCodecRegistry Name) (bytes : Bytes) :
    decodeBlock registry ⟨.raw, bytes⟩ = .known (.scalar (.inl (.bytes bytes))) :=
  registry.raw_decode bytes

/-- Extending a byte store may reveal missing blocks but cannot alter existing
ones. -/
def InformationLe (a b : CborBlockCas Name) : Prop :=
  ∀ name, Unknown.Le (a.get? name) (b.get? name)

instance : LE (CborBlockCas Name) := ⟨InformationLe⟩

omit [DecidableEq Name] in
private theorem interpret_mono (registry : CborCodecRegistry Name)
    {resolve₁ resolve₂ : Name → Unknown StringKeyCbor}
    (hresolve : ∀ name, Unknown.Le (resolve₁ name) (resolve₂ name))
    (block : CborBlock) :
    Unknown.Le
      ((decodeBlock registry block).bind (JsonCas.derefWith resolve₁))
      ((decodeBlock registry block).bind (JsonCas.derefWith resolve₂)) :=
  Unknown.bind_mono (Unknown.le_refl _) fun linked =>
    JsonCas.derefWith_mono hresolve linked

/-- Recursive codec-aware fetching is monotone under store extension. -/
theorem fetch_mono {a b : CborBlockCas Name} (hab : a ≤ b)
    (registry : CborCodecRegistry Name) : ∀ gas name,
    Unknown.Le (a.fetch registry gas name) (b.fetch registry gas name) := by
  intro gas
  induction gas with
  | zero => intro name; exact Unknown.unknown_le _
  | succ gas ih =>
      intro name
      exact Unknown.bind_mono (hab name) (interpret_mono registry ih)

/-- More traversal gas can only reveal more information. -/
theorem fetch_succ_mono (cas : CborBlockCas Name)
    (registry : CborCodecRegistry Name) : ∀ gas name,
    Unknown.Le (cas.fetch registry gas name) (cas.fetch registry (gas + 1) name) := by
  intro gas
  induction gas with
  | zero => intro name; exact Unknown.unknown_le _
  | succ gas ih =>
      intro name
      exact Unknown.bind_mono (Unknown.le_refl _) (interpret_mono registry ih)

theorem fetch_gas_mono (cas : CborBlockCas Name)
    (registry : CborCodecRegistry Name) {gas₁ gas₂ : Nat}
    (hgas : gas₁ ≤ gas₂) (name : Name) :
    Unknown.Le (cas.fetch registry gas₁ name) (cas.fetch registry gas₂ name) := by
  induction gas₂, hgas using Nat.le_induction with
  | base => exact Unknown.le_refl _
  | succ gas₂ _ ih =>
      exact Unknown.le_trans ih (fetch_succ_mono cas registry gas₂ name)

end CborBlockCas

end Nucleus
