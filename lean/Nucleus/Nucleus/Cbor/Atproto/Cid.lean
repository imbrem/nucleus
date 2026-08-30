import Nucleus.Cbor.Bytes
import Nucleus.O256

/-!
# AT Protocol content identifiers

AT Protocol accepts the deliberately small DASL CID subset: CIDv1, either
`raw` or `dag-cbor` (`DRISL`) content, SHA-256, and a 32-byte digest.  Every
code and length is therefore a one-byte unsigned varint, so the binary form is
exactly 36 bytes.  CBOR tag 42 contains one leading zero byte followed by that
binary CID.

Nucleus also needs BLAKE3 during migration.  It is represented as an explicit
policy extension, never as an AT Protocol blessed CID.  This module specifies
framing and policy; cryptographic implementations are supplied separately by
`DigestModel`.
-/

namespace Nucleus.Atproto

/-- Content kind carried by the CID codec code. -/
inductive CidCodec where
  | raw
  | drisl
  deriving DecidableEq, Repr

namespace CidCodec

/-- `raw = 0x55`; `drisl` retains the registered `dag-cbor = 0x71` code. -/
def code : CidCodec → UInt8
  | .raw => 0x55
  | .drisl => 0x71

/-- Decode precisely the two codecs blessed by AT Protocol. -/
def ofCode? : UInt8 → Option CidCodec
  | 0x55 => some .raw
  | 0x71 => some .drisl
  | _ => none

@[simp] theorem ofCode?_code (codec : CidCodec) :
    ofCode? codec.code = some codec := by
  cases codec <;> rfl

theorem code_injective : Function.Injective code := by
  intro left right equal
  have := congrArg ofCode? equal
  simpa using this

end CidCodec

/-- Hash algorithms understood by the migration format. -/
inductive CidHash where
  | sha256
  | blake3
  deriving DecidableEq, Repr

namespace CidHash

/-- Standard multihash codes: SHA-256 is `0x12`; BLAKE3 is `0x1e`. -/
def code : CidHash → UInt8
  | .sha256 => 0x12
  | .blake3 => 0x1e

/-- Decode the AT Protocol algorithm and the one explicit Nucleus extension. -/
def ofCode? : UInt8 → Option CidHash
  | 0x12 => some .sha256
  | 0x1e => some .blake3
  | _ => none

@[simp] theorem ofCode?_code (algorithm : CidHash) :
    ofCode? algorithm.code = some algorithm := by
  cases algorithm <;> rfl

theorem code_injective : Function.Injective code := by
  intro left right equal
  have := congrArg ofCode? equal
  simpa using this

end CidHash

/-- A CIDv1 in the fixed-width AT Protocol/Nucleus migration family. -/
structure Cid where
  codec : CidCodec
  hash : CidHash
  digest : O256
  deriving DecidableEq, Repr

namespace Cid

/-- CID version used by every accepted identifier. -/
def version : UInt8 := 0x01

/-- Fixed multihash digest-width field. -/
def digestLength : UInt8 := 0x20

/-- Binary CIDv1: version, codec, hash code, digest length, digest. -/
def binaryList (cid : Cid) : List UInt8 :=
  [version, cid.codec.code, cid.hash.code, digestLength] ++ cid.digest.bytes

/-- Compact binary CIDv1. -/
def binary (cid : Cid) : Bytes := Bytes.ofList cid.binaryList

/-- Tag-42 payload, including the mandatory historical zero prefix. -/
def tag42Payload (cid : Cid) : Bytes := Bytes.ofList (0x00 :: cid.binaryList)

@[simp] theorem binaryList_length (cid : Cid) : cid.binaryList.length = 36 := by
  simp [binaryList, O256.bytes_length]

@[simp] theorem binary_length (cid : Cid) : cid.binary.length = 36 := by
  simp [binary, binaryList_length]

@[simp] theorem tag42Payload_length (cid : Cid) : cid.tag42Payload.length = 37 := by
  simp [tag42Payload, binaryList_length]

/-- Parse the exact fixed-width binary CID subset. -/
def parseBinaryList? (bytes : List UInt8) : Option Cid := do
  if bytes.length != 36 then none else pure ()
  if bytes[0]? != some version then none else pure ()
  let codec ← CidCodec.ofCode? (← bytes[1]?)
  let hash ← CidHash.ofCode? (← bytes[2]?)
  if bytes[3]? != some digestLength then none else pure ()
  let digest ← O256.ofList? (bytes.drop 4)
  some ⟨codec, hash, digest⟩

/-- Parse one complete fixed-width binary CID. -/
def parseBinary? (bytes : Bytes) : Option Cid := parseBinaryList? bytes.toList

/-- Parse an exact tag-42 payload, including its required leading zero. -/
def parseTag42Payload? (bytes : Bytes) : Option Cid :=
  match bytes.toList with
  | 0x00 :: binary => parseBinaryList? binary
  | _ => none

@[simp] theorem parseBinaryList?_binaryList (cid : Cid) :
    parseBinaryList? cid.binaryList = some cid := by
  rcases cid with ⟨codec, hash, digest⟩
  cases codec <;> cases hash <;>
    simp [parseBinaryList?, binaryList, version, digestLength]

@[simp] theorem parseBinary?_binary (cid : Cid) :
    parseBinary? cid.binary = some cid := by
  simp [parseBinary?, binary]

@[simp] theorem parseTag42Payload?_tag42Payload (cid : Cid) :
    parseTag42Payload? cid.tag42Payload = some cid := by
  simp [parseTag42Payload?, tag42Payload]

/-- Binary framing is injective. -/
theorem binary_injective : Function.Injective binary := by
  intro left right equal
  have parsed := congrArg parseBinary? equal
  simpa using parsed

/-- Tag-42 payload framing is injective. -/
theorem tag42Payload_injective : Function.Injective tag42Payload := by
  intro left right equal
  have parsed := congrArg parseTag42Payload? equal
  simpa using parsed

/-- Hash and codec policy for links accepted at a data-model boundary. -/
structure Policy where
  acceptCodec : CidCodec → Bool
  acceptHash : CidHash → Bool

namespace Policy

/-- The exact AT Protocol blessed set: both codecs, SHA-256 only. -/
def atproto : Policy where
  acceptCodec := fun _ => true
  acceptHash
    | .sha256 => true
    | .blake3 => false

/-- Nucleus migration policy: AT Protocol plus 32-byte BLAKE3 multihashes. -/
def nucleus : Policy where
  acceptCodec := fun _ => true
  acceptHash := fun _ => true

/-- Whether a parsed CID is admitted by this policy. -/
def accepts (policy : Policy) (cid : Cid) : Bool :=
  policy.acceptCodec cid.codec && policy.acceptHash cid.hash

/-- Parse and check a complete tag-42 byte-string payload. -/
def acceptTag42Payload (policy : Policy) (bytes : Bytes) : Bool :=
  match parseTag42Payload? bytes with
  | some cid => policy.accepts cid
  | none => false

@[simp] theorem acceptTag42Payload_tag42Payload (policy : Policy) (cid : Cid) :
    policy.acceptTag42Payload cid.tag42Payload = policy.accepts cid := by
  simp [acceptTag42Payload]

@[simp] theorem atproto_accepts (codec : CidCodec) (digest : O256) :
    atproto.accepts ⟨codec, .sha256, digest⟩ = true := by
  cases codec <;> rfl

@[simp] theorem atproto_rejects_blake3 (codec : CidCodec) (digest : O256) :
    atproto.accepts ⟨codec, .blake3, digest⟩ = false := by
  cases codec <;> rfl

/-- AT Protocol policy is exactly the SHA-256 member of the migration family. -/
theorem atproto_accepts_iff (cid : Cid) :
    atproto.accepts cid = true ↔ cid.hash = .sha256 := by
  rcases cid with ⟨codec, hash, digest⟩
  cases codec <;> cases hash <;> simp [accepts, atproto]

@[simp] theorem nucleus_accepts (cid : Cid) : nucleus.accepts cid = true := by
  rcases cid with ⟨codec, hash, digest⟩
  cases codec <;> cases hash <;> rfl

/-- Every AT Protocol blessed CID is admitted by the Nucleus extension. -/
theorem atproto_implies_nucleus {cid : Cid}
    (_accepted : atproto.accepts cid = true) : nucleus.accepts cid = true :=
  nucleus_accepts cid

end Policy

/-- Abstract implementations of the two 256-bit digest algorithms.  Framing
theorems do not assume cryptographic properties of either function. -/
structure DigestModel where
  digest : CidHash → Bytes → O256

/-- The CID which addresses `content` under a selected codec and algorithm. -/
def address (model : DigestModel) (codec : CidCodec) (hash : CidHash)
    (content : Bytes) : Cid :=
  ⟨codec, hash, model.digest hash content⟩

/-- Semantic content-address claim made by a CID. -/
def Addresses (model : DigestModel) (cid : Cid) (content : Bytes) : Prop :=
  model.digest cid.hash content = cid.digest

instance (model : DigestModel) (cid : Cid) (content : Bytes) :
    Decidable (Addresses model cid content) := by
  unfold Addresses
  infer_instance

@[simp] theorem address_addresses (model : DigestModel) (codec : CidCodec)
    (hash : CidHash) (content : Bytes) :
    Addresses model (address model codec hash content) content := rfl

/-- AT Protocol normal-form address: DRISL codec and SHA-256. -/
def addressDrisl (model : DigestModel) (content : Bytes) : Cid :=
  address model .drisl .sha256 content

@[simp] theorem addressDrisl_blessed (model : DigestModel) (content : Bytes) :
    Policy.atproto.accepts (addressDrisl model content) = true := rfl

/-- Nucleus extension address: DRISL codec and BLAKE3. -/
def addressDrislBlake3 (model : DigestModel) (content : Bytes) : Cid :=
  address model .drisl .blake3 content

@[simp] theorem addressDrislBlake3_not_blessed
    (model : DigestModel) (content : Bytes) :
    Policy.atproto.accepts (addressDrislBlake3 model content) = false := rfl

@[simp] theorem addressDrislBlake3_nucleus
    (model : DigestModel) (content : Bytes) :
    Policy.nucleus.accepts (addressDrislBlake3 model content) = true := rfl

end Cid

end Nucleus.Atproto
