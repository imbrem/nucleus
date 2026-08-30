import Nucleus.Cbor.Atproto.Data

/-!
# Content addresses for AT Protocol values

This layer relates semantic values, their unique normal DRISL blocks, and CID
framing.  Hash collision resistance is not smuggled into canonicality: the
only theorem recovering bytes from equal CIDs takes injectivity of the chosen
digest function as an explicit hypothesis.
-/

namespace Nucleus.Atproto.Value

/-- A semantic value packaged with the structural bound needed to encode it. -/
abbrev Encodable (policy : Cid.Policy) :=
  {value : Value policy // Fits value}

/-- Normal value obtained from structural evidence. -/
noncomputable def Encodable.normal {policy : Cid.Policy}
    (value : Encodable policy) : {value : Value policy // Normal policy value} :=
  ⟨value.1, normal_of_fits value.1 value.2⟩

/-- Unique normal DRISL block for a structurally encodable value. -/
noncomputable def Encodable.block {policy : Cid.Policy}
    (value : Encodable policy) : Bytes :=
  encode value.normal

@[simp] theorem Encodable.decode?_block {policy : Cid.Policy}
    (value : Encodable policy) :
    decode? policy value.block = some value.1 := by
  exact decode?_encode value.normal

theorem Encodable.block_injective {policy : Cid.Policy}
    {left right : Encodable policy} (equal : left.block = right.block) :
    left = right := by
  apply Subtype.ext
  exact congrArg
    (fun normal : {value : Value policy // Normal policy value} => normal.1)
    (encode_injective equal)

/-- Blessed AT Protocol address: DRISL codec and SHA-256. -/
noncomputable def Encodable.addressSha256
    (model : Cid.DigestModel) (value : Encodable Cid.Policy.atproto) : Cid :=
  Cid.addressDrisl model value.block

@[simp] theorem Encodable.addressSha256_blessed
    (model : Cid.DigestModel) (value : Encodable Cid.Policy.atproto) :
    Cid.Policy.atproto.accepts (value.addressSha256 model) = true := rfl

@[simp] theorem Encodable.addressSha256_addresses
    (model : Cid.DigestModel) (value : Encodable Cid.Policy.atproto) :
    Cid.Addresses model (value.addressSha256 model) value.block := rfl

/-- Explicit Nucleus migration address: DRISL codec and BLAKE3. -/
noncomputable def Encodable.addressBlake3
    (model : Cid.DigestModel) (value : Encodable Cid.Policy.nucleus) : Cid :=
  Cid.addressDrislBlake3 model value.block

@[simp] theorem Encodable.addressBlake3_nucleus
    (model : Cid.DigestModel) (value : Encodable Cid.Policy.nucleus) :
    Cid.Policy.nucleus.accepts (value.addressBlake3 model) = true := rfl

@[simp] theorem Encodable.addressBlake3_not_blessed
    (model : Cid.DigestModel) (value : Encodable Cid.Policy.nucleus) :
    Cid.Policy.atproto.accepts (value.addressBlake3 model) = false := rfl

@[simp] theorem Encodable.addressBlake3_addresses
    (model : Cid.DigestModel) (value : Encodable Cid.Policy.nucleus) :
    Cid.Addresses model (value.addressBlake3 model) value.block := rfl

/-- Equal blessed addresses identify equal semantic values when SHA-256 is
injective on the relevant byte domain.  This cryptographic assumption is
separate from DRISL canonicality. -/
theorem Encodable.addressSha256_injective (model : Cid.DigestModel)
    (collisionFree : Function.Injective (model.digest .sha256)) :
    Function.Injective (Encodable.addressSha256 model) := by
  intro left right equal
  apply Encodable.block_injective
  apply collisionFree
  exact congrArg Cid.digest equal

/-- BLAKE3 analogue for the explicit Nucleus extension. -/
theorem Encodable.addressBlake3_injective (model : Cid.DigestModel)
    (collisionFree : Function.Injective (model.digest .blake3)) :
    Function.Injective (Encodable.addressBlake3 model) := by
  intro left right equal
  apply Encodable.block_injective
  apply collisionFree
  exact congrArg Cid.digest equal

end Nucleus.Atproto.Value
