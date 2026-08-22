import Nucleus.Cbor.Wire
import Nucleus.Hol.Ethane.Arena.OneBased.Cbor
import Nucleus.Hol.Ethane.Arena.OneBased.Resolve
import Nucleus.Json.Cas

/-!
# CAS-backed resolution of one-based Ethane arenas

The byte store, hash function, and successful-decode cache are kept separate.
Absence is unknown information and is therefore retryable.  A sound cache can
only return the same arena as an address-checked byte-store lookup.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus

/-- The CAS used by this object format chooses a 32-byte content hash. -/
class Hash32 where
  hash : Bytes → O256

/-- A partial content-addressed byte source. -/
structure ByteCas where
  get : O256 → Unknown Bytes

namespace ByteCas

/-- Store extension may reveal an address but cannot change known bytes. -/
def InformationLe (left right : ByteCas) : Prop :=
  ∀ address, Unknown.Le (left.get address) (right.get address)

instance : LE ByteCas := ⟨InformationLe⟩

end ByteCas

/-- Parse exactly one CBOR arena value. -/
def decodeCborArena? (bytes : Bytes) : Option Arena := do
  let value ← Nucleus.CborWire.parse? bytes
  Nucleus.Hol.Ethane.OneBased.Cbor.decodeArena? value

/-- Address-check and decode bytes obtained for `address`. -/
def decodeAddressed [Hash32] (address : O256) (bytes : Bytes) : Unknown Arena :=
  if Hash32.hash bytes = address then
    match decodeCborArena? bytes with
    | none => .unknown
    | some arena => .known arena
  else .unknown

/-- Fetch, authenticate, and decode one arena. -/
def ByteCas.fetch [Hash32] (cas : ByteCas) (address : O256) : Unknown Arena :=
  (cas.get address).bind (decodeAddressed address)

theorem ByteCas.fetch_mono [Hash32] {left right : ByteCas} (extension : left ≤ right)
    (address : O256) : Unknown.Le (left.fetch address) (right.fetch address) :=
  Unknown.bind_mono (extension address) fun bytes => Unknown.le_refl (decodeAddressed address bytes)

/-- Resolver induced by authenticated CBOR arena objects. -/
def ByteCas.resolver [Hash32] (cas : ByteCas) : Resolver := fun link =>
  match cas.fetch link.blake3 with
  | .unknown => none
  | .known arena => some arena

/-- Successful resolution persists when a CAS gains information. -/
theorem ByteCas.resolver_mono [Hash32] {left right : ByteCas} (extension : left ≤ right)
    {link : Link} {arena : Arena} (resolved : left.resolver link = some arena) :
    right.resolver link = some arena := by
  have monotone := left.fetch_mono extension link.blake3
  unfold ByteCas.resolver at resolved ⊢
  cases leftFetch : left.fetch link.blake3 with
  | unknown => simp [leftFetch] at resolved
  | known leftArena =>
      simp only [leftFetch] at resolved
      have equal : leftArena = arena := Option.some.inj resolved
      subst arena
      rw [leftFetch, Unknown.known_le_iff] at monotone
      rw [monotone]

/-- A cache is sound when every hit agrees with authenticated CAS decoding. -/
def CacheSound [Hash32] (cas : ByteCas) (cache : O256 → Option Arena) : Prop :=
  ∀ address arena, cache address = some arena → cas.fetch address = .known arena

/-- Consult a successful-result cache before the byte store. -/
def cachedFetch [Hash32] (cas : ByteCas) (cache : O256 → Option Arena)
    (address : O256) : Unknown Arena :=
  match cache address with
  | some arena => .known arena
  | none => cas.fetch address

/-- Sound cache contents are observationally irrelevant. -/
theorem cachedFetch_eq [Hash32] {cas : ByteCas} {cache : O256 → Option Arena}
    (sound : CacheSound cas cache) (address : O256) :
    cachedFetch cas cache address = cas.fetch address := by
  cases hit : cache address with
  | none => simp [cachedFetch, hit]
  | some arena =>
      simp only [cachedFetch, hit]
      exact (sound address arena hit).symm

def cachedResolver [Hash32] (cas : ByteCas) (cache : O256 → Option Arena) : Resolver :=
  fun link => match cachedFetch cas cache link.blake3 with
    | .unknown => none
    | .known arena => some arena

theorem cachedResolver_eq [Hash32] {cas : ByteCas} {cache : O256 → Option Arena}
    (sound : CacheSound cas cache) : cachedResolver cas cache = cas.resolver := by
  funext link
  simp [cachedResolver, ByteCas.resolver, cachedFetch_eq sound]

end Nucleus.Hol.Ethane.OneBased
