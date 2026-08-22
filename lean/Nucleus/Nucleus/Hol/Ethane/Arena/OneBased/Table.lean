import Nucleus.Cas.Basic
import Nucleus.Cbor.Wire
import Nucleus.Hol.Ethane.Arena.OneBased.Cbor
import Nucleus.Hol.Ethane.Arena.OneBased.Resolve

/-!
# Content-addressed Ethane tables

`Table` is the immutable LCF object `(O256, Arena)`. Its proof records that
checked complete bytes at that address decode to the arena. The bytes and
proof are erased from the Rust representation, which retains an `O256` and an
`Arc<Arena>`.

A table resolver is deliberately untrusted. The sealed Rust extension and
`resolveChecked` below verify that the returned table answers the requested
link. Caching, retries, locking, and storage policy are userspace concerns.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus

/-- Parse exactly one complete CBOR arena value. -/
def decodeCborArena? (bytes : Bytes) : Option Arena := do
  let value ← Nucleus.CborWire.parse? bytes
  Nucleus.Hol.Ethane.OneBased.Cbor.decodeArena? value

/-- An address and immutable arena justified by checked complete bytes. -/
structure Table [Name Bytes O256] where
  address : O256
  arena : Arena
  valid : ∃ pair : CasPair,
    pair.hash = address ∧ decodeCborArena? pair.blob = some arena

namespace Table

variable [Name Bytes O256]

/-- Decode a checked whole-blob fact into a table. -/
def ofPair? (pair : CasPair) : Option Table :=
  match decoded : decodeCborArena? pair.blob with
  | none => none
  | some arena => some {
      address := pair.hash
      arena
      valid := ⟨pair, rfl, decoded⟩ }

theorem ofPair?_sound {pair : CasPair} {table : Table}
    (decoded : ofPair? pair = some table) :
    table.address = pair.hash ∧
      decodeCborArena? pair.blob = some table.arena := by
  unfold ofPair? at decoded
  split at decoded
  · contradiction
  · rename_i arena equation
    have equal : ({
      address := pair.hash
      arena
      valid := ⟨pair, rfl, equation⟩ } : Table) = table :=
      Option.some.inj decoded
    rw [← equal]
    exact ⟨rfl, equation⟩

/-- Introduce a table from bytes already known to encode an arena.

This is the relational counterpart of Rust's fallible `Table::from_arena`:
the Rust encoder supplies the bytes and its successful round trip supplies
`decoded`. -/
def ofEncoded (arena : Arena) (bytes : Bytes)
    (decoded : decodeCborArena? bytes = some arena) : Table :=
  let pair := CasPair.ofBlob bytes
  {
    address := pair.hash
    arena
    valid := ⟨pair, rfl, decoded⟩ }

@[simp] theorem ofEncoded_address (arena : Arena) (bytes : Bytes)
    (decoded : decodeCborArena? bytes = some arena) :
    (ofEncoded arena bytes decoded).address = Name.name bytes := rfl

@[simp] theorem ofEncoded_arena (arena : Arena) (bytes : Bytes)
    (decoded : decodeCborArena? bytes = some arena) :
    (ofEncoded arena bytes decoded).arena = arena := rfl

theorem valid_decode (table : Table) :
    ∃ pair : CasPair,
      pair.hash = table.address ∧
        decodeCborArena? pair.blob = some table.arena :=
  table.valid

end Table

/-- An untrusted, possibly stateful provider of immutable tables.

The error parameter models lookup, I/O, and temporary-unavailability failures.
The Rust method takes `&mut self`; its state is intentionally absent from this
one-call denotation. -/
abbrev TableResolver (Error : Type) [Name Bytes O256] :=
  Link → Except Error Table

/-- Failure while checking a raw resolver answer. -/
inductive TableResolveError (Error : Type) where
  | resolver (error : Error)
  | wrongAddress (requested returned : O256)
  deriving DecidableEq

namespace TableResolver

variable {Error : Type} [Name Bytes O256]

/-- Resolve a table and check that it answers the requested link. -/
def resolveChecked (resolve : TableResolver Error) (link : Link) :
    Except (TableResolveError Error) Table :=
  match resolve link with
  | .error error => .error (.resolver error)
  | .ok table =>
      if table.address = link.blake3 then .ok table
      else .error (.wrongAddress link.blake3 table.address)

/-- Forget checked resolver failures to obtain the older partial arena
denotation used by the raw row semantics. -/
def toResolver (resolve : TableResolver Error) : Resolver := fun link =>
  match resolve.resolveChecked link with
  | .error _ => none
  | .ok table => some table.arena

theorem resolveChecked_eq_ok_iff {resolve : TableResolver Error}
    {link : Link} {table : Table} :
    resolve.resolveChecked link = .ok table ↔
      resolve link = .ok table ∧ table.address = link.blake3 := by
  constructor
  · intro resolved
    unfold resolveChecked at resolved
    cases provided : resolve link with
    | error error => simp [provided] at resolved
    | ok candidate =>
        simp only [provided] at resolved
        by_cases address : candidate.address = link.blake3
        · simp only [address, if_pos] at resolved
          have equal : candidate = table := Except.ok.inj resolved
          subst table
          exact ⟨rfl, address⟩
        · simp [address] at resolved
  · rintro ⟨provided, address⟩
    simp [resolveChecked, provided, address]

theorem toResolver_eq_some_iff {resolve : TableResolver Error}
    {link : Link} {arena : Arena} :
    resolve.toResolver link = some arena ↔
      ∃ table, resolve link = .ok table ∧
        table.address = link.blake3 ∧ table.arena = arena := by
  constructor
  · intro resolved
    unfold toResolver at resolved
    cases checked : resolve.resolveChecked link with
    | error error => simp [checked] at resolved
    | ok table =>
        simp only [checked] at resolved
        have arenaEqual : table.arena = arena := Option.some.inj resolved
        have raw := resolveChecked_eq_ok_iff.mp checked
        exact ⟨table, raw.1, raw.2, arenaEqual⟩
  · rintro ⟨table, provided, address, rfl⟩
    have checked : resolve.resolveChecked link = .ok table :=
      resolveChecked_eq_ok_iff.mpr ⟨provided, address⟩
    simp [toResolver, checked]

/-- Every successful raw resolution is backed by an address-matching table. -/
theorem exists_table_of_resolves {resolve : TableResolver Error}
    {link : Link} {arena : Arena}
    (resolved : resolve.toResolver link = some arena) :
    ∃ table, resolve link = .ok table ∧
      table.address = link.blake3 ∧ table.arena = arena :=
  toResolver_eq_some_iff.mp resolved

end TableResolver

end Nucleus.Hol.Ethane.OneBased
