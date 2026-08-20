import Nucleus.Json.Cas

/-!
# Hash sequences

This module specifies the semantic sequence underlying the Rust
`covalence-data-array` crate. A hash sequence is finite: position and
multiplicity are significant, and no sortedness or non-null invariant is
assumed.  The wire format is the concatenation of fixed-width element
encodings.

CAS-backed queries are factored through `resolve`.  A concrete byte CAS earns
such a resolver by checking that the addressed bytes have canonical width;
once resolved, every query below is a pure sequence operation.
-/

namespace Nucleus.HashSeq

/-- A hash sequence's semantic value. -/
abbrev Seq (α : Type) := List α

/-- The one-element sequence. -/
def singleton (value : α) : Seq α := [value]

/-- Append one element, preserving all existing positions. -/
def push (values : Seq α) (value : α) : Seq α := values ++ [value]

/-- Remove the last element and return it with the remaining prefix. -/
def pop? (values : Seq α) : Option (α × Seq α) :=
  match values.reverse with
  | [] => none
  | value :: rest => some (value, rest.reverse)

/-- Remove every element. -/
def clear (_ : Seq α) : Seq α := []

/-- Keep at most the first `limit` elements. -/
def truncate (values : Seq α) (limit : Nat) : Seq α := values.take limit

/-- Number of elements. -/
def length (values : Seq α) : Nat := values.length

/-- The element at a zero-based index. -/
def get? (values : Seq α) (index : Nat) : Option α := values[index]?

/-- The first element, when present. -/
def first? (values : Seq α) : Option α := values.head?

/-- The last element, when present. -/
def last? (values : Seq α) : Option α := values.reverse.head?

/-- The first position containing `value`. -/
def position? [BEq α] (value : α) : Seq α → Option Nat
  | [] => none
  | candidate :: rest =>
      if candidate == value then some 0 else (position? value rest).map Nat.succ

/-- Number of occurrences of `value`. -/
def count [BEq α] (value : α) : Seq α → Nat
  | [] => 0
  | candidate :: rest => (if candidate == value then 1 else 0) + count value rest

/-- Whether `value` occurs. -/
def contains [BEq α] (values : Seq α) (value : α) : Bool :=
  (position? value values).isSome

/-- A checked half-open element slice. -/
def slice? (values : Seq α) (start stop : Nat) : Option (Seq α) :=
  if start ≤ stop ∧ stop ≤ values.length then
    some ((values.drop start).take (stop - start))
  else
    none

/-- A checked split before `index`. -/
def splitAt? (values : Seq α) (index : Nat) : Option (Seq α × Seq α) :=
  if index ≤ values.length then some (values.take index, values.drop index) else none

/-- A fixed-width element encoder.  The proof is the sole wire-format
assumption needed by the sequence layer. -/
structure Encoding (α : Type) where
  width : Nat
  width_pos : 0 < width
  encode : α → List UInt8
  encode_length : ∀ value, (encode value).length = width

/-- Iroh-style bare concatenation: no header, count, or framing. -/
def encode (encoding : Encoding α) (values : Seq α) : List UInt8 :=
  values.flatMap encoding.encode

@[simp] theorem length_nil : length ([] : Seq α) = 0 := rfl

@[simp] theorem length_singleton (value : α) : length (singleton value) = 1 := rfl

@[simp] theorem length_push (values : Seq α) (value : α) :
    length (push values value) = length values + 1 := by
  simp [length, push]

@[simp] theorem pop_empty : pop? ([] : Seq α) = none := rfl

@[simp] theorem clear_eq_empty (values : Seq α) : clear values = [] := rfl

@[simp] theorem length_truncate (values : Seq α) (limit : Nat) :
    length (truncate values limit) = min limit (length values) := by
  simp [length, truncate]

@[simp] theorem get_singleton_zero (value : α) : get? (singleton value) 0 = some value := rfl

@[simp] theorem get_singleton_succ (value : α) (index : Nat) :
    get? (singleton value) (index + 1) = none := by
  simp [get?, singleton]

@[simp] theorem encode_nil (encoding : Encoding α) : encode encoding [] = [] := rfl

@[simp] theorem encode_cons (encoding : Encoding α) (value : α) (rest : Seq α) :
    encode encoding (value :: rest) = encoding.encode value ++ encode encoding rest := rfl

/-- Canonical bytes always have exactly `width * element_count` octets. -/
theorem encode_length (encoding : Encoding α) (values : Seq α) :
    (encode encoding values).length = encoding.width * values.length := by
  induction values with
  | nil => simp [encode]
  | cons value rest ih =>
      rw [encode_cons, List.length_append, encoding.encode_length, ih]
      simp only [List.length_cons, Nat.mul_succ]
      exact Nat.add_comm _ _

/-- The empty sequence is the empty blob. -/
@[simp] theorem encode_empty (encoding : Encoding α) :
    encode encoding ([] : Seq α) = [] := rfl

/-- A successful slice has exactly the requested length. -/
theorem slice_length {values : Seq α} {start stop : Nat}
    (hstart : start ≤ stop) (hstop : stop ≤ values.length) :
    (slice? values start stop).map List.length = some (stop - start) := by
  simp [slice?, hstart, hstop, List.length_take, List.length_drop]
  omega

/-- Splitting and appending recovers the original sequence. -/
theorem splitAt_append {values : Seq α} {index : Nat} (hindex : index ≤ values.length) :
    (splitAt? values index).map (fun parts => parts.1 ++ parts.2) = some values := by
  simp [splitAt?, hindex, List.take_append_drop]

/-- A checked semantic resolver supplied by a CAS/decoder boundary. -/
abbrev Resolver (Name : Type) (α : Type) := Name → Unknown (Seq α)

variable {Name : Type}

/-- Lift a pure sequence query through an existing checked CAS resolver. -/
def query (resolve : Resolver Name α) (operation : Seq α → β) (name : Name) : Unknown β :=
  (resolve name).bind (fun values => .known (operation values))

def queryLength (resolve : Resolver Name α) (name : Name) : Unknown Nat :=
  query resolve length name

def queryGet (resolve : Resolver Name α) (name : Name) (index : Nat) : Unknown (Option α) :=
  query resolve (fun values => get? values index) name

def queryContains [BEq α] (resolve : Resolver Name α) (name : Name) (value : α) : Unknown Bool :=
  query resolve (fun values => contains values value) name

@[simp] theorem query_unknown (operation : Seq α → β) (name : Name) :
    query (fun _ => .unknown) operation name = .unknown := rfl

@[simp] theorem query_known (values : Seq α) (operation : Seq α → β) (name : Name) :
    query (fun _ => .known values) operation name = .known (operation values) := rfl

/-- Queries preserve the existing flat information order under store
extension. -/
theorem query_mono {resolve₁ resolve₂ : Resolver Name α}
    (hresolve : ∀ name, Unknown.Le (resolve₁ name) (resolve₂ name))
    (operation : Seq α → β) (name : Name) :
    Unknown.Le (query resolve₁ operation name) (query resolve₂ operation name) := by
  unfold query
  rcases hresolve name with h | h
  · rw [h]
    exact Unknown.unknown_le _
  · rw [h]

end Nucleus.HashSeq
