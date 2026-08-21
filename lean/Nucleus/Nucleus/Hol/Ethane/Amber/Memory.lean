import Nucleus.Hol.Ethane.Amber.Cbor

/-!
# Rust-facing Amber memory model

`Memory` models the fields of a Rust dense forest directly: an optional parent
record and a growable array of rows.  `toDense` is its mathematical meaning.
All mutation is presented as pure Lean functions, which makes preservation
theorems usable as the specification of corresponding Rust methods.
-/

namespace Nucleus.Hol.Ethane.Amber

open Nucleus.Hol.Ethane
universe u v
set_option relaxedAutoImplicit true

/-- In-memory representation corresponding to a Rust `Option<Parent<K>>` and
`Vec<R>`. -/
structure Memory (Key : Type u) (R : Type v) where
  parent : Option (Parent Key)
  rows : Array R
  deriving DecidableEq

namespace Memory

/-- Mathematical list-backed meaning of the Rust-facing state. -/
def toDense (memory : Memory Key R) : Dense Key R :=
  ⟨memory.parent, memory.rows.toList⟩

/-- Materialize a mathematical forest as a Rust-facing state. -/
def ofDense (forest : Dense Key R) : Memory Key R :=
  ⟨forest.parent, forest.rows.toArray⟩

@[simp] theorem toDense_ofDense (forest : Dense Key R) :
    (ofDense forest).toDense = forest := by
  cases forest
  simp [ofDense, toDense]

@[simp] theorem ofDense_toDense (memory : Memory Key R) :
    ofDense memory.toDense = memory := by
  cases memory
  simp [ofDense, toDense]

/-- The next absolute index assigned by `push`. -/
def next (memory : Memory Key R) : Nat := memory.toDense.next

/-- Structural validity is exactly validity of the mathematical forest. -/
def Valid [Row R Tag Nat Extra] (memory : Memory Key R) : Prop :=
  memory.toDense.Valid

/-- Checked precondition for one append. -/
def CanPush [Row R Tag Nat Extra] (memory : Memory Key R) (row : R) : Prop :=
  memory.toDense.CanPush row

/-- Pure model of `Vec::push`. -/
def push (memory : Memory Key R) (row : R) : Memory Key R :=
  ⟨memory.parent, memory.rows.push row⟩

/-- Validate all child references before mutating. -/
noncomputable def push? [Row R Tag Nat Extra]
    (memory : Memory Key R) (row : R) : Option (Memory Key R) := by
  classical
  exact if memory.CanPush row then some (memory.push row) else none

/-- Repeated checked append. -/
noncomputable def extend? [Row R Tag Nat Extra] :
    Memory Key R → List R → Option (Memory Key R)
  | memory, [] => some memory
  | memory, row :: rows => do
      let memory ← memory.push? row
      extend? memory rows

@[simp] theorem toDense_push (memory : Memory Key R) (row : R) :
    (memory.push row).toDense = memory.toDense.push row := by
  cases memory
  simp [push, toDense, Dense.push]

@[simp] theorem next_push (memory : Memory Key R) (row : R) :
    (memory.push row).next = memory.next + 1 := by
  simp [next]

@[simp] theorem push?_eq_some [Row R Tag Nat Extra]
    (memory : Memory Key R) (row : R) :
    memory.push? row = some (memory.push row) ↔ memory.CanPush row := by
  classical
  unfold push?
  constructor
  · intro pushed
    by_contra invalid
    rw [if_neg invalid] at pushed
    contradiction
  · intro valid
    rw [if_pos valid]

theorem Valid.push [Row R Tag Nat Extra] {memory : Memory Key R}
    (memoryValid : memory.Valid) {row : R} (rowValid : memory.CanPush row) :
    (memory.push row).Valid := by
  unfold Valid CanPush at *
  rw [toDense_push]
  exact memoryValid.push rowValid

theorem push?_valid [Row R Tag Nat Extra] {memory next : Memory Key R}
    (memoryValid : memory.Valid) {row : R}
    (pushed : memory.push? row = some next) : next.Valid := by
  unfold push? at pushed
  split at pushed
  next rowValid =>
    cases pushed
    exact memoryValid.push rowValid
  next _ => contradiction

theorem extend?_valid [Row R Tag Nat Extra] {memory next : Memory Key R}
    (memoryValid : memory.Valid) {rows : List R}
    (extended : extend? memory rows = some next) : next.Valid := by
  induction rows generalizing memory with
  | nil =>
      change some memory = some next at extended
      injection extended with memoryEq
      subst next
      exact memoryValid
  | cons row rows ih =>
      simp only [extend?] at extended
      cases pushedEq : memory.push? row with
      | none => rw [pushedEq] at extended; contradiction
      | some pushed =>
          rw [pushedEq] at extended
          exact ih (push?_valid memoryValid pushedEq) extended

/-- Memory states fit CBOR exactly when their mathematical forests do. -/
def Fits [Row R Tag Nat Extra] (memory : Memory Key R) : Prop :=
  Cbor.FitsDense memory.toDense

/-- Serialize the Rust-facing state through its mathematical meaning. -/
def encode [Cbor.CasKey Key] [Row R Tag Nat Extra]
    (tag : Cbor.Codec Tag) (extra : Cbor.Codec Extra)
    (memory : Memory Key R) : Nucleus.Cbor :=
  Cbor.encodeDense tag extra memory.toDense

/-- Decode CBOR to a checked constructor forest and materialize its array. -/
def decode? [Cbor.CasKey Key]
    (tag : Cbor.Codec Tag) (extra : Cbor.Codec Extra)
    (ofView? : Row.View Tag Nat Extra → Option R)
    (value : Nucleus.Cbor) : Option (Memory Key R) :=
  (Cbor.decodeDense? tag extra ofView? value).map ofDense

@[simp] theorem decode?_encode [Cbor.CasKey Key] [Row R Tag Nat Extra]
    (tag : Cbor.Codec Tag) (extra : Cbor.Codec Extra)
    (ofView? : Row.View Tag Nat Extra → Option R)
    (ofView_view : ∀ row : R, ofView? (Row.view row) = some row)
    (memory : Memory Key R) (fits : memory.Fits) :
    decode? tag extra ofView? (encode tag extra memory) = some memory := by
  unfold decode? encode
  unfold Fits at fits
  rw [Cbor.decodeDense?_encode tag extra ofView? ofView_view memory.toDense fits]
  simp

/-- Rust-facing Ethane syntax state. -/
abbrev Syntax (Key : Type) (Sig : Signature.{u}) (Name : Type := Nat) :=
  Memory Key (Arena.Row Sig Name Nat)

/-- Exact CBOR encoder for an in-memory Ethane syntax forest. -/
def encodeSyntax [Cbor.CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (memory : Syntax Key Sig Name) : Nucleus.Cbor :=
  encode Cbor.syntaxTag (Cbor.syntaxExtra names symbols) memory

/-- Exact CBOR decoder for an in-memory Ethane syntax forest. -/
def decodeSyntax? [Cbor.CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (value : Nucleus.Cbor) : Option (Syntax Key Sig Name) :=
  decode? Cbor.syntaxTag (Cbor.syntaxExtra names symbols) SyntaxRow.ofView? value

@[simp] theorem decodeSyntax?_encode [Cbor.CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (memory : Syntax Key Sig Name) (fits : memory.Fits) :
    decodeSyntax? names symbols (encodeSyntax names symbols memory) = some memory := by
  exact decode?_encode Cbor.syntaxTag (Cbor.syntaxExtra names symbols)
    SyntaxRow.ofView? SyntaxRow.ofView?_view memory fits

end Memory

end Nucleus.Hol.Ethane.Amber
