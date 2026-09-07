import Nucleus.Hol.Ethane.Literals
import Nucleus.Hol.Propane.LiteralWire
import Nucleus.Hol.Propane.Syntax

/-!
# Checked literal DAG reduction

This is the literal/computation projection of the Rust arena after field
decoding and classifier resolution. Rust resolves classifiers through its
conversion union-find and arrow membership; this view stores the resolved
primitive/arrow type graph. Kind evidence and union-find transport belong to
the existing kernel validation and are not represented or proved here. Thus
this is not a verbatim model of every raw arena field or every Rust check.

Term references obey Rust's one-based bounds, excluding the signed-32-bit
maximum sentinel. Constant-table references are zero-based unsigned-32-bit
indices. The projected type graph and classifiers are checked separately from
values. Existing nonliteral syntax is opaque to this reducer.

Rust traverses the DAG with an explicit stack and memoizes completed values.
`Step` records exactly the successful cache insertions: leaves, builtin results,
and equalities. `Step.preserves` proves the invariant for arbitrary traversal
order and sharing in this projection. Work limits, cycle detection, scheduling, and failed
attempts never add evidence. `reduction_sound` is the theorem used at the final
equality-producing boundary, for any number of nested operations.
-/

namespace Nucleus.Hol.Ethane.Literals.Dag

open Nucleus.Hol.Propane Nucleus.Hol.Propane.LiteralWire
open Nucleus.HolE.Infinity

inductive Node where
  | type (type : LiteralTy)
  | arrow (domain codomain : Nat)
  | bool (value : Bool)
  | natInline (value : Nat)
  | intInline (value : Int)
  | wordInline (width : Width) (value : Int)
  | constRef (index : Nat)
  | builtin (op : Builtin)
  | app (function argument : Nat)
  | eq (type left right : Nat)
  | other
  deriving DecidableEq, Repr

structure Row where
  node : Node
  classifier : Nat
  deriving DecidableEq, Repr

structure Arena where
  rows : List Row
  constants : List RawConstant

def Arena.lookup (arena : Arena) (reference : Nat) : Option Row :=
  if 0 < reference ∧ reference < 2 ^ 31 - 1 then arena.rows[reference - 1]? else none

@[simp] theorem Arena.lookup_sentinel (arena : Arena) :
    arena.lookup (2 ^ 31 - 1) = none := by simp [lookup]

def Arena.typeAtFuel (arena : Arena) : Nat → Nat → Option Propane.Ty
  | 0, _ => none
  | fuel + 1, reference => do
      match (← arena.lookup reference).node with
      | .type type => return Ty.ofLiteral type
      | .arrow domain codomain =>
          return .arr (← arena.typeAtFuel fuel domain) (← arena.typeAtFuel fuel codomain)
      | _ => none

def Arena.typeAt (arena : Arena) (reference : Nat) : Option Propane.Ty :=
  arena.typeAtFuel (arena.rows.length + 1) reference

def Arena.classifierType (arena : Arena) (reference : Nat) : Option Propane.Ty := do
  arena.typeAt (← arena.lookup reference).classifier

def scalarType : Propane.Ty → Option LiteralTy
  | .bool => some .bool | .word width => some (.word width)
  | .nat => some .nat | .int => some .int | .bytes => some .bytes
  | .arr _ _ => none

def Arena.literalType (arena : Arena) (reference : Nat) : Option LiteralTy := do
  scalarType (← arena.classifierType reference)

def Node.leaf (constants : List RawConstant) : Node → Option LiteralValue
  | .bool value => some (.bool value)
  | .natInline value => decodeNatInline value
  | .intInline value => decodeIntInline value
  | .wordInline width value => decodeWordInline width value
  | .constRef index => decodeConstantRef constants index
  | _ => none

/-- Input order and multiplicity are preserved, including shared references. -/
def gather {α : Type} (lookup : Nat → Option α) : List Nat → Option (List α)
  | [] => some []
  | reference :: references => do return (← lookup reference) :: (← gather lookup references)

def Node.classify (arena : Arena) : Node → Option Propane.Ty
  | .bool _ => some .bool
  | .natInline _ => some .nat
  | .intInline _ => some .int
  | .wordInline width _ => some (.word width)
  | .constRef index => do return Ty.ofLiteral (← arena.constants[index]?).type
  | .builtin op => do
      let (inputs, output) ← op.signature
      return Ty.arrows inputs output
  | .app function argument => do
      match ← arena.classifierType function with
      | .arr domain codomain =>
          if (← arena.classifierType argument) = domain then some codomain else none
      | _ => none
  | .eq typeRef left right => do
      let expected ← arena.typeAt typeRef
      if (← arena.classifierType left) = expected ∧
          (← arena.classifierType right) = expected
        then some .bool else none
  | _ => none

def Arena.validRow (arena : Arena) (reference : Nat) : Bool :=
  match arena.lookup reference, arena.classifierType reference with
  | some row, some type => row.node.classify arena == some type
  | _, _ => false

/-- Inspect ordinary applications, checking every intermediate function row.
Fuel only declines malformed/cyclic/overlong syntax; it is not a semantic value. -/
def Arena.spineFuel (arena : Arena) : Nat → Nat → List Nat → Option (Builtin × List Nat)
  | 0, _, _ => none
  | fuel + 1, reference, arguments => do
      if !arena.validRow reference then none else
        match (← arena.lookup reference).node with
        | .builtin op => some (op, arguments)
        | .app function argument => arena.spineFuel fuel function (argument :: arguments)
        | _ => none

def Arena.spine (arena : Arena) (reference : Nat) : Option (Builtin × List Nat) :=
  arena.spineFuel (arena.rows.length + 1) reference []

theorem gather_some {α : Type} {lookup : Nat → Option α}
    {references : List Nat} {values : List α} (found : gather lookup references = some values) :
    List.Forall₂ (fun reference value => lookup reference = some value) references values := by
  induction references generalizing values with
  | nil => simpa [gather] using found
  | cons reference references ih =>
      simp only [gather] at found
      cases head : lookup reference with
      | none => simp [head] at found
      | some value =>
          cases tail : gather lookup references with
          | none => simp [head, tail] at found
          | some rest =>
              have equation : value :: rest = values := by simpa [head, tail] using found
              subst values
              exact .cons head (ih tail)

noncomputable section

/-- Independent relational meaning of literal rows in the constructed carriers. -/
inductive Denotes (naturals : CNatModel) (arena : Arena) : Nat → Value naturals → Prop
  | leaf {reference : Nat} {row : Row} {value : LiteralValue}
      (found : arena.lookup reference = some row)
      (valid : arena.validRow reference = true)
      (decoded : row.node.leaf arena.constants = some value) :
      Denotes naturals arena reference (quote naturals value)
  | builtin {reference : Nat} {row : Row} {op : Builtin} {references : List Nat}
      {values : List (Value naturals)} {value : Value naturals}
      (found : arena.lookup reference = some row)
      (resolved : arena.spine reference = some (op, references))
      (valid : arena.validRow reference = true)
      (arguments : List.Forall₂ (Denotes naturals arena) references values)
      (computed : interpret naturals op values = some value) :
      Denotes naturals arena reference value
  | eq {reference : Nat} {row : Row} {type left right : Nat}
      {leftValue rightValue : LiteralValue}
      (found : arena.lookup reference = some row)
      (node : row.node = .eq type left right)
      (valid : arena.validRow reference = true)
      (leftDenotes : Denotes naturals arena left (quote naturals leftValue))
      (rightDenotes : Denotes naturals arena right (quote naturals rightValue))
      (sameType : leftValue.type = rightValue.type) :
      Denotes naturals arena reference
        (quote naturals (.bool (decide (leftValue = rightValue))))

abbrev Cache := Nat → Option LiteralValue

def Cache.Sound (naturals : CNatModel) (arena : Arena) (cache : Cache) : Prop :=
  ∀ reference value, cache reference = some value →
    Denotes naturals arena reference (quote naturals value)

def Cache.insert (cache : Cache) (reference : Nat) (value : LiteralValue) : Cache :=
  fun candidate => if candidate = reference then some value else cache candidate

theorem Cache.insert_sound {naturals : CNatModel} {arena : Arena} {cache : Cache}
    {reference : Nat} {value : LiteralValue} (sound : cache.Sound naturals arena)
    (denotes : Denotes naturals arena reference (quote naturals value)) :
    (cache.insert reference value).Sound naturals arena := by
  intro candidate result found
  unfold insert at found
  split at found
  · rename_i same
    subst candidate
    cases Option.some.inj found
    exact denotes
  · exact sound candidate result found

theorem Cache.gather_sound {naturals : CNatModel} {arena : Arena} {cache : Cache}
    {references : List Nat} {values : List LiteralValue}
    (sound : cache.Sound naturals arena) (found : gather cache references = some values) :
    List.Forall₂ (Denotes naturals arena) references (values.map (quote naturals)) := by
  have relation := gather_some found
  clear found
  induction relation with
  | nil => exact .nil
  | cons head tail ih => exact .cons (sound _ _ head) ih

/-- Only these successful events can populate the evaluator's result cache. -/
inductive Step (arena : Arena) : Cache → Cache → Prop
  | leaf {cache : Cache} {reference : Nat} {row : Row} {value : LiteralValue}
      (found : arena.lookup reference = some row)
      (valid : arena.validRow reference = true)
      (decoded : row.node.leaf arena.constants = some value) :
      Step arena cache (cache.insert reference value)
  | builtin {cache : Cache} {reference : Nat} {row : Row} {op : Builtin}
      {references : List Nat} {values : List LiteralValue} {value : LiteralValue}
      (found : arena.lookup reference = some row)
      (resolved : arena.spine reference = some (op, references))
      (valid : arena.validRow reference = true)
      (arguments : gather cache references = some values)
      (computed : op.eval values = some value) :
      Step arena cache (cache.insert reference value)
  | eq {cache : Cache} {reference : Nat} {row : Row} {type left right : Nat}
      {leftValue rightValue : LiteralValue}
      (found : arena.lookup reference = some row)
      (node : row.node = .eq type left right)
      (valid : arena.validRow reference = true)
      (leftFound : cache left = some leftValue)
      (rightFound : cache right = some rightValue)
      (sameType : leftValue.type = rightValue.type) :
      Step arena cache
        (cache.insert reference (.bool (decide (leftValue = rightValue))))

/-- Every successful Rust-style cache insertion preserves semantic authority. -/
theorem Step.preserves {arena : Arena} {before after : Cache}
    (step : Step arena before after) (naturals : CNatModel)
    (sound : before.Sound naturals arena) : after.Sound naturals arena := by
  cases step with
  | leaf found valid decoded =>
      exact Cache.insert_sound sound (.leaf found valid decoded)
  | builtin found node valid arguments computed =>
      exact Cache.insert_sound sound (.builtin found node valid (Cache.gather_sound sound arguments)
        (builtin_sound naturals _ _ _ computed))
  | eq found node valid leftFound rightFound sameType =>
      exact Cache.insert_sound sound (.eq found node valid (sound _ _ leftFound)
        (sound _ _ rightFound) sameType)

/-- A complete successful evaluation may contain arbitrarily many nested operations. -/
inductive Steps (arena : Arena) : Cache → Cache → Prop
  | refl (cache : Cache) : Steps arena cache cache
  | next {before middle after : Cache} :
      Steps arena before middle → Step arena middle after → Steps arena before after

theorem Steps.preserves {arena : Arena} {before after : Cache}
    (steps : Steps arena before after) (naturals : CNatModel)
    (sound : before.Sound naturals arena) : after.Sound naturals arena := by
  induction steps with
  | refl => exact sound
  | next steps step ih => exact step.preserves naturals ih

theorem Steps.trans {arena : Arena} {before middle after : Cache}
    (first : Steps arena before middle) (second : Steps arena middle after) :
    Steps arena before after := by
  induction second with
  | refl => exact first
  | next steps step ih => exact .next ih step

/-- Executable checking of one scheduled row, returning its cache-invariant proof. -/
def visit (arena : Arena) (cache : Cache) (reference : Nat) :
    Option { after : Cache // Step arena cache after } :=
  match found : arena.lookup reference with
  | none => none
  | some row =>
      if valid : arena.validRow reference = true then
        match decoded : row.node.leaf arena.constants with
        | some value => some ⟨cache.insert reference value, .leaf found valid decoded⟩
        | none => match node : row.node with
          | .eq _type left right =>
              match leftFound : cache left, rightFound : cache right with
              | some leftValue, some rightValue =>
                  if sameType : leftValue.type = rightValue.type then
                    some ⟨cache.insert reference (.bool (decide (leftValue = rightValue))),
                      .eq found node valid leftFound rightFound sameType⟩
                  else none
              | _, _ => none
          | _ => match resolved : arena.spine reference with
            | none => none
            | some (op, references) =>
                match arguments : gather cache references with
                | none => none
                | some values => match computed : op.eval values with
                  | none => none
                  | some value => some ⟨cache.insert reference value,
                      .builtin found resolved valid arguments computed⟩
      else none

/-- A schedule is untrusted. Every visited row must pass all checks. -/
def replay (arena : Arena) : (schedule : List Nat) → (before : Cache) →
    Option { after : Cache // Steps arena before after }
  | [], before => some ⟨before, .refl before⟩
  | reference :: rest, before => do
      let next ← visit arena before reference
      let result ← replay arena rest next.val
      return ⟨result.val, (Steps.next (.refl before) next.property).trans result.property⟩

def check (arena : Arena) (schedule : List Nat) (reference : Nat) : Option LiteralValue := do
  let result ← replay arena schedule (fun _ => none)
  result.val reference

/-- Exact reference and exact result of successful nested reduction. -/
theorem reduction_sound {arena : Arena} {cache : Cache} {reference : Nat}
    {value : LiteralValue} (naturals : CNatModel)
    (steps : Steps arena (fun _ => none) cache) (result : cache reference = some value) :
    Denotes naturals arena reference (quote naturals value) :=
  steps.preserves naturals (by intro _ _ rejected; contradiction) reference value result

/-- Successful execution of the concrete reference checker yields the semantic fact. -/
theorem check_sound (naturals : CNatModel) {arena : Arena} {schedule : List Nat}
    {reference : Nat} {value : LiteralValue}
    (checked : check arena schedule reference = some value) :
    Denotes naturals arena reference (quote naturals value) := by
  unfold check at checked
  cases ran : replay arena schedule (fun _ => none) with
  | none => simp [ran] at checked
  | some result =>
      have found : result.val reference = some value := by simpa [ran] using checked
      exact reduction_sound naturals result.property found

end

end Nucleus.Hol.Ethane.Literals.Dag
