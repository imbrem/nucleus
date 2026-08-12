import Nucleus.HolLN
import Nucleus.Json
import Nucleus.PropTable

/-!
# JSON interchange for proposition tables

An initial, deliberately simple JSON-shaped interchange model.  Arrays carry
the schema positionally, so round-trip proofs are small and schema evolution
can later introduce tagged versions without changing the logical table model.
-/

namespace Nucleus.PropTable.Json

universe u v w

inductive Scalar where
  | integer : Int → Scalar
  | natural : Nat → Scalar
  | text : String → Scalar
  deriving DecidableEq, Repr

abbrev Value := RawJson Scalar

def array (values : List Value) : Value := .list (RawSyn.ofList values)
def object (entries : List (String × Value)) : Value := .map (RawSyn.ofEntries entries)

def decodeList (decode : Value → Except String α) :
    RawSyn Scalar .arr → Except String (List α)
  | .nil => .ok []
  | .cons head tail => return (← decode head) :: (← decodeList decode tail)

def encodeList (encode : α → Value) (values : List α) : Value :=
  array (values.map encode)

theorem decodeList_map (encode : α → Value) (decode : Value → Except String α)
    (roundTrip : ∀ value, decode (encode value) = .ok value) (values : List α) :
    decodeList decode (RawSyn.ofList (values.map encode)) = .ok values := by
  induction values with
  | nil => simp [decodeList]
  | cons head tail ih =>
      simp only [List.map_cons, RawSyn.ofList_cons, decodeList]
      rw [roundTrip head, ih]
      rfl

/-- A reusable JSON interface.  Its round-trip law is proof data, not a test oracle. -/
class Codec (α : Type u) where
  encode : α → Value
  decode : Value → Except String α
  decode_encode : ∀ value, decode (encode value) = .ok value

inductive Dependency where
  | table : String → Dependency
  | logical : (system : String) → (context : Value) → Dependency

structure WireRow where
  premise : Lit Nat
  source : Option String
  conclusion : Lit Nat
  /-- Zero is definition; other integers are theorem-reason data. -/
  reason : Int
  deriving DecidableEq, Repr

structure WireTable where
  dependencies : List Dependency
  rows : List WireRow

def WireRow.ofLogical (row : Row String Nat Int) : WireRow :=
  { premise := row.premise
    source := row.source
    conclusion := row.conclusion
    reason := match row.reason with
      | .definition => 0
      | .theorem reason => reason }

def WireRow.toLogical (row : WireRow) : Row String Nat Int :=
  { premise := row.premise
    source := row.source
    conclusion := row.conclusion
    reason := if row.reason = 0 then .definition else .theorem row.reason }

@[simp] theorem WireRow.toLogical_ofLogical_definition
    (row : Row String Nat Int) :
    (WireRow.ofLogical row.asDefinition).toLogical = row.asDefinition := by
  cases row
  rfl

@[simp] theorem WireRow.toLogical_ofLogical_theorem
    (row : Row String Nat Int) (reason : Int) (nonzero : reason ≠ 0) :
    (WireRow.ofLogical (row.asTheorem reason)).toLogical = row.asTheorem reason := by
  cases row
  simp [WireRow.ofLogical, WireRow.toLogical, Row.asTheorem, nonzero]

def WireTable.ofRows (dependencies : List Dependency)
    (rows : List (Row String Nat Int)) : WireTable :=
  ⟨dependencies, rows.map WireRow.ofLogical⟩

def encodeLit : Lit Nat → Value
  | .pos id => array [.scalar (.text "pos"), .scalar (.natural id)]
  | .neg id => array [.scalar (.text "neg"), .scalar (.natural id)]

def decodeLit : Value → Except String (Lit Nat)
  | .list (.cons (.scalar (.text "pos")) (.cons (.scalar (.natural id)) .nil)) => .ok (.pos id)
  | .list (.cons (.scalar (.text "neg")) (.cons (.scalar (.natural id)) .nil)) => .ok (.neg id)
  | _ => .error "expected literal"

@[simp] theorem decodeLit_encodeLit (literal : Lit Nat) :
    decodeLit (encodeLit literal) = .ok literal := by cases literal <;> rfl

def encodeSource : Option String → Value
  | none => array []
  | some source => array [.scalar (.text source)]

def decodeSource : Value → Except String (Option String)
  | .list .nil => .ok none
  | .list (.cons (.scalar (.text source)) .nil) => .ok (some source)
  | _ => .error "expected optional source"

@[simp] theorem decodeSource_encodeSource (source : Option String) :
    decodeSource (encodeSource source) = .ok source := by cases source <;> rfl

def encodeRow (row : WireRow) : Value :=
  array [encodeLit row.premise, encodeSource row.source, encodeLit row.conclusion,
    .scalar (.integer row.reason)]

def decodeRow : Value → Except String WireRow
  | .list (.cons premise (.cons source (.cons conclusion
      (.cons (.scalar (.integer reason)) .nil)))) =>
      return ⟨← decodeLit premise, ← decodeSource source, ← decodeLit conclusion, reason⟩
  | _ => .error "expected proposition row"

@[simp] theorem decodeRow_encodeRow (row : WireRow) :
    decodeRow (encodeRow row) = .ok row := by
  cases row with | mk premise source conclusion reason =>
    cases premise <;> cases source <;> cases conclusion <;> rfl

def encodeDependency : Dependency → Value
  | .table id => array [.scalar (.text "table"), .scalar (.text id)]
  | .logical system context => array [.scalar (.text "logical"), .scalar (.text system), context]

def decodeDependency : Value → Except String Dependency
  | .list (.cons (.scalar (.text "table")) (.cons (.scalar (.text id)) .nil)) =>
      .ok (.table id)
  | .list (.cons (.scalar (.text "logical"))
      (.cons (.scalar (.text system)) (.cons context .nil))) =>
      .ok (.logical system context)
  | _ => .error "expected dependency"

@[simp] theorem decodeDependency_encodeDependency (dependency : Dependency) :
    decodeDependency (encodeDependency dependency) = .ok dependency := by
  cases dependency <;> rfl

def encodeTable (table : WireTable) : Value :=
  object [
    ("dependencies", encodeList encodeDependency table.dependencies),
    ("rows", encodeList encodeRow table.rows)]

def decodeTable : Value → Except String WireTable
  | .map (.objCons "dependencies" (.list dependencies)
      (.objCons "rows" (.list rows) .objNil)) =>
      return ⟨← decodeList decodeDependency dependencies, ← decodeList decodeRow rows⟩
  | _ => .error "expected proposition table"

theorem decodeTable_encodeTable (table : WireTable) :
    decodeTable (encodeTable table) = .ok table := by
  cases table with
  | mk dependencies rows =>
      change (do
        let decodedDependencies ←
          decodeList decodeDependency (RawSyn.ofList (dependencies.map encodeDependency))
        let decodedRows ← decodeList decodeRow (RawSyn.ofList (rows.map encodeRow))
        pure (WireTable.mk decodedDependencies decodedRows)) = .ok ⟨dependencies, rows⟩
      rw [decodeList_map encodeDependency decodeDependency decodeDependency_encodeDependency]
      rw [decodeList_map encodeRow decodeRow decodeRow_encodeRow]
      rfl

instance : Codec WireTable where
  encode := encodeTable
  decode := decodeTable
  decode_encode := decodeTable_encodeTable

/-! ## Logical systems and serialized contexts -/

set_option linter.checkUnivs false in
/-- The table layer needs only names and codecs; it does not inspect foreign logic. -/
class LogicalSystem (System : Type u) where
  Context : Type v
  Formula : Type w
  systemId : System → String
  encodeContext : Context → Value
  decodeContext : Value → Except String Context
  contextRoundTrip : ∀ context, decodeContext (encodeContext context) = .ok context
  encodeFormula : Formula → Value
  decodeFormula : Value → Except String Formula
  formulaRoundTrip : ∀ formula, decodeFormula (encodeFormula formula) = .ok formula

structure DependsOn (System : Type u) [LogicalSystem System] where
  system : System
  context : LogicalSystem.Context System

variable {System : Type u}

def DependsOn.toDependency [LogicalSystem System] (dependency : DependsOn System) : Dependency :=
  .logical (LogicalSystem.systemId dependency.system)
    (LogicalSystem.encodeContext dependency.context)

namespace HolLN

variable {Base : Type u}

/-- A finite JSON-facing HOL context; it can later be elaborated to `FreeCtx`. -/
structure Context (Base : Type u) where
  declarations : List (Nat × Nucleus.HolLN.Ty Base)
  assumptions : List (Nucleus.HolLN.ClosedTm Base)

/-- Supplied by the eventual direct or array-based HOL.Ln JSON specification. -/
class JsonProfile (Base : Type u) where
  encodeContext : Context Base → Value
  decodeContext : Value → Except String (Context Base)
  contextRoundTrip : ∀ context, decodeContext (encodeContext context) = .ok context
  encodeFormula : Nucleus.HolLN.ClosedTm Base → Value
  decodeFormula : Value → Except String (Nucleus.HolLN.ClosedTm Base)
  formulaRoundTrip : ∀ formula, decodeFormula (encodeFormula formula) = .ok formula

inductive HolSystem (Base : Type u) where
  | holLN

instance [JsonProfile Base] : LogicalSystem (HolSystem Base) where
  Context := Context Base
  Formula := Nucleus.HolLN.ClosedTm Base
  systemId := fun | .holLN => "hol.ln"
  encodeContext := JsonProfile.encodeContext
  decodeContext := JsonProfile.decodeContext
  contextRoundTrip := JsonProfile.contextRoundTrip
  encodeFormula := JsonProfile.encodeFormula
  decodeFormula := JsonProfile.decodeFormula
  formulaRoundTrip := JsonProfile.formulaRoundTrip

end HolLN

end Nucleus.PropTable.Json
