import Mathlib.Data.List.Defs

/-!
# Source-qualified propositional tables

An executable design model for the small propositional table family.  It keeps
the logical objects independent of SQLite while making the intended physical
relations literal `List` operations.  Definitions and proved implications are
separate lists: all definition rows with one premise collectively define that
premise as the conjunction of their conclusions.

This is deliberately a first model.  Fixed-width codecs, checked source
resolution, proof objects, and correspondence with the Rust implementation are
follow-up proof obligations rather than axioms hidden here.
-/

namespace Nucleus.PropTable

inductive Lit (α : Type u) where
  | pos : α → Lit α
  | neg : α → Lit α
  deriving DecidableEq, Repr

namespace Lit

def compl : Lit α → Lit α
  | .pos p => .neg p
  | .neg p => .pos p

def map (f : α → β) : Lit α → Lit β
  | .pos p => .pos (f p)
  | .neg p => .neg (f p)

def eval (valuation : α → Bool) : Lit α → Bool
  | .pos p => valuation p
  | .neg p => !(valuation p)

@[simp] theorem eval_compl (valuation : α → Bool) (literal : Lit α) :
    eval valuation literal.compl = !(eval valuation literal) := by
  cases literal <;> simp [compl, eval]

end Lit

/-! ## Conventional formulas and the conjunction/negation basis -/

inductive Formula (α : Type u) where
  | atom : α → Formula α
  | top : Formula α
  | bot : Formula α
  | not : Formula α → Formula α
  | and : Formula α → Formula α → Formula α
  | or : Formula α → Formula α → Formula α
  | iff : Formula α → Formula α → Formula α
  deriving Repr

namespace Formula

def eval (valuation : α → Bool) : Formula α → Bool
  | .atom p => valuation p
  | .top => true
  | .bot => false
  | .not p => !(eval valuation p)
  | .and p q => eval valuation p && eval valuation q
  | .or p q => eval valuation p || eval valuation q
  | .iff p q => eval valuation p == eval valuation q

end Formula

inductive AndNot (α : Type u) where
  | atom : α → AndNot α
  | top : AndNot α
  | not : AndNot α → AndNot α
  | all : List (AndNot α) → AndNot α
  deriving Repr

namespace AndNot

mutual
  def eval (valuation : α → Bool) : AndNot α → Bool
    | .atom p => valuation p
    | .top => true
    | .not p => !(eval valuation p)
    | .all ps => evalList valuation ps

  def evalList (valuation : α → Bool) : List (AndNot α) → Bool
    | [] => true
    | p :: ps => eval valuation p && evalList valuation ps
end

def disj (p q : AndNot α) : AndNot α := .not (.all [.not p, .not q])

def lower : Formula α → AndNot α
  | .atom p => .atom p
  | .top => .top
  | .bot => .not .top
  | .not p => .not (lower p)
  | .and p q => .all [lower p, lower q]
  | .or p q => disj (lower p) (lower q)
  | .iff p q =>
      .all [disj (.not (lower p)) (lower q), disj (.not (lower q)) (lower p)]

theorem lower_correct (valuation : α → Bool) (formula : Formula α) :
    eval valuation (lower formula) = Formula.eval valuation formula := by
  induction formula with
  | atom | top | bot => rfl
  | not p ih => simp [lower, eval, Formula.eval, ih]
  | and p q ihp ihq => simp [lower, eval, evalList, Formula.eval, ihp, ihq]
  | or p q ihp ihq =>
      simp [lower, disj, eval, evalList, Formula.eval, ihp, ihq]
  | iff p q ihp ihq =>
      simp [lower, disj, eval, evalList, Formula.eval, ihp, ihq]
      cases Formula.eval valuation p <;> cases Formula.eval valuation q <;> rfl

end AndNot

/-! ## The two basic table kinds -/

structure LocalRow (α : Type u) where
  premise : Lit α
  conclusion : Lit α
  deriving DecidableEq, Repr

structure LocalTables (α : Type u) where
  definitions : List (LocalRow α)
  theorems : List (LocalRow α)
  deriving Repr

structure Ref (σ : Type v) (α : Type u) where
  /-- `none` is the current table; `some source` is an immutable foreign table. -/
  source : Option σ
  proposition : Lit α
  deriving DecidableEq, Repr

structure SourcedRow (σ : Type v) (α : Type u) where
  premise : Lit α
  conclusion : Ref σ α
  deriving DecidableEq, Repr

structure SourcedTables (σ : Type v) (α : Type u) where
  definitions : List (SourcedRow σ α)
  theorems : List (SourcedRow σ α)
  deriving Repr

/-!
The interchange/API row retains a source and a reason.  `definition` is a
distinguished reason: those rows materialize in the definition relation;
every other reason is theorem provenance and materializes in the theorem
relation.  The physical theorem table deliberately need not carry provenance.
-/

inductive Reason (ρ : Type w) where
  | definition
  | theorem : ρ → Reason ρ
  deriving DecidableEq, Repr

structure Row (σ : Type v) (α : Type u) (ρ : Type w) where
  premise : Lit α
  source : Option σ
  conclusion : Lit α
  reason : Reason ρ
  deriving DecidableEq, Repr

abbrev UnsourcedRow (α : Type u) (ρ : Type w) := Row Empty α ρ

namespace Row

def relationRow (row : Row σ α ρ) : SourcedRow σ α :=
  ⟨row.premise, ⟨row.source, row.conclusion⟩⟩

def asDefinition (row : Row σ α ρ) : Row σ α ρ :=
  { row with reason := .definition }

def asTheorem (row : Row σ α ρ) (reason : ρ) : Row σ α ρ :=
  { row with reason := .theorem reason }

def split (rows : List (Row σ α ρ)) : SourcedTables σ α :=
  { definitions := rows.filterMap fun row => match row.reason with
      | .definition => some row.relationRow
      | .theorem _ => none
    theorems := rows.filterMap fun row => match row.reason with
      | .definition => none
      | .theorem _ => some row.relationRow }

/-- Materialize only theorem reasons accepted by an explicit soundness policy. -/
def splitWithPolicy (sound : ρ → Bool) (rows : List (Row σ α ρ)) : SourcedTables σ α :=
  { definitions := rows.filterMap fun row => match row.reason with
      | .definition => some row.relationRow
      | .theorem _ => none
    theorems := rows.filterMap fun row => match row.reason with
      | .definition => none
      | .theorem reason => if sound reason then some row.relationRow else none }

theorem splitWithPolicy_definitions (sound : ρ → Bool) (rows : List (Row σ α ρ)) :
    (splitWithPolicy sound rows).definitions = (split rows).definitions := by
  simp only [splitWithPolicy, split]

theorem splitWithPolicy_theorems_subset (sound : ρ → Bool) (rows : List (Row σ α ρ)) :
    ∀ theoremRow ∈ (splitWithPolicy sound rows).theorems,
      theoremRow ∈ (split rows).theorems := by
  intro theoremRow membership
  simp only [splitWithPolicy, List.mem_filterMap] at membership
  obtain ⟨row, rowIn, accepted⟩ := membership
  simp only [split, List.mem_filterMap]
  refine ⟨row, rowIn, ?_⟩
  split at accepted
  · contradiction
  · split at accepted
    · exact accepted
    · contradiction

@[simp] theorem split_definition (row : Row σ α ρ) :
    split [row.asDefinition] =
      ⟨[row.relationRow], []⟩ := by
  simp [split, asDefinition, relationRow]

@[simp] theorem split_theorem (row : Row σ α ρ) (reason : ρ) :
    split [row.asTheorem reason] =
      ⟨[], [row.relationRow]⟩ := by
  simp [split, asTheorem, relationRow]

end Row

/-! ## Experimental signed-reason convention

This adapter studies a possible SQLite encoding without selecting it as the
default design: zero means definition, positive integers are admitted theorem
reasons, and negative integers remain present as unverified provenance but are
filtered from queries for established facts.
-/

namespace SignedReason

def row (premise : Lit α) (source : Option σ) (conclusion : Lit α)
    (reason : Int) : Row σ α Int :=
  if reason = 0 then ⟨premise, source, conclusion, .definition⟩
  else ⟨premise, source, conclusion, .theorem reason⟩

def trusted (reason : Int) : Bool := decide (0 < reason)

def materialize (rows : List (Row σ α Int)) : SourcedTables σ α :=
  Row.splitWithPolicy trusted rows

example (premise conclusion : Lit α) (source : Option σ) :
    (materialize [row premise source conclusion 0]).definitions =
      [⟨premise, ⟨source, conclusion⟩⟩] := by
  simp [materialize, row, Row.splitWithPolicy, Row.relationRow]

example (premise conclusion : Lit α) (source : Option σ) :
    (materialize [row premise source conclusion 1]).theorems =
      [⟨premise, ⟨source, conclusion⟩⟩] := by
  simp [materialize, row, trusted, Row.splitWithPolicy, Row.relationRow]

example (premise conclusion : Lit α) (source : Option σ) :
    (materialize [row premise source conclusion (-1)]).theorems = [] := by
  simp [materialize, row, trusted, Row.splitWithPolicy]

end SignedReason

def LocalRow.withLocalSource (row : LocalRow α) : SourcedRow σ α :=
  ⟨row.premise, ⟨none, row.conclusion⟩⟩

def LocalTables.withLocalSource (tables : LocalTables α) : SourcedTables σ α :=
  ⟨tables.definitions.map LocalRow.withLocalSource,
   tables.theorems.map LocalRow.withLocalSource⟩

/-! ## Relational algebra over `List record` -/

namespace Rel

def select (predicate : α → Bool) (rows : List α) : List α := rows.filter predicate

def project (f : α → β) (rows : List α) : List β := rows.map f

def union (left right : List α) : List α := left ++ right

def join (related : α → β → Bool) (left : List α) (right : List β) : List (α × β) :=
  left.flatMap fun a => right.filterMap fun b => if related a b then some (a, b) else none

end Rel

namespace LocalTables

variable [DecidableEq α]

def definitionRows (tables : LocalTables α) (premise : Lit α) : List (LocalRow α) :=
  Rel.select (fun row => decide (row.premise = premise)) tables.definitions

def definition (tables : LocalTables α) (premise : Lit α) : List (Lit α) :=
  Rel.project LocalRow.conclusion (tables.definitionRows premise)

def impliedBy (tables : LocalTables α) (premise : Lit α) : List (Lit α) :=
  Rel.project LocalRow.conclusion <|
    Rel.select (fun row => decide (row.premise = premise)) tables.theorems

def implying (tables : LocalTables α) (conclusion : Lit α) : List (Lit α) :=
  Rel.project LocalRow.premise <|
    Rel.select (fun row => decide (row.conclusion = conclusion)) tables.theorems

def equivalent (tables : LocalTables α) (left right : Lit α) : Bool :=
  tables.theorems.any (fun row => decide (row = ⟨left, right⟩)) &&
    tables.theorems.any (fun row => decide (row = ⟨right, left⟩))

def tautologies (tables : LocalTables α) : List α :=
  tables.theorems.filterMap fun row => match row with
    | ⟨.neg p, .pos q⟩ => if p = q then some p else none
    | _ => none

def unsatisfiable (tables : LocalTables α) : List α :=
  tables.theorems.filterMap fun row => match row with
    | ⟨.pos p, .neg q⟩ => if p = q then some p else none
    | _ => none

/-- All defining rows for `premise` collectively mean an iff with this conjunction. -/
def definitionHolds (tables : LocalTables α) (valuation : α → Bool) (premise : Lit α) : Bool :=
  Lit.eval valuation premise == (tables.definition premise).all (Lit.eval valuation)

def theoremHolds (valuation : α → Bool) (row : LocalRow α) : Bool :=
  !(Lit.eval valuation row.premise) || Lit.eval valuation row.conclusion

def holds (tables : LocalTables α) (valuation : α → Bool) : Bool :=
  let premises := tables.definitions.map LocalRow.premise
  premises.all (tables.definitionHolds valuation) && tables.theorems.all (theoremHolds valuation)

end LocalTables

namespace SourcedTables

variable [DecidableEq σ] [DecidableEq α]

def evalRef (localValuation : α → Bool) (foreign : σ → α → Bool) (ref : Ref σ α) : Bool :=
  match ref.source with
  | none => Lit.eval localValuation ref.proposition
  | some source => Lit.eval (foreign source) ref.proposition

def definition (tables : SourcedTables σ α) (premise : Lit α) : List (Ref σ α) :=
  Rel.project SourcedRow.conclusion <|
    Rel.select (fun row => decide (row.premise = premise)) tables.definitions

def impliedBy (tables : SourcedTables σ α) (premise : Lit α) : List (Ref σ α) :=
  Rel.project SourcedRow.conclusion <|
    Rel.select (fun row => decide (row.premise = premise)) tables.theorems

def implying (tables : SourcedTables σ α) (conclusion : Ref σ α) : List (Lit α) :=
  Rel.project SourcedRow.premise <|
    Rel.select (fun row => decide (row.conclusion = conclusion)) tables.theorems

def hasTheorem (tables : SourcedTables σ α) (premise : Lit α)
    (conclusion : Ref σ α) : Bool :=
  tables.theorems.any fun row => decide (row = ⟨premise, conclusion⟩)

/-- Equivalence inside the current table; foreign equivalence requires an import bridge. -/
def equivalentLocal (tables : SourcedTables σ α) (left right : Lit α) : Bool :=
  tables.hasTheorem left ⟨none, right⟩ && tables.hasTheorem right ⟨none, left⟩

def tautologies (tables : SourcedTables σ α) : List α :=
  tables.theorems.filterMap fun row => match row with
    | ⟨.neg p, ⟨none, .pos q⟩⟩ => if p = q then some p else none
    | _ => none

def unsatisfiable (tables : SourcedTables σ α) : List α :=
  tables.theorems.filterMap fun row => match row with
    | ⟨.pos p, ⟨none, .neg q⟩⟩ => if p = q then some p else none
    | _ => none

def definitionHolds (tables : SourcedTables σ α) (localValuation : α → Bool)
    (foreign : σ → α → Bool) (premise : Lit α) : Bool :=
  Lit.eval localValuation premise ==
    (tables.definition premise).all (evalRef localValuation foreign)

end SourcedTables

/-! ## CNF and DNF embeddings -/

abbrev Cnf (α : Type u) := List (List (Lit α))
abbrev Dnf (α : Type u) := List (List (Lit α))

namespace Cnf

def eval (valuation : α → Bool) (cnf : Cnf α) : Bool :=
  cnf.all fun clause => clause.any (Lit.eval valuation)

inductive Id (α : Type u) where
  | variable : α → Id α
  | clauseFailure : Nat → Id α
  | root : Id α
  deriving DecidableEq, Repr

def rowsFrom (index : Nat) : Cnf α → List (LocalRow (Id α))
  | [] => []
  | clause :: rest =>
      clause.map (fun literal =>
        ⟨.pos (.clauseFailure index), (literal.map Id.variable).compl⟩) ++
      rowsFrom (index + 1) rest

def toTable (cnf : Cnf α) : LocalTables (Id α) :=
  { definitions := rowsFrom 0 cnf ++
      (List.range cnf.length).map fun index =>
        ⟨.pos .root, .neg (.clauseFailure index)⟩
    theorems := [] }

def root : Lit (Id α) := .pos .root

/-- The efficiently decodable subset carries the shape witness explicitly. -/
structure Encoding (α : Type u) where
  clauses : Cnf α
  table : LocalTables (Id α)
  shaped : table = toTable clauses

def encode (cnf : Cnf α) : Encoding α := ⟨cnf, toTable cnf, rfl⟩
def decode (encoding : Encoding α) : Cnf α := encoding.clauses

@[simp] theorem decode_encode (cnf : Cnf α) : decode (encode cnf) = cnf := rfl

end Cnf

namespace Dnf

def eval (valuation : α → Bool) (dnf : Dnf α) : Bool :=
  dnf.any fun term => term.all (Lit.eval valuation)

inductive Id (α : Type u) where
  | variable : α → Id α
  | term : Nat → Id α
  | allTermsFalse : Id α
  deriving DecidableEq, Repr

def rowsFrom (index : Nat) : Dnf α → List (LocalRow (Id α))
  | [] => []
  | term :: rest =>
      term.map (fun literal => ⟨.pos (.term index), literal.map Id.variable⟩) ++
      rowsFrom (index + 1) rest

def toTable (dnf : Dnf α) : LocalTables (Id α) :=
  { definitions := rowsFrom 0 dnf ++
      (List.range dnf.length).map fun index =>
        ⟨.pos .allTermsFalse, .neg (.term index)⟩
    theorems := [] }

/-- The DNF itself is the negation of the node saying every term is false. -/
def root : Lit (Id α) := .neg .allTermsFalse

structure Encoding (α : Type u) where
  terms : Dnf α
  table : LocalTables (Id α)
  shaped : table = toTable terms

def encode (dnf : Dnf α) : Encoding α := ⟨dnf, toTable dnf, rfl⟩
def decode (encoding : Encoding α) : Dnf α := encoding.terms

@[simp] theorem decode_encode (dnf : Dnf α) : decode (encode dnf) = dnf := rfl

end Dnf

/-! ## Binary decision diagrams -/

inductive Bdd (α : Type u) where
  | leaf : Bool → Bdd α
  | branch : α → Bdd α → Bdd α → Bdd α
  deriving Repr

namespace Bdd

def eval (valuation : α → Bool) : Bdd α → Bool
  | .leaf value => value
  | .branch question onFalse onTrue =>
      if valuation question then eval valuation onTrue else eval valuation onFalse

def formula : Bdd α → Formula α
  | .leaf false => .bot
  | .leaf true => .top
  | .branch question onFalse onTrue =>
      .or (.and (.atom question) (formula onTrue))
          (.and (.not (.atom question)) (formula onFalse))

theorem formula_correct (valuation : α → Bool) (bdd : Bdd α) :
    Formula.eval valuation bdd.formula = bdd.eval valuation := by
  induction bdd with
  | leaf value => cases value <;> rfl
  | branch question onFalse onTrue falseCorrect trueCorrect =>
      simp [formula, Formula.eval, eval, falseCorrect, trueCorrect]
      cases valuation question <;> simp

structure Row (ι : Type v) (α : Type u) where
  id : ι
  question : α
  onFalse : ι
  onTrue : ι
  deriving DecidableEq, Repr

def lookup [DecidableEq ι] (rows : List (Row ι α)) (id : ι) : Option (Row ι α) :=
  rows.find? fun row => row.id = id

/-- One query-driven evaluation step; the row id remains available for metadata lookup. -/
def answer (row : Row ι α) (value : Bool) : ι := if value then row.onTrue else row.onFalse

end Bdd

/-! ## Small executable examples -/

example :
    (LocalTables.impliedBy
      { definitions := [], theorems := [⟨.pos 1, .neg 2⟩] }
      (.pos 1)) = [.neg 2] := by decide

example :
    (LocalTables.unsatisfiable
      { definitions := [], theorems := [⟨.pos 7, .neg 7⟩] }) = [7] := by decide

example : Cnf.decode (Cnf.encode [[.pos "p", .neg "q"]]) = [[.pos "p", .neg "q"]] := rfl

example : Dnf.decode (Dnf.encode [[.pos "p"], [.neg "q"]]) = [[.pos "p"], [.neg "q"]] := rfl

end Nucleus.PropTable
