import Nucleus.Hol.Ethane.Amb
import Nucleus.Hol.Ethane.Arena.OneBased.Columns
import Nucleus.Hol.Ethane.Arena.OneBased.Kernel
import Nucleus.Hol.Ethane.Arena.OneBased.SynFacts

/-!
# Nested one-based arena layout

This file is the logical model of the first `amb`/column Rust refactor.  Its
structures follow the serialized object exactly:

* `import` is the import vector;
* `amb` contains predicate atoms, named ambient axiom capabilities, ambient
  CNF context, and ambient theorems;
* `pred.syl` contains valuation-independent classical syllogisms;
* `hol` contains expression-only definitions, named HOL axioms, HOL context
  and theorems, the semantic equality column, and the nested syntactic
  columns/cache.

There is no separate premise/conclusion metadata layer. Imported validity and
sorting obligations are ordinary `amb.pred` atoms placed in positive unit
clauses in `amb.ctx`.
`amb.ax` is a `Finset String`, exactly like `hol.ax`; this version defines no
primitive ambient axiom names.
-/

namespace Nucleus.Hol.Ethane.OneBased.Layout

open Nucleus.Hol.Ethane
open Nucleus.Hol.Ethane.ClassicalMatrix
open Nucleus.Hol.Ethane.OneBased

/-! ## Classical wire matrices

Rust keeps a tombstone at every deleted CNF/DNF row so that row identifiers
remain stable.  Those inner tombstones are serialized.  In contrast, a
`ClassicalArena` serializes only its live theorem slots.  Keeping the wire
shape distinct from `ClassicalMatrix.Cnf`/`Dnf` prevents the semantic model
from accidentally forgetting an observable row position. -/

structure WireCnf where
  rows : List (Option (Clause Ref))
  deriving DecidableEq

structure WireDnf where
  rows : List (Option (Cube Ref))
  deriving DecidableEq

structure WireSequent where
  left : WireCnf
  right : WireDnf
  deriving DecidableEq

def WireCnf.semantic (cnf : WireCnf) : Cnf Ref :=
  ⟨cnf.rows.filterMap id⟩

def WireDnf.semantic (dnf : WireDnf) : Dnf Ref :=
  ⟨dnf.rows.filterMap id⟩

def WireSequent.semantic (fact : WireSequent) : Sequent Ref :=
  ⟨fact.left.semantic, fact.right.semantic⟩

@[simp] theorem WireCnf.semantic_tombstone (rows : List (Option (Clause Ref))) :
    (WireCnf.mk (none :: rows)).semantic = (WireCnf.mk rows).semantic := rfl

@[simp] theorem WireDnf.semantic_tombstone (rows : List (Option (Cube Ref))) :
    (WireDnf.mk (none :: rows)).semantic = (WireDnf.mk rows).semantic := rfl

/-- The serialized theorem sequence. Rust's outer mutable free-list and
deleted theorem slots are absent from serialization; only live rows occur. -/
abbrev ClassicalArena := List WireSequent

/-- `ThmId` is a positive `i32`, hence at most this many compact live rows can
be accepted by Rust's `ClassicalArena::from_rows`. -/
def ClassicalArena.WireValid (arena : ClassicalArena) : Prop :=
  arena.length ≤ 2_147_483_647

/-- Exactly the two ambient atoms implemented by Rust. -/
abbrev Pred := Amb.Pred ImportId Ref

structure AmbSection where
  pred : List Pred
  ax : Finset String
  ctx : WireCnf
  thm : ClassicalArena
  deriving DecidableEq

structure PredSection where
  syl : ClassicalArena
  deriving DecidableEq

structure SynSection where
  subst1 : List SynSlot
  subst1Free : Option SynFactId
  eq : Columns.Column Ref
  conv : Columns.Column Ref
  deriving DecidableEq, Repr

structure HolSection where
  defs : List detail.Expr
  ax : Finset String
  ctx : Finset Ref
  thm : ClassicalArena
  eq : Columns.Column Ref
  syn : SynSection
  deriving DecidableEq

/- Literal imports recursively contain the same current nested arena shape,
exactly as Rust's `Import::Literal(Box<Arena>)`. -/
mutual

inductive Import where
  | null
  | literal (arena : Arena)
  | link (value : OneBased.Link)

/-- The normalized logical value of the nested Rust arena. -/
inductive Arena where
  | mk («import» : List Import) (amb : AmbSection)
      (pred : PredSection) (hol : HolSection)

end

/-! Structural measures and recursive wire validity. These recurse through
literal imports without imposing any artificial reference-space cutoff. The
separate wire-depth bound below is the concrete CBOR decoder limit, not a HOL
reference-space limit. -/

mutual

def Import.literalDepth : Import → Nat
  | .null => 0
  | .literal arena => arena.literalDepth + 1
  | .link _ => 0

def Arena.literalDepth : Arena → Nat
  | .mk imports _ _ _ => Imports.literalDepth imports

def Imports.literalDepth : List Import → Nat
  | [] => 0
  | entry :: entries => max entry.literalDepth (Imports.literalDepth entries)

end

/-- The concrete CBOR decoder accepts at most 126 nested literal imports.

This is one below its 127-container recursion budget.  It is a property of the
Rust byte decoder, not of the recursive logical arena datatype or of `Ref`. -/
def maxLiteralImportDepth : Nat := 126

namespace Arena

@[simp] def imports : Arena → List Import | .mk imports .. => imports
@[simp] def amb : Arena → AmbSection | .mk _ amb .. => amb
@[simp] def pred : Arena → PredSection | .mk _ _ pred .. => pred
@[simp] def hol : Arena → HolSection | .mk _ _ _ hol => hol

end Arena

/-! ## Exact Serde view

The following view uses lists at the two `BTreeSet` boundaries and permits
non-normal trailing nulls, exactly as deserialization does before constructing
an `Arena`. -/

inductive ArenaTag | arena deriving DecidableEq

structure AmbView where
  pred : List Pred
  ax : List String
  ctx : WireCnf
  thm : ClassicalArena

structure SynView where
  subst1 : List SynSlot
  subst1Free : Option SynFactId
  eq : Columns.Column Ref
  conv : Columns.Column Ref

structure HolView where
  defs : List detail.Expr
  ax : List String
  ctx : List Ref
  thm : ClassicalArena
  eq : Columns.Column Ref
  syn : SynView

structure View where
  tag : ArenaTag
  «import» : List Import
  amb : AmbView
  pred : PredSection
  hol : HolView

def View.columnsResident (view : View) : Prop :=
  let dense : Columns.Dense := {
    defs := view.hol.defs
    eq := view.hol.eq
    synEq := view.hol.syn.eq
    conv := view.hol.syn.conv
  }
  dense.WellFormed

def View.classicalResident (view : View) : Prop :=
  view.amb.thm.WireValid ∧ view.pred.syl.WireValid ∧ view.hol.thm.WireValid

/-- Rust rejects a non-null column member beyond `defs`, then strips trailing
nulls and normalizes the two string/reference sets. -/
noncomputable def View.normalize? (view : View) : Option Arena := by
  classical
  exact if view.columnsResident ∧ view.classicalResident then
    some (.mk view.«import» {
        pred := view.amb.pred
        ax := view.amb.ax.toFinset
        ctx := view.amb.ctx
        thm := view.amb.thm
      } view.pred {
        defs := view.hol.defs
        ax := view.hol.ax.toFinset
        ctx := view.hol.ctx.toFinset
        thm := view.hol.thm
        eq := view.hol.eq.normalize
        syn := {
          subst1 := view.hol.syn.subst1
          subst1Free := view.hol.syn.subst1Free
          eq := view.hol.syn.eq.normalize
          conv := view.hol.syn.conv.normalize
        }
      })
    else none

def Arena.toView (arena : Arena) : View := {
  tag := .arena
  «import» := arena.imports
  amb := {
    pred := arena.amb.pred
    ax := arena.amb.ax.sort (· ≤ ·)
    ctx := arena.amb.ctx
    thm := arena.amb.thm
  }
  pred := arena.pred
  hol := {
    defs := arena.hol.defs
    ax := arena.hol.ax.sort (· ≤ ·)
    ctx := arena.hol.ctx.sort (· ≤ ·)
    thm := arena.hol.thm
    eq := arena.hol.eq
    syn := {
      subst1 := arena.hol.syn.subst1
      subst1Free := arena.hol.syn.subst1Free
      eq := arena.hol.syn.eq
      conv := arena.hol.syn.conv
    }
  }
}

def Arena.ColumnsNormalized (arena : Arena) : Prop :=
  arena.hol.eq.normalize = arena.hol.eq ∧
  arena.hol.syn.eq.normalize = arena.hol.syn.eq ∧
  arena.hol.syn.conv.normalize = arena.hol.syn.conv

def Arena.ClassicalWireValid (arena : Arena) : Prop :=
  arena.amb.thm.WireValid ∧ arena.pred.syl.WireValid ∧ arena.hol.thm.WireValid

/-- The dense expression/equality tables, with the unchanged `subst1` cache
alongside them. Rows themselves contain only expressions. -/
def Arena.columns (arena : Arena) : Columns.Arena where
  dense := {
    defs := arena.hol.defs
    eq := arena.hol.eq
    synEq := arena.hol.syn.eq
    conv := arena.hol.syn.conv
  }
  subst1 := arena.hol.syn.subst1
  subst1Free := arena.hol.syn.subst1Free

/-! Recursive projection into the established HOL proof core. -/

mutual

def Import.holCore : Import → OneBased.Import
  | .null => .null
  | .literal arena => .literal arena.holCore
  | .link value => .link value

/-- Project the nested wire arena into the proof core while preserving its
dense HOL storage exactly. -/
def Arena.holCore : Arena → OneBased.Arena
  | .mk imports _ _ hol =>
      let dense : Columns.Dense := {
        defs := hol.defs
        eq := hol.eq
        synEq := hol.syn.eq
        conv := hol.syn.conv
      }
      .mk (imports.map Import.holCore) hol.ax
        dense
        hol.syn.subst1 hol.syn.subst1Free hol.ctx [] []

end

@[simp] theorem Arena.holCore_dense (arena : Arena) :
    arena.holCore.dense = arena.columns.dense := by
  cases arena
  simp [Arena.holCore, Arena.columns, OneBased.Arena.dense]

@[simp] theorem Arena.holCore_defs (arena : Arena) :
    arena.holCore.defs = arena.columns.dense.rows := by
  simp [OneBased.Arena.defs, Arena.holCore_dense]

@[simp] theorem Arena.holCore_imports (arena : Arena) :
    arena.holCore.imports =
      arena.imports.map Import.holCore := by
  cases arena; simp [Arena.holCore, OneBased.Arena.imports]

@[simp] theorem Arena.holCore_axs (arena : Arena) :
    arena.holCore.axs = arena.hol.ax := by
  cases arena; simp [Arena.holCore, OneBased.Arena.axs]

@[simp] theorem Arena.holCore_ctx (arena : Arena) :
    arena.holCore.ctx = arena.hol.ctx := by
  cases arena; simp [Arena.holCore, OneBased.Arena.ctx]

theorem Arena.holCore_row? (arena : Arena) (reference : Ref) :
    arena.holCore.row? reference = arena.columns.dense.row? reference := by
  simp [OneBased.Arena.row?, Arena.holCore_dense]

@[simp] theorem Arena.columns_subst1 (arena : Arena) :
    arena.columns.subst1 = arena.hol.syn.subst1 := rfl

@[simp] theorem Arena.columns_subst1Free (arena : Arena) :
    arena.columns.subst1Free = arena.hol.syn.subst1Free := rfl

@[simp] theorem Arena.columns_semanticEq (arena : Arena) :
    arena.columns.dense.eq = arena.hol.eq := rfl

@[simp] theorem Arena.columns_synEq (arena : Arena) :
    arena.columns.dense.synEq = arena.hol.syn.eq := rfl

@[simp] theorem Arena.columns_conv (arena : Arena) :
    arena.columns.dense.conv = arena.hol.syn.conv := rfl

/-- Exact decoder invariant: a non-null cell's position is resident. Targets
may dangle in a raw decoded arena, matching Rust. -/
def Arena.ColumnsWireValid (arena : Arena) : Prop :=
  arena.columns.dense.WellFormed

/-- Stronger checked-kernel invariant. Checked union/classifier operations
only install resident targets, although raw deserialization need not. -/
def Arena.ColumnsChecked (arena : Arena) : Prop :=
  Columns.FusedChecked arena.columns.dense

mutual

def Import.WireCanonical : Import → Prop
  | .null => True
  | .literal arena => arena.WireCanonical
  | .link _ => True

def Arena.WireCanonical : Arena → Prop
  | .mk imports amb pred hol =>
      Imports.WireCanonical imports ∧
      (Arena.mk imports amb pred hol).ColumnsWireValid ∧
      (Arena.mk imports amb pred hol).ClassicalWireValid ∧
      (Arena.mk imports amb pred hol).ColumnsNormalized

def Imports.WireCanonical : List Import → Prop
  | [] => True
  | entry :: entries => entry.WireCanonical ∧ Imports.WireCanonical entries

end

/-- A canonical arena that the current Rust byte decoder can deserialize.

This deliberately does not participate in `WireCanonical`: arenas and the
parsed-CBOR model are structurally recursive without a depth cutoff.  The
bound records only the current serde implementation's container budget. -/
def Arena.ByteWireCanonical (arena : Arena) : Prop :=
  arena.WireCanonical ∧ arena.literalDepth ≤ maxLiteralImportDepth

theorem Arena.toView_columnsResident {arena : Arena}
    (wireValid : arena.ColumnsWireValid) : arena.toView.columnsResident := wireValid

theorem Arena.toView_classicalResident {arena : Arena}
    (wireValid : arena.ClassicalWireValid) : arena.toView.classicalResident := wireValid

/-- Exact normalized Serde roundtrip. This is the representation isomorphism
between the nested wire view and the logical arena value. -/
theorem Arena.normalize?_toView {arena : Arena}
    (wireValid : arena.ColumnsWireValid) (classicalValid : arena.ClassicalWireValid)
    (normalized : arena.ColumnsNormalized) :
    arena.toView.normalize? = some arena := by
  rcases normalized with ⟨eq, synEq, conv⟩
  rw [View.normalize?]
  have resident : arena.toView.columnsResident ∧ arena.toView.classicalResident :=
    ⟨Arena.toView_columnsResident wireValid,
      Arena.toView_classicalResident classicalValid⟩
  rw [if_pos resident]
  cases arena with
  | mk imports amb pred hol =>
      cases amb
      cases pred
      cases hol
      simp_all [Arena.toView]

/-- The refinement invariant maintained by checked equality insertion. -/
def Arena.EqualityRefines (arena : Arena) : Prop :=
  Columns.Refines arena.columns.dense

theorem Arena.synEq_implies_semantic {arena : Arena} {left right : Ref}
    (refines : arena.EqualityRefines)
    (related : Columns.Class arena.columns.dense .syn left right) :
    Columns.Class arena.columns.dense .semantic left right :=
  refines.syn_semantic related

/-! ## Recursive import semantics

Linked imports are supplied by an external object resolver.  Literal imports
need no resolver and retain the complete nested arena.  Trust is deliberately
an external predicate: this layer records `arena.ok`, but does not bake a PKI
or a circular notion of validator acceptance into the HOL TCB. -/

abbrev Resolver := OneBased.Link → Option Arena

def resolveImport? (resolve : Resolver) : Import → Option Arena
  | .null => none
  | .literal arena => some arena
  | .link value => resolve value

def coreResolver (resolve : Resolver) : OneBased.Resolver :=
  fun link => (resolve link).map Arena.holCore

def Arena.import? (arena : Arena) (source : ImportId) : Option Import :=
  arena.imports[source.value.toNat - 1]?

/-- Resolve an ambient `arena.ok src` atom through the arena's import table.
This asserts validity according to the caller's explicit trust interpretation,
not merely successful graph resolution. -/
def Arena.ImportOk (trusted : Arena → Prop) (resolve : Resolver) (arena : Arena)
    (source : ImportId) : Prop :=
  ∃ entry imported,
    arena.import? source = some entry ∧
    resolveImport? resolve entry = some imported ∧
    trusted imported

/-- Resolve an ambient `hol.sort src ix sort` atom through the exact source,
foreign reference, and local classifier stored by Rust. -/
def Arena.ImportSort (resolve : Resolver) (arena : Arena) (source : ImportId)
    (foreign sort : Ref) : Prop :=
  ∃ entry imported value classifier,
    arena.import? source = some entry ∧
    resolveImport? resolve entry = some imported ∧
    Resolves (coreResolver resolve) imported.holCore foreign value ∧
    Resolves (coreResolver resolve) arena.holCore sort classifier ∧
    value.HasSort classifier

def Arena.ambientTheory (arena : Arena) : Amb.Theory ImportId Ref where
  ax := arena.amb.ax
  defs := fun reference => arena.amb.pred[reference.value.toNat - 1]?
  ctx := arena.amb.ctx.semantic

/-- No primitive ambient axiom name exists in PR1.  Consequently a checked
kernel can carry only an empty `amb.ax`; raw arenas may deserialize arbitrary
names but cannot be promoted by this invariant. -/
def AllowedAmbientAxiom (_name : String) : Prop := False

theorem allowsAmbientAxioms_iff_empty (arena : Arena) :
    arena.ambientTheory.AllowsAxioms AllowedAmbientAxiom ↔ arena.amb.ax = ∅ := by
  constructor
  · intro allowed
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨name, member⟩
    exact allowed name member
  · intro empty name member
    change name ∈ arena.amb.ax at member
    rw [empty] at member
    simp at member

/-- `amb.thm` consists exactly of consequences of definitions and the ambient
CNF context.  Named axioms are checked separately and contribute no formula. -/
def Arena.AmbThmSound (trusted : Arena → Prop) (resolve : Resolver) (arena : Arena) : Prop :=
  ∀ fact ∈ arena.amb.thm,
    arena.ambientTheory.Proves (arena.ImportOk trusted resolve) (arena.ImportSort resolve)
      fact.semantic

/-- `pred.syl` is independent of all HOL and ambient assumptions. -/
def Arena.SylSound (arena : Arena) : Prop :=
  ∀ fact ∈ arena.pred.syl, fact.semantic.Sound

/-- A source equality, an argument, and the equality obtained by applying both
functions to that argument, reconstructed from their checked arena rows. -/
def Arena.FunctionApplicationEquality (resolve : Resolver) (arena : Arena)
    (source argument target : Ref) : Prop :=
  ∃ boolType domain codomain function varied value,
    Resolves (coreResolver resolve) arena.holCore source
      (.term boolType (.eq (.arr domain codomain) function varied)) ∧
    Resolves (coreResolver resolve) arena.holCore argument (.term domain value) ∧
    Resolves (coreResolver resolve) arena.holCore target
      (.term boolType (.eq codomain (.app function value) (.app varied value)))

/-- A source equality and the equality obtained by abstracting both operands
over one checked free variable. Rust separately checks that the variable is
fresh for the theorem's entire premise matrix. -/
def Arena.AbstractionEquality (resolve : Resolver) (arena : Arena)
    (source binder target : Ref) : Prop :=
  ∃ boolType domain codomain name left right,
    Resolves (coreResolver resolve) arena.holCore source
      (.term boolType (.eq codomain left right)) ∧
    Resolves (coreResolver resolve) arena.holCore binder
      (.term domain (.tmFv name domain)) ∧
    Resolves (coreResolver resolve) arena.holCore target
      (.term boolType (.eq (.arr domain codomain)
        (.lam name domain left) (.lam name domain right)))

/-- A checked term and its reflexive object-language equality (`REFL`). -/
def Arena.ReflexiveEquality (resolve : Resolver) (arena : Arena)
    (term target : Ref) : Prop :=
  ∃ boolType domain value,
    Resolves (coreResolver resolve) arena.holCore term (.term domain value) ∧
    Resolves (coreResolver resolve) arena.holCore target
      (.term boolType (.eq domain value value))

/-- An equality and the equality obtained by applying one checked function to
both operands (`AP_TERM`). -/
def Arena.FunctionArgumentEquality (resolve : Resolver) (arena : Arena)
    (source function target : Ref) : Prop :=
  ∃ boolType domain codomain left right applied,
    Resolves (coreResolver resolve) arena.holCore source
      (.term boolType (.eq domain left right)) ∧
    Resolves (coreResolver resolve) arena.holCore function
      (.term (.arr domain codomain) applied) ∧
    Resolves (coreResolver resolve) arena.holCore target
      (.term boolType (.eq codomain (.app applied left) (.app applied right)))

/-- Boolean equality, its left proposition, and its right proposition, as
consumed by `EQ_MP`. -/
def Arena.EqualityModusPonens (resolve : Resolver) (arena : Arena)
    (equality premise target : Ref) : Prop :=
  ∃ boolType left right,
    Resolves (coreResolver resolve) arena.holCore equality
      (.term boolType (.eq .boolTy left right)) ∧
    Resolves (coreResolver resolve) arena.holCore premise (.term .boolTy left) ∧
    Resolves (coreResolver resolve) arena.holCore target (.term .boolTy right)

/-- An equality of one checked proposition with the Boolean truth literal. -/
def Arena.EqualityToTruth (resolve : Resolver) (arena : Arena)
    (source target : Ref) : Prop :=
  ∃ boolType equalityType proposition,
    Resolves (coreResolver resolve) arena.holCore source
      (.term boolType (.eq equalityType proposition (.bool true))) ∧
    Resolves (coreResolver resolve) arena.holCore target
      (.term equalityType proposition)

/-- A checked Boolean body and its standard equality-encoded universal.
This is the reference-level shape consumed by HOL's `GEN` rule. -/
def Arena.Generalization (resolve : Resolver) (arena : Arena)
    (source binder target : Ref) : Prop :=
  ∃ boolType domain name body,
    Resolves (coreResolver resolve) arena.holCore source (.term boolType body) ∧
    Resolves (coreResolver resolve) arena.holCore binder (.term domain (.tmFv name domain)) ∧
    Resolves (coreResolver resolve) arena.holCore target
      (.term boolType (Expr.forallTm name domain body))

/-- A checked Boolean proposition and its closure over one named free type.
This is the reference-level shape consumed by premise-free `TY_GEN`. -/
def Arena.TypeGeneralization (resolve : Resolver) (arena : Arena)
    (source target : Ref) : Prop :=
  ∃ boolType name predicate,
    Resolves (coreResolver resolve) arena.holCore source (.term boolType predicate) ∧
    Resolves (coreResolver resolve) arena.holCore target
      (.term boolType (.tyForall name predicate))

/-- A proved predicate application and the application at its Hilbert-selected
witness. This is the reference-level shape consumed by the choice rule. -/
def Arena.ChoiceApplication (resolve : Resolver) (arena : Arena)
    (source target : Ref) : Prop :=
  ∃ boolType domain predicate argument,
    Resolves (coreResolver resolve) arena.holCore source
      (.term boolType (.app predicate argument)) ∧
    Resolves (coreResolver resolve) arena.holCore target
      (.term boolType (.app predicate (.eps domain predicate)))

/-- HOL theorem atoms have a partial interpretation.  A checked Boolean row
may later supply its actual HOL truth value; unknown or ill-sorted references
remain indeterminate.  Classical soundness is required for every completion,
which is precisely the discipline used by `CheckedArena`. -/
structure Arena.HolInterpretationSound (resolve : Resolver) (arena : Arena)
    (interpretation : PartialValuation Ref) : Prop where
  /-- Every checked Boolean row has a proposition denotation.  Ill-sorted and
  absent rows may remain indeterminate. -/
  total : ∀ reference, ContextClaim (coreResolver resolve) arena.holCore reference →
    ∃ proposition, interpretation reference = some proposition
  /-- Semantic equality classes denote logically equivalent propositions. -/
  equality : ∀ {left right leftProp rightProp},
    ContextClaim (coreResolver resolve) arena.holCore left →
    ContextClaim (coreResolver resolve) arena.holCore right →
    Columns.Class arena.columns.dense .semantic left right →
    interpretation left = some leftProp → interpretation right = some rightProp →
    (leftProp ↔ rightProp)
  /-- Every checked term is equal to itself (`REFL`). -/
  reflexivity : ∀ {term target targetProp},
    arena.ReflexiveEquality resolve term target →
    interpretation target = some targetProp → targetProp
  /-- Equality remains true after applying equal functions to one checked
  argument. This is the reference-level form of HOL's standard `AP_THM` rule. -/
  applyFunction : ∀ {source argument target sourceProp targetProp},
    arena.FunctionApplicationEquality resolve source argument target →
    interpretation source = some sourceProp →
    interpretation target = some targetProp →
    (sourceProp → targetProp)
  /-- Equality remains true after abstracting both operands over a fresh
  checked variable (`ABS_THM`). -/
  abstract : ∀ {source binder target sourceProp targetProp},
    arena.AbstractionEquality resolve source binder target →
    interpretation source = some sourceProp →
    interpretation target = some targetProp →
    (sourceProp → targetProp)
  /-- Equality is preserved by applying one checked function (`AP_TERM`). -/
  applyArgument : ∀ {source function target sourceProp targetProp},
    arena.FunctionArgumentEquality resolve source function target →
    interpretation source = some sourceProp →
    interpretation target = some targetProp →
    (sourceProp → targetProp)
  /-- Boolean equality transports proof of its left side to its right side
  (`EQ_MP`). -/
  equalityMp : ∀ {equality premise target equalityProp premiseProp targetProp},
    arena.EqualityModusPonens resolve equality premise target →
    interpretation equality = some equalityProp →
    interpretation premise = some premiseProp →
    interpretation target = some targetProp →
    (equalityProp → premiseProp → targetProp)
  /-- Equality with truth may be eliminated (`EQT_ELIM`). -/
  equalityToTruth : ∀ {source target sourceProp targetProp},
    arena.EqualityToTruth resolve source target →
    interpretation source = some sourceProp →
    interpretation target = some targetProp →
    (sourceProp → targetProp)
  /-- A theorem may be generalized over one checked free term variable
  (`GEN`) when that variable is fresh for its premise matrix. -/
  generalize : ∀ {source binder target sourceProp targetProp},
    arena.Generalization resolve source binder target →
    interpretation source = some sourceProp →
    interpretation target = some targetProp →
    (sourceProp → targetProp)
  /-- A premise-free theorem may be generalized over one named free type
  (`TY_GEN`). Uniformity comes from its open type environment. -/
  typeGeneralize : ∀ {source target sourceProp targetProp},
    arena.TypeGeneralization resolve source target →
    interpretation source = some sourceProp →
    interpretation target = some targetProp →
    (sourceProp → targetProp)
  /-- A proved witness may be replaced by the Hilbert-selected witness. -/
  choice : ∀ {source target sourceProp targetProp},
    arena.ChoiceApplication resolve source target →
    interpretation source = some sourceProp →
    interpretation target = some targetProp →
    (sourceProp → targetProp)

/-- Every completion assigns the same truth value to semantically equal
checked Boolean rows. -/
theorem Arena.HolInterpretationSound.completion_eq {resolve : Resolver}
    {arena : Arena} {interpretation : PartialValuation Ref}
    (sound : arena.HolInterpretationSound resolve interpretation)
    {left right : Ref}
    (leftBool : ContextClaim (coreResolver resolve) arena.holCore left)
    (rightBool : ContextClaim (coreResolver resolve) arena.holCore right)
    (related : Columns.Class arena.columns.dense .semantic left right)
    {valuation : Valuation Ref} (completion : valuation.Completes interpretation) :
    valuation left ↔ valuation right := by
  obtain ⟨leftProp, leftFound⟩ := sound.total left leftBool
  obtain ⟨rightProp, rightFound⟩ := sound.total right rightBool
  exact (completion left leftProp leftFound).trans <|
    (sound.equality leftBool rightBool related leftFound rightFound).trans <|
      (completion right rightProp rightFound).symm

def Arena.HolThmSound (trusted : Arena → Prop) (resolve : Resolver) (arena : Arena)
    (interpretation : PartialValuation Ref) : Prop :=
  ∀ ambientValuation,
    arena.ambientTheory.Admits (arena.ImportOk trusted resolve) (arena.ImportSort resolve)
      ambientValuation →
    ∀ fact ∈ arena.hol.thm, ∀ valuation,
      valuation.Completes interpretation → fact.semantic.Holds valuation

/-- Ordinary HOL soundness is conditional on the explicit ambient context.
This is the crucial replacement for the old premise list: a foreign proxy is
sound in every ambient valuation that satisfies the unit atom emitted with
that proxy. -/
def Arena.HolKernelSound (trusted : Arena → Prop) (resolve : Resolver) (arena : Arena) : Prop :=
  ∀ valuation,
    arena.ambientTheory.Admits (arena.ImportOk trusted resolve) (arena.ImportSort resolve)
      valuation →
    arena.holCore.KernelValid (coreResolver resolve)

/-- Syntactic cache facts are interpreted in the same reconstructed HOL arena
as ordinary kernel facts.  In particular, the fused conversion column also
supplies their classifiers, so cache soundness is conditional on exactly the
same admitted ambient valuation as `HolKernelSound`. -/
def Arena.SynFactsSound (trusted : Arena → Prop) (resolve : Resolver) (arena : Arena) : Prop :=
  ∀ valuation,
    arena.ambientTheory.Admits (arena.ImportOk trusted resolve) (arena.ImportSort resolve)
      valuation →
    SynArena.Sound (coreResolver resolve) arena.holCore

/-- Complete soundness invariant of the nested checked kernel.  The first
field reuses all existing HOL constructor/equality/context soundness proofs on
the exact row view reconstructed from columns. -/
structure Arena.KernelValid (trusted : Arena → Prop) (resolve : Resolver) (arena : Arena)
    (interpretation : PartialValuation Ref) : Prop where
  columns : arena.ColumnsChecked
  synFacts : arena.SynFactsSound trusted resolve
  synFree : SynArena.FreeListSafe arena.holCore
  hol : arena.HolKernelSound trusted resolve
  equalityRefines : arena.EqualityRefines
  ambientAxioms : arena.ambientTheory.AllowsAxioms AllowedAmbientAxiom
  ambientTheorems : arena.AmbThmSound trusted resolve
  syllogisms : arena.SylSound
  holInterpretation : arena.HolInterpretationSound resolve interpretation
  holTheorems : arena.HolThmSound trusted resolve interpretation

/-- Under any admitted ambient valuation, the nested kernel specializes to
the original proved HOL kernel.  Thus every constructor, substitution,
conversion, equality, context, Model, and Subtype soundness theorem already
proved for `OneBased.Kernel` applies without being duplicated. -/
def Arena.KernelValid.coreKernel {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    (valuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) valuation) : OneBased.Kernel (coreResolver resolve) :=
  ⟨arena.holCore, valid.hol valuation admitted⟩

/-- Under an admitted ambient valuation, the nested state specializes to the
complete checked HOL kernel, including every cached substitution and
conversion fact. -/
def Arena.KernelValid.fullKernel {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    (valuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) valuation) : OneBased.FullKernel (coreResolver resolve) :=
  ⟨arena.holCore, valid.hol valuation admitted,
    valid.synFacts valuation admitted, valid.synFree⟩

/-- Any semantic-column class is exactly an equality class consumed by the
existing kernel proof. -/
theorem Arena.semanticClass_sound {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {left right : Ref}
    (related : Columns.Class arena.columns.dense .semantic left right)
    (leftResident : arena.columns.dense.expr? left ≠ none)
    (rightResident : arena.columns.dense.expr? right ≠ none)
    (valuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) valuation) :
    ReferenceEqual (coreResolver resolve) arena.holCore left right := by
  have connected : EqClass arena.holCore left right := by
    apply Columns.Class.sound (R := EqClass arena.holCore) (connected := related)
    · intro edgeLeft edgeRight edge
      apply Relation.EqvGen.rel
      unfold EqEdge
      have resident := (valid.columns.eqTargets _ _ edge).1
      simpa [OneBased.Arena.eq?, Arena.holCore_dense,
        Columns.Edge, Columns.Dense.column] using edge
    · exact fun reference => Relation.EqvGen.refl reference
    · exact fun connected => Relation.EqvGen.symm _ _ connected
    · exact fun leftMiddle middleRight =>
        Relation.EqvGen.trans _ _ _ leftMiddle middleRight
  have leftRow : arena.holCore.row? left ≠ none := by
    rw [arena.holCore_row?]
    unfold Columns.Dense.row? OneBased.Dense.row?
    cases found : arena.columns.dense.expr? left with
    | none => contradiction
    | some expr =>
        have found' : Nucleus.Hol.Ethane.OneBased.Dense.expr?
            arena.columns.dense left = some expr := found
        simp [found']
  have rightRow : arena.holCore.row? right ≠ none := by
    rw [arena.holCore_row?]
    unfold Columns.Dense.row? OneBased.Dense.row?
    cases found : arena.columns.dense.expr? right with
    | none => contradiction
    | some expr =>
        have found' : Nucleus.Hol.Ethane.OneBased.Dense.expr?
            arena.columns.dense right = some expr := found
        simp [found']
  have connectedCore : EqClass arena.holCore.withoutSyn left right := by
    have edges : EqEdge arena.holCore.withoutSyn = EqEdge arena.holCore := by
      funext edgeLeft edgeRight
      simp [EqEdge]
    unfold EqClass
    rw [edges]
    exact connected
  have core := valid.hol valuation admitted
  have proved := core.classes
    (left := left) (right := right)
    (by simpa using leftRow)
    (by simpa using rightRow)
    connectedCore
  simpa [ReferenceEqual] using proved

/-- A HOL theorem remains sound when every occurrence of one checked Boolean
atom is replaced by a semantically equal checked Boolean atom.  This is the
semantic contract of the Rust theorem-transport rule; physical matrix layout
and theorem-slot mutation are orthogonal refinements. -/
theorem Arena.holTheorem_replaceSemantic {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {fact : WireSequent} (member : fact ∈ arena.hol.thm)
    {source target : Ref}
    (sourceBool : ContextClaim (coreResolver resolve) arena.holCore source)
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (related : Columns.Class arena.columns.dense .semantic source target) :
    ∀ ambientValuation,
      arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
        (arena.ImportSort resolve) ambientValuation →
      ∀ valuation : Valuation Ref, valuation.Completes interpretation →
        (fact.semantic.replaceAtom source target).Holds valuation := by
  intro ambientValuation admitted valuation completion
  apply fact.semantic.replaceAtom_holds source target
  · exact valid.holTheorems ambientValuation admitted fact member valuation completion
  · exact valid.holInterpretation.completion_eq sourceBool targetBool related completion

/-- Semantic transport may rewrite only the conclusion matrix, leaving a
physically shared premise atom untouched. -/
theorem Arena.holTheorem_replaceRightSemantic {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {fact : WireSequent} (member : fact ∈ arena.hol.thm)
    {source target : Ref}
    (sourceBool : ContextClaim (coreResolver resolve) arena.holCore source)
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (related : Columns.Class arena.columns.dense .semantic source target) :
    ∀ ambientValuation,
      arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
        (arena.ImportSort resolve) ambientValuation →
      ∀ valuation : Valuation Ref, valuation.Completes interpretation →
        (fact.semantic.replaceRightAtom source target).Holds valuation := by
  intro ambientValuation admitted valuation completion
  apply fact.semantic.replaceRightAtom_holds source target
  · exact valid.holTheorems ambientValuation admitted fact member valuation completion
  · exact valid.holInterpretation.completion_eq sourceBool targetBool related completion

/-- Equality reflexivity introduces an exact premise-free theorem. -/
theorem Arena.holTheorem_reflexivity {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {term target : Ref}
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (shape : arena.ReflexiveEquality resolve term target) :
    ∀ valuation : Valuation Ref, valuation.Completes interpretation →
      (Sequent.assert target).Holds valuation := by
  intro valuation completion
  obtain ⟨targetProp, targetFound⟩ := valid.holInterpretation.total target targetBool
  rw [Sequent.assert_holds]
  exact (completion target targetProp targetFound).mpr
    (valid.holInterpretation.reflexivity shape targetFound)

/-- A theorem of function equality may be specialized at one
checked argument. This is the semantic contract of Rust's `AP_THM` operation;
syntax construction and theorem-slot allocation are separate refinements. -/
theorem Arena.holTheorem_applyFunction {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {fact : WireSequent} (member : fact ∈ arena.hol.thm)
    {source argument target : Ref}
    (exactRight : fact.semantic.right = (Sequent.assert source).right)
    (sourceBool : ContextClaim (coreResolver resolve) arena.holCore source)
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (application : arena.FunctionApplicationEquality resolve source argument target) :
    ∀ ambientValuation,
      arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
        (arena.ImportSort resolve) ambientValuation →
      ∀ valuation : Valuation Ref, valuation.Completes interpretation →
        (⟨fact.semantic.left, (Sequent.assert target).right⟩ : Sequent Ref).Holds valuation := by
  intro ambientValuation admitted valuation completion
  obtain ⟨sourceProp, sourceFound⟩ := valid.holInterpretation.total source sourceBool
  obtain ⟨targetProp, targetFound⟩ := valid.holInterpretation.total target targetBool
  intro leftHolds
  change (Sequent.assert target).right.Holds valuation
  rw [Sequent.assertRight_holds]
  apply (completion target targetProp targetFound).mpr
  apply valid.holInterpretation.applyFunction application sourceFound targetFound
  apply (completion source sourceProp sourceFound).mp
  have sourceHolds := valid.holTheorems ambientValuation admitted fact member valuation completion
  have rightHolds := sourceHolds leftHolds
  rw [exactRight] at rightHolds
  exact (Sequent.assertRight_holds valuation source).mp rightHolds

/-- A theorem of equality may be abstracted over a checked variable fresh for
its premise matrix. This is the semantic contract of Rust's `ABS_THM`; syntax
construction, the free-variable scan, and theorem-slot allocation are
separate refinements. -/
theorem Arena.holTheorem_abstract {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {fact : WireSequent} (member : fact ∈ arena.hol.thm)
    {source binder target : Ref}
    (exactRight : fact.semantic.right = (Sequent.assert source).right)
    (sourceBool : ContextClaim (coreResolver resolve) arena.holCore source)
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (abstraction : arena.AbstractionEquality resolve source binder target) :
    ∀ ambientValuation,
      arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
        (arena.ImportSort resolve) ambientValuation →
      ∀ valuation : Valuation Ref, valuation.Completes interpretation →
        (⟨fact.semantic.left, (Sequent.assert target).right⟩ : Sequent Ref).Holds valuation := by
  intro ambientValuation admitted valuation completion leftHolds
  obtain ⟨sourceProp, sourceFound⟩ := valid.holInterpretation.total source sourceBool
  obtain ⟨targetProp, targetFound⟩ := valid.holInterpretation.total target targetBool
  change (Sequent.assert target).right.Holds valuation
  rw [Sequent.assertRight_holds]
  apply (completion target targetProp targetFound).mpr
  apply valid.holInterpretation.abstract abstraction sourceFound targetFound
  apply (completion source sourceProp sourceFound).mp
  have sourceHolds := valid.holTheorems ambientValuation admitted fact member valuation completion
    leftHolds
  rw [exactRight] at sourceHolds
  exact (Sequent.assertRight_holds valuation source).mp sourceHolds

/-- A proved equality remains true after applying one checked function. -/
theorem Arena.holTheorem_applyArgument {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {fact : WireSequent} (member : fact ∈ arena.hol.thm)
    {source function target : Ref}
    (exactRight : fact.semantic.right = (Sequent.assert source).right)
    (sourceBool : ContextClaim (coreResolver resolve) arena.holCore source)
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (application : arena.FunctionArgumentEquality resolve source function target) :
    ∀ ambientValuation,
      arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
        (arena.ImportSort resolve) ambientValuation →
      ∀ valuation : Valuation Ref, valuation.Completes interpretation →
        (⟨fact.semantic.left, (Sequent.assert target).right⟩ : Sequent Ref).Holds valuation := by
  intro ambientValuation admitted valuation completion leftHolds
  obtain ⟨sourceProp, sourceFound⟩ := valid.holInterpretation.total source sourceBool
  obtain ⟨targetProp, targetFound⟩ := valid.holInterpretation.total target targetBool
  change (Sequent.assert target).right.Holds valuation
  rw [Sequent.assertRight_holds]
  apply (completion target targetProp targetFound).mpr
  apply valid.holInterpretation.applyArgument application sourceFound targetFound
  apply (completion source sourceProp sourceFound).mp
  have sourceHolds := valid.holTheorems ambientValuation admitted fact member valuation completion
  have rightHolds := sourceHolds leftHolds
  rw [exactRight] at rightHolds
  exact (Sequent.assertRight_holds valuation source).mp rightHolds

/-- `EQ_MP` combines Boolean equality and its proved left proposition. -/
theorem Arena.holTheorem_equalityMp {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {equalityFact premiseFact : WireSequent}
    (equalityMember : equalityFact ∈ arena.hol.thm)
    (premiseMember : premiseFact ∈ arena.hol.thm)
    {equality premise target : Ref}
    (equalityRight : equalityFact.semantic.right = (Sequent.assert equality).right)
    (premiseRight : premiseFact.semantic.right = (Sequent.assert premise).right)
    (equalityBool : ContextClaim (coreResolver resolve) arena.holCore equality)
    (premiseBool : ContextClaim (coreResolver resolve) arena.holCore premise)
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (shape : arena.EqualityModusPonens resolve equality premise target) :
    ∀ ambientValuation,
      arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
        (arena.ImportSort resolve) ambientValuation →
      ∀ valuation : Valuation Ref, valuation.Completes interpretation →
        (⟨equalityFact.semantic.left.append premiseFact.semantic.left,
          (Sequent.assert target).right⟩ : Sequent Ref).Holds valuation := by
  intro ambientValuation admitted valuation completion leftHolds
  rw [Cnf.append_holds] at leftHolds
  obtain ⟨equalityProp, equalityFound⟩ :=
    valid.holInterpretation.total equality equalityBool
  obtain ⟨premiseProp, premiseFound⟩ := valid.holInterpretation.total premise premiseBool
  obtain ⟨targetProp, targetFound⟩ := valid.holInterpretation.total target targetBool
  change (Sequent.assert target).right.Holds valuation
  rw [Sequent.assertRight_holds]
  apply (completion target targetProp targetFound).mpr
  apply valid.holInterpretation.equalityMp shape equalityFound premiseFound targetFound
  · apply (completion equality equalityProp equalityFound).mp
    have holds := valid.holTheorems ambientValuation admitted equalityFact equalityMember
      valuation completion leftHolds.1
    rw [equalityRight] at holds
    exact (Sequent.assertRight_holds valuation equality).mp holds
  · apply (completion premise premiseProp premiseFound).mp
    have holds := valid.holTheorems ambientValuation admitted premiseFact premiseMember
      valuation completion leftHolds.2
    rw [premiseRight] at holds
    exact (Sequent.assertRight_holds valuation premise).mp holds

/-- An exact theorem `⊢ p = true` yields the exact theorem `⊢ p`. -/
theorem Arena.holTheorem_equalityToTruth {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {fact : WireSequent} (member : fact ∈ arena.hol.thm)
    {source target : Ref}
    (exactRight : fact.semantic.right = (Sequent.assert source).right)
    (sourceBool : ContextClaim (coreResolver resolve) arena.holCore source)
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (equality : arena.EqualityToTruth resolve source target) :
    ∀ ambientValuation,
      arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
        (arena.ImportSort resolve) ambientValuation →
      ∀ valuation : Valuation Ref, valuation.Completes interpretation →
        (⟨fact.semantic.left, (Sequent.assert target).right⟩ : Sequent Ref).Holds valuation := by
  intro ambientValuation admitted valuation completion
  obtain ⟨sourceProp, sourceFound⟩ := valid.holInterpretation.total source sourceBool
  obtain ⟨targetProp, targetFound⟩ := valid.holInterpretation.total target targetBool
  intro leftHolds
  change (Sequent.assert target).right.Holds valuation
  rw [Sequent.assertRight_holds]
  apply (completion target targetProp targetFound).mpr
  apply valid.holInterpretation.equalityToTruth equality sourceFound targetFound
  apply (completion source sourceProp sourceFound).mp
  have sourceHolds := valid.holTheorems ambientValuation admitted fact member valuation completion
  have rightHolds := sourceHolds leftHolds
  rw [exactRight] at rightHolds
  exact (Sequent.assertRight_holds valuation source).mp rightHolds

/-- A theorem may be universally generalized while preserving a premise
matrix for which the binder is fresh. The reference implementation checks
that syntactic side condition before invoking this semantic contract. -/
theorem Arena.holTheorem_generalize {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {fact : WireSequent} (member : fact ∈ arena.hol.thm)
    {source binder target : Ref}
    (exactRight : fact.semantic.right = (Sequent.assert source).right)
    (sourceBool : ContextClaim (coreResolver resolve) arena.holCore source)
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (generalization : arena.Generalization resolve source binder target) :
    ∀ ambientValuation,
      arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
        (arena.ImportSort resolve) ambientValuation →
      ∀ valuation : Valuation Ref, valuation.Completes interpretation →
        (⟨fact.semantic.left, (Sequent.assert target).right⟩ : Sequent Ref).Holds valuation := by
  intro ambientValuation admitted valuation completion
  obtain ⟨sourceProp, sourceFound⟩ := valid.holInterpretation.total source sourceBool
  obtain ⟨targetProp, targetFound⟩ := valid.holInterpretation.total target targetBool
  intro leftHolds
  change (Sequent.assert target).right.Holds valuation
  rw [Sequent.assertRight_holds]
  apply (completion target targetProp targetFound).mpr
  apply valid.holInterpretation.generalize generalization sourceFound targetFound
  apply (completion source sourceProp sourceFound).mp
  have sourceHolds := valid.holTheorems ambientValuation admitted fact member valuation completion
  have rightHolds := sourceHolds leftHolds
  rw [exactRight] at rightHolds
  exact (Sequent.assertRight_holds valuation source).mp rightHolds

/-- A premise-free theorem may be universally generalized over one named free
type. `tyForallIntro_sound` supplies the underlying HolE semantic law; this is
its one-based theorem-slot contract. -/
theorem Arena.holTheorem_typeGeneralize {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {fact : WireSequent} (member : fact ∈ arena.hol.thm)
    {source target : Ref}
    (exact : fact.semantic = Sequent.assert source)
    (sourceBool : ContextClaim (coreResolver resolve) arena.holCore source)
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (generalization : arena.TypeGeneralization resolve source target) :
    ∀ ambientValuation,
      arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
        (arena.ImportSort resolve) ambientValuation →
      ∀ valuation : Valuation Ref, valuation.Completes interpretation →
        (Sequent.assert target).Holds valuation := by
  intro ambientValuation admitted valuation completion leftHolds
  obtain ⟨sourceProp, sourceFound⟩ := valid.holInterpretation.total source sourceBool
  obtain ⟨targetProp, targetFound⟩ := valid.holInterpretation.total target targetBool
  rw [Sequent.assertRight_holds]
  apply (completion target targetProp targetFound).mpr
  apply valid.holInterpretation.typeGeneralize generalization sourceFound targetFound
  apply (completion source sourceProp sourceFound).mp
  have sourceHolds := valid.holTheorems ambientValuation admitted fact member valuation completion
  rw [exact] at sourceHolds
  exact (Sequent.assertRight_holds valuation source).mp (sourceHolds leftHolds)

/-- A theorem of one predicate application yields the application at the
Hilbert-selected witness, preserving its premise matrix. -/
theorem Arena.holTheorem_choice {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena} {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {fact : WireSequent} (member : fact ∈ arena.hol.thm)
    {source target : Ref}
    (exactRight : fact.semantic.right = (Sequent.assert source).right)
    (sourceBool : ContextClaim (coreResolver resolve) arena.holCore source)
    (targetBool : ContextClaim (coreResolver resolve) arena.holCore target)
    (choice : arena.ChoiceApplication resolve source target) :
    ∀ ambientValuation,
      arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
        (arena.ImportSort resolve) ambientValuation →
      ∀ valuation : Valuation Ref, valuation.Completes interpretation →
        (⟨fact.semantic.left, (Sequent.assert target).right⟩ : Sequent Ref).Holds valuation := by
  intro ambientValuation admitted valuation completion leftHolds
  obtain ⟨sourceProp, sourceFound⟩ := valid.holInterpretation.total source sourceBool
  obtain ⟨targetProp, targetFound⟩ := valid.holInterpretation.total target targetBool
  change (Sequent.assert target).right.Holds valuation
  rw [Sequent.assertRight_holds]
  apply (completion target targetProp targetFound).mpr
  apply valid.holInterpretation.choice choice sourceFound targetFound
  apply (completion source sourceProp sourceFound).mp
  have sourceHolds := valid.holTheorems ambientValuation admitted fact member valuation completion
  have rightHolds := sourceHolds leftHolds
  rw [exactRight] at rightHolds
  exact (Sequent.assertRight_holds valuation source).mp rightHolds

/-- Conversion-column lookup is sound because checked insertion refines it
into semantic equality. -/
theorem Arena.convClass_sound {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {left right : Ref}
    (related : Columns.Class arena.columns.dense .conv left right)
    (leftResident : arena.columns.dense.expr? left ≠ none)
    (rightResident : arena.columns.dense.expr? right ≠ none)
    (valuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) valuation) :
    ReferenceEqual (coreResolver resolve) arena.holCore left right :=
  arena.semanticClass_sound valid (valid.equalityRefines.conv_semantic related)
    leftResident rightResident valuation admitted

/-- Syntactic-equality-column lookup is sound through the complete
`syn.eq ⊆ syn.conv ⊆ eq` refinement chain. -/
theorem Arena.synClass_sound {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (valid : arena.KernelValid trusted resolve interpretation)
    {left right : Ref}
    (related : Columns.Class arena.columns.dense .syn left right)
    (leftResident : arena.columns.dense.expr? left ≠ none)
    (rightResident : arena.columns.dense.expr? right ≠ none)
    (valuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) valuation) :
    ReferenceEqual (coreResolver resolve) arena.holCore left right :=
  arena.convClass_sound valid (valid.equalityRefines.syn_conv related)
    leftResident rightResident valuation admitted

/-- A checked proxy emission appends one exact atom and its positive unit
clause.  This is the only way PR1 grows `amb.ctx`. -/
def Arena.pushAmbientContext (arena : Arena) (predicate : Pred) (next : Ref) : Arena :=
  match arena with
  | .mk imports amb pred hol =>
      .mk imports { amb with
        pred := amb.pred ++ [predicate]
        ctx := ⟨amb.ctx.rows ++ [some (Clause.mk [(next, false)])]⟩ } pred hol

structure Arena.CanPushAmbient (arena : Arena) (next : Ref) : Prop where
  nextValue : next.value.toNat = arena.amb.pred.length + 1

theorem Arena.pushAmbientContext_pred_lookup {arena : Arena} {next : Ref}
    (fresh : arena.CanPushAmbient next) (predicate : Pred) :
    (arena.pushAmbientContext predicate next).ambientTheory.defs next = some predicate := by
  cases arena with
  | mk imports ambient predicates hol =>
      have position : next.value.toNat - 1 = ambient.pred.length := by
        have nextValue : next.value.toNat = ambient.pred.length + 1 := by
          simpa using fresh.nextValue
        rw [nextValue]
        omega
      simp [Arena.ambientTheory, Arena.pushAmbientContext, position]

theorem Arena.pushAmbientContext_exact_unit (arena : Arena) (next : Ref)
    (predicate : Pred) :
    (arena.pushAmbientContext predicate next).amb.ctx =
      ⟨arena.amb.ctx.rows ++ [some (Clause.mk [(next, false)])]⟩ := by
  cases arena
  rfl

/-- Every admitted valuation of the extended theory makes the freshly emitted
atom true and therefore establishes its exact imported-object obligation. -/
theorem Arena.pushAmbientContext_holds {trusted : Arena → Prop} {resolve : Resolver}
    {arena : Arena}
    {next : Ref} (fresh : arena.CanPushAmbient next) (predicate : Pred)
    (valuation : Valuation Ref)
    (admitted : (arena.pushAmbientContext predicate next).ambientTheory.Admits
      ((arena.pushAmbientContext predicate next).ImportOk trusted resolve)
      ((arena.pushAmbientContext predicate next).ImportSort resolve) valuation) :
    predicate.Holds
      ((arena.pushAmbientContext predicate next).ImportOk trusted resolve)
      ((arena.pushAmbientContext predicate next).ImportSort resolve) := by
  have definition := admitted.1 next predicate
    (arena.pushAmbientContext_pred_lookup fresh predicate)
  apply definition.mp
  have context := admitted.2
  have finalClause : Clause.mk [(next, false)] ∈
      (arena.pushAmbientContext predicate next).amb.ctx.semantic.clauses := by
    cases arena
    simp [Arena.pushAmbientContext, WireCnf.semantic]
  obtain ⟨literal, member, truth⟩ := context _ finalClause
  simp at member
  subst literal
  simpa [Lit.Holds] using truth

@[simp] theorem Arena.pushAmbientContext_import (arena : Arena) (next : Ref)
    (predicate : Pred) :
    (arena.pushAmbientContext predicate next).imports = arena.imports := by
  cases arena
  rfl

/-- Exact `kind_ref` ambient emission. -/
def Arena.pushKindRefPremise (arena : Arena) (source : ImportId) (next : Ref) : Arena :=
  arena.pushAmbientContext (.arenaOk source) next

/-- Exact `ty_ref`/`tm_ref` ambient emission. -/
def Arena.pushSortPremise (arena : Arena) (source : ImportId)
    (foreign sort next : Ref) : Arena :=
  arena.pushAmbientContext (.holSort source foreign sort) next

theorem Arena.kindRefPremise_exact {arena : Arena} {source : ImportId} {next : Ref}
    (fresh : arena.CanPushAmbient next) :
    (arena.pushKindRefPremise source next).ambientTheory.defs next =
      some (.arenaOk source) :=
  arena.pushAmbientContext_pred_lookup fresh _

theorem Arena.sortPremise_exact {arena : Arena} {source : ImportId}
    {foreign sort next : Ref} (fresh : arena.CanPushAmbient next) :
    (arena.pushSortPremise source foreign sort next).ambientTheory.defs next =
      some (.holSort source foreign sort) :=
  arena.pushAmbientContext_pred_lookup fresh _

theorem Arena.kindRef_admitted_importOk {trusted : Arena → Prop} {resolve : Resolver}
    {arena : Arena}
    {source : ImportId} {next : Ref} (fresh : arena.CanPushAmbient next)
    (valuation : Valuation Ref)
    (admitted : (arena.pushKindRefPremise source next).ambientTheory.Admits
      ((arena.pushKindRefPremise source next).ImportOk trusted resolve)
      ((arena.pushKindRefPremise source next).ImportSort resolve) valuation) :
    (arena.pushKindRefPremise source next).ImportOk trusted resolve source := by
  exact arena.pushAmbientContext_holds fresh (.arenaOk source) valuation admitted

theorem Arena.sort_admitted_importSort {trusted : Arena → Prop} {resolve : Resolver}
    {arena : Arena}
    {source : ImportId} {foreign sort next : Ref} (fresh : arena.CanPushAmbient next)
    (valuation : Valuation Ref)
    (admitted : (arena.pushSortPremise source foreign sort next).ambientTheory.Admits
      ((arena.pushSortPremise source foreign sort next).ImportOk trusted resolve)
      ((arena.pushSortPremise source foreign sort next).ImportSort resolve) valuation) :
    (arena.pushSortPremise source foreign sort next).ImportSort resolve source foreign sort := by
  exact arena.pushAmbientContext_holds fresh (.holSort source foreign sort)
    valuation admitted

/-- Evidence available at every successful checked proxy call: Rust resolves
the foreign row before appending the atom, so `src` necessarily names the
exact resident import recorded here. -/
def Arena.ProxySourceResident (arena : Arena) (source : ImportId) : Prop :=
  ∃ entry, arena.import? source = some entry

theorem Arena.kindRefEmission_resident {arena : Arena} {source : ImportId}
    {next : Ref} (resident : arena.ProxySourceResident source) :
    (arena.pushKindRefPremise source next).ProxySourceResident source := by
  rcases resident with ⟨entry, lookup⟩
  refine ⟨entry, ?_⟩
  cases arena
  simpa [Arena.pushKindRefPremise, Arena.pushAmbientContext, Arena.import?] using lookup

theorem Arena.sortEmission_resident {arena : Arena} {source : ImportId}
    {foreign sort next : Ref} (resident : arena.ProxySourceResident source) :
    (arena.pushSortPremise source foreign sort next).ProxySourceResident source := by
  rcases resident with ⟨entry, lookup⟩
  refine ⟨entry, ?_⟩
  cases arena
  simpa [Arena.pushSortPremise, Arena.pushAmbientContext, Arena.import?] using lookup

end Nucleus.Hol.Ethane.OneBased.Layout
