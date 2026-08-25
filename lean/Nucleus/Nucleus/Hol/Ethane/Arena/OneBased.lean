import Nucleus.Hol.Ethane.Arena
import Nucleus.Hol.Ethane.Builtin
import Nucleus.O256.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Basic

/-!
# One-based HOL proof core

This is the semantic storage model used by the established HOL soundness
proofs.  As in Rust, physical rows contain syntax only and semantic equality
and sort/classifier information live in separate dense columns.  The derived
Proof-facing row lookup remains syntax-only; column facts are queried directly.
`OneBased.Layout` adds the surrounding nested wire structure.
Local definition references are positive `i32` values strictly below
`i32::MAX`, so signed-literal negation is total. Import and syntactic-fact
indices are positive `i32` values and may use `i32::MAX`.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus

/-- The exclusive upper bound shared with signed `Lit` on the Rust wire. -/
def Ref.maxExclusive : Nat := 2_147_483_647

/-- A local reference.  Value `n` addresses definition `n - 1` and always
admits a lossless positive or negative signed proposition encoding. -/
def Ref := { value : UInt64 // value ≠ 0 ∧ value.toNat < Ref.maxExclusive }

deriving instance DecidableEq for Ref
deriving instance Repr for Ref

instance : LinearOrder Ref := LinearOrder.lift' (fun value => value.1.toNat) (by
  intro left right equal
  apply Subtype.ext
  exact UInt64.toNat_inj.mp equal)

namespace Ref

def ofUInt64? (value : UInt64) : Option Ref :=
  if valid : value ≠ 0 ∧ value.toNat < maxExclusive then some ⟨value, valid⟩ else none

def value (reference : Ref) : UInt64 := reference.1

@[simp] theorem ofUInt64?_value (reference : Ref) :
    ofUInt64? reference.value = some reference := by
  rcases reference with ⟨value, valid⟩
  simp [ofUInt64?, Ref.value, valid]

@[simp] theorem ofUInt64?_zero : ofUInt64? 0 = none := by
  simp [ofUInt64?]

@[simp] theorem ofUInt64?_maxExclusive :
    ofUInt64? (UInt64.ofNat maxExclusive) = none := by
  decide

end Ref

/-- A one-based positive-`i32` index into the import table. -/
def ImportId.maxInclusive : Nat := 2_147_483_647
def ImportId := { value : UInt64 // value ≠ 0 ∧ value.toNat ≤ ImportId.maxInclusive }

deriving instance DecidableEq for ImportId
deriving instance Repr for ImportId

instance : LinearOrder ImportId := LinearOrder.lift' (fun value => value.1.toNat) (by
  intro left right equal
  apply Subtype.ext
  exact UInt64.toNat_inj.mp equal)

namespace ImportId

def ofUInt64? (value : UInt64) : Option ImportId :=
  if valid : value ≠ 0 ∧ value.toNat ≤ maxInclusive then some ⟨value, valid⟩ else none

def value (source : ImportId) : UInt64 := source.1

@[simp] theorem ofUInt64?_value (source : ImportId) :
    ofUInt64? source.value = some source := by
  rcases source with ⟨value, valid⟩
  simp [ofUInt64?, ImportId.value, valid]

@[simp] theorem ofUInt64?_zero : ofUInt64? 0 = none := by
  simp [ofUInt64?]

@[simp] theorem ofUInt64?_aboveMax :
    ofUInt64? (UInt64.ofNat (maxInclusive + 1)) = none := by
  decide

end ImportId

/-! ## Unchecked syntactic-fact wire objects -/

/-- A one-based positive-`i32` syntactic-fact slot ID. -/
def SynFactId.maxInclusive : Nat := 2_147_483_647
def SynFactId := { value : UInt64 // value ≠ 0 ∧ value.toNat ≤ SynFactId.maxInclusive }

deriving instance DecidableEq for SynFactId
deriving instance Repr for SynFactId

instance : LinearOrder SynFactId := LinearOrder.lift' (fun value => value.1.toNat) (by
  intro left right equal
  apply Subtype.ext
  exact UInt64.toNat_inj.mp equal)

namespace SynFactId

def ofUInt64? (value : UInt64) : Option SynFactId :=
  if valid : value ≠ 0 ∧ value.toNat ≤ maxInclusive then some ⟨value, valid⟩ else none

def value (id : SynFactId) : UInt64 := id.1

/-- Convert the one-based wire ID to a zero-based list position. -/
def position (id : SynFactId) : Nat := id.value.toNat - 1

@[simp] theorem ofUInt64?_value (id : SynFactId) :
    ofUInt64? id.value = some id := by
  rcases id with ⟨value, valid⟩
  simp [ofUInt64?, SynFactId.value, valid]

@[simp] theorem ofUInt64?_zero : ofUInt64? 0 = none := by
  simp [ofUInt64?]

@[simp] theorem ofUInt64?_aboveMax :
    ofUInt64? (UInt64.ofNat (maxInclusive + 1)) = none := by
  decide

end SynFactId

/-- Literal syntax, alpha equivalence, and conversion, in refinement order. -/
inductive SynRel where
  | syn
  | alpha
  | conv
  deriving DecidableEq, Repr

namespace SynRel

def rank : SynRel → Nat
  | .syn => 0
  | .alpha => 1
  | .conv => 2

/-- A finer fact may be consumed by a rule requesting a coarser relation. -/
def Refines (source target : SynRel) : Prop := source.rank ≤ target.rank

instance (source target : SynRel) : Decidable (Refines source target) :=
  Nat.decLe source.rank target.rank

@[simp] theorem refines_refl (relation : SynRel) : relation.Refines relation := by
  simp [Refines]

theorem Refines.trans {left middle right : SynRel}
    (leftMiddle : Refines left middle)
    (middleRight : Refines middle right) : Refines left right :=
  Nat.le_trans leftMiddle middleRight

@[simp] theorem syn_refines_alpha : syn.Refines alpha := by simp [Refines, rank]
@[simp] theorem alpha_refines_conv : alpha.Refines conv := by simp [Refines, rank]
@[simp] theorem syn_refines_conv : syn.Refines conv := by simp [Refines, rank]

end SynRel

/-- The exact unchecked payload serialized by Rust. -/
structure SynFact where
  rel : SynRel
  var : Option Ref := none
  val : Option Ref := none
  input : Ref
  output : Ref
  deriving DecidableEq, Repr

/-- Payload of a removed slot. -/
structure SynFree where
  next : Option SynFactId := none
  deriving DecidableEq, Repr

/-- An occupied proof slot or a link in the arena-local free list. -/
inductive SynSlot where
  | fact (value : SynFact)
  | free (value : SynFree)
  deriving DecidableEq, Repr

/-- The syntactic category declared by a row tag. -/
inductive TagSort where
  | kind
  | ty
  | tm
  deriving DecidableEq, Repr

inductive KindTag where
  | star
  | arr
  | ref
  deriving DecidableEq, Repr

namespace KindTag

def name : KindTag → String
  | .star => "kind.star"
  | .arr => "kind.arr"
  | .ref => "kind.ref"

end KindTag

inductive TyTag where
  | bool
  | arr
  | app
  | lam
  | fv
  | model
  | ref
  deriving DecidableEq, Repr

namespace TyTag

def name : TyTag → String
  | .bool => "ty.bool"
  | .arr => "ty.arr"
  | .app => "ty.app"
  | .lam => "ty.lam"
  | .fv => "ty.fv"
  | .model => "ty.model"
  | .ref => "ty.ref"

end TyTag

inductive TmTag where
  | tyExists
  | tyForall
  | fv
  | app
  | lam
  | bool
  | op1
  | op2
  | eq
  | eps
  | ref
  deriving DecidableEq, Repr

namespace TmTag

def name : TmTag → String
  | .tyExists => "tm.ty_exists"
  | .tyForall => "tm.ty_forall"
  | .fv => "tm.fv"
  | .app => "tm.app"
  | .lam => "tm.lam"
  | .bool => "tm.bool"
  | .op1 => Nucleus.Hol.Ethane.Builtin.op1RowTag
  | .op2 => Nucleus.Hol.Ethane.Builtin.op2RowTag
  | .eq => "tm.eq"
  | .eps => "tm.eps"
  | .ref => "tm.ref"

end TmTag

/-- The fixed tags of the complete raw Ethane row vocabulary. -/
inductive Tag where
  | kind (tag : KindTag)
  | ty (tag : TyTag)
  | tm (tag : TmTag)
  deriving DecidableEq, Repr

namespace Tag

def name : Tag → String
  | .kind tag => tag.name
  | .ty tag => tag.name
  | .tm tag => tag.name

def sort : Tag → TagSort
  | .kind _ => .kind
  | .ty _ => .ty
  | .tm _ => .tm

def ofName? : String → Option Tag
  | "kind.star" => some (.kind .star)
  | "kind.arr" => some (.kind .arr)
  | "ty.bool" => some (.ty .bool)
  | "ty.arr" => some (.ty .arr)
  | "ty.app" => some (.ty .app)
  | "ty.lam" => some (.ty .lam)
  | "ty.fv" => some (.ty .fv)
  | "tm.ty_exists" => some (.tm .tyExists)
  | "tm.ty_forall" => some (.tm .tyForall)
  | "ty.model" => some (.ty .model)
  | "tm.fv" => some (.tm .fv)
  | "tm.app" => some (.tm .app)
  | "tm.lam" => some (.tm .lam)
  | "tm.bool" => some (.tm .bool)
  | "tm.op1.v1" => some (.tm .op1)
  | "tm.op2.v1" => some (.tm .op2)
  | "tm.eq" => some (.tm .eq)
  | "tm.eps" => some (.tm .eps)
  | "tm.ref" => some (.tm .ref)
  | "ty.ref" => some (.ty .ref)
  | "kind.ref" => some (.kind .ref)
  | _ => none

@[simp] theorem ofName?_name (tag : Tag) : ofName? tag.name = some tag := by
  cases tag with
  | kind tag => cases tag <;> rfl
  | ty tag => cases tag <;> rfl
  | tm tag => cases tag <;> rfl

end Tag

namespace detail

/-- Scalar payload of an ordinary row. -/
inductive Value where
  | nat (value : UInt64)
  | bool (value : Bool)
  deriving DecidableEq, Repr

/-- A private expression row after exact arity and payload validation. -/
inductive Expr where
  | kindStar
  | kindArr (domain codomain : Ref)
  | boolTy
  | tyArr (domain codomain : Ref)
  /-- Type-family application: function and argument. -/
  | tyApp (function argument : Ref)
  /-- Type-family abstraction: free-variable binder and body. -/
  | tyLam (binder body : Ref)
  | tyFv (name : UInt64) (kind : Ref)
  | tyExists (name : UInt64) (predicate : Ref)
  | tyForall (name : UInt64) (predicate : Ref)
  | model (name : UInt64) (predicate : Ref)
  | tmFv (name : UInt64) (type : Ref)
  | app (function argument : Ref)
  | lam (binder body : Ref)
  | bool (value : Bool)
  | op1 (op : Nucleus.Hol.Ethane.Builtin.Op1) (operand : Ref)
  | op2 (op : Nucleus.Hol.Ethane.Builtin.Op2) (left right : Ref)
  /-- Equality's immutable operand type, followed by its two operands. -/
  | eq (type left right : Ref)
  | eps (type predicate : Ref)
  | tmRef (source : ImportId) (foreign : Ref)
  | tyRef (source : ImportId) (foreign : Ref)
  | kindRef (source : ImportId) (foreign : Ref)
  deriving DecidableEq, Repr

def Expr.tag : Expr → Tag
  | .kindStar => .kind .star
  | .kindArr .. => .kind .arr
  | .boolTy => .ty .bool
  | .tyArr .. => .ty .arr
  | .tyApp .. => .ty .app
  | .tyLam .. => .ty .lam
  | .tyFv .. => .ty .fv
  | .tyExists .. => .tm .tyExists
  | .tyForall .. => .tm .tyForall
  | .model .. => .ty .model
  | .tmFv .. => .tm .fv
  | .app .. => .tm .app
  | .lam .. => .tm .lam
  | .bool .. => .tm .bool
  | .op1 .. => .tm .op1
  | .op2 .. => .tm .op2
  | .eq .. => .tm .eq
  | .eps .. => .tm .eps
  | .tmRef .. => .tm .ref
  | .tyRef .. => .ty .ref
  | .kindRef .. => .kind .ref

/-- Exact field-level Serde view. Empty ordinary child lists are omitted. -/
structure RowView where
  tag : Tag
  ixs : Option (List Ref) := none
  val : Option Value := none
  src : Option ImportId := none
  ix : Option Ref := none
  deriving DecidableEq, Repr

/-- One private immutable syntax row.  Logical classifiers and equality
parents live exclusively in the arena's dense columns. -/
structure Row where
  expr : Expr
  deriving DecidableEq, Repr

def Row.toView (row : Row) : RowView :=
  let ordinary (tag : Tag) (ixs : List Ref) (val : Option Value := none) : RowView :=
    { tag, ixs := if ixs.isEmpty then none else some ixs, val }
  let foreign (tag : Tag) (src : ImportId) (ix : Ref) : RowView :=
    { tag, src := some src, ix := some ix }
  match row.expr with
  | .kindStar => ordinary (.kind .star) []
  | .kindArr a b => ordinary (.kind .arr) [a, b]
  | .boolTy => ordinary (.ty .bool) []
  | .tyArr a b => ordinary (.ty .arr) [a, b]
  | .tyApp a b => ordinary (.ty .app) [a, b]
  | .tyLam binder body => ordinary (.ty .lam) [binder, body]
  | .tyFv name kind => ordinary (.ty .fv) [kind] (some (.nat name))
  | .tyExists name predicate => ordinary (.tm .tyExists) [predicate] (some (.nat name))
  | .tyForall name predicate => ordinary (.tm .tyForall) [predicate] (some (.nat name))
  | .model name predicate => ordinary (.ty .model) [predicate] (some (.nat name))
  | .tmFv name type => ordinary (.tm .fv) [type] (some (.nat name))
  | .app f a => ordinary (.tm .app) [f, a]
  | .lam binder body => ordinary (.tm .lam) [binder, body]
  | .bool value => ordinary (.tm .bool) [] (some (.bool value))
  | .op1 op operand => ordinary (.tm .op1) [operand] (some (.nat op.code.toUInt64))
  | .op2 op left right => ordinary (.tm .op2) [left, right] (some (.nat op.code.toUInt64))
  | .eq type left right => ordinary (.tm .eq) [type, left, right]
  | .eps type predicate => ordinary (.tm .eps) [type, predicate]
  | .tmRef src ix => foreign (.tm .ref) src ix
  | .tyRef src ix => foreign (.ty .ref) src ix
  | .kindRef src ix => foreign (.kind .ref) src ix

def Row.ofView? (view : RowView) : Option Row := do
  let expr ← match view.tag, view.ixs, view.val, view.src, view.ix with
    | .kind .star, none, none, none, none => some .kindStar
    | .kind .arr, some [a, b], none, none, none => some (.kindArr a b)
    | .ty .bool, none, none, none, none => some .boolTy
    | .ty .arr, some [a, b], none, none, none => some (.tyArr a b)
    | .ty .app, some [a, b], none, none, none => some (.tyApp a b)
    | .ty .lam, some [binder, body], none, none, none => some (.tyLam binder body)
    | .ty .fv, some [kind], some (.nat name), none, none => some (.tyFv name kind)
    | .tm .tyExists, some [predicate], some (.nat name), none, none =>
        some (.tyExists name predicate)
    | .tm .tyForall, some [predicate], some (.nat name), none, none =>
        some (.tyForall name predicate)
    | .ty .model, some [predicate], some (.nat name), none, none =>
        some (.model name predicate)
    | .tm .fv, some [type], some (.nat name), none, none => some (.tmFv name type)
    | .tm .app, some [f, a], none, none, none => some (.app f a)
    | .tm .lam, some [binder, body], none, none, none => some (.lam binder body)
    | .tm .bool, none, some (.bool value), none, none => some (.bool value)
    | .tm .op1, some [operand], some (.nat code), none, none =>
        some (.op1 (← Nucleus.Hol.Ethane.Builtin.Op1.ofUInt64? code) operand)
    | .tm .op2, some [left, right], some (.nat code), none, none =>
        some (.op2 (← Nucleus.Hol.Ethane.Builtin.Op2.ofUInt64? code) left right)
    | .tm .eq, some [type, left, right], none, none, none =>
        some (.eq type left right)
    | .tm .eps, some [type, predicate], none, none, none => some (.eps type predicate)
    | .tm .ref, none, none, some src, some ix => some (.tmRef src ix)
    | .ty .ref, none, none, some src, some ix => some (.tyRef src ix)
    | .kind .ref, none, none, some src, some ix => some (.kindRef src ix)
    | _, _, _, _, _ => none
  return { expr }

@[simp] theorem Row.ofView?_toView (row : Row) : Row.ofView? row.toView = some row := by
  cases row with
  | mk expr =>
      cases expr <;> try rfl
      case mk.op2 op left right => cases op <;> rfl

end detail

/-! ## Dense logical columns

These definitions live in the base model because the base arena owns this
storage.  `Columns` adds invariants and union-find relations without defining
a second representation. -/

/-- A dense optional column. Missing positions and stored nulls both denote
absence. -/
abbrev Column (α : Type) := List (Option α)

namespace Column

def get? (column : Column α) (reference : Ref) : Option α :=
  column[(reference.value.toNat - 1)]?.bind id

def Decreases (column : Column Ref) : Prop :=
  ∀ {source target}, column.get? source = some target → target < source

@[simp] theorem get?_nil (reference : Ref) :
    get? ([] : Column α) reference = none := by simp [get?]

def normalize : Column α → Column α
  | [] => []
  | none :: tail =>
      let normalized := normalize tail
      if normalized.isEmpty then [] else none :: normalized
  | some value :: tail => some value :: normalize tail

@[simp] theorem normalize_nil : normalize ([] : Column α) = [] := rfl

theorem normalize_cons_some (value : α) (tail : Column α) :
    normalize (some value :: tail) = some value :: normalize tail := rfl

@[simp] theorem normalize_idempotent (column : Column α) :
    normalize (normalize column) = normalize column := by
  induction column with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | some value => simp [normalize, ih]
      | none =>
          simp only [normalize]
          split <;> simp_all [normalize]

@[simp] theorem getElem?_normalize_bind (column : Column α) (position : Nat) :
    (normalize column)[position]?.bind id = column[position]?.bind id := by
  induction column generalizing position with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | some value =>
          cases position with
          | zero => rfl
          | succ position => simpa [normalize] using ih position
      | none =>
          simp only [normalize]
          split
          · rename_i empty
            have normalizedNil : normalize tail = [] := List.isEmpty_iff.mp empty
            cases position with
            | zero => simp
            | succ position =>
                have tailNone : tail[position]?.bind id = none := by
                  rw [← ih position, normalizedNil]
                  rfl
                simpa using tailNone.symm
          · rename_i nonempty
            cases position with
            | zero => rfl
            | succ position => simpa using ih position

@[simp] theorem get?_normalize (column : Column α) (reference : Ref) :
    get? (normalize column) reference = get? column reference := by
  exact getElem?_normalize_bind column (reference.value.toNat - 1)

end Column

/-- Physical HOL definition and union-find storage, matching Rust. -/
structure Dense where
  defs : List detail.Expr
  eq : Column Ref := []
  synEq : Column Ref := []
  conv : Column Ref := []
  deriving DecidableEq, Repr

namespace Dense

def expr? (dense : Dense) (reference : Ref) : Option detail.Expr :=
  dense.defs[(reference.value.toNat - 1)]?

def tagSort? (dense : Dense) (reference : Ref) : Option TagSort :=
  (dense.expr? reference).map (·.tag.sort)

def classifierSort? : TagSort → Option TagSort
  | .kind => none
  | .ty => some .kind
  | .tm => some .ty

def classifierAt? (dense : Dense) : Nat → Ref → Option Ref
  | 0, _ => none
  | fuel + 1, reference =>
      match dense.conv.get? reference with
      | none => none
      | some target =>
          if dense.tagSort? reference = dense.tagSort? target then
            dense.classifierAt? fuel target
          else if (dense.tagSort? reference).bind classifierSort? = dense.tagSort? target then
            some target
          else none

def classifier? (dense : Dense) (reference : Ref) : Option Ref :=
  dense.classifierAt? (dense.defs.length + 1) reference

def classifierFrom? (dense : Dense) : Nat → TagSort → Option Ref → Option Ref
  | 0, _, _ => none
  | _, _, none => none
  | fuel + 1, category, some target =>
      if dense.tagSort? target = some category then
        dense.classifierAt? fuel target
      else if classifierSort? category = dense.tagSort? target then some target else none

theorem classifierAt?_eq_classifierFrom? (dense : Dense) (fuel : Nat)
    (reference : Ref) (expr : detail.Expr)
    (found : dense.expr? reference = some expr) :
    dense.classifierAt? fuel reference =
      dense.classifierFrom? fuel expr.tag.sort (dense.conv.get? reference) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases link : dense.conv.get? reference with
      | none => simp [classifierAt?, classifierFrom?, link]
      | some target =>
          simp only [classifierAt?, classifierFrom?, link]
          have source : dense.tagSort? reference = some expr.tag.sort := by
            simp [tagSort?, found]
          rw [source]
          by_cases same : dense.tagSort? target = some expr.tag.sort
          · rw [if_pos same, if_pos same.symm]
          · have reverse : some expr.tag.sort ≠ dense.tagSort? target :=
              fun equal => same equal.symm
            rw [if_neg same, if_neg reverse]
            simp only [Option.bind_some]

def row? (dense : Dense) (reference : Ref) : Option detail.Expr :=
  dense.expr? reference

def rows (dense : Dense) : List detail.Expr := dense.defs

@[simp] theorem rows_length (dense : Dense) : dense.rows.length = dense.defs.length := by
  simp [rows]

theorem rows_get? (dense : Dense) (position : Nat) :
    dense.rows[position]? = dense.defs[position]? := rfl

theorem rows_row? (dense : Dense) (reference : Ref) :
    dense.rows[(reference.value.toNat - 1)]? = dense.row? reference := by
  rfl

end Dense

/-- BLAKE3 is fixed by the Rust link format; Lean treats its bytes abstractly. -/
structure Link where
  blake3 : O256
  deriving DecidableEq, Repr

/-- Internal proxy-obligation adapter retained for the established resolver
lemmas. Current arenas encode these obligations as `amb.pred` atoms and
`amb.ctx` unit clauses; this type is not part of their wire format. -/
inductive Meta where
  | valid (source : ImportId)
  | wf (source : ImportId) (foreign sort : Ref)
  deriving DecidableEq, Repr

mutual

/-- A null slot, literal nested arena, or lazy CBOR link. -/
inductive Import where
  | null
  | literal (arena : Arena)
  | link (value : Link)

/-- Internal HOL proof-core value. `Layout.Arena` is the normalized Rust arena
value and supplies empty adapter metadata when materializing this core. -/
inductive Arena where
  | mk
      (imports : List Import)
      (axs : Finset String)
      (dense : Dense)
      (synFacts : List SynSlot)
      (synFree : Option SynFactId)
      (ctx : Finset Ref)
      (assume : List Meta)
      (assert : List Meta)

end

namespace Arena

def imports : Arena → List Import | .mk imports .. => imports
def axs : Arena → Finset String | .mk _ axs .. => axs
def dense : Arena → Dense | .mk _ _ dense .. => dense
/-- Syntax rows. Equality and classifiers remain separate dense columns. -/
def defs (arena : Arena) : List detail.Expr := arena.dense.rows
def synFacts : Arena → List SynSlot | .mk _ _ _ synFacts .. => synFacts
def synFree : Arena → Option SynFactId | .mk _ _ _ _ synFree .. => synFree
def ctx : Arena → Finset Ref | .mk _ _ _ _ _ ctx .. => ctx
def assume : Arena → List Meta | .mk _ _ _ _ _ _ assume _ => assume
def assert : Arena → List Meta | .mk _ _ _ _ _ _ _ assert => assert

def empty : Arena := .mk [] ∅ { defs := [] } [] none ∅ [] []

/-- Erase the proof cache while preserving the logical row/import arena. -/
def withoutSyn : Arena → Arena
  | .mk imports axs dense _ _ ctx assume assert =>
      .mk imports axs dense [] none ctx assume assert

@[simp] theorem withoutSyn_empty : empty.withoutSyn = empty := rfl

@[simp] theorem imports_withoutSyn (arena : Arena) :
    arena.withoutSyn.imports = arena.imports := by cases arena; rfl

@[simp] theorem axs_withoutSyn (arena : Arena) :
    arena.withoutSyn.axs = arena.axs := by cases arena; rfl

@[simp] theorem defs_withoutSyn (arena : Arena) :
    arena.withoutSyn.defs = arena.defs := by cases arena; rfl

@[simp] theorem ctx_withoutSyn (arena : Arena) :
    arena.withoutSyn.ctx = arena.ctx := by cases arena; rfl

@[simp] theorem assume_withoutSyn (arena : Arena) :
    arena.withoutSyn.assume = arena.assume := by cases arena; rfl

@[simp] theorem assert_withoutSyn (arena : Arena) :
    arena.withoutSyn.assert = arena.assert := by cases arena; rfl

def row? (arena : Arena) (reference : Ref) : Option detail.Expr :=
  arena.dense.row? reference

def tag? (arena : Arena) (reference : Ref) : Option Tag :=
  (arena.row? reference).map (·.tag)

def eq? (arena : Arena) (reference : Ref) : Option Ref :=
  arena.dense.eq.get? reference

def sort? (arena : Arena) (reference : Ref) : Option Ref :=
  arena.dense.classifier? reference

theorem row?_resident {arena : Arena} {reference : Ref} {row : detail.Expr}
    (found : arena.row? reference = some row) :
    arena.dense.expr? reference ≠ none := by
  intro missing
  simp [Arena.row?, Dense.row?, missing] at found

@[simp] theorem row?_withoutSyn (arena : Arena) (reference : Ref) :
  arena.withoutSyn.row? reference = arena.row? reference := by
  cases arena; rfl

@[simp] theorem tag?_withoutSyn (arena : Arena) (reference : Ref) :
    arena.withoutSyn.tag? reference = arena.tag? reference := by
  simp [tag?]

@[simp] theorem eq?_withoutSyn (arena : Arena) (reference : Ref) :
  arena.withoutSyn.eq? reference = arena.eq? reference := by
  cases arena; rfl

@[simp] theorem sort?_withoutSyn (arena : Arena) (reference : Ref) :
  arena.withoutSyn.sort? reference = arena.sort? reference := by
  cases arena; rfl

end Arena

/-- The field-level Serde view before `axs` and `ctx` normalization. -/
structure View where
  imports : List Import
  axs : List String
  defs : List detail.Expr
  eq : Column Ref := []
  synEq : Column Ref := []
  conv : Column Ref := []
  synFacts : List SynSlot := []
  synFree : Option SynFactId := none
  ctx : List Ref
  assume : List Meta
  assert : List Meta

def View.normalize (view : View) : Arena :=
  .mk view.imports view.axs.toFinset
    { defs := view.defs, eq := view.eq, synEq := view.synEq, conv := view.conv }
    view.synFacts view.synFree
    view.ctx.toFinset view.assume view.assert

def Arena.toView (arena : Arena) : View :=
  { imports := arena.imports
    axs := arena.axs.sort (· ≤ ·)
    defs := arena.dense.defs
    eq := arena.dense.eq
    synEq := arena.dense.synEq
    conv := arena.dense.conv
    synFacts := arena.synFacts
    synFree := arena.synFree
    ctx := arena.ctx.sort (· ≤ ·)
    assume := arena.assume
    assert := arena.assert }

@[simp] theorem normalize_toView (arena : Arena) : arena.toView.normalize = arena := by
  cases arena with
  | mk imports axs dense synFacts synFree ctx assume assert =>
      simp [Arena.toView, View.normalize, Arena.imports, Arena.axs,
        Arena.dense, Arena.synFacts, Arena.synFree, Arena.ctx, Arena.assume, Arena.assert]

@[simp] theorem toView_normalize (view : View) :
    view.normalize.toView =
      { view with
        axs := view.axs.toFinset.sort (· ≤ ·)
        ctx := view.ctx.toFinset.sort (· ≤ ·) } := by
  simp [Arena.toView, View.normalize, Arena.imports, Arena.axs, Arena.dense,
    Arena.synFacts, Arena.synFree, Arena.ctx, Arena.assume, Arena.assert]

theorem toView_axs_nodup (arena : Arena) : arena.toView.axs.Nodup := by
  exact Finset.sort_nodup _ _

theorem toView_ctx_nodup (arena : Arena) : arena.toView.ctx.Nodup := by
  exact Finset.sort_nodup _ _

end Nucleus.Hol.Ethane.OneBased
