import Nucleus.Hol.Ethane.Arena
import Nucleus.Hol.Ethane.Builtin
import Nucleus.O256.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Basic

/-!
# One-based HOL proof core

This is the semantic row model used by the established HOL soundness proofs.
The current Rust arena is modeled exactly by `OneBased.Layout`; its separate
columns are materialized into this proof core only through
`Layout.Arena.holCore`. It is not the current serialized arena shape.
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
  | model (name : UInt64) (predicate : Ref)
  | tmFv (name : UInt64) (type : Ref)
  | app (function argument : Ref)
  | lam (binder body : Ref)
  | bool (value : Bool)
  | op1 (op : Nucleus.Hol.Ethane.Builtin.Op1) (operand : Ref)
  | op2 (op : Nucleus.Hol.Ethane.Builtin.Op2) (left right : Ref)
  /-- Equality operands; their common type is recovered during checking. -/
  | eq (left right : Ref)
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
  eq : Option Ref := none
  sort : Option Ref := none
  deriving DecidableEq, Repr

/-- One private row and its optional unvalidated inline members. -/
structure Row where
  expr : Expr
  eq : Option Ref := none
  sort : Option Ref := none
  deriving DecidableEq, Repr

def Row.toView (row : Row) : RowView :=
  let ordinary (tag : Tag) (ixs : List Ref) (val : Option Value := none) : RowView :=
    { tag, ixs := if ixs.isEmpty then none else some ixs,
      val, eq := row.eq, sort := row.sort }
  let foreign (tag : Tag) (src : ImportId) (ix : Ref) : RowView :=
    { tag, src := some src, ix := some ix, eq := row.eq, sort := row.sort }
  match row.expr with
  | .kindStar => ordinary (.kind .star) []
  | .kindArr a b => ordinary (.kind .arr) [a, b]
  | .boolTy => ordinary (.ty .bool) []
  | .tyArr a b => ordinary (.ty .arr) [a, b]
  | .tyApp a b => ordinary (.ty .app) [a, b]
  | .tyLam binder body => ordinary (.ty .lam) [binder, body]
  | .tyFv name kind => ordinary (.ty .fv) [kind] (some (.nat name))
  | .tyExists name predicate => ordinary (.tm .tyExists) [predicate] (some (.nat name))
  | .model name predicate => ordinary (.ty .model) [predicate] (some (.nat name))
  | .tmFv name type => ordinary (.tm .fv) [type] (some (.nat name))
  | .app f a => ordinary (.tm .app) [f, a]
  | .lam binder body => ordinary (.tm .lam) [binder, body]
  | .bool value => ordinary (.tm .bool) [] (some (.bool value))
  | .op1 op operand => ordinary (.tm .op1) [operand] (some (.nat op.code.toUInt64))
  | .op2 op left right => ordinary (.tm .op2) [left, right] (some (.nat op.code.toUInt64))
  | .eq left right => ordinary (.tm .eq) [left, right]
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
    | .tm .eq, some [left, right], none, none, none => some (.eq left right)
    | .tm .eps, some [type, predicate], none, none, none => some (.eps type predicate)
    | .tm .ref, none, none, some src, some ix => some (.tmRef src ix)
    | .ty .ref, none, none, some src, some ix => some (.tyRef src ix)
    | .kind .ref, none, none, some src, some ix => some (.kindRef src ix)
    | _, _, _, _, _ => none
  return { expr, eq := view.eq, sort := view.sort }

@[simp] theorem Row.ofView?_toView (row : Row) : Row.ofView? row.toView = some row := by
  cases row with
  | mk expr eq sort =>
      cases expr <;> try rfl
      case mk.op2 op left right => cases op <;> rfl

end detail

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
      (defs : List detail.Row)
      (synFacts : List SynSlot)
      (synFree : Option SynFactId)
      (ctx : Finset Ref)
      (assume : List Meta)
      (assert : List Meta)

end

namespace Arena

def imports : Arena → List Import | .mk imports .. => imports
def axs : Arena → Finset String | .mk _ axs .. => axs
def defs : Arena → List detail.Row | .mk _ _ defs .. => defs
def synFacts : Arena → List SynSlot | .mk _ _ _ synFacts .. => synFacts
def synFree : Arena → Option SynFactId | .mk _ _ _ _ synFree .. => synFree
def ctx : Arena → Finset Ref | .mk _ _ _ _ _ ctx .. => ctx
def assume : Arena → List Meta | .mk _ _ _ _ _ _ assume _ => assume
def assert : Arena → List Meta | .mk _ _ _ _ _ _ _ assert => assert

def empty : Arena := .mk [] ∅ [] [] none ∅ [] []

/-- Erase the proof cache while preserving the logical row/import arena. -/
def withoutSyn : Arena → Arena
  | .mk imports axs defs _ _ ctx assume assert =>
      .mk imports axs defs [] none ctx assume assert

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

def row? (arena : Arena) (reference : Ref) : Option detail.Row :=
  arena.defs[(reference.value.toNat - 1)]?

def tag? (arena : Arena) (reference : Ref) : Option Tag :=
  (arena.row? reference).map (·.expr.tag)

def eq? (arena : Arena) (reference : Ref) : Option Ref :=
  (arena.row? reference).bind (·.eq)

def sort? (arena : Arena) (reference : Ref) : Option Ref :=
  (arena.row? reference).bind (·.sort)

@[simp] theorem row?_withoutSyn (arena : Arena) (reference : Ref) :
    arena.withoutSyn.row? reference = arena.row? reference := by
  simp [row?]

@[simp] theorem tag?_withoutSyn (arena : Arena) (reference : Ref) :
    arena.withoutSyn.tag? reference = arena.tag? reference := by
  simp [tag?]

@[simp] theorem eq?_withoutSyn (arena : Arena) (reference : Ref) :
    arena.withoutSyn.eq? reference = arena.eq? reference := by
  simp [eq?]

@[simp] theorem sort?_withoutSyn (arena : Arena) (reference : Ref) :
    arena.withoutSyn.sort? reference = arena.sort? reference := by
  simp [sort?]

end Arena

/-- The field-level Serde view before `axs` and `ctx` normalization. -/
structure View where
  imports : List Import
  axs : List String
  defs : List detail.Row
  synFacts : List SynSlot := []
  synFree : Option SynFactId := none
  ctx : List Ref
  assume : List Meta
  assert : List Meta

def View.normalize (view : View) : Arena :=
  .mk view.imports view.axs.toFinset view.defs view.synFacts view.synFree
    view.ctx.toFinset view.assume view.assert

def Arena.toView (arena : Arena) : View :=
  { imports := arena.imports
    axs := arena.axs.sort (· ≤ ·)
    defs := arena.defs
    synFacts := arena.synFacts
    synFree := arena.synFree
    ctx := arena.ctx.sort (· ≤ ·)
    assume := arena.assume
    assert := arena.assert }

@[simp] theorem normalize_toView (arena : Arena) : arena.toView.normalize = arena := by
  cases arena with
  | mk imports axs defs synFacts synFree ctx assume assert =>
      simp [Arena.toView, View.normalize, Arena.imports, Arena.axs, Arena.defs,
        Arena.synFacts, Arena.synFree, Arena.ctx, Arena.assume, Arena.assert]

@[simp] theorem toView_normalize (view : View) :
    view.normalize.toView =
      { view with
        axs := view.axs.toFinset.sort (· ≤ ·)
        ctx := view.ctx.toFinset.sort (· ≤ ·) } := by
  simp [Arena.toView, View.normalize, Arena.imports, Arena.axs, Arena.defs,
    Arena.synFacts, Arena.synFree, Arena.ctx, Arena.assume, Arena.assert]

theorem toView_axs_nodup (arena : Arena) : arena.toView.axs.Nodup := by
  exact Finset.sort_nodup _ _

theorem toView_ctx_nodup (arena : Arena) : arena.toView.ctx.Nodup := by
  exact Finset.sort_nodup _ _

end Nucleus.Hol.Ethane.OneBased
