import Mathlib.Data.List.Infix
import Nucleus.Bytes

/-!
# Compact natural and byte expressions

This is the first Propane value-language slice.  It fixes the observable
meaning of compact literals and the small operation vocabulary needed by a
Wasm decoder without granting any new theorem rule.  `Target` describes a
deterministic lowering package; `Target.Sound` is the obligation an ordinary
Ethane/init implementation must discharge.

Checked slicing is half-open and returns `none` when its bounds are invalid.
Substring is the contiguous-list predicate, not subsequence membership.
-/

namespace Nucleus.Hol.Propane.Compact

/-- The value types needed by the initial compact surface. -/
inductive Ty where
  | bool
  | nat
  | bytes
  | option (element : Ty)
  deriving DecidableEq, Repr

/-- Direct mathematical meaning used to specify lowering packages. -/
@[reducible] def Ty.denote : Ty → Type
  | .bool => Bool
  | .nat => Nat
  | .bytes => Nucleus.Bytes
  | .option element => Option element.denote

/-- Whether `needle` occurs contiguously in `haystack`. -/
def bytesSubstring (needle haystack : Nucleus.Bytes) : Bool :=
  decide (needle.toList <:+: haystack.toList)

/-- Intrinsically typed compact expressions.  Logical values are independent
of whether a table later stores them inline or behind an arena pointer. -/
inductive Expr : Ty → Type where
  | bool (value : Bool) : Expr .bool
  | nat (value : Nat) : Expr .nat
  | bytes (literal : Nucleus.Bytes) : Expr .bytes
  | add (left right : Expr .nat) : Expr .nat
  | le (left right : Expr .nat) : Expr .bool
  | lt (left right : Expr .nat) : Expr .bool
  | cat (left right : Expr .bytes) : Expr .bytes
  | len (value : Expr .bytes) : Expr .nat
  | slice (value : Expr .bytes) (start stop : Expr .nat) :
      Expr (.option .bytes)
  | substring (needle haystack : Expr .bytes) : Expr .bool

/-- Executable reference semantics. -/
def Expr.eval {type : Ty} : Expr type → type.denote
  | .bool value => value
  | .nat value => value
  | .bytes literal => literal
  | .add left right => left.eval + right.eval
  | .le left right => decide (left.eval ≤ right.eval)
  | .lt left right => decide (left.eval < right.eval)
  | .cat left right => left.eval.append right.eval
  | .len value => value.eval.length
  | .slice value start stop => value.eval.slice? start.eval (some stop.eval)
  | .substring needle haystack => bytesSubstring needle.eval haystack.eval

/-- Operations supplied by a concrete lowering.  The terms may be ordinary
Ethane expressions, arena references, or another Lean design under study. -/
structure Target where
  Term : Ty → Type
  bool : Bool → Term .bool
  nat : Nat → Term .nat
  bytes : Nucleus.Bytes → Term .bytes
  add : Term .nat → Term .nat → Term .nat
  le : Term .nat → Term .nat → Term .bool
  lt : Term .nat → Term .nat → Term .bool
  cat : Term .bytes → Term .bytes → Term .bytes
  len : Term .bytes → Term .nat
  slice : Term .bytes → Term .nat → Term .nat → Term (.option .bytes)
  substring : Term .bytes → Term .bytes → Term .bool

/-- Deterministic structural lowering. -/
def Expr.lower {type : Ty} (target : Target) : Expr type → target.Term type
  | .bool value => target.bool value
  | .nat literal => target.nat literal
  | .bytes literal => target.bytes literal
  | .add left right => target.add (left.lower target) (right.lower target)
  | .le left right => target.le (left.lower target) (right.lower target)
  | .lt left right => target.lt (left.lower target) (right.lower target)
  | .cat left right => target.cat (left.lower target) (right.lower target)
  | .len value => target.len (value.lower target)
  | .slice value start stop =>
      target.slice (value.lower target) (start.lower target) (stop.lower target)
  | .substring needle haystack =>
      target.substring (needle.lower target) (haystack.lower target)

namespace Target

/-- Semantic obligations for a lowering package.  These are userspace facts:
the compact syntax itself cannot create a theorem. -/
structure Sound (target : Target) where
  denote : {type : Ty} → target.Term type → type.denote
  bool (value : Bool) : denote (target.bool value) = value
  nat (value : Nat) : denote (target.nat value) = value
  bytes (literal : Nucleus.Bytes) : denote (target.bytes literal) = literal
  add (left right : target.Term .nat) :
    denote (target.add left right) = denote left + denote right
  le (left right : target.Term .nat) :
    denote (target.le left right) = decide (denote left ≤ denote right)
  lt (left right : target.Term .nat) :
    denote (target.lt left right) = decide (denote left < denote right)
  cat (left right : target.Term .bytes) :
    denote (target.cat left right) = (denote left).append (denote right)
  len (value : target.Term .bytes) :
    denote (target.len value) = (denote value).length
  slice (value : target.Term .bytes) (start stop : target.Term .nat) :
    denote (target.slice value start stop) =
      (denote value).slice? (denote start) (some (denote stop))
  substring (needle haystack : target.Term .bytes) :
    denote (target.substring needle haystack) =
      bytesSubstring (denote needle) (denote haystack)

/-- The reference lowering executes directly in the specified value types. -/
def direct : Target where
  Term := Ty.denote
  bool := id
  nat := id
  bytes := id
  add := (· + ·)
  le := fun left right => decide (left ≤ right)
  lt := fun left right => decide (left < right)
  cat := Nucleus.Bytes.append
  len := Nucleus.Bytes.length
  slice := fun value start stop => value.slice? start (some stop)
  substring := bytesSubstring

def directSound : direct.Sound where
  denote := id
  bool := by intro; rfl
  nat := by intro; rfl
  bytes := by intro; rfl
  add := by intros; rfl
  le := by intros; rfl
  lt := by intros; rfl
  cat := by intros; rfl
  len := by intros; rfl
  slice := by intros; rfl
  substring := by intros; rfl

end Target

/-- A sound package makes compact evaluation agree exactly with lowering. -/
theorem Expr.lower_sound (target : Target) (sound : target.Sound)
    {type : Ty} (expression : Expr type) :
    sound.denote (expression.lower target) = expression.eval := by
  induction expression with
  | bool value => exact sound.bool value
  | nat literal => exact sound.nat literal
  | bytes literal => exact sound.bytes literal
  | add left right ihLeft ihRight =>
      rw [Expr.lower, Expr.eval, sound.add, ihLeft, ihRight]
  | le left right ihLeft ihRight =>
      rw [Expr.lower, Expr.eval, sound.le, ihLeft, ihRight]
  | lt left right ihLeft ihRight =>
      rw [Expr.lower, Expr.eval, sound.lt, ihLeft, ihRight]
  | cat left right ihLeft ihRight =>
      rw [Expr.lower, Expr.eval, sound.cat, ihLeft, ihRight]
  | len value ih =>
      rw [Expr.lower, Expr.eval, sound.len, ih]
  | slice value start stop ihValue ihStart ihStop =>
      rw [Expr.lower, Expr.eval, sound.slice, ihValue, ihStart, ihStop]
  | substring needle haystack ihNeedle ihHaystack =>
      rw [Expr.lower, Expr.eval, sound.substring, ihNeedle, ihHaystack]

@[simp] theorem Expr.lower_direct {type : Ty} (expression : Expr type) :
    expression.lower Target.direct = expression.eval :=
  expression.lower_sound Target.direct Target.directSound

end Nucleus.Hol.Propane.Compact
