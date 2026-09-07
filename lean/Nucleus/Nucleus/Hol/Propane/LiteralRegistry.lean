import Nucleus.Hol.Propane.LiteralRegistryBuiltin
import Nucleus.Hol.Propane.LiteralSignatureCode

/-!
# Immutable negative-reference registry

An identifier is the positive magnitude of a negative term reference. Types,
function constants, signature suffixes, and tiny literals are generated without
arena state. Unassigned identifiers fail lookup. These identities do not assert
that two different builtin functions have different denotations.
-/

namespace Nucleus.Hol.Propane.LiteralRegistry

set_option maxRecDepth 8192

inductive Entry where
  | star
  | type (type : LiteralTy)
  | literal (value : LiteralValue)
  | builtin (op : Builtin)
  | arrow (types : List LiteralTy)
  deriving DecidableEq, Repr

def typeRef (type : LiteralTy) : Int := -(typeCode type + 2 : Nat)

def signatureRef : List LiteralTy → Int
  | [] => 0
  | [type] => typeRef type
  | types => -(131072 + signatureCode types : Nat)

def builtinRef (op : Builtin) : Int := -(1024 + builtinCode (canonicalBuiltin op) : Nat)

def tinyWordBase : Width → Nat
  | .i8 => 1179648 | .i16 => 1245184 | .i32 => 1310720 | .i64 => 1376256

def tinyWordLimit : Width → Nat
  | .i8 => 256 | _ => 65536

def decodeTiny (identifier : Nat) : Option LiteralValue :=
  if 1048576 ≤ identifier ∧ identifier < 1114112 then some (.nat (identifier - 1048576))
  else if 1114112 ≤ identifier ∧ identifier < 1179648 then
    some (.int ((identifier : Int) - 1114112 - 32768))
  else if 1179648 ≤ identifier ∧ identifier < 1179904 then
    some (.word .i8 (BitVec.ofNat 8 (identifier - 1179648)))
  else if 1245184 ≤ identifier ∧ identifier < 1310720 then
    some (.word .i16 (BitVec.ofNat 16 (identifier - 1245184)))
  else if 1310720 ≤ identifier ∧ identifier < 1376256 then
    some (.word .i32 (BitVec.ofNat 32 (identifier - 1310720)))
  else if 1376256 ≤ identifier ∧ identifier < 1441792 then
    some (.word .i64 (BitVec.ofNat 64 (identifier - 1376256)))
  else none

def decodeGlobal (identifier : Nat) : Option Entry :=
  if identifier = 1 then some .star
  else if 2 ≤ identifier ∧ identifier ≤ 9 then .type <$> decodeType (identifier - 2)
  else if identifier = 10 then some (.literal (.bool false))
  else if identifier = 11 then some (.literal (.bool true))
  else if 1024 ≤ identifier ∧ identifier < 1440 then
    .builtin <$> decodeBuiltin (identifier - 1024)
  else if 131072 ≤ identifier ∧ identifier < 196608 then do
    let types ← decodeSignature 6 (identifier - 131072)
    if 2 ≤ types.length ∧ types.length ≤ 5 then some (.arrow types) else none
  else .literal <$> decodeTiny identifier

def lookup (reference : Int) : Option Entry :=
  if reference < 0 then decodeGlobal reference.natAbs else none

def Entry.classifier : Entry → Int
  | .star => 0
  | .type _ | .arrow _ => -1
  | .literal value => typeRef value.type
  | .builtin op => match op.signature with
      | some (inputs, output) => signatureRef (inputs ++ [output])
      | none => 0

/-- Only decoded resident tiny values use these codes; Bytes has no tiny code. -/
def tinyCode : LiteralValue → Nat
  | .bool value => if value then 11 else 10
  | .nat value => 1048576 + value
  | .int value => 1114112 + (value + 32768).toNat
  | .word width value => tinyWordBase width + value.toNat
  | .bytes _ => 0

/-- Reconstruction of an assigned registry identifier, not a validator for arbitrary entries. -/
def Entry.code : Entry → Nat
  | .star => 1
  | .type literalType => typeCode literalType + 2
  | .literal value => tinyCode value
  | .builtin op => 1024 + builtinCode op
  | .arrow types => 131072 + signatureCode types

@[simp] theorem decode_global_type (type : LiteralTy) :
    decodeGlobal (typeCode type + 2) = some (.type type) := by
  cases type with
  | word width => cases width <;> decide
  | _ => decide

@[simp] theorem lookup_type (type : LiteralTy) : lookup (typeRef type) = some (.type type) := by
  cases type with
  | word width => cases width <;> decide
  | _ => decide

theorem typeRef_injective : Function.Injective typeRef := by
  intro left right equal
  have found := lookup_type left
  rw [equal, lookup_type right] at found
  exact Entry.type.inj (Option.some.inj found).symm

theorem decode_tiny_nat (value : Nat) (bounded : value < 65536) :
    decodeTiny (1048576 + value) = some (.nat value) := by
  have inside : 1048576 ≤ 1048576 + value ∧ 1048576 + value < 1114112 := by omega
  simp [decodeTiny, inside]

theorem decode_tiny_int (value : Int) (bounded : -32768 ≤ value ∧ value < 32768) :
    decodeTiny (1114112 + (value + 32768).toNat) = some (.int value) := by
  have magnitude : ((value + 32768).toNat : Int) = value + 32768 := by omega
  have outside : ¬(1048576 ≤ 1114112 + (value + 32768).toNat ∧
      1114112 + (value + 32768).toNat < 1114112) := by omega
  have inside : 1114112 ≤ 1114112 + (value + 32768).toNat ∧
      1114112 + (value + 32768).toNat < 1179648 := by omega
  simp [decodeTiny, outside, inside, magnitude]

theorem decode_tiny_word (width : Width) (value : BitVec width.bits)
    (bounded : value.toNat < tinyWordLimit width) :
    decodeTiny (tinyWordBase width + value.toNat) = some (.word width value) := by
  cases width <;>
    simp only [tinyWordBase, tinyWordLimit] at bounded ⊢ <;>
    unfold decodeTiny
  all_goals repeat' first | omega | split
  all_goals
    simp only [Nat.add_sub_cancel_left, Option.some.injEq]
    apply congrArg (LiteralValue.word _)
    exact (BitVec.ofNat_toNat _ value).trans (BitVec.setWidth_eq value)

private theorem builtin_classifier_check : allBuiltins.all
    (fun op => decide ((Entry.builtin op).classifier ≠ typeRef .bool)) = true := by decide

theorem builtin_classifier_not_bool (op : Builtin) :
    (Entry.builtin op).classifier ≠ typeRef .bool := by
  exact of_decide_eq_true
    (List.all_eq_true.mp builtin_classifier_check op (allBuiltins_complete op))

theorem decodeTiny_not_bool {identifier : Nat} {value : LiteralValue}
    (found : decodeTiny identifier = some value) : value.type ≠ .bool := by
  unfold decodeTiny at found
  repeat' split at found
  all_goals cases found <;> simp [LiteralValue.type]

private theorem tinyWordCode (width : Width) (value : Nat) (bounded : value < 2 ^ width.bits) :
    tinyCode (.word width (BitVec.ofNat width.bits value)) = tinyWordBase width + value := by
  simp only [tinyCode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]

theorem decodeTiny_canonical {identifier : Nat} {value : LiteralValue}
    (found : decodeTiny identifier = some value) : tinyCode value = identifier := by
  unfold decodeTiny at found
  repeat' split at found
  all_goals cases found
  all_goals first
    | { simp only [tinyCode]; omega }
    | {
        rw [tinyWordCode _ _ (by simp only [Width.bits]; omega)]
        simp only [tinyWordBase]
        omega }

theorem decodeGlobal_canonical {identifier : Nat} {entry : Entry}
    (found : decodeGlobal identifier = some entry) : entry.code = identifier := by
  unfold decodeGlobal at found
  split at found
  · cases found
    exact (by assumption : identifier = 1).symm
  · split at found
    · cases decoded : decodeType (identifier - 2) with
      | none => simp [decoded] at found
      | some type =>
          have equal : Entry.type type = entry := by simpa [decoded] using found
          subst entry
          have code := decodeType_spec decoded
          simp only [Entry.code]
          omega
    · split at found
      · cases found
        exact (by assumption : identifier = 10).symm
      · split at found
        · cases found
          exact (by assumption : identifier = 11).symm
        · split at found
          · cases decoded : decodeBuiltin (identifier - 1024) with
            | none => simp [decoded] at found
            | some op =>
                have equal : Entry.builtin op = entry := by simpa [decoded] using found
                subst entry
                have code := (decodeBuiltin_spec decoded).1
                simp only [Entry.code]
                omega
          · split at found
            · cases decoded : decodeSignature 6 (identifier - 131072) with
              | none => simp [decoded] at found
              | some types =>
                  rw [decoded] at found
                  change (if 2 ≤ types.length ∧ types.length ≤ 5 then
                    some (.arrow types) else none) = some entry at found
                  split at found
                  · cases found
                    have code := decodeSignature_canonical decoded
                    simp only [Entry.code]
                    omega
                  · cases found
            · cases decoded : decodeTiny identifier with
              | none => simp [decoded] at found
              | some value =>
                  have equal : Entry.literal value = entry := by simpa [decoded] using found
                  subst entry
                  exact decodeTiny_canonical decoded

/-- Two assigned IDs cannot decode to the same syntax entry. No semantic inequality follows. -/
theorem decodeGlobal_injective {left right : Nat} {entry : Entry}
    (first : decodeGlobal left = some entry) (second : decodeGlobal right = some entry) :
    left = right := (decodeGlobal_canonical first).symm.trans (decodeGlobal_canonical second)

theorem lookup_injective {left right : Int} {entry : Entry}
    (first : lookup left = some entry) (second : lookup right = some entry) : left = right := by
  cases left with
  | ofNat value =>
      unfold lookup at first
      split at first
      · exact False.elim ((Int.not_lt.mpr (Int.natCast_nonneg value)) (by assumption))
      · cases first
  | negSucc left =>
      cases right with
      | ofNat value =>
          unfold lookup at second
          split at second
          · exact False.elim ((Int.not_lt.mpr (Int.natCast_nonneg value)) (by assumption))
          · cases second
      | negSucc right =>
          have first' : decodeGlobal (left + 1) = some entry := by simpa [lookup] using first
          have second' : decodeGlobal (right + 1) = some entry := by simpa [lookup] using second
          have equal := decodeGlobal_injective first' second'
          congr 1
          omega

theorem decodeGlobal_boolean_only {identifier : Nat} {entry : Entry}
    (found : decodeGlobal identifier = some entry)
    (boolean : entry.classifier = typeRef .bool) : identifier = 10 ∨ identifier = 11 := by
  unfold decodeGlobal at found
  split at found
  · cases found
    contradiction
  · split at found
    · cases decoded : decodeType (identifier - 2) with
      | none => simp [decoded] at found
      | some type =>
          have equal : Entry.type type = entry := by simpa [decoded] using found
          subst entry
          simp [Entry.classifier, typeRef, typeCode] at boolean
    · split at found
      · exact Or.inl (by assumption)
      · split at found
        · exact Or.inr (by assumption)
        · split at found
          · cases decoded : decodeBuiltin (identifier - 1024) with
            | none => simp [decoded] at found
            | some op =>
                have equal : Entry.builtin op = entry := by simpa [decoded] using found
                subst entry
                exact False.elim (builtin_classifier_not_bool op boolean)
          · split at found
            · cases decoded : decodeSignature 6 (identifier - 131072) with
              | none => simp [decoded] at found
              | some types =>
                  rw [decoded] at found
                  change (if 2 ≤ types.length ∧ types.length ≤ 5 then
                    some (.arrow types) else none) = some entry at found
                  split at found
                  · cases found
                    simp [Entry.classifier, typeRef, typeCode] at boolean
                  · cases found
            · cases decoded : decodeTiny identifier with
              | none => simp [decoded] at found
              | some value =>
                  have equal : Entry.literal value = entry := by simpa [decoded] using found
                  subst entry
                  have typeEqual := typeRef_injective boolean
                  exact False.elim (decodeTiny_not_bool decoded typeEqual)

end Nucleus.Hol.Propane.LiteralRegistry
