import Nucleus.Hol.Propane.Syntax
import Mathlib.Data.List.Induction

/-! # Sentinel-prefixed base-eight codes for global function types -/

namespace Nucleus.Hol.Propane.LiteralRegistry

def typeCode : LiteralTy → Nat
  | .bool => 0 | .word .i8 => 1 | .word .i16 => 2
  | .word .i32 => 3 | .word .i64 => 4 | .nat => 5 | .int => 6 | .bytes => 7

def decodeType : Nat → Option LiteralTy
  | 0 => some .bool | 1 => some (.word .i8) | 2 => some (.word .i16)
  | 3 => some (.word .i32) | 4 => some (.word .i64)
  | 5 => some .nat | 6 => some .int | 7 => some .bytes | _ => none

@[simp] theorem decode_typeCode (type : LiteralTy) : decodeType (typeCode type) = some type := by
  cases type with
  | word width => cases width <;> rfl
  | _ => rfl

theorem typeCode_bound (type : LiteralTy) : typeCode type < 8 := by
  cases type with
  | word width => cases width <;> decide
  | _ => decide

theorem decodeType_spec {code : Nat} {type : LiteralTy} (found : decodeType code = some type) :
    typeCode type = code := by
  match code with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => cases found; rfl
  | code + 8 => simp [decodeType] at found

def signatureCode (types : List LiteralTy) : Nat :=
  types.foldl (fun code type => code * 8 + typeCode type) 1

@[simp] theorem signatureCode_nil : signatureCode [] = 1 := rfl

@[simp] theorem signatureCode_append (types : List LiteralTy) (type : LiteralTy) :
    signatureCode (types ++ [type]) = signatureCode types * 8 + typeCode type := by
  simp [signatureCode, List.foldl_append]

theorem signatureCode_positive (types : List LiteralTy) : 0 < signatureCode types := by
  induction types using List.reverseRecOn with
  | nil => decide
  | append_singleton types type ih => rw [signatureCode_append]; omega

/-- Fuel six suffices for the at-most-five types of a registered signature. -/
def decodeSignature : Nat → Nat → Option (List LiteralTy)
  | 0, _ => none
  | fuel + 1, code =>
      if code = 1 then some []
      else do
        let initial ← decodeSignature fuel (code / 8)
        let last ← decodeType (code % 8)
        return initial ++ [last]

theorem decode_signatureCode (types : List LiteralTy) (fuel : Nat)
    (enough : types.length < fuel) :
    decodeSignature fuel (signatureCode types) = some types := by
  induction types using List.reverseRecOn generalizing fuel with
  | nil => cases fuel <;> simp_all [decodeSignature]
  | append_singleton types type ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have positive := signatureCode_positive types
          have bounded := typeCode_bound type
          have different : signatureCode types * 8 + typeCode type ≠ 1 := by omega
          have quotient : (signatureCode types * 8 + typeCode type) / 8 =
              signatureCode types := by omega
          have remainder : (signatureCode types * 8 + typeCode type) % 8 = typeCode type := by omega
          have shorter : types.length < fuel := by
            simp only [List.length_append, List.length_singleton] at enough
            omega
          simp [decodeSignature, different, quotient, remainder, ih fuel shorter]

theorem signatureCode_injective : Function.Injective signatureCode := by
  intro left right equal
  have first := decode_signatureCode left (left.length + right.length + 1) (by omega)
  have second := decode_signatureCode right (left.length + right.length + 1) (by omega)
  rw [equal, second] at first
  exact (Option.some.inj first).symm

theorem decodeSignature_canonical {fuel code : Nat} {types : List LiteralTy}
    (found : decodeSignature fuel code = some types) : signatureCode types = code := by
  induction fuel generalizing code types with
  | zero => simp [decodeSignature] at found
  | succ fuel ih =>
      by_cases sentinel : code = 1
      · subst code
        have empty : types = [] := by simpa [decodeSignature] using found.symm
        subst types
        rfl
      · simp only [decodeSignature, sentinel, ↓reduceIte] at found
        cases initial : decodeSignature fuel (code / 8) with
        | none => simp [initial] at found
        | some prefixTypes =>
            cases last : decodeType (code % 8) with
            | none => simp [initial, last] at found
            | some type =>
                have equal : prefixTypes ++ [type] = types := by simpa [initial, last] using found
                subst types
                rw [signatureCode_append, ih initial, decodeType_spec last]
                simpa [Nat.mul_comm] using Nat.div_add_mod code 8

end Nucleus.Hol.Propane.LiteralRegistry
