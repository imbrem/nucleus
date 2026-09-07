import Nucleus.Hol.Propane.Builtin

/-! # Arithmetic codes for canonical immutable builtin functions

The code assignments mirror the pure Rust registry; aliases have no separate
negative row. This registry is syntax, not evidence of semantic inequality.
-/

namespace Nucleus.Hol.Propane.LiteralRegistry

set_option maxRecDepth 8192

private def widthCode : Width → Nat
  | .i8 => 0 | .i16 => 1 | .i32 => 2 | .i64 => 3

private def boolCode : BoolOp → Nat
  | .not => 0
  | .and => 1
  | .or => 2
  | .imp => 3
  | .iff => 4

private def wordCode : WordOp → Nat
  | .add => 0
  | .sub => 1
  | .mul => 2
  | .divU => 3
  | .divS => 4
  | .remU => 5
  | .remS => 6
  | .and => 7
  | .or => 8
  | .xor => 9
  | .not => 10
  | .shl => 11
  | .shrU => 12
  | .shrS => 13
  | .rotl => 14
  | .rotr => 15
  | .clz => 16
  | .ctz => 17
  | .popcnt => 18
  | .eqz => 19
  | .eq => 20
  | .ne => 21
  | .ltU => 22
  | .leU => 23
  | .gtU => 24
  | .geU => 25
  | .ltS => 26
  | .leS => 27
  | .gtS => 28
  | .geS => 29
  | .extendSign width => 30 + widthCode width

private def natCode : NatOp → Nat
  | .add => 0
  | .sub => 1
  | .mul => 2
  | .div => 3
  | .rem => 4
  | .succ => 5
  | .pred => 6
  | .pow => 7
  | .eq => 8
  | .ne => 9
  | .lt => 10
  | .le => 11
  | .gt => 12
  | .ge => 13
  | .min => 14
  | .max => 15
  | .and => 16
  | .or => 17
  | .xor => 18
  | .shl => 19
  | .shr => 20

private def intCode : IntOp → Nat
  | .add => 0
  | .sub => 1
  | .mul => 2
  | .div => 3
  | .rem => 4
  | .succ => 5
  | .pred => 6
  | .neg => 7
  | .abs => 8
  | .pow => 9
  | .eq => 10
  | .ne => 11
  | .lt => 12
  | .le => 13
  | .gt => 14
  | .ge => 15
  | .min => 16
  | .max => 17
  | .and => 18
  | .or => 19
  | .xor => 20
  | .not => 21
  | .shl => 22
  | .shr => 23

private def bytesCode : BytesOp → Nat
  | .empty => 0
  | .singleton => 1
  | .cons => 2
  | .snoc => 3
  | .append => 4
  | .repeat => 5
  | .length => 6
  | .eq => 7
  | .ne => 8
  | .lt => 9
  | .le => 10
  | .gt => 11
  | .ge => 12
  | .get => 13
  | .set => 14
  | .slice => 15
  | .replace => 16
  | .take => 17
  | .drop => 18
  | .encode width endian => 32 + 2 * widthCode width + (if endian = .little then 0 else 1)
  | .decode width endian => 40 + 2 * widthCode width + (if endian = .little then 0 else 1)
  | .read width endian => 48 + 2 * widthCode width + (if endian = .little then 0 else 1)
  | .write width endian => 56 + 2 * widthCode width + (if endian = .little then 0 else 1)

private def castCode : CastOp → Nat
  | .natToInt => 320 | .intToNat => 321
  | .wordToNat width => 328 + widthCode width
  | .wordToIntU width => 332 + widthCode width
  | .wordToIntS width => 336 + widthCode width
  | .natToWord width => 340 + widthCode width
  | .intToWordU width => 344 + widthCode width
  | .intToWordS width => 348 + widthCode width
  | .natToWordWrap width => 352 + widthCode width
  | .intToWordWrap width => 356 + widthCode width
  | .wordWrap source target => 368 + 4 * widthCode source + widthCode target
  | .wordZeroExtend source target => 384 + 4 * widthCode source + widthCode target
  | .wordSignExtend source target => 400 + 4 * widthCode source + widthCode target

def builtinCode : Builtin → Nat
  | .bool op => boolCode op
  | .word width op => 16 + 40 * widthCode width + wordCode op
  | .nat op => 192 + natCode op
  | .int op => 224 + intCode op
  | .bytes op => 256 + bytesCode op
  | .cast op => castCode op

def canonicalBuiltin : Builtin → Builtin
  | .bytes (.encode .i8 _) => .bytes .singleton
  | .bytes (.decode .i8 _) => .bytes (.decode .i8 .little)
  | .bytes (.read .i8 _) => .bytes (.read .i8 .little)
  | .bytes (.write .i8 _) => .bytes (.write .i8 .little)
  | .cast (.wordZeroExtend source target) =>
      if source = target then .cast (.wordWrap source target)
      else .cast (.wordZeroExtend source target)
  | .cast (.wordSignExtend source target) =>
      if source = target then .cast (.wordWrap source target)
      else .cast (.wordSignExtend source target)
  | op => op

private def widths : List Width := [.i8,
      .i16,
      .i32,
      .i64]
private def endians : List Endian := [.little,
      .big]

def allBuiltins : List Builtin :=
  [.bool .not,
      .bool .and,
      .bool .or,
      .bool .imp,
      .bool .iff] ++
  widths.flatMap (fun width =>
    ([.word width .add,
      .word width .sub,
      .word width .mul,
      .word width .divU,
      .word width .divS,
      .word width .remU,
      .word width .remS,
      .word width .and,
      .word width .or,
      .word width .xor,
      .word width .not,
      .word width .shl,
      .word width .shrU,
      .word width .shrS,
      .word width .rotl,
      .word width .rotr,
      .word width .clz,
      .word width .ctz,
      .word width .popcnt,
      .word width .eqz,
      .word width .eq,
      .word width .ne,
      .word width .ltU,
      .word width .leU,
      .word width .gtU,
      .word width .geU,
      .word width .ltS,
      .word width .leS,
      .word width .gtS,
      .word width .geS] ++
    widths.map (fun source => .word width (.extendSign source)))) ++
  [.nat .add,
      .nat .sub,
      .nat .mul,
      .nat .div,
      .nat .rem,
      .nat .succ,
      .nat .pred,
      .nat .pow,
      .nat .eq,
      .nat .ne,
      .nat .lt,
      .nat .le,
      .nat .gt,
      .nat .ge,
      .nat .min,
      .nat .max,
      .nat .and,
      .nat .or,
      .nat .xor,
      .nat .shl,
      .nat .shr] ++
  [.int .add,
      .int .sub,
      .int .mul,
      .int .div,
      .int .rem,
      .int .succ,
      .int .pred,
      .int .neg,
      .int .abs,
      .int .pow,
      .int .eq,
      .int .ne,
      .int .lt,
      .int .le,
      .int .gt,
      .int .ge,
      .int .min,
      .int .max,
      .int .and,
      .int .or,
      .int .xor,
      .int .not,
      .int .shl,
      .int .shr] ++
  [.bytes .empty,
      .bytes .singleton,
      .bytes .cons,
      .bytes .snoc,
      .bytes .append,
      .bytes .repeat,
      .bytes .length,
      .bytes .eq,
      .bytes .ne,
      .bytes .lt,
      .bytes .le,
      .bytes .gt,
      .bytes .ge,
      .bytes .get,
      .bytes .set,
      .bytes .slice,
      .bytes .replace,
      .bytes .take,
      .bytes .drop] ++
  widths.flatMap (fun width => endians.flatMap (fun endian =>
    [.bytes (.encode width endian),
      .bytes (.decode width endian),
      .bytes (.read width endian),
      .bytes (.write width endian)])) ++
  [.cast .natToInt,
      .cast .intToNat] ++
  widths.flatMap (fun width =>
    [.cast (.wordToNat width),
      .cast (.wordToIntU width),
      .cast (.wordToIntS width),
      .cast (.natToWord width),
      .cast (.intToWordU width),
      .cast (.intToWordS width),
      .cast (.natToWordWrap width),
      .cast (.intToWordWrap width)]) ++
  widths.flatMap (fun source => widths.flatMap (fun target =>
    [.cast (.wordWrap source target),
      .cast (.wordZeroExtend source target),
      .cast (.wordSignExtend source target)]))

def builtinEntries : List (Nat × Builtin) :=
  (allBuiltins.filter (fun op => op.signature.isSome && canonicalBuiltin op == op)).map
    (fun op => (builtinCode op, op))

def decodeBuiltin (code : Nat) : Option Builtin := builtinEntries.lookup code

private theorem lookup_member {α : Type} {entries : List (Nat × α)}
    {code : Nat} {value : α} (found : entries.lookup code = some value) :
    (code, value) ∈ entries := by
  induction entries with
  | nil => simp at found
  | cons entry entries ih =>
      rcases entry with ⟨key, result⟩
      by_cases same : code = key
      · subst key
        have equal : result = value := by simpa using found
        subst result
        exact .head _
      · have different : (code == key) = false := beq_eq_false_iff_ne.mpr same
        simp only [List.lookup_cons, different] at found
        exact .tail _ (ih found)

theorem decodeBuiltin_spec {code : Nat} {op : Builtin}
    (found : decodeBuiltin code = some op) :
    builtinCode op = code ∧ canonicalBuiltin op = op ∧ op.signature.isSome = true := by
  have member := lookup_member found
  obtain ⟨source, sourceMember, equal⟩ := List.mem_map.mp member
  have selected := (List.mem_filter.mp sourceMember).2
  have selected' : source.signature.isSome = true ∧ canonicalBuiltin source = source := by
    simpa using selected
  cases Prod.mk.inj equal with
  | intro codeEqual opEqual =>
      subst source
      exact ⟨codeEqual, selected'.2, selected'.1⟩

theorem allBuiltins_complete (op : Builtin) : op ∈ allBuiltins := by
  cases op with
  | bool op => cases op <;> decide
  | word width op =>
      cases width <;> cases op <;> (try rename_i source; cases source) <;> decide
  | nat op => cases op <;> decide
  | int op => cases op <;> decide
  | bytes op =>
      cases op <;> (try rename_i width endian; cases width <;> cases endian) <;> decide
  | cast op =>
      cases op <;> (try rename_i source target; cases source <;> cases target) <;>
        (try rename_i width; cases width) <;> decide

theorem builtin_codes_nodup : (builtinEntries.map Prod.fst).Nodup := by decide

private theorem lookup_of_member {α : Type} {entries : List (Nat × α)}
    {code : Nat} {value : α} (unique : (entries.map Prod.fst).Nodup)
    (member : (code, value) ∈ entries) : entries.lookup code = some value := by
  induction entries with
  | nil => simp at member
  | cons entry entries ih =>
      rcases entry with ⟨key, result⟩
      have distinct := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        simp
      · have different : code ≠ key := by
          intro same
          apply distinct.1
          exact List.mem_map.mpr ⟨(code, value), member, same⟩
        have notEqual : (code == key) = false := beq_eq_false_iff_ne.mpr different
        simpa only [List.lookup_cons, notEqual] using ih distinct.2 member

theorem decode_builtinCode (op : Builtin) (valid : op.signature.isSome = true)
    (canonical : canonicalBuiltin op = op) : decodeBuiltin (builtinCode op) = some op := by
  apply lookup_of_member builtin_codes_nodup
  apply List.mem_map.mpr
  refine ⟨op, List.mem_filter.mpr ⟨allBuiltins_complete op, ?_⟩, rfl⟩
  simp [valid, canonical]

theorem canonical_code_injective {left right : Builtin}
    (leftValid : left.signature.isSome = true) (rightValid : right.signature.isSome = true)
    (leftCanonical : canonicalBuiltin left = left) (rightCanonical : canonicalBuiltin right = right)
    (equal : builtinCode left = builtinCode right) : left = right := by
  have first := decode_builtinCode left leftValid leftCanonical
  rw [equal, decode_builtinCode right rightValid rightCanonical] at first
  exact (Option.some.inj first).symm

end Nucleus.Hol.Propane.LiteralRegistry
