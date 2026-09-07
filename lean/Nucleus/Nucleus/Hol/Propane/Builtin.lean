import Nucleus.Hol.Propane.Literal
import Mathlib.Data.Int.Bitwise

/-!
# Literal builtin contract

This is the exhaustive mathematical operation inventory shared with
`crates/logic/hol/src/literals.rs`. Failure is explicit. In particular division
by zero, signed division overflow, failed exact casts, and invalid byte bounds
cannot produce successful reduction evidence. Resource limits are deliberately
absent: they may prevent evaluation but cannot change its mathematical result.
-/

namespace Nucleus.Hol.Propane

inductive WordOp where
  | add | sub | mul | divU | divS | remU | remS | and | or | xor | not
  | shl | shrU | shrS | rotl | rotr | clz | ctz | popcnt | eqz
  | eq | ne | ltU | leU | gtU | geU | ltS | leS | gtS | geS
  | extendSign (source : Width)
  deriving DecidableEq, Repr

inductive NatOp where
  | add | sub | mul | div | rem | succ | pred | pow
  | eq | ne | lt | le | gt | ge | min | max | and | or | xor | shl | shr
  deriving DecidableEq, Repr

inductive IntOp where
  | add | sub | mul | div | rem | succ | pred | neg | abs | pow
  | eq | ne | lt | le | gt | ge | min | max | and | or | xor | not | shl | shr
  deriving DecidableEq, Repr

inductive Endian where
  | little | big
  deriving DecidableEq, Repr

inductive BytesOp where
  | empty | singleton | cons | snoc | append | repeat | length
  | eq | ne | lt | le | gt | ge | get | set | slice | replace | take | drop
  | encode (width : Width) (endian : Endian)
  | decode (width : Width) (endian : Endian)
  | read (width : Width) (endian : Endian)
  | write (width : Width) (endian : Endian)
  deriving DecidableEq, Repr

inductive CastOp where
  | natToInt | intToNat
  | wordToNat (width : Width) | wordToIntU (width : Width) | wordToIntS (width : Width)
  | natToWord (width : Width) | intToWordU (width : Width) | intToWordS (width : Width)
  | natToWordWrap (width : Width) | intToWordWrap (width : Width)
  | wordWrap (source target : Width) | wordZeroExtend (source target : Width)
  | wordSignExtend (source target : Width)
  deriving DecidableEq, Repr

inductive Builtin where
  | word (width : Width) (op : WordOp)
  | nat (op : NatOp) | int (op : IntOp) | bytes (op : BytesOp) | cast (op : CastOp)
  deriving DecidableEq, Repr

def WordOp.unary : WordOp → Bool
  | .not | .clz | .ctz | .popcnt | .eqz | .extendSign _ => true
  | _ => false

def WordOp.comparison : WordOp → Bool
  | .eqz | .eq | .ne | .ltU | .leU | .gtU | .geU | .ltS | .leS | .gtS | .geS => true
  | _ => false

def NatOp.comparison : NatOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

def IntOp.comparison : IntOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

def Builtin.signature : Builtin → Option (List LiteralTy × LiteralTy)
  | .word width op => do
      if let .extendSign source := op then
        if source.bits ≥ width.bits then none else pure ()
      let inputs := List.replicate (if op.unary then 1 else 2) (.word width)
      return (inputs, if op.comparison then .bool else .word width)
  | .nat op =>
      some (List.replicate (if op = .succ ∨ op = .pred then 1 else 2) .nat,
        if op.comparison then .bool else .nat)
  | .int op =>
      let inputs := if op = .succ ∨ op = .pred ∨ op = .neg ∨ op = .abs ∨ op = .not
        then [.int] else if op = .pow ∨ op = .shl ∨ op = .shr then [.int, .nat]
        else [.int, .int]
      some (inputs, if op.comparison then .bool else if op = .abs then .nat else .int)
  | .bytes op => some <| match op with
      | .empty => ([], .bytes)
      | .singleton => ([.word .i8], .bytes)
      | .cons => ([.word .i8, .bytes], .bytes)
      | .snoc => ([.bytes, .word .i8], .bytes)
      | .append => ([.bytes, .bytes], .bytes)
      | .repeat => ([.word .i8, .nat], .bytes)
      | .length => ([.bytes], .nat)
      | .eq | .ne | .lt | .le | .gt | .ge => ([.bytes, .bytes], .bool)
      | .get => ([.bytes, .nat], .word .i8)
      | .set => ([.bytes, .nat, .word .i8], .bytes)
      | .slice => ([.bytes, .nat, .nat], .bytes)
      | .replace => ([.bytes, .nat, .nat, .bytes], .bytes)
      | .take | .drop => ([.bytes, .nat], .bytes)
      | .encode width _ => ([.word width], .bytes)
      | .decode width _ => ([.bytes], .word width)
      | .read width _ => ([.bytes, .nat], .word width)
      | .write width _ => ([.bytes, .nat, .word width], .bytes)
  | .cast op => match op with
      | .natToInt => some ([.nat], .int)
      | .intToNat => some ([.int], .nat)
      | .wordToNat width => some ([.word width], .nat)
      | .wordToIntU width | .wordToIntS width => some ([.word width], .int)
      | .natToWord width | .natToWordWrap width => some ([.nat], .word width)
      | .intToWordU width | .intToWordS width | .intToWordWrap width =>
          some ([.int], .word width)
      | .wordWrap source target =>
          if target.bits ≤ source.bits then some ([.word source], .word target) else none
      | .wordZeroExtend source target | .wordSignExtend source target =>
          if source.bits ≤ target.bits then some ([.word source], .word target) else none

private def operand (args : List LiteralValue) (type : LiteralTy) (index : Nat) :
    Option type.denote := do (← args[index]?).as type

def WordOp.eval (width : Width) (op : WordOp) (args : List LiteralValue) :
    Option LiteralValue := do
  let left ← operand args (.word width) 0
  let word := LiteralValue.word width
  match op with
  | .not => return word (~~~left)
  | .clz => return word left.clz
  | .ctz => return word left.ctz
  | .popcnt => return word left.cpop
  | .eqz => return .bool (left == 0)
  | .extendSign source =>
      if source.bits ≥ width.bits then none
      else return word (BitVec.ofInt width.bits (BitVec.ofNat source.bits left.toNat).toInt)
  | op =>
      let right ← operand args (.word width) 1
      let shift := right.toNat % width.bits
      match op with
      | .add => return word (left + right)
      | .sub => return word (left - right)
      | .mul => return word (left * right)
      | .divU => if right = 0 then none else return word (left.udiv right)
      | .divS =>
          if right = 0 ∨ left.sdivOverflow right then none
          else return word (left.sdiv right)
      | .remU => if right = 0 then none else return word (left.umod right)
      | .remS => if right = 0 then none else return word (left.srem right)
      | .and => return word (left &&& right)
      | .or => return word (left ||| right)
      | .xor => return word (left ^^^ right)
      | .shl => return word (left <<< shift)
      | .shrU => return word (left >>> shift)
      | .shrS => return word (left.sshiftRight shift)
      | .rotl => return word (left.rotateLeft shift)
      | .rotr => return word (left.rotateRight shift)
      | .eq => return .bool (left == right)
      | .ne => return .bool (left != right)
      | .ltU => return .bool (left.ult right)
      | .leU => return .bool (left.ule right)
      | .gtU => return .bool (right.ult left)
      | .geU => return .bool (right.ule left)
      | .ltS => return .bool (left.slt right)
      | .leS => return .bool (left.sle right)
      | .gtS => return .bool (right.slt left)
      | .geS => return .bool (right.sle left)
      | _ => none

def NatOp.eval (op : NatOp) (args : List LiteralValue) : Option LiteralValue := do
  let left ← operand args .nat 0
  match op with
  | .succ => return .nat (left + 1)
  | .pred => return .nat (left - 1)
  | op =>
      let right ← operand args .nat 1
      match op with
      | .add => return .nat (left + right)
      | .sub => return .nat (left - right)
      | .mul => return .nat (left * right)
      | .div => if right = 0 then none else return .nat (left / right)
      | .rem => if right = 0 then none else return .nat (left % right)
      | .pow => return .nat (left ^ right)
      | .eq => return .bool (left == right)
      | .ne => return .bool (left != right)
      | .lt => return .bool (left < right)
      | .le => return .bool (left ≤ right)
      | .gt => return .bool (left > right)
      | .ge => return .bool (left ≥ right)
      | .min => return .nat (Min.min left right)
      | .max => return .nat (Max.max left right)
      | .and => return .nat (left &&& right)
      | .or => return .nat (left ||| right)
      | .xor => return .nat (left ^^^ right)
      | .shl => return .nat (left <<< right)
      | .shr => return .nat (left >>> right)
      | _ => none

def IntOp.eval (op : IntOp) (args : List LiteralValue) : Option LiteralValue := do
  let left ← operand args .int 0
  match op with
  | .succ => return .int (left + 1)
  | .pred => return .int (left - 1)
  | .neg => return .int (-left)
  | .abs => return .nat left.natAbs
  | .not => return .int (~~~left)
  | .pow | .shl | .shr =>
      let count ← operand args .nat 1
      match op with
      | .pow => return .int (left ^ count)
      | .shl => return .int (left <<< count)
      | _ => return .int (left >>> count)
  | op =>
      let right ← operand args .int 1
      match op with
      | .add => return .int (left + right)
      | .sub => return .int (left - right)
      | .mul => return .int (left * right)
      | .div => if right = 0 then none else return .int (left.tdiv right)
      | .rem => if right = 0 then none else return .int (left.tmod right)
      | .eq => return .bool (left == right)
      | .ne => return .bool (left != right)
      | .lt => return .bool (left < right)
      | .le => return .bool (left ≤ right)
      | .gt => return .bool (left > right)
      | .ge => return .bool (left ≥ right)
      | .min => return .int (Min.min left right)
      | .max => return .int (Max.max left right)
      | .and => return .int (Int.land left right)
      | .or => return .int (Int.lor left right)
      | .xor => return .int (Int.xor left right)
      | _ => none

def encodeWord (width : Width) (endian : Endian) (value : BitVec width.bits) : List UInt8 :=
  let little := (List.range (width.bits / 8)).map
    (fun index => UInt8.ofNat (value.toNat >>> (8 * index)))
  match endian with | .little => little | .big => little.reverse

def decodeWord (width : Width) (endian : Endian) (bytes : List UInt8) :
    Option (BitVec width.bits) :=
  if bytes.length = width.bits / 8 then
    let big := match endian with | .little => bytes.reverse | .big => bytes
    some (BitVec.ofNat width.bits (big.foldl (fun value byte => value * 256 + byte.toNat) 0))
  else none

private def sliceBytes (bytes : List UInt8) (start length : Nat) : Option (List UInt8) :=
  if start + length ≤ bytes.length then some ((bytes.drop start).take length) else none

private def replaceBytes (bytes : List UInt8) (start length : Nat)
    (replacement : List UInt8) : Option (List UInt8) :=
  if start + length ≤ bytes.length then
    some (bytes.take start ++ replacement ++ bytes.drop (start + length)) else none

private def lexBytes : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: lefts, right :: rights =>
      if left < right then .lt else if right < left then .gt else lexBytes lefts rights

def BytesOp.eval (op : BytesOp) (args : List LiteralValue) : Option LiteralValue := do
  match op with
  | .empty => return .bytes []
  | .singleton => return .bytes [(← operand args (.word .i8) 0).toNat.toUInt8]
  | .cons => return .bytes ((← operand args (.word .i8) 0).toNat.toUInt8 ::
      (← operand args .bytes 1))
  | .snoc => return .bytes ((← operand args .bytes 0) ++
      [(← operand args (.word .i8) 1).toNat.toUInt8])
  | .append => return .bytes ((← operand args .bytes 0) ++ (← operand args .bytes 1))
  | .repeat => return .bytes (List.replicate (← operand args .nat 1)
      (← operand args (.word .i8) 0).toNat.toUInt8)
  | .length => return .nat (← operand args .bytes 0).length
  | .eq | .ne | .lt | .le | .gt | .ge =>
      let left ← operand args .bytes 0
      let right ← operand args .bytes 1
      let order := lexBytes left right
      return .bool (match op with
        | .eq => left == right | .ne => left != right
        | .lt => order == .lt | .le => order != .gt
        | .gt => order == .gt | _ => order != .lt)
  | .get =>
      let bytes ← operand args .bytes 0
      let index ← operand args .nat 1
      return .word .i8 (← bytes[index]?).toBitVec
  | .set =>
      let bytes ← operand args .bytes 0
      let index ← operand args .nat 1
      let value ← operand args (.word .i8) 2
      if index < bytes.length then return .bytes (bytes.set index value.toNat.toUInt8) else none
  | .slice => return .bytes (← sliceBytes (← operand args .bytes 0)
      (← operand args .nat 1) (← operand args .nat 2))
  | .replace => return .bytes (← replaceBytes (← operand args .bytes 0)
      (← operand args .nat 1) (← operand args .nat 2) (← operand args .bytes 3))
  | .take => return .bytes ((← operand args .bytes 0).take (← operand args .nat 1))
  | .drop => return .bytes ((← operand args .bytes 0).drop (← operand args .nat 1))
  | .encode width endian => return .bytes (encodeWord width endian (← operand args (.word width) 0))
  | .decode width endian =>
      return .word width (← decodeWord width endian (← operand args .bytes 0))
  | .read width endian =>
      let selected ← sliceBytes (← operand args .bytes 0) (← operand args .nat 1) (width.bits / 8)
      return .word width (← decodeWord width endian selected)
  | .write width endian =>
      let value := encodeWord width endian (← operand args (.word width) 2)
      return .bytes (← replaceBytes (← operand args .bytes 0) (← operand args .nat 1)
        (width.bits / 8) value)

def CastOp.eval (op : CastOp) (args : List LiteralValue) : Option LiteralValue := do
  match op with
  | .natToInt => return .int (← operand args .nat 0)
  | .intToNat =>
      let value ← operand args .int 0
      if value < 0 then none else return .nat value.toNat
  | .wordToNat width => return .nat (← operand args (.word width) 0).toNat
  | .wordToIntU width => return .int (← operand args (.word width) 0).toNat
  | .wordToIntS width => return .int (← operand args (.word width) 0).toInt
  | .natToWord width =>
      let value ← operand args .nat 0
      if value < 2 ^ width.bits then return .word width (BitVec.ofNat width.bits value) else none
  | .intToWordU width =>
      let value ← operand args .int 0
      if 0 ≤ value ∧ value < 2 ^ width.bits then
        return .word width (BitVec.ofInt width.bits value) else none
  | .intToWordS width =>
      let value ← operand args .int 0
      if -(2 ^ (width.bits - 1)) ≤ value ∧ value < 2 ^ (width.bits - 1) then
        return .word width (BitVec.ofInt width.bits value) else none
  | .natToWordWrap width =>
      return .word width (BitVec.ofNat width.bits (← operand args .nat 0))
  | .intToWordWrap width =>
      return .word width (BitVec.ofInt width.bits (← operand args .int 0))
  | .wordWrap source target =>
      if target.bits ≤ source.bits then
        return .word target (BitVec.ofNat target.bits
          (← operand args (.word source) 0).toNat) else none
  | .wordZeroExtend source target =>
      if source.bits ≤ target.bits then
        return .word target (BitVec.ofNat target.bits
          (← operand args (.word source) 0).toNat) else none
  | .wordSignExtend source target =>
      if source.bits ≤ target.bits then
        return .word target (BitVec.ofInt target.bits
          (← operand args (.word source) 0).toInt) else none

def Builtin.evalRaw : Builtin → List LiteralValue → Option LiteralValue
  | .word width op => op.eval width
  | .nat op => op.eval
  | .int op => op.eval
  | .bytes op => op.eval
  | .cast op => op.eval

/-- The successful mathematical reduction boundary checks the entire signature. -/
def Builtin.eval (op : Builtin) (args : List LiteralValue) : Option LiteralValue := do
  let (inputs, output) ← op.signature
  if args.map LiteralValue.type ≠ inputs then none else do
    let result ← op.evalRaw args
    if result.type = output then some result else none

theorem Builtin.eval_typed {op : Builtin} {args : List LiteralValue} {result : LiteralValue}
    (evaluates : op.eval args = some result) :
    op.signature = some (args.map LiteralValue.type, result.type) := by
  unfold eval at evaluates
  cases sig : op.signature with
  | none => simp [sig] at evaluates
  | some pair =>
      rcases pair with ⟨inputs, output⟩
      simp only [sig, bind, Option.bind] at evaluates
      split at evaluates
      · contradiction
      · rename_i inputTypes
        cases raw : op.evalRaw args with
        | none => simp [raw] at evaluates
        | some value =>
            simp only [raw] at evaluates
            split at evaluates
            · rename_i resultType
              cases Option.some.inj evaluates
              simp_all
            · contradiction

end Nucleus.Hol.Propane
