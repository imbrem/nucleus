//! Concrete literal values and the regular builtin vocabulary.
//!
//! Fixed integers are bit patterns; signedness belongs to operations. Partial
//! operations decline reduction. Resource limits are operational errors and
//! never values of the logic.
// Local enum imports keep the exhaustive operation tables readable.
#![allow(clippy::enum_glob_use)]

use covalence_data_num::{Int, Num};
use serde::{Deserialize, Serialize};

/// The supported fixed widths.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum WordWidth {
    W8,
    W16,
    W32,
    W64,
}
impl WordWidth {
    /// Number of bits.
    #[must_use]
    pub const fn bits(self) -> u32 {
        match self {
            Self::W8 => 8,
            Self::W16 => 16,
            Self::W32 => 32,
            Self::W64 => 64,
        }
    }
    /// Corresponding literal type.
    #[must_use]
    pub const fn ty(self) -> LiteralType {
        match self {
            Self::W8 => LiteralType::I8,
            Self::W16 => LiteralType::I16,
            Self::W32 => LiteralType::I32,
            Self::W64 => LiteralType::I64,
        }
    }
    fn mask(self) -> u64 {
        u64::MAX >> (64 - self.bits())
    }
}
/// The intrinsic literal carriers.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum LiteralType {
    Bool,
    I8,
    I16,
    I32,
    I64,
    Nat,
    Int,
    Bytes,
}
/// Semantic values; arena allocation is private.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LiteralValue {
    Bool(bool),
    I8(u8),
    I16(u16),
    I32(u32),
    I64(u64),
    Nat(Num),
    Int(Int),
    Bytes(bytes::Bytes),
}
impl LiteralValue {
    /// The value's carrier.
    #[must_use]
    pub const fn ty(&self) -> LiteralType {
        match self {
            Self::Bool(_) => LiteralType::Bool,
            Self::I8(_) => LiteralType::I8,
            Self::I16(_) => LiteralType::I16,
            Self::I32(_) => LiteralType::I32,
            Self::I64(_) => LiteralType::I64,
            Self::Nat(_) => LiteralType::Nat,
            Self::Int(_) => LiteralType::Int,
            Self::Bytes(_) => LiteralType::Bytes,
        }
    }
    /// Constructs a bit pattern, explicitly truncating high bits.
    #[must_use]
    pub fn wrapping_word(width: WordWidth, bits: u64) -> Self {
        let bytes = bits.to_le_bytes();
        match width {
            WordWidth::W8 => Self::I8(bytes[0]),
            WordWidth::W16 => Self::I16(u16::from_le_bytes([bytes[0], bytes[1]])),
            WordWidth::W32 => {
                Self::I32(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
            }
            WordWidth::W64 => Self::I64(bits),
        }
    }
    /// Unsigned bits of a fixed integer.
    #[must_use]
    pub fn word_bits(&self) -> Option<u64> {
        match self {
            Self::I8(x) => Some(u64::from(*x)),
            Self::I16(x) => Some(u64::from(*x)),
            Self::I32(x) => Some(u64::from(*x)),
            Self::I64(x) => Some(*x),
            _ => None,
        }
    }
}
/// Operations shared by all four fixed widths.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum WordOp {
    Add,
    Sub,
    Mul,
    DivU,
    DivS,
    RemU,
    RemS,
    And,
    Or,
    Xor,
    Not,
    Shl,
    ShrU,
    ShrS,
    Rotl,
    Rotr,
    Clz,
    Ctz,
    Popcnt,
    Eqz,
    Eq,
    Ne,
    LtU,
    LeU,
    GtU,
    GeU,
    LtS,
    LeS,
    GtS,
    GeS,
    ExtendSign(WordWidth),
}
/// Natural operations. Subtraction and predecessor truncate at zero.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum NatOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Succ,
    Pred,
    Pow,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Min,
    Max,
    And,
    Or,
    Xor,
    Shl,
    Shr,
}
/// Integer operations. Division truncates toward zero; shifts sign extend.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum IntOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Succ,
    Pred,
    Neg,
    Abs,
    Pow,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Min,
    Max,
    And,
    Or,
    Xor,
    Not,
    Shl,
    Shr,
}
/// Byte order for fixed word codecs.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Endian {
    Little,
    Big,
}
/// Finite-octet-list operations.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum BytesOp {
    Empty,
    Singleton,
    Cons,
    Snoc,
    Append,
    Repeat,
    Length,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Get,
    Set,
    Slice,
    Replace,
    Take,
    Drop,
    Encode(WordWidth, Endian),
    Decode(WordWidth, Endian),
    Read(WordWidth, Endian),
    Write(WordWidth, Endian),
}
/// Explicit conversions; wrapping is always named.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum CastOp {
    NatToInt,
    IntToNat,
    WordToNat(WordWidth),
    WordToIntU(WordWidth),
    WordToIntS(WordWidth),
    NatToWord(WordWidth),
    IntToWordU(WordWidth),
    IntToWordS(WordWidth),
    NatToWordWrap(WordWidth),
    IntToWordWrap(WordWidth),
    WordWrap(WordWidth, WordWidth),
    WordZeroExtend(WordWidth, WordWidth),
    WordSignExtend(WordWidth, WordWidth),
}
/// Closed regular builtin vocabulary.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Builtin {
    Bool(BoolOp),
    Word(WordWidth, WordOp),
    Nat(NatOp),
    Int(IntOp),
    Bytes(BytesOp),
    Cast(CastOp),
}
/// Boolean functions; equality and equivalence share `Iff`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum BoolOp {
    Not,
    And,
    Or,
    Imp,
    Iff,
}
/// Resource bounds for one concrete evaluation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EvalLimits {
    /// Maximum bytestring length or numeric magnitude size rounded up to bytes.
    /// This bounds each value, not total memory or its serialized sign padding.
    pub max_bytes: usize,
    /// Maximum exponent or shift work.
    pub max_steps: u32,
}
impl Default for EvalLimits {
    fn default() -> Self {
        Self {
            max_bytes: 1024 * 1024,
            max_steps: 1_000_000,
        }
    }
}
/// A reduction declined without producing a theorem.
#[derive(Clone, Debug, Eq, PartialEq, covalence_lib_error::snafu::Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum EvalError {
    /// Incorrect arity or operand types.
    #[snafu(display("builtin signature mismatch"))]
    Signature,
    /// A mathematical operation is outside its successful domain.
    #[snafu(display("builtin is undefined for these operands"))]
    Undefined,
    /// A caller resource bound was exceeded.
    #[snafu(display("builtin resource limit exceeded"))]
    Resource,
}
impl Builtin {
    /// Exact operand and result carriers.
    /// # Errors
    /// Rejects impossible width-extension descriptors.
    #[expect(
        clippy::too_many_lines,
        reason = "one exhaustive, auditable builtin signature inventory"
    )]
    pub fn signature(self) -> Result<(Vec<LiteralType>, LiteralType), EvalError> {
        use LiteralType::{Bool, Bytes, I8, Int, Nat};
        let pair = match self {
            Self::Bool(op) => (vec![Bool; if op == BoolOp::Not { 1 } else { 2 }], Bool),
            Self::Word(w, op) => {
                use WordOp::*;
                if let ExtendSign(from) = op
                    && from.bits() >= w.bits()
                {
                    return Err(EvalError::Signature);
                }
                let n = if matches!(op, Not | Clz | Ctz | Popcnt | Eqz | ExtendSign(_)) {
                    1
                } else {
                    2
                };
                (
                    vec![w.ty(); n],
                    if matches!(
                        op,
                        Eqz | Eq | Ne | LtU | LeU | GtU | GeU | LtS | LeS | GtS | GeS
                    ) {
                        Bool
                    } else {
                        w.ty()
                    },
                )
            }
            Self::Nat(op) => {
                use NatOp::*;
                (
                    vec![Nat; if matches!(op, Succ | Pred) { 1 } else { 2 }],
                    if matches!(op, Eq | Ne | Lt | Le | Gt | Ge) {
                        Bool
                    } else {
                        Nat
                    },
                )
            }
            Self::Int(op) => {
                use IntOp::*;
                let args = if matches!(op, Succ | Pred | Neg | Abs | Not) {
                    vec![Int]
                } else if matches!(op, Pow | Shl | Shr) {
                    vec![Int, Nat]
                } else {
                    vec![Int, Int]
                };
                (
                    args,
                    if matches!(op, Eq | Ne | Lt | Le | Gt | Ge) {
                        Bool
                    } else if matches!(op, Abs) {
                        Nat
                    } else {
                        Int
                    },
                )
            }
            Self::Bytes(op) => {
                use BytesOp::*;
                match op {
                    Empty => (vec![], Bytes),
                    Singleton => (vec![I8], Bytes),
                    Cons => (vec![I8, Bytes], Bytes),
                    Snoc => (vec![Bytes, I8], Bytes),
                    Append => (vec![Bytes, Bytes], Bytes),
                    Repeat => (vec![I8, Nat], Bytes),
                    Length => (vec![Bytes], Nat),
                    Eq | Ne | Lt | Le | Gt | Ge => (vec![Bytes, Bytes], Bool),
                    Get => (vec![Bytes, Nat], I8),
                    Set => (vec![Bytes, Nat, I8], Bytes),
                    Slice => (vec![Bytes, Nat, Nat], Bytes),
                    Replace => (vec![Bytes, Nat, Nat, Bytes], Bytes),
                    Take | Drop => (vec![Bytes, Nat], Bytes),
                    Encode(w, _) => (vec![w.ty()], Bytes),
                    Decode(w, _) => (vec![Bytes], w.ty()),
                    Read(w, _) => (vec![Bytes, Nat], w.ty()),
                    Write(w, _) => (vec![Bytes, Nat, w.ty()], Bytes),
                }
            }
            Self::Cast(op) => {
                use CastOp::*;
                match op {
                    NatToInt => (vec![Nat], Int),
                    IntToNat => (vec![Int], Nat),
                    WordToNat(w) => (vec![w.ty()], Nat),
                    WordToIntU(w) | WordToIntS(w) => (vec![w.ty()], Int),
                    NatToWord(w) | NatToWordWrap(w) => (vec![Nat], w.ty()),
                    IntToWordU(w) | IntToWordS(w) | IntToWordWrap(w) => (vec![Int], w.ty()),
                    WordWrap(a, b) | WordZeroExtend(a, b) | WordSignExtend(a, b) => {
                        if (matches!(op, WordWrap(..)) && b.bits() > a.bits())
                            || (!matches!(op, WordWrap(..)) && b.bits() < a.bits())
                        {
                            return Err(EvalError::Signature);
                        }
                        (vec![a.ty()], b.ty())
                    }
                }
            }
        };
        Ok(pair)
    }
    /// Evaluates literal arguments without creating kernel facts.
    /// # Errors
    /// Returns signature, undefined-operation, or resource errors.
    pub fn evaluate(
        self,
        args: &[LiteralValue],
        limits: EvalLimits,
    ) -> Result<LiteralValue, EvalError> {
        let (inputs, output) = self.signature()?;
        if inputs.len() != args.len() || !inputs.iter().zip(args).all(|(t, v)| *t == v.ty()) {
            return Err(EvalError::Signature);
        }
        for arg in args {
            check_size(arg, limits)?;
        }
        let result = match self {
            Self::Bool(op) => {
                let LiteralValue::Bool(left) = args[0] else {
                    return Err(EvalError::Signature);
                };
                let right = if let Some(LiteralValue::Bool(value)) = args.get(1) {
                    *value
                } else {
                    false
                };
                LiteralValue::Bool(match op {
                    BoolOp::Not => !left,
                    BoolOp::And => left && right,
                    BoolOp::Or => left || right,
                    BoolOp::Imp => !left || right,
                    BoolOp::Iff => left == right,
                })
            }
            Self::Word(w, o) => eval_word(w, o, args)?,
            Self::Nat(o) => eval_nat(o, args, limits)?,
            Self::Int(o) => eval_int(o, args, limits)?,
            Self::Bytes(o) => eval_bytes(o, args, limits)?,
            Self::Cast(o) => eval_cast(o, args)?,
        };
        if result.ty() != output {
            return Err(EvalError::Signature);
        }
        check_size(&result, limits)?;
        Ok(result)
    }
}
pub(crate) fn check_size(value: &LiteralValue, l: EvalLimits) -> Result<(), EvalError> {
    let n = match value {
        LiteralValue::Nat(x) => usize::try_from(x.bits().div_ceil(8)).unwrap_or(usize::MAX),
        LiteralValue::Int(x) => usize::try_from(x.bits().div_ceil(8)).unwrap_or(usize::MAX),
        LiteralValue::Bytes(x) => x.len(),
        _ => 0,
    };
    if n > l.max_bytes {
        Err(EvalError::Resource)
    } else {
        Ok(())
    }
}
fn word(v: &LiteralValue) -> u64 {
    v.word_bits().expect("signature checked")
}
fn signed(w: WordWidth, v: u64) -> i64 {
    i64::from_ne_bytes((v << (64 - w.bits())).to_ne_bytes()) >> (64 - w.bits())
}
fn nat(v: &LiteralValue) -> &Num {
    let LiteralValue::Nat(n) = v else {
        unreachable!("signature checked")
    };
    n
}
fn int(v: &LiteralValue) -> &Int {
    let LiteralValue::Int(n) = v else {
        unreachable!("signature checked")
    };
    n
}
fn bytes(v: &LiteralValue) -> &bytes::Bytes {
    let LiteralValue::Bytes(n) = v else {
        unreachable!("signature checked")
    };
    n
}
fn count(v: &LiteralValue) -> Result<usize, EvalError> {
    usize::try_from(nat(v)).map_err(|_| EvalError::Resource)
}

fn eval_word(w: WordWidth, op: WordOp, args: &[LiteralValue]) -> Result<LiteralValue, EvalError> {
    use WordOp::*;
    let a = word(&args[0]);
    let b = args.get(1).map_or(0, word);
    let n = w.bits();
    let shift = u32::try_from(b % u64::from(n)).expect("masked count");
    let sa = signed(w, a);
    let sb = signed(w, b);
    let boolean = match op {
        Eqz => Some(a == 0),
        Eq => Some(a == b),
        Ne => Some(a != b),
        LtU => Some(a < b),
        LeU => Some(a <= b),
        GtU => Some(a > b),
        GeU => Some(a >= b),
        LtS => Some(sa < sb),
        LeS => Some(sa <= sb),
        GtS => Some(sa > sb),
        GeS => Some(sa >= sb),
        _ => None,
    };
    if let Some(result) = boolean {
        return Ok(LiteralValue::Bool(result));
    }
    let value = match op {
        Add => a.wrapping_add(b),
        Sub => a.wrapping_sub(b),
        Mul => a.wrapping_mul(b),
        And => a & b,
        Or => a | b,
        Xor => a ^ b,
        Not => !a,
        DivU => a.checked_div(b).ok_or(EvalError::Undefined)?,
        RemU => a.checked_rem(b).ok_or(EvalError::Undefined)?,
        DivS => {
            if sb == 0 || (sa == signed(w, 1 << (n - 1)) && sb == -1) {
                return Err(EvalError::Undefined);
            }
            u64::from_ne_bytes((sa / sb).to_ne_bytes())
        }
        RemS => {
            if sb == 0 {
                return Err(EvalError::Undefined);
            }
            u64::from_ne_bytes(sa.checked_rem(sb).unwrap_or(0).to_ne_bytes())
        }
        Shl => a << shift,
        ShrU => a >> shift,
        ShrS => u64::from_ne_bytes((sa >> shift).to_ne_bytes()),
        Rotl => {
            if shift == 0 {
                a
            } else {
                (a << shift) | (a >> (n - shift))
            }
        }
        Rotr => {
            if shift == 0 {
                a
            } else {
                (a >> shift) | (a << (n - shift))
            }
        }
        Clz => u64::from(a.leading_zeros() - (64 - n)),
        Ctz => u64::from(a.trailing_zeros().min(n)),
        Popcnt => u64::from(a.count_ones()),
        ExtendSign(from) => u64::from_ne_bytes(signed(from, a & from.mask()).to_ne_bytes()),
        Eqz | Eq | Ne | LtU | LeU | GtU | GeU | LtS | LeS | GtS | GeS => {
            unreachable!("comparison returned")
        }
    };
    Ok(LiteralValue::wrapping_word(w, value))
}
fn growth(bits: u64, factor: u64, limits: EvalLimits) -> Result<(), EvalError> {
    if bits.saturating_mul(factor)
        > u64::try_from(limits.max_bytes)
            .unwrap_or(u64::MAX)
            .saturating_mul(8)
    {
        Err(EvalError::Resource)
    } else {
        Ok(())
    }
}
fn work_count(v: &LiteralValue, l: EvalLimits) -> Result<u32, EvalError> {
    let n = u32::try_from(nat(v)).map_err(|_| EvalError::Resource)?;
    if n > l.max_steps {
        Err(EvalError::Resource)
    } else {
        Ok(n)
    }
}
fn eval_nat(op: NatOp, args: &[LiteralValue], l: EvalLimits) -> Result<LiteralValue, EvalError> {
    use NatOp::*;
    let a = nat(&args[0]);
    let b = args.get(1).map(nat);
    let one = Num::from(1u8);
    let cmp = match op {
        Eq => Some(a == b.unwrap()),
        Ne => Some(a != b.unwrap()),
        Lt => Some(a < b.unwrap()),
        Le => Some(a <= b.unwrap()),
        Gt => Some(a > b.unwrap()),
        Ge => Some(a >= b.unwrap()),
        _ => None,
    };
    if let Some(v) = cmp {
        return Ok(LiteralValue::Bool(v));
    }
    let value = match op {
        Succ => a + &one,
        Pred => a.checked_sub(&one).unwrap_or(Num::ZERO),
        Add => a + b.unwrap(),
        Sub => a.checked_sub(b.unwrap()).unwrap_or(Num::ZERO),
        Mul => {
            growth(a.bits().saturating_add(b.unwrap().bits()), 1, l)?;
            a * b.unwrap()
        }
        Div => a.div_rem(b.unwrap()).map_err(|_| EvalError::Undefined)?.0,
        Rem => a.div_rem(b.unwrap()).map_err(|_| EvalError::Undefined)?.1,
        Pow => {
            let e = work_count(&args[1], l)?;
            growth(a.bits(), u64::from(e), l)?;
            a.pow(e)
        }
        Min => a.min(b.unwrap()).clone(),
        Max => a.max(b.unwrap()).clone(),
        And => a & b.unwrap(),
        Or => a | b.unwrap(),
        Xor => a ^ b.unwrap(),
        Shl => {
            let e = work_count(&args[1], l)?;
            growth(a.bits().saturating_add(u64::from(e)), 1, l)?;
            a << usize::try_from(e).map_err(|_| EvalError::Resource)?
        }
        Shr => {
            let e = work_count(&args[1], l)?;
            a >> usize::try_from(e).map_err(|_| EvalError::Resource)?
        }
        Eq | Ne | Lt | Le | Gt | Ge => unreachable!("comparison returned"),
    };
    Ok(LiteralValue::Nat(value))
}
fn eval_int(op: IntOp, args: &[LiteralValue], l: EvalLimits) -> Result<LiteralValue, EvalError> {
    use IntOp::*;
    let a = int(&args[0]);
    let b = args.get(1).and_then(|v| {
        if let LiteralValue::Int(n) = v {
            Some(n)
        } else {
            None
        }
    });
    let one = Int::from(1i8);
    if op == Abs {
        return Ok(LiteralValue::Nat(a.magnitude()));
    }
    let cmp = match op {
        Eq => Some(a == b.unwrap()),
        Ne => Some(a != b.unwrap()),
        Lt => Some(a < b.unwrap()),
        Le => Some(a <= b.unwrap()),
        Gt => Some(a > b.unwrap()),
        Ge => Some(a >= b.unwrap()),
        _ => None,
    };
    if let Some(v) = cmp {
        return Ok(LiteralValue::Bool(v));
    }
    let value = match op {
        Succ => a + &one,
        Pred => a - &one,
        Neg => -a,
        Add => a + b.unwrap(),
        Sub => a - b.unwrap(),
        Mul => {
            growth(a.bits().saturating_add(b.unwrap().bits()), 1, l)?;
            a * b.unwrap()
        }
        Div => a.div_rem(b.unwrap()).map_err(|_| EvalError::Undefined)?.0,
        Rem => a.div_rem(b.unwrap()).map_err(|_| EvalError::Undefined)?.1,
        Pow => {
            let e = work_count(&args[1], l)?;
            growth(a.bits(), u64::from(e), l)?;
            a.pow(e)
        }
        Min => a.min(b.unwrap()).clone(),
        Max => a.max(b.unwrap()).clone(),
        And => a & b.unwrap(),
        Or => a | b.unwrap(),
        Xor => a ^ b.unwrap(),
        Not => !a,
        Shl => {
            let e = work_count(&args[1], l)?;
            growth(a.bits().saturating_add(u64::from(e)), 1, l)?;
            a << usize::try_from(e).map_err(|_| EvalError::Resource)?
        }
        Shr => {
            let e = work_count(&args[1], l)?;
            a >> usize::try_from(e).map_err(|_| EvalError::Resource)?
        }
        Abs | Eq | Ne | Lt | Le | Gt | Ge => unreachable!("comparison returned"),
    };
    Ok(LiteralValue::Int(value))
}
fn allocate(len: usize, l: EvalLimits) -> Result<Vec<u8>, EvalError> {
    if len > l.max_bytes {
        return Err(EvalError::Resource);
    }
    let mut out = Vec::new();
    out.try_reserve_exact(len)
        .map_err(|_| EvalError::Resource)?;
    Ok(out)
}
fn range(start: usize, len: usize, total: usize) -> Result<std::ops::Range<usize>, EvalError> {
    let end = start
        .checked_add(len)
        .filter(|e| *e <= total)
        .ok_or(EvalError::Undefined)?;
    Ok(start..end)
}
fn encode(w: WordWidth, e: Endian, value: u64) -> Vec<u8> {
    let size = usize::try_from(w.bits() / 8).expect("word bytes");
    match e {
        Endian::Little => value.to_le_bytes()[..size].to_vec(),
        Endian::Big => value.to_be_bytes()[8 - size..].to_vec(),
    }
}
fn decode(w: WordWidth, e: Endian, value: &[u8]) -> Result<LiteralValue, EvalError> {
    if value.len() != usize::try_from(w.bits() / 8).expect("word bytes") {
        return Err(EvalError::Undefined);
    }
    let mut out = [0u8; 8];
    let bits = match e {
        Endian::Little => {
            out[..value.len()].copy_from_slice(value);
            u64::from_le_bytes(out)
        }
        Endian::Big => {
            out[8 - value.len()..].copy_from_slice(value);
            u64::from_be_bytes(out)
        }
    };
    Ok(LiteralValue::wrapping_word(w, bits))
}
#[allow(clippy::too_many_lines)]
fn eval_bytes(
    op: BytesOp,
    args: &[LiteralValue],
    limits: EvalLimits,
) -> Result<LiteralValue, EvalError> {
    use BytesOp::*;
    let out = match op {
        Empty => Vec::new(),
        Singleton => vec![u8::try_from(word(&args[0])).expect("i8")],
        Cons | Snoc => {
            let (left, right) = if op == Cons {
                (bytes(&args[1]), word(&args[0]))
            } else {
                (bytes(&args[0]), word(&args[1]))
            };
            let mut out = allocate(
                left.len().checked_add(1).ok_or(EvalError::Resource)?,
                limits,
            )?;
            if op == Cons {
                out.push(u8::try_from(right).expect("i8"));
                out.extend_from_slice(left);
            } else {
                out.extend_from_slice(left);
                out.push(u8::try_from(right).expect("i8"));
            }
            out
        }
        Append => {
            let left = bytes(&args[0]);
            let right = bytes(&args[1]);
            let mut out = allocate(
                left.len()
                    .checked_add(right.len())
                    .ok_or(EvalError::Resource)?,
                limits,
            )?;
            out.extend_from_slice(left);
            out.extend_from_slice(right);
            out
        }
        Repeat => {
            let n = count(&args[1])?;
            let mut out = allocate(n, limits)?;
            out.resize(n, u8::try_from(word(&args[0])).expect("i8"));
            out
        }
        Length => return Ok(LiteralValue::Nat(Num::from(bytes(&args[0]).len()))),
        Eq | Ne | Lt | Le | Gt | Ge => {
            let left = bytes(&args[0]);
            let right = bytes(&args[1]);
            return Ok(LiteralValue::Bool(match op {
                Eq => left == right,
                Ne => left != right,
                Lt => left < right,
                Le => left <= right,
                Gt => left > right,
                Ge => left >= right,
                _ => unreachable!(),
            }));
        }
        Get => {
            return Ok(LiteralValue::I8(
                *bytes(&args[0])
                    .get(count(&args[1])?)
                    .ok_or(EvalError::Undefined)?,
            ));
        }
        Set => {
            let left = bytes(&args[0]);
            let ix = count(&args[1])?;
            range(ix, 1, left.len())?;
            let mut out = left.to_vec();
            out[ix] = u8::try_from(word(&args[2])).expect("i8");
            out
        }
        Slice => {
            let left = bytes(&args[0]);
            return Ok(LiteralValue::Bytes(left.slice(range(
                count(&args[1])?,
                count(&args[2])?,
                left.len(),
            )?)));
        }
        Replace => {
            let left = bytes(&args[0]);
            let selected = range(count(&args[1])?, count(&args[2])?, left.len())?;
            let right = bytes(&args[3]);
            let mut out = allocate(
                (left.len() - selected.len())
                    .checked_add(right.len())
                    .ok_or(EvalError::Resource)?,
                limits,
            )?;
            out.extend_from_slice(&left[..selected.start]);
            out.extend_from_slice(right);
            out.extend_from_slice(&left[selected.end..]);
            out
        }
        Take | Drop => {
            let left = bytes(&args[0]);
            let n = usize::try_from(nat(&args[1]))
                .unwrap_or(usize::MAX)
                .min(left.len());
            return Ok(LiteralValue::Bytes(if op == Take {
                left.slice(..n)
            } else {
                left.slice(n..)
            }));
        }
        Encode(width, endian) => encode(width, endian, word(&args[0])),
        Decode(width, endian) => return decode(width, endian, bytes(&args[0])),
        Read(width, endian) => {
            let left = bytes(&args[0]);
            return decode(
                width,
                endian,
                &left[range(
                    count(&args[1])?,
                    usize::try_from(width.bits() / 8).expect("word bytes"),
                    left.len(),
                )?],
            );
        }
        Write(width, endian) => {
            let left = bytes(&args[0]);
            let ix = count(&args[1])?;
            let right = encode(width, endian, word(&args[2]));
            let selected = range(ix, right.len(), left.len())?;
            let mut out = left.to_vec();
            out[selected].copy_from_slice(&right);
            out
        }
    };
    Ok(LiteralValue::Bytes(out.into()))
}
fn low_bits(value: &Int) -> u64 {
    let bytes = value.to_canonical_bytes();
    let mut out = if value < &Int::ZERO {
        [255u8; 8]
    } else {
        [0; 8]
    };
    let len = bytes.len().min(8);
    out[8 - len..].copy_from_slice(&bytes[bytes.len() - len..]);
    u64::from_be_bytes(out)
}
fn eval_cast(op: CastOp, args: &[LiteralValue]) -> Result<LiteralValue, EvalError> {
    use CastOp::*;
    let v = &args[0];
    let result = match op {
        NatToInt => LiteralValue::Int(Int::from(nat(v))),
        IntToNat => LiteralValue::Nat(Num::try_from(int(v)).map_err(|_| EvalError::Undefined)?),
        WordToNat(_) => LiteralValue::Nat(Num::from(word(v))),
        WordToIntU(_) => LiteralValue::Int(Int::from(Num::from(word(v)))),
        WordToIntS(w) => LiteralValue::Int(Int::from(signed(w, word(v)))),
        NatToWord(w) => {
            let n = u64::try_from(nat(v)).map_err(|_| EvalError::Undefined)?;
            if n > w.mask() {
                return Err(EvalError::Undefined);
            }
            LiteralValue::wrapping_word(w, n)
        }
        IntToWordU(w) => {
            let n = Num::try_from(int(v)).map_err(|_| EvalError::Undefined)?;
            let n = u64::try_from(n).map_err(|_| EvalError::Undefined)?;
            if n > w.mask() {
                return Err(EvalError::Undefined);
            }
            LiteralValue::wrapping_word(w, n)
        }
        IntToWordS(w) => {
            let n = i64::try_from(int(v)).map_err(|_| EvalError::Undefined)?;
            if i128::from(n) < -(1i128 << (w.bits() - 1))
                || i128::from(n) >= (1i128 << (w.bits() - 1))
            {
                return Err(EvalError::Undefined);
            }
            LiteralValue::wrapping_word(w, u64::from_ne_bytes(n.to_ne_bytes()))
        }
        NatToWordWrap(w) => LiteralValue::wrapping_word(w, low_bits(&Int::from(nat(v)))),
        IntToWordWrap(w) => LiteralValue::wrapping_word(w, low_bits(int(v))),
        WordWrap(_, to) | WordZeroExtend(_, to) => LiteralValue::wrapping_word(to, word(v)),
        WordSignExtend(from, to) => {
            LiteralValue::wrapping_word(to, u64::from_ne_bytes(signed(from, word(v)).to_ne_bytes()))
        }
    };
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn eval(op: Builtin, args: &[LiteralValue]) -> Result<LiteralValue, EvalError> {
        op.evaluate(args, EvalLimits::default())
    }
    #[test]
    fn all_widths_signed_edges_and_masked_shifts() {
        for w in [
            WordWidth::W8,
            WordWidth::W16,
            WordWidth::W32,
            WordWidth::W64,
        ] {
            let v = |x| LiteralValue::wrapping_word(w, x);
            let n = w.bits();
            let min = 1 << (n - 1);
            assert_eq!(
                eval(Builtin::Word(w, WordOp::Add), &[v(w.mask()), v(1)]).unwrap(),
                v(0)
            );
            assert_eq!(
                eval(Builtin::Word(w, WordOp::DivS), &[v(min), v(w.mask())]),
                Err(EvalError::Undefined)
            );
            assert_eq!(
                eval(Builtin::Word(w, WordOp::RemS), &[v(min), v(w.mask())]).unwrap(),
                v(0)
            );
            assert_eq!(
                eval(Builtin::Word(w, WordOp::Shl), &[v(1), v(u64::from(n))]).unwrap(),
                v(1)
            );
            assert_eq!(
                eval(
                    Builtin::Word(w, WordOp::ShrS),
                    &[v(min), v(u64::from(n - 1))]
                )
                .unwrap(),
                v(w.mask())
            );
            assert_eq!(
                eval(Builtin::Word(w, WordOp::Clz), &[v(0)]).unwrap(),
                v(u64::from(n))
            );
            assert_eq!(
                eval(Builtin::Word(w, WordOp::Ctz), &[v(0)]).unwrap(),
                v(u64::from(n))
            );
            for op in [
                WordOp::Add,
                WordOp::Sub,
                WordOp::Mul,
                WordOp::DivU,
                WordOp::DivS,
                WordOp::RemU,
                WordOp::RemS,
                WordOp::And,
                WordOp::Or,
                WordOp::Xor,
                WordOp::Shl,
                WordOp::ShrU,
                WordOp::ShrS,
                WordOp::Rotl,
                WordOp::Rotr,
                WordOp::Eq,
                WordOp::Ne,
                WordOp::LtU,
                WordOp::LeU,
                WordOp::GtU,
                WordOp::GeU,
                WordOp::LtS,
                WordOp::LeS,
                WordOp::GtS,
                WordOp::GeS,
            ] {
                let builtin = Builtin::Word(w, op);
                assert_eq!(
                    eval(builtin, &[v(7), v(3)]).unwrap().ty(),
                    builtin.signature().unwrap().1
                );
            }
            for op in [
                WordOp::Not,
                WordOp::Clz,
                WordOp::Ctz,
                WordOp::Popcnt,
                WordOp::Eqz,
            ] {
                let builtin = Builtin::Word(w, op);
                assert_eq!(
                    eval(builtin, &[v(7)]).unwrap().ty(),
                    builtin.signature().unwrap().1
                );
            }
        }
    }
    #[test]
    fn exhaustive_i8_arithmetic_matches_wide_reference() {
        for a in 0u16..=255 {
            for b in 0u16..=255 {
                let values = [
                    LiteralValue::I8(u8::try_from(a).unwrap()),
                    LiteralValue::I8(u8::try_from(b).unwrap()),
                ];
                for (op, expected) in [
                    (WordOp::Add, (a + b) % 256),
                    (WordOp::Sub, (256 + a - b) % 256),
                    (WordOp::Mul, (a * b) % 256),
                ] {
                    assert_eq!(
                        eval(Builtin::Word(WordWidth::W8, op), &values).unwrap(),
                        LiteralValue::I8(u8::try_from(expected).unwrap())
                    );
                }
            }
        }
    }
    #[test]
    fn unbounded_integer_and_natural_families() {
        for op in [
            NatOp::Add,
            NatOp::Sub,
            NatOp::Mul,
            NatOp::Div,
            NatOp::Rem,
            NatOp::Pow,
            NatOp::Eq,
            NatOp::Ne,
            NatOp::Lt,
            NatOp::Le,
            NatOp::Gt,
            NatOp::Ge,
            NatOp::Min,
            NatOp::Max,
            NatOp::And,
            NatOp::Or,
            NatOp::Xor,
            NatOp::Shl,
            NatOp::Shr,
        ] {
            let builtin = Builtin::Nat(op);
            assert_eq!(
                eval(
                    builtin,
                    &[
                        LiteralValue::Nat(Num::from(7u8)),
                        LiteralValue::Nat(Num::from(3u8))
                    ]
                )
                .unwrap()
                .ty(),
                builtin.signature().unwrap().1
            );
        }
        for op in [
            IntOp::Add,
            IntOp::Sub,
            IntOp::Mul,
            IntOp::Div,
            IntOp::Rem,
            IntOp::Eq,
            IntOp::Ne,
            IntOp::Lt,
            IntOp::Le,
            IntOp::Gt,
            IntOp::Ge,
            IntOp::Min,
            IntOp::Max,
            IntOp::And,
            IntOp::Or,
            IntOp::Xor,
        ] {
            let builtin = Builtin::Int(op);
            assert_eq!(
                eval(
                    builtin,
                    &[
                        LiteralValue::Int(Int::from(-7)),
                        LiteralValue::Int(Int::from(3))
                    ]
                )
                .unwrap()
                .ty(),
                builtin.signature().unwrap().1
            );
        }
        assert_eq!(
            eval(
                Builtin::Int(IntOp::Rem),
                &[
                    LiteralValue::Int(Int::from(-7)),
                    LiteralValue::Int(Int::from(3))
                ]
            )
            .unwrap(),
            LiteralValue::Int(Int::from(-1))
        );
        assert_eq!(
            eval(
                Builtin::Int(IntOp::Shr),
                &[
                    LiteralValue::Int(Int::from(-7)),
                    LiteralValue::Nat(Num::from(1u8))
                ]
            )
            .unwrap(),
            LiteralValue::Int(Int::from(-4))
        );
    }
    #[test]
    fn endian_roundtrips_and_bytes_bounds() {
        for w in [
            WordWidth::W8,
            WordWidth::W16,
            WordWidth::W32,
            WordWidth::W64,
        ] {
            for e in [Endian::Big, Endian::Little] {
                let word = LiteralValue::wrapping_word(w, 0xfedc_ba98_7654_3210);
                let data = eval(
                    Builtin::Bytes(BytesOp::Encode(w, e)),
                    std::slice::from_ref(&word),
                )
                .unwrap();
                assert_eq!(
                    eval(Builtin::Bytes(BytesOp::Decode(w, e)), &[data]).unwrap(),
                    word
                );
            }
        }
        let b = LiteralValue::Bytes(vec![1, 2, 3].into());
        let n = |v| LiteralValue::Nat(Num::from(v));
        assert_eq!(
            eval(Builtin::Bytes(BytesOp::Slice), &[b.clone(), n(2u8), n(2u8)]),
            Err(EvalError::Undefined)
        );
        assert_eq!(
            eval(Builtin::Bytes(BytesOp::Take), &[b.clone(), n(255u8)]).unwrap(),
            b
        );
        assert_eq!(
            eval(
                Builtin::Bytes(BytesOp::Replace),
                &[b, n(1u8), n(1u8), LiteralValue::Bytes(vec![4, 5].into())]
            )
            .unwrap(),
            LiteralValue::Bytes(vec![1, 4, 5, 3].into())
        );
    }
    #[test]
    fn exact_and_wrapping_casts_differ() {
        let minus = LiteralValue::Int(Int::from(-1));
        assert_eq!(
            eval(
                Builtin::Cast(CastOp::IntToWordU(WordWidth::W8)),
                std::slice::from_ref(&minus)
            ),
            Err(EvalError::Undefined)
        );
        assert_eq!(
            eval(
                Builtin::Cast(CastOp::IntToWordWrap(WordWidth::W8)),
                &[minus]
            )
            .unwrap(),
            LiteralValue::I8(255)
        );
        assert_eq!(
            eval(
                Builtin::Cast(CastOp::WordSignExtend(WordWidth::W8, WordWidth::W64)),
                &[LiteralValue::I8(255)]
            )
            .unwrap(),
            LiteralValue::I64(u64::MAX)
        );
        assert!(
            Builtin::Word(WordWidth::W8, WordOp::ExtendSign(WordWidth::W16))
                .signature()
                .is_err()
        );
    }
    #[test]
    fn resource_bound_precedes_large_allocations() {
        let limits = EvalLimits {
            max_bytes: 32,
            max_steps: 1024,
        };
        assert_eq!(
            Builtin::Bytes(BytesOp::Repeat).evaluate(
                &[
                    LiteralValue::I8(0),
                    LiteralValue::Nat(Num::from(1_000_000u32))
                ],
                limits
            ),
            Err(EvalError::Resource)
        );
        assert_eq!(
            Builtin::Nat(NatOp::Pow).evaluate(
                &[
                    LiteralValue::Nat(Num::from(2u8)),
                    LiteralValue::Nat(Num::from(1000u32))
                ],
                limits
            ),
            Err(EvalError::Resource)
        );
    }
}
