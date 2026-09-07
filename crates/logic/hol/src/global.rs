//! Immutable negative-reference vocabulary. IDs identify syntax, never facts.
//!
//! Tiny values and curried scalar arrow types are decoded arithmetically;
//! there is no heap table or remembered per-kernel initialization state.
use crate::{
    Ref, Row,
    literals::{
        BoolOp, Builtin, BytesOp, CastOp, Endian, IntOp, LiteralType, LiteralValue, NatOp, WordOp,
        WordWidth,
    },
    row::Expr as Node,
};

impl crate::Arena {
    /// Descriptor of an immutable builtin function constant.
    #[must_use]
    pub fn builtin_op(&self, reference: Ref) -> Option<Builtin> {
        match *self.row(reference)?.expr() {
            Node::Builtin(op) => Some(op),
            _ => None,
        }
    }
    /// Recognizes a builtin application spine in source argument order.
    #[must_use]
    pub fn builtin_application(&self, reference: Ref) -> Option<(Builtin, Vec<Ref>)> {
        let mut current = reference;
        let mut args = Vec::new();
        loop {
            match *self.row(current)?.expr() {
                Node::Builtin(op) => {
                    args.reverse();
                    return Some((op, args));
                }
                Node::App(function, arg) => {
                    if args.len() >= 4 {
                        return None;
                    }
                    args.push(arg);
                    current = function;
                }
                _ => return None,
            }
        }
    }
}

const BOOL_OPS: [BoolOp; 5] = [
    BoolOp::Not,
    BoolOp::And,
    BoolOp::Or,
    BoolOp::Imp,
    BoolOp::Iff,
];
const WORD_OPS: [WordOp; 30] = [
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
    WordOp::Not,
    WordOp::Shl,
    WordOp::ShrU,
    WordOp::ShrS,
    WordOp::Rotl,
    WordOp::Rotr,
    WordOp::Clz,
    WordOp::Ctz,
    WordOp::Popcnt,
    WordOp::Eqz,
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
];
const NAT_OPS: [NatOp; 21] = [
    NatOp::Add,
    NatOp::Sub,
    NatOp::Mul,
    NatOp::Div,
    NatOp::Rem,
    NatOp::Succ,
    NatOp::Pred,
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
];
const INT_OPS: [IntOp; 24] = [
    IntOp::Add,
    IntOp::Sub,
    IntOp::Mul,
    IntOp::Div,
    IntOp::Rem,
    IntOp::Succ,
    IntOp::Pred,
    IntOp::Neg,
    IntOp::Abs,
    IntOp::Pow,
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
    IntOp::Not,
    IntOp::Shl,
    IntOp::Shr,
];
const BYTES_OPS: [BytesOp; 19] = [
    BytesOp::Empty,
    BytesOp::Singleton,
    BytesOp::Cons,
    BytesOp::Snoc,
    BytesOp::Append,
    BytesOp::Repeat,
    BytesOp::Length,
    BytesOp::Eq,
    BytesOp::Ne,
    BytesOp::Lt,
    BytesOp::Le,
    BytesOp::Gt,
    BytesOp::Ge,
    BytesOp::Get,
    BytesOp::Set,
    BytesOp::Slice,
    BytesOp::Replace,
    BytesOp::Take,
    BytesOp::Drop,
];
const WIDTHS: [WordWidth; 4] = [
    WordWidth::W8,
    WordWidth::W16,
    WordWidth::W32,
    WordWidth::W64,
];
const TYPES: [LiteralType; 8] = [
    LiteralType::Bool,
    LiteralType::I8,
    LiteralType::I16,
    LiteralType::I32,
    LiteralType::I64,
    LiteralType::Nat,
    LiteralType::Int,
    LiteralType::Bytes,
];
const NAT: i32 = 1_048_576;
const INT: i32 = 1_114_112;
const I8: i32 = 1_179_648;
const I16: i32 = 1_245_184;
const I32: i32 = 1_310_720;
const I64: i32 = 1_376_256;
fn reference(id: i32) -> Ref {
    Ref::new(-id).expect("global id is valid")
}
pub(crate) fn star() -> Ref {
    reference(1)
}
pub(crate) fn boolean(value: bool) -> Ref {
    reference(if value { 11 } else { 10 })
}
pub(crate) fn ty(ty: LiteralType) -> Ref {
    reference(2 + ty as i32)
}
pub(crate) fn canonical(op: Builtin) -> Builtin {
    match op {
        Builtin::Cast(
            CastOp::WordWrap(a, b) | CastOp::WordZeroExtend(a, b) | CastOp::WordSignExtend(a, b),
        ) if a == b => Builtin::Cast(CastOp::WordWrap(a, b)),
        Builtin::Bytes(BytesOp::Encode(WordWidth::W8, _)) => Builtin::Bytes(BytesOp::Singleton),
        Builtin::Bytes(BytesOp::Decode(WordWidth::W8, _)) => {
            Builtin::Bytes(BytesOp::Decode(WordWidth::W8, Endian::Little))
        }
        Builtin::Bytes(BytesOp::Read(WordWidth::W8, _)) => {
            Builtin::Bytes(BytesOp::Read(WordWidth::W8, Endian::Little))
        }
        Builtin::Bytes(BytesOp::Write(WordWidth::W8, _)) => {
            Builtin::Bytes(BytesOp::Write(WordWidth::W8, Endian::Little))
        }
        other => other,
    }
}
fn width_index(w: WordWidth) -> usize {
    match w {
        WordWidth::W8 => 0,
        WordWidth::W16 => 1,
        WordWidth::W32 => 2,
        WordWidth::W64 => 3,
    }
}
fn code(op: Builtin) -> usize {
    match canonical(op) {
        Builtin::Bool(op) => BOOL_OPS
            .iter()
            .position(|x| *x == op)
            .expect("complete bool operations"),
        Builtin::Word(w, op) => {
            16 + 40 * width_index(w)
                + match op {
                    WordOp::ExtendSign(from) => 30 + width_index(from),
                    other => WORD_OPS
                        .iter()
                        .position(|x| *x == other)
                        .expect("complete word operations"),
                }
        }
        Builtin::Nat(op) => {
            192 + NAT_OPS
                .iter()
                .position(|x| *x == op)
                .expect("complete natural operations")
        }
        Builtin::Int(op) => {
            224 + INT_OPS
                .iter()
                .position(|x| *x == op)
                .expect("complete integer operations")
        }
        Builtin::Bytes(op) => match op {
            BytesOp::Encode(w, e)
            | BytesOp::Decode(w, e)
            | BytesOp::Read(w, e)
            | BytesOp::Write(w, e) => {
                let kind = match op {
                    BytesOp::Encode(..) => 0,
                    BytesOp::Decode(..) => 1,
                    BytesOp::Read(..) => 2,
                    _ => 3,
                };
                288 + 8 * kind + 2 * width_index(w) + usize::from(e == Endian::Big)
            }
            other => {
                256 + BYTES_OPS
                    .iter()
                    .position(|x| *x == other)
                    .expect("complete byte operations")
            }
        },
        Builtin::Cast(op) => match op {
            CastOp::NatToInt => 320,
            CastOp::IntToNat => 321,
            CastOp::WordToNat(w) => 328 + width_index(w),
            CastOp::WordToIntU(w) => 332 + width_index(w),
            CastOp::WordToIntS(w) => 336 + width_index(w),
            CastOp::NatToWord(w) => 340 + width_index(w),
            CastOp::IntToWordU(w) => 344 + width_index(w),
            CastOp::IntToWordS(w) => 348 + width_index(w),
            CastOp::NatToWordWrap(w) => 352 + width_index(w),
            CastOp::IntToWordWrap(w) => 356 + width_index(w),
            CastOp::WordWrap(a, b) => 368 + 4 * width_index(a) + width_index(b),
            CastOp::WordZeroExtend(a, b) => 384 + 4 * width_index(a) + width_index(b),
            CastOp::WordSignExtend(a, b) => 400 + 4 * width_index(a) + width_index(b),
        },
    }
}
fn operation(code: usize) -> Option<Builtin> {
    let op = match code {
        0..=4 => Builtin::Bool(BOOL_OPS[code]),
        16..=175 => {
            let part = code - 16;
            let w = WIDTHS[part / 40];
            let part = part % 40;
            let op = if part < 30 {
                WORD_OPS[part]
            } else {
                WordOp::ExtendSign(*WIDTHS.get(part.checked_sub(30)?)?)
            };
            Builtin::Word(w, op)
        }
        192..=212 => Builtin::Nat(NAT_OPS[code - 192]),
        224..=247 => Builtin::Int(INT_OPS[code - 224]),
        256..=274 => Builtin::Bytes(BYTES_OPS[code - 256]),
        288..=319 => {
            let part = code - 288;
            let w = WIDTHS[(part % 8) / 2];
            let e = if part.is_multiple_of(2) {
                Endian::Little
            } else {
                Endian::Big
            };
            Builtin::Bytes(match part / 8 {
                0 => BytesOp::Encode(w, e),
                1 => BytesOp::Decode(w, e),
                2 => BytesOp::Read(w, e),
                _ => BytesOp::Write(w, e),
            })
        }
        320 => Builtin::Cast(CastOp::NatToInt),
        321 => Builtin::Cast(CastOp::IntToNat),
        328..=359 => {
            let part = code - 328;
            let w = WIDTHS[part % 4];
            Builtin::Cast(match part / 4 {
                0 => CastOp::WordToNat(w),
                1 => CastOp::WordToIntU(w),
                2 => CastOp::WordToIntS(w),
                3 => CastOp::NatToWord(w),
                4 => CastOp::IntToWordU(w),
                5 => CastOp::IntToWordS(w),
                6 => CastOp::NatToWordWrap(w),
                _ => CastOp::IntToWordWrap(w),
            })
        }
        368..=415 => {
            let part = code - 368;
            let a = WIDTHS[(part % 16) / 4];
            let b = WIDTHS[part % 4];
            Builtin::Cast(match part / 16 {
                0 => CastOp::WordWrap(a, b),
                1 => CastOp::WordZeroExtend(a, b),
                _ => CastOp::WordSignExtend(a, b),
            })
        }
        _ => return None,
    };
    op.signature().ok()?;
    (canonical(op) == op).then_some(op)
}
pub(crate) fn builtin(op: Builtin) -> Option<Ref> {
    op.signature().ok()?;
    Some(reference(1024 + i32::try_from(code(op)).ok()?))
}
pub(crate) fn signature_type(inputs: &[LiteralType], output: LiteralType) -> Ref {
    if inputs.is_empty() {
        return ty(output);
    }
    let code = inputs
        .iter()
        .copied()
        .chain([output])
        .fold(1i32, |code, ty| code * 8 + ty as i32);
    reference(131_072 + code)
}
fn signature(mut code: i32) -> Option<Vec<LiteralType>> {
    let mut types = Vec::new();
    while code > 1 {
        types.push(*TYPES.get(usize::try_from(code % 8).ok()?)?);
        code /= 8;
        if types.len() > 5 {
            return None;
        }
    }
    if code != 1 || types.len() < 2 {
        return None;
    }
    types.reverse();
    Some(types)
}
pub(crate) fn arrow(domain: Ref, codomain: Ref) -> Option<Ref> {
    let Node::LiteralTy(domain_ty) = row(domain)?.expr().to_owned() else {
        if domain == ty(LiteralType::Bool) {
            return arrow_from(LiteralType::Bool, codomain);
        }
        return None;
    };
    arrow_from(domain_ty, codomain)
}
fn arrow_from(domain: LiteralType, codomain: Ref) -> Option<Ref> {
    if let Some(output) = type_value(codomain) {
        return Some(signature_type(&[domain], output));
    }
    let mut types = signature((-codomain.get()).checked_sub(131_072)?)?;
    if types.len() >= 5 {
        return None;
    }
    types.insert(0, domain);
    let output = types.pop()?;
    Some(signature_type(&types, output))
}
fn type_value(reference: Ref) -> Option<LiteralType> {
    let id = -reference.get();
    if (2..=9).contains(&id) {
        Some(TYPES[usize::try_from(id - 2).ok()?])
    } else {
        None
    }
}
pub(crate) fn literal(value: &LiteralValue) -> Option<Ref> {
    Some(match value {
        LiteralValue::Bool(value) => boolean(*value),
        LiteralValue::Nat(value) => reference(NAT + i32::from(u16::try_from(value).ok()?)),
        LiteralValue::Int(value) => reference(INT + i32::from(i16::try_from(value).ok()?) + 32768),
        LiteralValue::I8(value) => reference(I8 + i32::from(*value)),
        LiteralValue::I16(value) => reference(I16 + i32::from(*value)),
        LiteralValue::I32(value) => reference(I32 + i32::from(u16::try_from(*value).ok()?)),
        LiteralValue::I64(value) => reference(I64 + i32::from(u16::try_from(*value).ok()?)),
        LiteralValue::Bytes(value) if value.is_empty() => builtin(Builtin::Bytes(BytesOp::Empty))?,
        LiteralValue::Bytes(_) => return None,
    })
}
pub(crate) fn row(r: Ref) -> Option<Row> {
    let id = r.get().checked_neg()?;
    let node = match id {
        1 => Node::KindStar,
        2 => Node::BoolTy,
        3..=9 => Node::LiteralTy(TYPES[usize::try_from(id - 2).ok()?]),
        10 => Node::Bool(false),
        11 => Node::Bool(true),
        1024..=1439 => Node::Builtin(operation(usize::try_from(id - 1024).ok()?)?),
        131_136..=196_607 => {
            let mut types = signature(id - 131_072)?;
            let output = types.pop()?;
            let domain = types.remove(0);
            Node::TyArr(ty(domain), signature_type(&types, output))
        }
        NAT..=1_114_111 => Node::Nat(u64::try_from(id - NAT).ok()?),
        INT..=1_179_647 => Node::Int(i64::from(id - INT - 32768)),
        I8..=1_179_903 => Node::Word(
            WordWidth::W8,
            i64::from(i8::from_ne_bytes([u8::try_from(id - I8).ok()?])),
        ),
        I16..=1_310_719 => Node::Word(
            WordWidth::W16,
            i64::from(i16::from_ne_bytes(
                u16::try_from(id - I16).ok()?.to_ne_bytes(),
            )),
        ),
        I32..=1_376_255 => Node::Word(WordWidth::W32, i64::from(id - I32)),
        I64..=1_441_791 => Node::Word(WordWidth::W64, i64::from(id - I64)),
        _ => return None,
    };
    Some(Row::new(node))
}
pub(crate) fn classifier(r: Ref) -> Option<Ref> {
    Some(match *row(r)?.expr() {
        Node::BoolTy | Node::LiteralTy(_) | Node::TyArr(..) => star(),
        Node::Bool(_) => ty(LiteralType::Bool),
        Node::Nat(_) => ty(LiteralType::Nat),
        Node::Int(_) => ty(LiteralType::Int),
        Node::Word(w, _) => ty(w.ty()),
        Node::Builtin(op) => {
            let (inputs, output) = op.signature().ok()?;
            signature_type(&inputs, output)
        }
        _ => return None,
    })
}
pub(crate) fn requires_infinity(r: Ref) -> bool {
    match row(r).map(|row| *row.expr()) {
        Some(Node::KindStar | Node::BoolTy | Node::Bool(_) | Node::Builtin(Builtin::Bool(_)))
        | None => false,
        Some(Node::TyArr(a, b)) => requires_infinity(a) || requires_infinity(b),
        Some(_) => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Arena, Kernel};
    use covalence_data_num::{Int, Num};

    #[test]
    fn tiny_values_roundtrip_without_resident_rows() {
        let mut arena = Arena::empty();
        for bits in 0..=u16::MAX {
            let values = [
                LiteralValue::Nat(Num::from(bits)),
                LiteralValue::Int(Int::from(i32::from(bits) - 32768)),
                LiteralValue::I16(bits),
                LiteralValue::I32(u32::from(bits)),
                LiteralValue::I64(u64::from(bits)),
            ];
            for value in values {
                let reference = arena.push_literal(value.clone()).unwrap();
                assert!(reference.get() < 0);
                assert_eq!(arena.literal_value(reference), Some(value.clone()));
                assert_eq!(
                    arena.literal_type(arena.sort(reference).unwrap()),
                    Some(value.ty())
                );
            }
        }
        for bits in 0..=u8::MAX {
            let value = LiteralValue::I8(bits);
            let reference = arena.push_literal(value.clone()).unwrap();
            assert_eq!(arena.literal_value(reference), Some(value));
        }
        assert!(arena.is_empty());
    }

    #[test]
    fn builtin_and_signature_registry_roundtrips_and_canonicalizes_aliases() {
        for id in 0..=415 {
            if let Some(op) = operation(id) {
                let reference = builtin(op).unwrap();
                assert_eq!(reference.get(), -(1024 + i32::try_from(id).unwrap()));
                assert_eq!(*row(reference).unwrap().expr(), Node::Builtin(op));
                let (inputs, output) = op.signature().unwrap();
                let mut carrier = classifier(reference).unwrap();
                for input in inputs {
                    let Node::TyArr(domain, codomain) = *row(carrier).unwrap().expr() else {
                        panic!("signature arrow")
                    };
                    assert_eq!(domain, ty(input));
                    assert_eq!(arrow(domain, codomain), Some(carrier));
                    carrier = codomain;
                }
                assert_eq!(carrier, ty(output));
            }
        }
        for width in WIDTHS {
            assert_eq!(
                builtin(Builtin::Cast(CastOp::WordWrap(width, width))),
                builtin(Builtin::Cast(CastOp::WordSignExtend(width, width)))
            );
        }
        assert_eq!(
            builtin(Builtin::Bytes(BytesOp::Singleton)),
            builtin(Builtin::Bytes(BytesOp::Encode(WordWidth::W8, Endian::Big)))
        );
        assert_eq!(
            literal(&LiteralValue::Bytes(bytes::Bytes::new())),
            builtin(Builtin::Bytes(BytesOp::Empty))
        );
        for unknown in [-12, -1023, -1439, -131_135, -1_179_904, -i32::MAX] {
            assert!(row(Ref::new(unknown).unwrap()).is_none());
        }
    }

    #[test]
    fn negative_syntax_never_grants_infinity_or_classical_polarity() {
        let mut kernel = Kernel::new();
        let nat = ty(LiteralType::Nat);
        let zero = literal(&LiteralValue::Nat(Num::ZERO)).unwrap();
        assert!(kernel.category(nat).is_err());
        assert!(kernel.classifier(zero).is_err());
        assert!(kernel.tm_fv(0, nat).is_err());
        assert!(kernel.lit(boolean(true)).is_err());
        assert!(boolean(false).positive().is_err());
        let local = Ref::new(1).unwrap();
        assert_eq!(Ref::from_literal(local.positive().unwrap()), local);
        assert!(kernel.arena().is_empty());
        let truth = kernel.bool(ty(LiteralType::Bool), true).unwrap();
        let negated = kernel.not(truth).unwrap();
        let (value, _) = kernel
            .reduce_builtin(negated, crate::literals::EvalLimits::default())
            .unwrap();
        assert_eq!(value, boolean(false));
    }
}
