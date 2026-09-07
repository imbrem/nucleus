//! Shared fixture generation and checked-kernel exercise for every builtin.
use covalence_data_num::{Int, Num};
use covalence_lib_json::serde_json::{Value, json};
use covalence_logic_hol::literals::{
    Builtin, BytesOp, CastOp, Endian, EvalError, EvalLimits, IntOp, LiteralType, LiteralValue,
    NatOp, WordOp, WordWidth,
};
fn name(ty: LiteralType) -> &'static str {
    match ty {
        LiteralType::Bool => "bool",
        LiteralType::I8 => "i8",
        LiteralType::I16 => "i16",
        LiteralType::I32 => "i32",
        LiteralType::I64 => "i64",
        LiteralType::Nat => "nat",
        LiteralType::Int => "int",
        LiteralType::Bytes => "bytes",
    }
}
fn value(v: &LiteralValue) -> Value {
    json!([
        name(v.ty()),
        match v {
            LiteralValue::Bool(v) => json!(v),
            LiteralValue::Bytes(v) => json!(v.to_vec()),
            LiteralValue::Nat(v) => json!(v.to_string()),
            LiteralValue::Int(v) => json!(v.to_string()),
            _ => json!(v.word_bits().unwrap().to_string()),
        }
    ])
}
fn sample(ty: LiteralType) -> LiteralValue {
    match ty {
        LiteralType::Bool => LiteralValue::Bool(true),
        LiteralType::I8 => LiteralValue::I8(3),
        LiteralType::I16 => LiteralValue::I16(3),
        LiteralType::I32 => LiteralValue::I32(3),
        LiteralType::I64 => LiteralValue::I64(3),
        LiteralType::Nat => LiteralValue::Nat(Num::from(1u8)),
        LiteralType::Int => LiteralValue::Int(Int::from(-7)),
        LiteralType::Bytes => LiteralValue::Bytes(vec![1, 2, 3, 4, 5, 6, 7, 8].into()),
    }
}
fn record(op: Builtin, args: Vec<LiteralValue>) -> Value {
    let (inputs, output) = op.signature().unwrap();
    let mut kernel = covalence_logic_hol::Kernel::new();
    kernel.add_axiom(covalence_logic_hol::AX_INF).unwrap();
    let terms = args
        .iter()
        .cloned()
        .map(|v| kernel.literal(v).unwrap())
        .collect::<Vec<_>>();
    let term = kernel.builtin(op, &terms).unwrap();
    let checked = kernel.reduce_builtin(term, EvalLimits::default());
    let result = match op.evaluate(&args, EvalLimits::default()) {
        Ok(v) => {
            let (actual, theorem) = checked.unwrap();
            assert_eq!(kernel.literal_value(actual).unwrap(), Some(v.clone()));
            let proof = kernel.theorems().get(theorem).unwrap();
            assert_eq!(proof.lhs.rows().count(), 0);
            assert_eq!(proof.rhs.rows().count(), 1);
            value(&v)
        }
        Err(EvalError::Undefined) => {
            assert!(matches!(
                checked,
                Err(covalence_logic_hol::KernelError::Literal {
                    source: EvalError::Undefined
                })
            ));
            Value::Null
        }
        Err(e) => panic!("unexpected fixture error {e:?} for {op:?}"),
    };
    json!({"op":op,"inputs":inputs.into_iter().map(name).collect::<Vec<_>>(),"output":name(output),"args":args.into_iter().map(|v|value(&v)).collect::<Vec<_>>(),"result":result})
}
#[allow(clippy::too_many_lines)]
pub(crate) fn vectors() -> Vec<Value> {
    let widths = [
        WordWidth::W8,
        WordWidth::W16,
        WordWidth::W32,
        WordWidth::W64,
    ];
    let mut ops = Vec::new();
    for w in widths {
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
        ] {
            ops.push(Builtin::Word(w, op));
        }
        for from in widths {
            if from.bits() < w.bits() {
                ops.push(Builtin::Word(w, WordOp::ExtendSign(from)));
            }
        }
        for e in [Endian::Little, Endian::Big] {
            for op in [
                BytesOp::Encode(w, e),
                BytesOp::Decode(w, e),
                BytesOp::Read(w, e),
                BytesOp::Write(w, e),
            ] {
                ops.push(Builtin::Bytes(op));
            }
        }
        for op in [
            CastOp::WordToNat(w),
            CastOp::WordToIntU(w),
            CastOp::WordToIntS(w),
            CastOp::NatToWord(w),
            CastOp::IntToWordU(w),
            CastOp::IntToWordS(w),
            CastOp::NatToWordWrap(w),
            CastOp::IntToWordWrap(w),
        ] {
            ops.push(Builtin::Cast(op));
        }
        for to in widths {
            if to.bits() <= w.bits() {
                ops.push(Builtin::Cast(CastOp::WordWrap(w, to)));
            }
            if to.bits() >= w.bits() {
                ops.push(Builtin::Cast(CastOp::WordZeroExtend(w, to)));
                ops.push(Builtin::Cast(CastOp::WordSignExtend(w, to)));
            }
        }
    }
    for op in [
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
    ] {
        ops.push(Builtin::Nat(op));
    }
    for op in [
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
    ] {
        ops.push(Builtin::Int(op));
    }
    for op in [
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
    ] {
        ops.push(Builtin::Bytes(op));
    }
    ops.extend([
        Builtin::Cast(CastOp::NatToInt),
        Builtin::Cast(CastOp::IntToNat),
    ]);
    let mut vectors = Vec::new();
    for op in ops {
        let mut args = op
            .signature()
            .unwrap()
            .0
            .into_iter()
            .map(sample)
            .collect::<Vec<_>>();
        match op {
            Builtin::Word(width, _) => {
                args[0] = LiteralValue::wrapping_word(width, (u64::MAX >> (64 - width.bits())) - 6);
            }
            Builtin::Nat(_) => {
                args[0] = LiteralValue::Nat(Num::from(7u8));
                if args.len() == 2 {
                    args[1] = LiteralValue::Nat(Num::from(3u8));
                }
            }
            Builtin::Int(_) => {
                if args.len() == 2 {
                    args[1] = if args[1].ty() == LiteralType::Nat {
                        LiteralValue::Nat(Num::from(3u8))
                    } else {
                        LiteralValue::Int(Int::from(3))
                    };
                }
            }
            Builtin::Bytes(
                BytesOp::Eq | BytesOp::Ne | BytesOp::Lt | BytesOp::Le | BytesOp::Gt | BytesOp::Ge,
            ) => {
                args[1] = LiteralValue::Bytes(vec![1, 3].into());
            }
            Builtin::Cast(
                CastOp::WordWrap(from, _)
                | CastOp::WordZeroExtend(from, _)
                | CastOp::WordSignExtend(from, _),
            ) => {
                args[0] = LiteralValue::wrapping_word(from, (1u64 << (from.bits() - 1)) + 3);
            }
            _ => {}
        }
        // Codecs get their exact length; byte reads/writes start at zero.
        if let Builtin::Bytes(BytesOp::Decode(w, _)) = op {
            args[0] =
                LiteralValue::Bytes(vec![0x89; usize::try_from(w.bits() / 8).unwrap()].into());
        }
        if matches!(op, Builtin::Bytes(BytesOp::Read(..) | BytesOp::Write(..))) {
            args[1] = LiteralValue::Nat(Num::ZERO);
        }
        vectors.push(record(op, args));
    }
    for w in widths {
        let word = |n| LiteralValue::wrapping_word(w, n);
        let mask = u64::MAX >> (64 - w.bits());
        let min = 1u64 << (w.bits() - 1);
        for op in [WordOp::DivS, WordOp::RemS] {
            vectors.push(record(Builtin::Word(w, op), vec![word(min), word(mask)]));
        }
        for op in [WordOp::DivS, WordOp::RemS, WordOp::DivU, WordOp::RemU] {
            vectors.push(record(Builtin::Word(w, op), vec![word(3), word(0)]));
        }
        for op in [
            WordOp::Shl,
            WordOp::ShrS,
            WordOp::ShrU,
            WordOp::Rotl,
            WordOp::Rotr,
        ] {
            vectors.push(record(
                Builtin::Word(w, op),
                vec![word(min + 3), word(u64::from(w.bits()))],
            ));
            vectors.push(record(
                Builtin::Word(w, op),
                vec![word(min + 3), word(u64::from(w.bits() + 1))],
            ));
        }
        for op in [WordOp::Clz, WordOp::Ctz, WordOp::Popcnt] {
            vectors.push(record(Builtin::Word(w, op), vec![word(0)]));
            vectors.push(record(Builtin::Word(w, op), vec![word(mask)]));
        }
        for op in [
            CastOp::WordToIntS(w),
            CastOp::WordToIntU(w),
            CastOp::WordToNat(w),
        ] {
            vectors.push(record(Builtin::Cast(op), vec![word(mask)]));
        }
        for from in widths {
            if from.bits() < w.bits() {
                vectors.push(record(
                    Builtin::Word(w, WordOp::ExtendSign(from)),
                    vec![word((1u64 << from.bits()) - 1)],
                ));
            }
        }
        for (op, arg) in [
            (
                CastOp::NatToWord(w),
                LiteralValue::Nat(Num::from(1u128 << w.bits())),
            ),
            (
                CastOp::IntToWordS(w),
                LiteralValue::Int(Int::from(1i128 << (w.bits() - 1))),
            ),
            (
                CastOp::IntToWordS(w),
                LiteralValue::Int(Int::from(-(1i128 << (w.bits() - 1)))),
            ),
            (
                CastOp::IntToWordU(w),
                LiteralValue::Int(Int::from(Num::from(mask))),
            ),
        ] {
            vectors.push(record(Builtin::Cast(op), vec![arg]));
        }
        for endian in [Endian::Little, Endian::Big] {
            vectors.push(record(
                Builtin::Bytes(BytesOp::Decode(w, endian)),
                vec![LiteralValue::Bytes(bytes::Bytes::new())],
            ));
            vectors.push(record(
                Builtin::Bytes(BytesOp::Read(w, endian)),
                vec![
                    LiteralValue::Bytes(bytes::Bytes::new()),
                    LiteralValue::Nat(Num::ZERO),
                ],
            ));
            vectors.push(record(
                Builtin::Bytes(BytesOp::Write(w, endian)),
                vec![
                    LiteralValue::Bytes(bytes::Bytes::new()),
                    LiteralValue::Nat(Num::ZERO),
                    word(1),
                ],
            ));
        }
    }
    for op in [NatOp::Div, NatOp::Rem] {
        vectors.push(record(
            Builtin::Nat(op),
            vec![
                LiteralValue::Nat(Num::from(7u8)),
                LiteralValue::Nat(Num::ZERO),
            ],
        ));
    }
    for op in [IntOp::Div, IntOp::Rem] {
        vectors.push(record(
            Builtin::Int(op),
            vec![
                LiteralValue::Int(Int::from(-7)),
                LiteralValue::Int(Int::ZERO),
            ],
        ));
    }
    for (op, args) in [
        (
            Builtin::Nat(NatOp::Sub),
            vec![
                LiteralValue::Nat(Num::ZERO),
                LiteralValue::Nat(Num::from(5u8)),
            ],
        ),
        (
            Builtin::Nat(NatOp::Pred),
            vec![LiteralValue::Nat(Num::ZERO)],
        ),
        (
            Builtin::Int(IntOp::Rem),
            vec![
                LiteralValue::Int(Int::from(-7)),
                LiteralValue::Int(Int::from(3)),
            ],
        ),
        (
            Builtin::Int(IntOp::Div),
            vec![
                LiteralValue::Int(Int::from(-7)),
                LiteralValue::Int(Int::from(3)),
            ],
        ),
        (
            Builtin::Int(IntOp::Shr),
            vec![
                LiteralValue::Int(Int::from(-7)),
                LiteralValue::Nat(Num::from(1u8)),
            ],
        ),
        (
            Builtin::Bytes(BytesOp::Get),
            vec![
                LiteralValue::Bytes(vec![1].into()),
                LiteralValue::Nat(Num::from(1u8)),
            ],
        ),
        (
            Builtin::Bytes(BytesOp::Slice),
            vec![
                LiteralValue::Bytes(vec![1].into()),
                LiteralValue::Nat(Num::ZERO),
                LiteralValue::Nat(Num::from(2u8)),
            ],
        ),
        (
            Builtin::Cast(CastOp::IntToNat),
            vec![LiteralValue::Int(Int::from(-1))],
        ),
    ] {
        vectors.push(record(op, args));
    }
    for op in [
        NatOp::Add,
        NatOp::Mul,
        NatOp::Div,
        NatOp::Rem,
        NatOp::And,
        NatOp::Xor,
    ] {
        vectors.push(record(
            Builtin::Nat(op),
            vec![
                LiteralValue::Nat(Num::from_canonical_bytes(&[0x81; 33]).unwrap()),
                LiteralValue::Nat(Num::from(7u8)),
            ],
        ));
    }
    for op in [
        IntOp::Add,
        IntOp::Mul,
        IntOp::Div,
        IntOp::Rem,
        IntOp::And,
        IntOp::Xor,
    ] {
        vectors.push(record(
            Builtin::Int(op),
            vec![
                LiteralValue::Int(Int::from_canonical_bytes(&[0x81; 33]).unwrap()),
                LiteralValue::Int(Int::from(7)),
            ],
        ));
    }
    vectors
}
