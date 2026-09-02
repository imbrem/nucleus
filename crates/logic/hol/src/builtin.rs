//! Frozen compact-builtin identifiers for the first Ethane wire contract.
//!
//! Builtins are syntax. Their meaning comes from lowering to the opcode-free
//! definitions in the init slice, so they are absent from the init manifest.
//!
//! Version 1 reserves every unassigned `u8` in each family. An existing
//! `(family, code)` pair never changes meaning; new operations take unused
//! codes or a new row-tag version.
//!
//! Families split by arity and by whether the kernel can type them:
//!
//! - `op1` and `op2` are the Boolean connectives. The kernel types them
//!   directly, since `ty.bool` is a sort it defines itself.
//! - `num1` and `num2` are numeric. The kernel cannot type one until the init
//!   slice defines `nat` and `int`, so a numeric row is well formed on the
//!   wire and rejected by row validation, like an unlowered literal.
//!
//! Assigning a code promises a meaning, not a construction.
//!
//! See `docs/research/ethane-builtins-v1.md` for the lowering, totality,
//! equality, resource, and compatibility policy.

/// The registry version carried by the versioned row tags.
pub const VERSION: u8 = 1;

/// Version-1 unary row tag.
pub const OP1_ROW_TAG: &str = "tm.op1.v1";

/// Version-1 binary row tag.
pub const OP2_ROW_TAG: &str = "tm.op2.v1";

/// Version-1 unary numeric row tag.
pub const NUM1_ROW_TAG: &str = "tm.num1.v1";

/// Version-1 binary numeric row tag.
pub const NUM2_ROW_TAG: &str = "tm.num2.v1";

/// A sort a numeric builtin operates over.
///
/// `Nat` and `Int` name constants the init slice must define; `Bool` is
/// `ty.bool`, which the kernel types on its own.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NumSort {
    Bool,
    Nat,
    Int,
}

impl NumSort {
    /// The registry spelling of this sort.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Bool => "bool",
            Self::Nat => "nat",
            Self::Int => "int",
        }
    }
}

/// The result an operation gives where the mathematical operation is undefined.
///
/// Ethane has no partial operations, so this is part of the frozen meaning.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Total {
    /// Defined on every input.
    Never,
    /// Gives the zero of its result sort.
    Zero,
    /// Gives the dividend unchanged.
    Dividend,
}

impl Total {
    /// The registry spelling of this fallback.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Never => "-",
            Self::Zero => "zero",
            Self::Dividend => "dividend",
        }
    }
}

/// The sorts one numeric opcode consumes and produces.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Signature {
    /// Operand sorts, left to right.
    pub operands: &'static [NumSort],
    /// Result sort.
    pub result: NumSort,
    /// The result where the mathematical operation is undefined.
    pub total: Total,
}

/// Unary Boolean builtins. All codes other than zero are reserved in v1.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Op1 {
    Not = 0,
}

impl Op1 {
    #[must_use]
    pub const fn code(self) -> u8 {
        self as u8
    }

    #[must_use]
    pub const fn from_code(code: u8) -> Option<Self> {
        match code {
            0 => Some(Self::Not),
            _ => None,
        }
    }

    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Not => "not",
        }
    }
}

/// Binary Boolean builtins. Codes 3 through 255 are reserved in v1.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Op2 {
    And = 0,
    Or = 1,
    Imp = 2,
}

impl Op2 {
    #[must_use]
    pub const fn code(self) -> u8 {
        self as u8
    }

    #[must_use]
    pub const fn from_code(code: u8) -> Option<Self> {
        match code {
            0 => Some(Self::And),
            1 => Some(Self::Or),
            2 => Some(Self::Imp),
            _ => None,
        }
    }

    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::And => "and",
            Self::Or => "or",
            Self::Imp => "imp",
        }
    }
}

/// Unary numeric builtins. Every unassigned code is reserved in v1.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Num1 {
    NatSucc = 0,
    NatPred = 1,
    IntSucc = 2,
    IntPred = 3,
    IntAbs = 4,
    IntSign = 5,
    NatToInt = 6,
    IntToNatZigzag = 7,
    NatToIntZigzag = 8,
    IntNeg = 9,
}

/// Signature of every assigned `num1` code, indexed by that code.
const SIGNATURES_NUM1: [Signature; 10] = [
    Signature {
        operands: &[NumSort::Nat],
        result: NumSort::Nat,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Nat],
        result: NumSort::Nat,
        total: Total::Zero,
    },
    Signature {
        operands: &[NumSort::Int],
        result: NumSort::Int,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Int],
        result: NumSort::Int,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Int],
        result: NumSort::Nat,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Int],
        result: NumSort::Int,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Nat],
        result: NumSort::Int,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Int],
        result: NumSort::Nat,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Nat],
        result: NumSort::Int,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Int],
        result: NumSort::Int,
        total: Total::Never,
    },
];

impl Num1 {
    /// This opcode's wire code.
    #[must_use]
    pub const fn code(self) -> u8 {
        self as u8
    }

    /// The opcode a wire code names, if v1 assigns one.
    #[must_use]
    pub const fn from_code(code: u8) -> Option<Self> {
        match code {
            0 => Some(Self::NatSucc),
            1 => Some(Self::NatPred),
            2 => Some(Self::IntSucc),
            3 => Some(Self::IntPred),
            4 => Some(Self::IntAbs),
            5 => Some(Self::IntSign),
            6 => Some(Self::NatToInt),
            7 => Some(Self::IntToNatZigzag),
            8 => Some(Self::NatToIntZigzag),
            9 => Some(Self::IntNeg),
            _ => None,
        }
    }

    /// The registry name, which is also the init constant this lowers to.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::NatSucc => "nat.succ",
            Self::NatPred => "nat.pred",
            Self::IntSucc => "int.succ",
            Self::IntPred => "int.pred",
            Self::IntAbs => "int.abs",
            Self::IntSign => "int.sign",
            Self::NatToInt => "nat.to_int",
            Self::IntToNatZigzag => "int.to_nat.zigzag",
            Self::NatToIntZigzag => "nat.to_int.zigzag",
            Self::IntNeg => "int.neg",
        }
    }

    /// The sorts this opcode consumes and produces.
    #[must_use]
    pub const fn signature(self) -> Signature {
        SIGNATURES_NUM1[self.code() as usize]
    }
}

/// Binary numeric builtins. Every unassigned code is reserved in v1.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Num2 {
    NatAdd = 0,
    NatSub = 1,
    NatMul = 2,
    NatDiv = 3,
    NatMod = 4,
    NatLe = 5,
    NatLt = 6,
    IntAdd = 7,
    IntSub = 8,
    IntMul = 9,
    IntDiv = 10,
    IntMod = 11,
    IntLe = 12,
    IntLt = 13,
}

/// Signature of every assigned `num2` code, indexed by that code.
const SIGNATURES_NUM2: [Signature; 14] = [
    Signature {
        operands: &[NumSort::Nat, NumSort::Nat],
        result: NumSort::Nat,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Nat, NumSort::Nat],
        result: NumSort::Nat,
        total: Total::Zero,
    },
    Signature {
        operands: &[NumSort::Nat, NumSort::Nat],
        result: NumSort::Nat,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Nat, NumSort::Nat],
        result: NumSort::Nat,
        total: Total::Zero,
    },
    Signature {
        operands: &[NumSort::Nat, NumSort::Nat],
        result: NumSort::Nat,
        total: Total::Dividend,
    },
    Signature {
        operands: &[NumSort::Nat, NumSort::Nat],
        result: NumSort::Bool,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Nat, NumSort::Nat],
        result: NumSort::Bool,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Int, NumSort::Int],
        result: NumSort::Int,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Int, NumSort::Int],
        result: NumSort::Int,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Int, NumSort::Int],
        result: NumSort::Int,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Int, NumSort::Int],
        result: NumSort::Int,
        total: Total::Zero,
    },
    Signature {
        operands: &[NumSort::Int, NumSort::Int],
        result: NumSort::Int,
        total: Total::Dividend,
    },
    Signature {
        operands: &[NumSort::Int, NumSort::Int],
        result: NumSort::Bool,
        total: Total::Never,
    },
    Signature {
        operands: &[NumSort::Int, NumSort::Int],
        result: NumSort::Bool,
        total: Total::Never,
    },
];

impl Num2 {
    /// This opcode's wire code.
    #[must_use]
    pub const fn code(self) -> u8 {
        self as u8
    }

    /// The opcode a wire code names, if v1 assigns one.
    #[must_use]
    pub const fn from_code(code: u8) -> Option<Self> {
        match code {
            0 => Some(Self::NatAdd),
            1 => Some(Self::NatSub),
            2 => Some(Self::NatMul),
            3 => Some(Self::NatDiv),
            4 => Some(Self::NatMod),
            5 => Some(Self::NatLe),
            6 => Some(Self::NatLt),
            7 => Some(Self::IntAdd),
            8 => Some(Self::IntSub),
            9 => Some(Self::IntMul),
            10 => Some(Self::IntDiv),
            11 => Some(Self::IntMod),
            12 => Some(Self::IntLe),
            13 => Some(Self::IntLt),
            _ => None,
        }
    }

    /// The registry name, which is also the init constant this lowers to.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::NatAdd => "nat.add",
            Self::NatSub => "nat.sub",
            Self::NatMul => "nat.mul",
            Self::NatDiv => "nat.div",
            Self::NatMod => "nat.mod",
            Self::NatLe => "nat.le",
            Self::NatLt => "nat.lt",
            Self::IntAdd => "int.add",
            Self::IntSub => "int.sub",
            Self::IntMul => "int.mul",
            Self::IntDiv => "int.div",
            Self::IntMod => "int.mod",
            Self::IntLe => "int.le",
            Self::IntLt => "int.lt",
        }
    }

    /// The sorts this opcode consumes and produces.
    #[must_use]
    pub const fn signature(self) -> Signature {
        SIGNATURES_NUM2[self.code() as usize]
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;

    use super::*;
    use crate::Ref;
    use crate::row::{Expr, Row, RowSerde};
    use covalence_lib_cbor::{from_reader, into_writer};

    const MANIFEST: &str = include_str!("../builtins-v1.tsv");

    const fn reference(value: i32) -> Ref {
        Ref::new(value).unwrap()
    }

    /// Checks every registry column against the executable tables.
    ///
    /// Lean pins the TSV bytes, so this compares field by field instead of
    /// restating the file.
    #[test]
    fn declarative_registry_matches_the_executable_registry() {
        let mut counts = (0_u8, 0_u8, 0_u8, 0_u8);
        for line in MANIFEST.lines() {
            if line.starts_with('#') || line.is_empty() {
                continue;
            }
            let columns: Vec<_> = line.split('\t').collect();
            assert_eq!(columns.len(), 7, "{line}");
            assert_eq!(columns[0], VERSION.to_string(), "{line}");
            let code: u8 = columns[2].parse().unwrap();
            match columns[1] {
                // The Boolean families carry no signature: the kernel types
                // them directly, and every operand and result is `bool`.
                "op1" => {
                    assert_eq!(code, counts.0);
                    counts.0 += 1;
                    assert_eq!(columns[3], Op1::from_code(code).unwrap().name(), "{line}");
                    assert_eq!(columns[4], "bool", "{line}");
                    assert_eq!(columns[5], "bool", "{line}");
                    assert_eq!(columns[6], "-", "{line}");
                }
                "op2" => {
                    assert_eq!(code, counts.1);
                    counts.1 += 1;
                    assert_eq!(columns[3], Op2::from_code(code).unwrap().name(), "{line}");
                    assert_eq!(columns[4], "bool,bool", "{line}");
                    assert_eq!(columns[5], "bool", "{line}");
                    assert_eq!(columns[6], "-", "{line}");
                }
                "num1" => {
                    assert_eq!(code, counts.2);
                    counts.2 += 1;
                    let op = Num1::from_code(code).unwrap();
                    assert_eq!(columns[3], op.name(), "{line}");
                    assert_signature(&columns, op.signature(), line);
                }
                "num2" => {
                    assert_eq!(code, counts.3);
                    counts.3 += 1;
                    let op = Num2::from_code(code).unwrap();
                    assert_eq!(columns[3], op.name(), "{line}");
                    assert_signature(&columns, op.signature(), line);
                }
                family => panic!("unknown builtin family {family}"),
            }
        }
        assert_eq!(usize::from(counts.2), SIGNATURES_NUM1.len());
        assert_eq!(usize::from(counts.3), SIGNATURES_NUM2.len());
    }

    fn assert_signature(columns: &[&str], signature: Signature, line: &str) {
        let operands: Vec<_> = signature.operands.iter().map(|sort| sort.name()).collect();
        assert_eq!(columns[4], operands.join(","), "{line}");
        assert_eq!(columns[5], signature.result.name(), "{line}");
        assert_eq!(columns[6], signature.total.name(), "{line}");
    }

    /// Codes past the last assigned one, and the top of the range, stay reserved.
    #[test]
    fn reserved_and_unknown_codes_are_rejected() {
        assert_eq!(Op1::from_code(1), None);
        assert_eq!(Op1::from_code(u8::MAX), None);
        assert_eq!(Op2::from_code(3), None);
        assert_eq!(Op2::from_code(u8::MAX), None);
        assert_eq!(
            Num1::from_code(u8::try_from(SIGNATURES_NUM1.len()).unwrap()),
            None
        );
        assert_eq!(Num1::from_code(u8::MAX), None);
        assert_eq!(
            Num2::from_code(u8::try_from(SIGNATURES_NUM2.len()).unwrap()),
            None
        );
        assert_eq!(Num2::from_code(u8::MAX), None);
    }

    /// A comparison has a `bool` result but numeric operands, so a `bool`
    /// result alone does not make an opcode Boolean.
    #[test]
    fn comparisons_return_bool_from_the_numeric_families() {
        for op in [Num2::NatLe, Num2::NatLt, Num2::IntLe, Num2::IntLt] {
            assert_eq!(op.signature().result, NumSort::Bool);
        }
    }

    /// Division and remainder by zero keep `a = b * (a / b) + a % b`: the
    /// quotient is zero and the remainder is the dividend, as in Lean, Coq and
    /// Isabelle/HOL.
    #[test]
    fn totality_fallbacks_are_pinned_where_mathematics_gives_none() {
        for op in [Num2::NatSub, Num2::NatDiv, Num2::IntDiv] {
            assert_eq!(op.signature().total, Total::Zero, "{}", op.name());
        }
        for op in [Num2::NatMod, Num2::IntMod] {
            assert_eq!(op.signature().total, Total::Dividend, "{}", op.name());
        }
        assert_eq!(Num1::NatPred.signature().total, Total::Zero);
        assert_eq!(Num2::NatAdd.signature().total, Total::Never);
    }

    #[test]
    fn row_level_v1_goldens_freeze_tags_codes_and_operand_order() {
        let one = reference(1);
        let two = reference(2);
        for (row, golden) in [
            (
                Row::new(Expr::Op1(Op1::Not, one)),
                "a36374616769746d2e6f70312e76316369787381016376616c00",
            ),
            (
                Row::new(Expr::Op2(Op2::And, one, two)),
                "a36374616769746d2e6f70322e7631636978738201026376616c00",
            ),
            (
                Row::new(Expr::Op2(Op2::Or, one, two)),
                "a36374616769746d2e6f70322e7631636978738201026376616c01",
            ),
            (
                Row::new(Expr::Op2(Op2::Imp, one, two)),
                "a36374616769746d2e6f70322e7631636978738201026376616c02",
            ),
        ] {
            let mut bytes = Vec::new();
            into_writer(&row.encode(&[]).unwrap(), &mut bytes).unwrap();
            assert_eq!(hex(&bytes), golden);
            let wire = from_reader::<RowSerde, _>(bytes.as_slice()).unwrap();
            assert_eq!(Row::decode(wire, &mut Vec::new()).unwrap(), row);
        }
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().fold(String::new(), |mut output, byte| {
            write!(output, "{byte:02x}").unwrap();
            output
        })
    }
}
