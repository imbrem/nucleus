//! Frozen compact-builtin identifiers for the first Ethane wire contract.
//!
//! Builtins are syntax whose meaning will be supplied by canonical lowering;
//! they are deliberately absent from the opcode-free init manifest. Version 1
//! reserves every unassigned `u8` value independently in each arity family.
//! Future meanings must use a new code or a new row-tag version: an existing
//! `(family, code)` pair may never change meaning.
//!
//! See `docs/research/ethane-builtins-v1.md` for the lowering, equality,
//! resource, and compatibility policy that implementations must follow.

/// The registry version carried by the eventual versioned row tags.
pub const VERSION: u8 = 1;

/// Version-1 unary row tag.
pub const OP1_ROW_TAG: &str = "tm.op1.v1";

/// Version-1 binary row tag.
pub const OP2_ROW_TAG: &str = "tm.op2.v1";

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

    #[test]
    fn declarative_registry_matches_the_executable_registry() {
        let entries: Vec<_> = MANIFEST
            .lines()
            .filter(|line| !line.starts_with('#') && !line.is_empty())
            .collect();
        assert_eq!(
            entries,
            [
                "1\top1\t0\tnot\tbool\tbool",
                "1\top2\t0\tand\tbool,bool\tbool",
                "1\top2\t1\tor\tbool,bool\tbool",
                "1\top2\t2\timp\tbool,bool\tbool",
            ]
        );
        assert_eq!(Op1::from_code(0), Some(Op1::Not));
        assert_eq!(Op2::from_code(0), Some(Op2::And));
        assert_eq!(Op2::from_code(1), Some(Op2::Or));
        assert_eq!(Op2::from_code(2), Some(Op2::Imp));
        for entry in entries {
            let columns: Vec<_> = entry.split('\t').collect();
            assert_eq!(columns.len(), 6);
            assert_eq!(columns[0], VERSION.to_string());
            assert_eq!(columns[5], "bool");
            let code: u8 = columns[2].parse().unwrap();
            match columns[1] {
                "op1" => {
                    let op = Op1::from_code(code).unwrap();
                    assert_eq!(columns[3], op.name());
                    assert_eq!(columns[4], "bool");
                }
                "op2" => {
                    let op = Op2::from_code(code).unwrap();
                    assert_eq!(columns[3], op.name());
                    assert_eq!(columns[4], "bool,bool");
                }
                family => panic!("unknown builtin family {family}"),
            }
        }
    }

    #[test]
    fn reserved_and_unknown_codes_are_rejected() {
        assert_eq!(Op1::from_code(1), None);
        assert_eq!(Op1::from_code(u8::MAX), None);
        assert_eq!(Op2::from_code(3), None);
        assert_eq!(Op2::from_code(u8::MAX), None);
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
