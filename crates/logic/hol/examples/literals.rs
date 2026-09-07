//! Checked construction without exposing rows or constant-table allocation.

use covalence_data_num::{Int, Num};
use covalence_logic_hol::literals::{
    Builtin, BytesOp, EvalLimits, LiteralValue, WordOp, WordWidth,
};
use covalence_logic_hol::{AX_INF, Kernel, KernelError};

fn main() -> Result<(), KernelError> {
    let mut kernel = Kernel::new();
    kernel.add_axiom(AX_INF)?;

    let left = kernel.literal(LiteralValue::I32(20))?;
    let right = kernel.literal(LiteralValue::I32(22))?;
    let add = kernel.builtin_const(Builtin::Word(WordWidth::W32, WordOp::Add))?;
    let add_twenty = kernel.app(add, left)?;
    let sum = kernel.app(add_twenty, right)?;
    let (result, theorem) = kernel.reduce_builtin(sum, EvalLimits::default())?;
    assert_eq!(kernel.literal_value(result)?, Some(LiteralValue::I32(42)));
    assert!(kernel.theorems().get(theorem).is_some());

    let large = &Num::from(1_u8) << 200;
    kernel.literal(LiteralValue::Nat(large))?;
    kernel.literal(LiteralValue::Int(Int::from(-7)))?;
    let wasm_magic = kernel.literal(LiteralValue::Bytes(vec![0, b'a', b's', b'm'].into()))?;
    let length = kernel.builtin(Builtin::Bytes(BytesOp::Length), &[wasm_magic])?;
    let (result, _) = kernel.reduce_builtin(length, EvalLimits::default())?;
    assert_eq!(
        kernel.literal_value(result)?,
        Some(LiteralValue::Nat(Num::from(4_u8)))
    );
    Ok(())
}
