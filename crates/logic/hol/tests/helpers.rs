//! Public convenience API remains independent of the builtin-reference layout.

use covalence_logic_hol::literals::{BoolOp, Builtin, EvalLimits, LiteralValue, WordOp, WordWidth};
use covalence_logic_hol::{AX_INF, Kernel};

#[test]
fn constructors_and_matchers_use_regular_applications() {
    let mut kernel = Kernel::new();
    kernel.add_axiom(AX_INF).unwrap();
    let left = kernel.literal(LiteralValue::I32(20)).unwrap();
    let right = kernel.literal(LiteralValue::I32(22)).unwrap();
    assert_eq!(kernel.len(), 0, "tiny arguments do not occupy arena rows");

    let sum = kernel.add_i32(left, right).unwrap();
    assert_eq!(kernel.match_add_i32(sum), Some([left, right]));
    assert_eq!(kernel.match_sub_i32(sum), None);
    assert_eq!(kernel.match_add_i16(sum), None);
    let add = kernel
        .builtin_const(Builtin::Word(WordWidth::W32, WordOp::Add))
        .unwrap();
    let partial = kernel.app(add, left).unwrap();
    assert_eq!(kernel.match_add_i32(add), None);
    assert_eq!(kernel.match_add_i32(partial), None);

    let (answer, _) = kernel.reduce_builtin(sum, EvalLimits::default()).unwrap();
    assert!(answer.get() < 0);
    assert_eq!(
        kernel.literal_value(answer).unwrap(),
        Some(LiteralValue::I32(42))
    );
    assert_eq!(kernel.find(sum).unwrap(), answer);
    assert_eq!(kernel.match_add_i32(sum), Some([left, right]));
}

#[test]
fn boolean_helpers_need_no_infinity_and_do_not_create_theorem_atoms() {
    let mut kernel = Kernel::new();
    let truth = kernel.literal(LiteralValue::Bool(true)).unwrap();
    let falsity = kernel.literal(LiteralValue::Bool(false)).unwrap();
    let conjunction = kernel.and(truth, falsity).unwrap();
    assert_eq!(kernel.match_and(conjunction), Some([truth, falsity]));
    assert_eq!(kernel.match_or(conjunction), None);
    let negation = kernel.not(conjunction).unwrap();
    assert_eq!(kernel.match_not(negation), Some([conjunction]));
    assert_eq!(kernel.match_iff(negation), None);
    let (answer, _) = kernel
        .reduce_builtin(negation, EvalLimits::default())
        .unwrap();
    assert_eq!(answer, truth);
    assert!(kernel.lit(answer).is_err());
    assert!(kernel.lit(negation).unwrap().is_positive());
    assert!(kernel.axioms().next().is_none());

    // Matchers recognize raw shape; typed construction remains checked.
    let function = kernel.builtin_const(Builtin::Bool(BoolOp::Not)).unwrap();
    let before = kernel.arena().clone();
    assert!(kernel.and(function, truth).is_err());
    assert_eq!(kernel.arena(), &before);
}
