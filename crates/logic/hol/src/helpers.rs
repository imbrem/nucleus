//! Ergonomic construction and structural matching of ordinary builtin applications.
//!
//! These helpers add no representation or trusted rule. Construction delegates
//! to `Kernel::builtin`; matching checks the descriptor and exact argument count.
//! Raw arena matches describe syntax only, not checked typing or theorem facts.

use crate::literals::{BoolOp, Builtin, BytesOp, IntOp, NatOp, WordOp, WordWidth};
use crate::{Arena, Kernel, KernelError, Ref};

fn arguments<const N: usize>(arena: &Arena, term: Ref, operation: Builtin) -> Option<[Ref; N]> {
    let (actual, arguments) = arena.builtin_application(term)?;
    (actual == operation).then_some(arguments)?.try_into().ok()
}

macro_rules! helpers {
    ($($name:ident, $matcher:ident => $operation:expr; $arity:literal; ($($arg:ident),+);)+) => {
        impl Kernel {
            $(
                #[doc = concat!("Constructs `", stringify!($operation), "` using ordinary applications.")]
                ///
                /// # Errors
                ///
                /// Rejects incorrect argument types, missing capabilities, or arena exhaustion.
                pub fn $name(&mut self, $($arg: Ref),+) -> Result<Ref, KernelError> {
                    self.builtin($operation, &[$($arg),+])
                }
            )+
        }
        impl Arena {
            $(
                #[doc = concat!("Matches a fully applied `", stringify!($operation), "` in argument order.")]
                ///
                /// This checks raw syntax and arity, not typing or theorem authority.
                #[must_use]
                pub fn $matcher(&self, term: Ref) -> Option<[Ref; $arity]> {
                    arguments(self, term, $operation)
                }
            )+
        }
    };
}

helpers! {
    not, match_not => Builtin::Bool(BoolOp::Not); 1; (value);
    and, match_and => Builtin::Bool(BoolOp::And); 2; (lhs, rhs);
    or, match_or => Builtin::Bool(BoolOp::Or); 2; (lhs, rhs);
    implies, match_implies => Builtin::Bool(BoolOp::Imp); 2; (lhs, rhs);
    iff, match_iff => Builtin::Bool(BoolOp::Iff); 2; (lhs, rhs);

    add_i8, match_add_i8 => Builtin::Word(WordWidth::W8, WordOp::Add); 2; (lhs, rhs);
    sub_i8, match_sub_i8 => Builtin::Word(WordWidth::W8, WordOp::Sub); 2; (lhs, rhs);
    mul_i8, match_mul_i8 => Builtin::Word(WordWidth::W8, WordOp::Mul); 2; (lhs, rhs);
    div_u_i8, match_div_u_i8 => Builtin::Word(WordWidth::W8, WordOp::DivU); 2; (lhs, rhs);
    div_s_i8, match_div_s_i8 => Builtin::Word(WordWidth::W8, WordOp::DivS); 2; (lhs, rhs);
    rem_u_i8, match_rem_u_i8 => Builtin::Word(WordWidth::W8, WordOp::RemU); 2; (lhs, rhs);
    rem_s_i8, match_rem_s_i8 => Builtin::Word(WordWidth::W8, WordOp::RemS); 2; (lhs, rhs);
    and_i8, match_and_i8 => Builtin::Word(WordWidth::W8, WordOp::And); 2; (lhs, rhs);
    or_i8, match_or_i8 => Builtin::Word(WordWidth::W8, WordOp::Or); 2; (lhs, rhs);
    xor_i8, match_xor_i8 => Builtin::Word(WordWidth::W8, WordOp::Xor); 2; (lhs, rhs);
    not_i8, match_not_i8 => Builtin::Word(WordWidth::W8, WordOp::Not); 1; (value);
    shl_i8, match_shl_i8 => Builtin::Word(WordWidth::W8, WordOp::Shl); 2; (lhs, rhs);
    shr_u_i8, match_shr_u_i8 => Builtin::Word(WordWidth::W8, WordOp::ShrU); 2; (lhs, rhs);
    shr_s_i8, match_shr_s_i8 => Builtin::Word(WordWidth::W8, WordOp::ShrS); 2; (lhs, rhs);
    rotl_i8, match_rotl_i8 => Builtin::Word(WordWidth::W8, WordOp::Rotl); 2; (lhs, rhs);
    rotr_i8, match_rotr_i8 => Builtin::Word(WordWidth::W8, WordOp::Rotr); 2; (lhs, rhs);
    clz_i8, match_clz_i8 => Builtin::Word(WordWidth::W8, WordOp::Clz); 1; (value);
    ctz_i8, match_ctz_i8 => Builtin::Word(WordWidth::W8, WordOp::Ctz); 1; (value);
    popcnt_i8, match_popcnt_i8 => Builtin::Word(WordWidth::W8, WordOp::Popcnt); 1; (value);
    eqz_i8, match_eqz_i8 => Builtin::Word(WordWidth::W8, WordOp::Eqz); 1; (value);
    eq_i8, match_eq_i8 => Builtin::Word(WordWidth::W8, WordOp::Eq); 2; (lhs, rhs);
    ne_i8, match_ne_i8 => Builtin::Word(WordWidth::W8, WordOp::Ne); 2; (lhs, rhs);
    lt_u_i8, match_lt_u_i8 => Builtin::Word(WordWidth::W8, WordOp::LtU); 2; (lhs, rhs);
    le_u_i8, match_le_u_i8 => Builtin::Word(WordWidth::W8, WordOp::LeU); 2; (lhs, rhs);
    gt_u_i8, match_gt_u_i8 => Builtin::Word(WordWidth::W8, WordOp::GtU); 2; (lhs, rhs);
    ge_u_i8, match_ge_u_i8 => Builtin::Word(WordWidth::W8, WordOp::GeU); 2; (lhs, rhs);
    lt_s_i8, match_lt_s_i8 => Builtin::Word(WordWidth::W8, WordOp::LtS); 2; (lhs, rhs);
    le_s_i8, match_le_s_i8 => Builtin::Word(WordWidth::W8, WordOp::LeS); 2; (lhs, rhs);
    gt_s_i8, match_gt_s_i8 => Builtin::Word(WordWidth::W8, WordOp::GtS); 2; (lhs, rhs);
    ge_s_i8, match_ge_s_i8 => Builtin::Word(WordWidth::W8, WordOp::GeS); 2; (lhs, rhs);

    add_i16, match_add_i16 => Builtin::Word(WordWidth::W16, WordOp::Add); 2; (lhs, rhs);
    sub_i16, match_sub_i16 => Builtin::Word(WordWidth::W16, WordOp::Sub); 2; (lhs, rhs);
    mul_i16, match_mul_i16 => Builtin::Word(WordWidth::W16, WordOp::Mul); 2; (lhs, rhs);
    div_u_i16, match_div_u_i16 => Builtin::Word(WordWidth::W16, WordOp::DivU); 2; (lhs, rhs);
    div_s_i16, match_div_s_i16 => Builtin::Word(WordWidth::W16, WordOp::DivS); 2; (lhs, rhs);
    rem_u_i16, match_rem_u_i16 => Builtin::Word(WordWidth::W16, WordOp::RemU); 2; (lhs, rhs);
    rem_s_i16, match_rem_s_i16 => Builtin::Word(WordWidth::W16, WordOp::RemS); 2; (lhs, rhs);
    and_i16, match_and_i16 => Builtin::Word(WordWidth::W16, WordOp::And); 2; (lhs, rhs);
    or_i16, match_or_i16 => Builtin::Word(WordWidth::W16, WordOp::Or); 2; (lhs, rhs);
    xor_i16, match_xor_i16 => Builtin::Word(WordWidth::W16, WordOp::Xor); 2; (lhs, rhs);
    not_i16, match_not_i16 => Builtin::Word(WordWidth::W16, WordOp::Not); 1; (value);
    shl_i16, match_shl_i16 => Builtin::Word(WordWidth::W16, WordOp::Shl); 2; (lhs, rhs);
    shr_u_i16, match_shr_u_i16 => Builtin::Word(WordWidth::W16, WordOp::ShrU); 2; (lhs, rhs);
    shr_s_i16, match_shr_s_i16 => Builtin::Word(WordWidth::W16, WordOp::ShrS); 2; (lhs, rhs);
    rotl_i16, match_rotl_i16 => Builtin::Word(WordWidth::W16, WordOp::Rotl); 2; (lhs, rhs);
    rotr_i16, match_rotr_i16 => Builtin::Word(WordWidth::W16, WordOp::Rotr); 2; (lhs, rhs);
    clz_i16, match_clz_i16 => Builtin::Word(WordWidth::W16, WordOp::Clz); 1; (value);
    ctz_i16, match_ctz_i16 => Builtin::Word(WordWidth::W16, WordOp::Ctz); 1; (value);
    popcnt_i16, match_popcnt_i16 => Builtin::Word(WordWidth::W16, WordOp::Popcnt); 1; (value);
    eqz_i16, match_eqz_i16 => Builtin::Word(WordWidth::W16, WordOp::Eqz); 1; (value);
    eq_i16, match_eq_i16 => Builtin::Word(WordWidth::W16, WordOp::Eq); 2; (lhs, rhs);
    ne_i16, match_ne_i16 => Builtin::Word(WordWidth::W16, WordOp::Ne); 2; (lhs, rhs);
    lt_u_i16, match_lt_u_i16 => Builtin::Word(WordWidth::W16, WordOp::LtU); 2; (lhs, rhs);
    le_u_i16, match_le_u_i16 => Builtin::Word(WordWidth::W16, WordOp::LeU); 2; (lhs, rhs);
    gt_u_i16, match_gt_u_i16 => Builtin::Word(WordWidth::W16, WordOp::GtU); 2; (lhs, rhs);
    ge_u_i16, match_ge_u_i16 => Builtin::Word(WordWidth::W16, WordOp::GeU); 2; (lhs, rhs);
    lt_s_i16, match_lt_s_i16 => Builtin::Word(WordWidth::W16, WordOp::LtS); 2; (lhs, rhs);
    le_s_i16, match_le_s_i16 => Builtin::Word(WordWidth::W16, WordOp::LeS); 2; (lhs, rhs);
    gt_s_i16, match_gt_s_i16 => Builtin::Word(WordWidth::W16, WordOp::GtS); 2; (lhs, rhs);
    ge_s_i16, match_ge_s_i16 => Builtin::Word(WordWidth::W16, WordOp::GeS); 2; (lhs, rhs);

    add_i32, match_add_i32 => Builtin::Word(WordWidth::W32, WordOp::Add); 2; (lhs, rhs);
    sub_i32, match_sub_i32 => Builtin::Word(WordWidth::W32, WordOp::Sub); 2; (lhs, rhs);
    mul_i32, match_mul_i32 => Builtin::Word(WordWidth::W32, WordOp::Mul); 2; (lhs, rhs);
    div_u_i32, match_div_u_i32 => Builtin::Word(WordWidth::W32, WordOp::DivU); 2; (lhs, rhs);
    div_s_i32, match_div_s_i32 => Builtin::Word(WordWidth::W32, WordOp::DivS); 2; (lhs, rhs);
    rem_u_i32, match_rem_u_i32 => Builtin::Word(WordWidth::W32, WordOp::RemU); 2; (lhs, rhs);
    rem_s_i32, match_rem_s_i32 => Builtin::Word(WordWidth::W32, WordOp::RemS); 2; (lhs, rhs);
    and_i32, match_and_i32 => Builtin::Word(WordWidth::W32, WordOp::And); 2; (lhs, rhs);
    or_i32, match_or_i32 => Builtin::Word(WordWidth::W32, WordOp::Or); 2; (lhs, rhs);
    xor_i32, match_xor_i32 => Builtin::Word(WordWidth::W32, WordOp::Xor); 2; (lhs, rhs);
    not_i32, match_not_i32 => Builtin::Word(WordWidth::W32, WordOp::Not); 1; (value);
    shl_i32, match_shl_i32 => Builtin::Word(WordWidth::W32, WordOp::Shl); 2; (lhs, rhs);
    shr_u_i32, match_shr_u_i32 => Builtin::Word(WordWidth::W32, WordOp::ShrU); 2; (lhs, rhs);
    shr_s_i32, match_shr_s_i32 => Builtin::Word(WordWidth::W32, WordOp::ShrS); 2; (lhs, rhs);
    rotl_i32, match_rotl_i32 => Builtin::Word(WordWidth::W32, WordOp::Rotl); 2; (lhs, rhs);
    rotr_i32, match_rotr_i32 => Builtin::Word(WordWidth::W32, WordOp::Rotr); 2; (lhs, rhs);
    clz_i32, match_clz_i32 => Builtin::Word(WordWidth::W32, WordOp::Clz); 1; (value);
    ctz_i32, match_ctz_i32 => Builtin::Word(WordWidth::W32, WordOp::Ctz); 1; (value);
    popcnt_i32, match_popcnt_i32 => Builtin::Word(WordWidth::W32, WordOp::Popcnt); 1; (value);
    eqz_i32, match_eqz_i32 => Builtin::Word(WordWidth::W32, WordOp::Eqz); 1; (value);
    eq_i32, match_eq_i32 => Builtin::Word(WordWidth::W32, WordOp::Eq); 2; (lhs, rhs);
    ne_i32, match_ne_i32 => Builtin::Word(WordWidth::W32, WordOp::Ne); 2; (lhs, rhs);
    lt_u_i32, match_lt_u_i32 => Builtin::Word(WordWidth::W32, WordOp::LtU); 2; (lhs, rhs);
    le_u_i32, match_le_u_i32 => Builtin::Word(WordWidth::W32, WordOp::LeU); 2; (lhs, rhs);
    gt_u_i32, match_gt_u_i32 => Builtin::Word(WordWidth::W32, WordOp::GtU); 2; (lhs, rhs);
    ge_u_i32, match_ge_u_i32 => Builtin::Word(WordWidth::W32, WordOp::GeU); 2; (lhs, rhs);
    lt_s_i32, match_lt_s_i32 => Builtin::Word(WordWidth::W32, WordOp::LtS); 2; (lhs, rhs);
    le_s_i32, match_le_s_i32 => Builtin::Word(WordWidth::W32, WordOp::LeS); 2; (lhs, rhs);
    gt_s_i32, match_gt_s_i32 => Builtin::Word(WordWidth::W32, WordOp::GtS); 2; (lhs, rhs);
    ge_s_i32, match_ge_s_i32 => Builtin::Word(WordWidth::W32, WordOp::GeS); 2; (lhs, rhs);

    add_i64, match_add_i64 => Builtin::Word(WordWidth::W64, WordOp::Add); 2; (lhs, rhs);
    sub_i64, match_sub_i64 => Builtin::Word(WordWidth::W64, WordOp::Sub); 2; (lhs, rhs);
    mul_i64, match_mul_i64 => Builtin::Word(WordWidth::W64, WordOp::Mul); 2; (lhs, rhs);
    div_u_i64, match_div_u_i64 => Builtin::Word(WordWidth::W64, WordOp::DivU); 2; (lhs, rhs);
    div_s_i64, match_div_s_i64 => Builtin::Word(WordWidth::W64, WordOp::DivS); 2; (lhs, rhs);
    rem_u_i64, match_rem_u_i64 => Builtin::Word(WordWidth::W64, WordOp::RemU); 2; (lhs, rhs);
    rem_s_i64, match_rem_s_i64 => Builtin::Word(WordWidth::W64, WordOp::RemS); 2; (lhs, rhs);
    and_i64, match_and_i64 => Builtin::Word(WordWidth::W64, WordOp::And); 2; (lhs, rhs);
    or_i64, match_or_i64 => Builtin::Word(WordWidth::W64, WordOp::Or); 2; (lhs, rhs);
    xor_i64, match_xor_i64 => Builtin::Word(WordWidth::W64, WordOp::Xor); 2; (lhs, rhs);
    not_i64, match_not_i64 => Builtin::Word(WordWidth::W64, WordOp::Not); 1; (value);
    shl_i64, match_shl_i64 => Builtin::Word(WordWidth::W64, WordOp::Shl); 2; (lhs, rhs);
    shr_u_i64, match_shr_u_i64 => Builtin::Word(WordWidth::W64, WordOp::ShrU); 2; (lhs, rhs);
    shr_s_i64, match_shr_s_i64 => Builtin::Word(WordWidth::W64, WordOp::ShrS); 2; (lhs, rhs);
    rotl_i64, match_rotl_i64 => Builtin::Word(WordWidth::W64, WordOp::Rotl); 2; (lhs, rhs);
    rotr_i64, match_rotr_i64 => Builtin::Word(WordWidth::W64, WordOp::Rotr); 2; (lhs, rhs);
    clz_i64, match_clz_i64 => Builtin::Word(WordWidth::W64, WordOp::Clz); 1; (value);
    ctz_i64, match_ctz_i64 => Builtin::Word(WordWidth::W64, WordOp::Ctz); 1; (value);
    popcnt_i64, match_popcnt_i64 => Builtin::Word(WordWidth::W64, WordOp::Popcnt); 1; (value);
    eqz_i64, match_eqz_i64 => Builtin::Word(WordWidth::W64, WordOp::Eqz); 1; (value);
    eq_i64, match_eq_i64 => Builtin::Word(WordWidth::W64, WordOp::Eq); 2; (lhs, rhs);
    ne_i64, match_ne_i64 => Builtin::Word(WordWidth::W64, WordOp::Ne); 2; (lhs, rhs);
    lt_u_i64, match_lt_u_i64 => Builtin::Word(WordWidth::W64, WordOp::LtU); 2; (lhs, rhs);
    le_u_i64, match_le_u_i64 => Builtin::Word(WordWidth::W64, WordOp::LeU); 2; (lhs, rhs);
    gt_u_i64, match_gt_u_i64 => Builtin::Word(WordWidth::W64, WordOp::GtU); 2; (lhs, rhs);
    ge_u_i64, match_ge_u_i64 => Builtin::Word(WordWidth::W64, WordOp::GeU); 2; (lhs, rhs);
    lt_s_i64, match_lt_s_i64 => Builtin::Word(WordWidth::W64, WordOp::LtS); 2; (lhs, rhs);
    le_s_i64, match_le_s_i64 => Builtin::Word(WordWidth::W64, WordOp::LeS); 2; (lhs, rhs);
    gt_s_i64, match_gt_s_i64 => Builtin::Word(WordWidth::W64, WordOp::GtS); 2; (lhs, rhs);
    ge_s_i64, match_ge_s_i64 => Builtin::Word(WordWidth::W64, WordOp::GeS); 2; (lhs, rhs);

    add_nat, match_add_nat => Builtin::Nat(NatOp::Add); 2; (lhs, rhs);
    sub_nat, match_sub_nat => Builtin::Nat(NatOp::Sub); 2; (lhs, rhs);
    mul_nat, match_mul_nat => Builtin::Nat(NatOp::Mul); 2; (lhs, rhs);
    div_nat, match_div_nat => Builtin::Nat(NatOp::Div); 2; (lhs, rhs);
    rem_nat, match_rem_nat => Builtin::Nat(NatOp::Rem); 2; (lhs, rhs);
    succ_nat, match_succ_nat => Builtin::Nat(NatOp::Succ); 1; (value);
    pred_nat, match_pred_nat => Builtin::Nat(NatOp::Pred); 1; (value);
    pow_nat, match_pow_nat => Builtin::Nat(NatOp::Pow); 2; (lhs, rhs);
    eq_nat, match_eq_nat => Builtin::Nat(NatOp::Eq); 2; (lhs, rhs);
    ne_nat, match_ne_nat => Builtin::Nat(NatOp::Ne); 2; (lhs, rhs);
    lt_nat, match_lt_nat => Builtin::Nat(NatOp::Lt); 2; (lhs, rhs);
    le_nat, match_le_nat => Builtin::Nat(NatOp::Le); 2; (lhs, rhs);
    gt_nat, match_gt_nat => Builtin::Nat(NatOp::Gt); 2; (lhs, rhs);
    ge_nat, match_ge_nat => Builtin::Nat(NatOp::Ge); 2; (lhs, rhs);
    min_nat, match_min_nat => Builtin::Nat(NatOp::Min); 2; (lhs, rhs);
    max_nat, match_max_nat => Builtin::Nat(NatOp::Max); 2; (lhs, rhs);
    and_nat, match_and_nat => Builtin::Nat(NatOp::And); 2; (lhs, rhs);
    or_nat, match_or_nat => Builtin::Nat(NatOp::Or); 2; (lhs, rhs);
    xor_nat, match_xor_nat => Builtin::Nat(NatOp::Xor); 2; (lhs, rhs);
    shl_nat, match_shl_nat => Builtin::Nat(NatOp::Shl); 2; (lhs, rhs);
    shr_nat, match_shr_nat => Builtin::Nat(NatOp::Shr); 2; (lhs, rhs);

    add_int, match_add_int => Builtin::Int(IntOp::Add); 2; (lhs, rhs);
    sub_int, match_sub_int => Builtin::Int(IntOp::Sub); 2; (lhs, rhs);
    mul_int, match_mul_int => Builtin::Int(IntOp::Mul); 2; (lhs, rhs);
    div_int, match_div_int => Builtin::Int(IntOp::Div); 2; (lhs, rhs);
    rem_int, match_rem_int => Builtin::Int(IntOp::Rem); 2; (lhs, rhs);
    succ_int, match_succ_int => Builtin::Int(IntOp::Succ); 1; (value);
    pred_int, match_pred_int => Builtin::Int(IntOp::Pred); 1; (value);
    pow_int, match_pow_int => Builtin::Int(IntOp::Pow); 2; (lhs, rhs);
    eq_int, match_eq_int => Builtin::Int(IntOp::Eq); 2; (lhs, rhs);
    ne_int, match_ne_int => Builtin::Int(IntOp::Ne); 2; (lhs, rhs);
    lt_int, match_lt_int => Builtin::Int(IntOp::Lt); 2; (lhs, rhs);
    le_int, match_le_int => Builtin::Int(IntOp::Le); 2; (lhs, rhs);
    gt_int, match_gt_int => Builtin::Int(IntOp::Gt); 2; (lhs, rhs);
    ge_int, match_ge_int => Builtin::Int(IntOp::Ge); 2; (lhs, rhs);
    min_int, match_min_int => Builtin::Int(IntOp::Min); 2; (lhs, rhs);
    max_int, match_max_int => Builtin::Int(IntOp::Max); 2; (lhs, rhs);
    and_int, match_and_int => Builtin::Int(IntOp::And); 2; (lhs, rhs);
    or_int, match_or_int => Builtin::Int(IntOp::Or); 2; (lhs, rhs);
    xor_int, match_xor_int => Builtin::Int(IntOp::Xor); 2; (lhs, rhs);
    shl_int, match_shl_int => Builtin::Int(IntOp::Shl); 2; (lhs, rhs);
    shr_int, match_shr_int => Builtin::Int(IntOp::Shr); 2; (lhs, rhs);
    neg_int, match_neg_int => Builtin::Int(IntOp::Neg); 1; (value);
    abs_int, match_abs_int => Builtin::Int(IntOp::Abs); 1; (value);
    not_int, match_not_int => Builtin::Int(IntOp::Not); 1; (value);

    singleton_bytes, match_singleton_bytes => Builtin::Bytes(BytesOp::Singleton); 1; (value);
    cons_bytes, match_cons_bytes => Builtin::Bytes(BytesOp::Cons); 2; (lhs, rhs);
    snoc_bytes, match_snoc_bytes => Builtin::Bytes(BytesOp::Snoc); 2; (lhs, rhs);
    append_bytes, match_append_bytes => Builtin::Bytes(BytesOp::Append); 2; (lhs, rhs);
    repeat_bytes, match_repeat_bytes => Builtin::Bytes(BytesOp::Repeat); 2; (lhs, rhs);
    length_bytes, match_length_bytes => Builtin::Bytes(BytesOp::Length); 1; (value);
    eq_bytes, match_eq_bytes => Builtin::Bytes(BytesOp::Eq); 2; (lhs, rhs);
    ne_bytes, match_ne_bytes => Builtin::Bytes(BytesOp::Ne); 2; (lhs, rhs);
    lt_bytes, match_lt_bytes => Builtin::Bytes(BytesOp::Lt); 2; (lhs, rhs);
    le_bytes, match_le_bytes => Builtin::Bytes(BytesOp::Le); 2; (lhs, rhs);
    gt_bytes, match_gt_bytes => Builtin::Bytes(BytesOp::Gt); 2; (lhs, rhs);
    ge_bytes, match_ge_bytes => Builtin::Bytes(BytesOp::Ge); 2; (lhs, rhs);
    get_bytes, match_get_bytes => Builtin::Bytes(BytesOp::Get); 2; (lhs, rhs);
    set_bytes, match_set_bytes => Builtin::Bytes(BytesOp::Set); 3; (first, second, third);
    slice_bytes, match_slice_bytes => Builtin::Bytes(BytesOp::Slice); 3; (first, second, third);
    replace_bytes, match_replace_bytes => Builtin::Bytes(BytesOp::Replace); 4; (first, second, third, fourth);
    take_bytes, match_take_bytes => Builtin::Bytes(BytesOp::Take); 2; (lhs, rhs);
    drop_bytes, match_drop_bytes => Builtin::Bytes(BytesOp::Drop); 2; (lhs, rhs);
}
