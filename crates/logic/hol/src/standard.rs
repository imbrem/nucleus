//! Ordinary Ethane initialization arena.
//!
//! Natural numbers are not a primitive row. `nat` is `Model P`, where `P`
//! asks for a categorical second-order Peano structure. `succ` and `zero` are
//! Hilbert-choice projections of one such structure. The separate `infinity`
//! root retains the weaker Dedekind-infinity sentence.

use crate::{Arena, Ref};

const TYPE_NAME: u64 = 1;
const FUNCTION_NAME: u64 = 2;
const ZERO_NAME: u64 = 3;
const X_NAME: u64 = 4;
const Y_NAME: u64 = 5;
const PREDICATE_NAME: u64 = 7;
const N_NAME: u64 = 8;

const LOGIC_P_NAME: u64 = 100;
const LOGIC_Q_NAME: u64 = 101;
const LOGIC_FUNCTION_NAME: u64 = 102;

/// Stable public roots of the ordinary initialization arena.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Roots {
    pub star: Ref,
    pub bool_ty: Ref,
    pub truth: Ref,
    pub falsehood: Ref,
    pub not: Ref,
    pub and: Ref,
    pub or: Ref,
    pub imp: Ref,
    pub infinity: Ref,
    pub nat_exists: Ref,
    pub nat: Ref,
    pub zero: Ref,
    pub succ: Ref,
}

const fn reference(value: u64) -> Ref {
    match Ref::new(value) {
        Some(reference) => reference,
        None => panic!("standard arena references are nonzero"),
    }
}

/// Number of rows in the stable ordinary initialization arena.
pub const ROW_COUNT: usize = 296;

/// Stable one-based references exported by the ordinary initialization arena.
pub const ROOTS: Roots = Roots {
    star: reference(1),
    bool_ty: reference(2),
    truth: reference(4),
    falsehood: reference(3),
    not: reference(8),
    and: reference(27),
    or: reference(38),
    imp: reference(48),
    infinity: reference(89),
    nat_exists: reference(161),
    nat: reference(162),
    zero: reference(296),
    succ: reference(232),
};

/// One freshly constructed ordinary initialization arena and its roots.
#[derive(Clone, Debug)]
pub struct Init {
    arena: Arena,
    roots: Roots,
}

impl Init {
    /// Construct all definitions using only the core one-based Ethane rows.
    #[must_use]
    pub fn new() -> Self {
        let mut arena = Arena::empty();
        let star = required(arena.push_kind_star());
        let bool_ty = required(arena.push_bool_ty());
        let falsehood = required(arena.push_bool(false));
        let truth = required(arena.push_bool(true));

        let not = build_not(&mut arena, bool_ty, falsehood);
        let and = build_and(&mut arena, bool_ty, truth);
        let or = build_or(&mut arena, bool_ty, not, and);
        let imp = build_imp(&mut arena, bool_ty, not, and);

        let mut builder = Builder {
            arena,
            bool_ty,
            truth,
            not,
            and,
            imp,
        };

        let carrier = builder.ty_fv(TYPE_NAME, star);
        let infinity_predicate = builder.type_predicate(carrier);
        let infinity = builder.ty_exists(TYPE_NAME, infinity_predicate);

        let peano_predicate = builder.peano_type_predicate(carrier);
        let nat_exists = builder.ty_exists(TYPE_NAME, peano_predicate);
        let nat = builder.model(TYPE_NAME, peano_predicate);

        let succ = builder.chosen_successor(nat);
        let zero = builder.chosen_zero(nat, succ);
        builder.arena.insert_axiom("ax.inf");

        let generated_roots = Roots {
            star,
            bool_ty,
            truth,
            falsehood,
            not,
            and,
            or,
            imp,
            infinity,
            nat_exists,
            nat,
            zero,
            succ,
        };
        debug_assert_eq!(builder.arena.len(), ROW_COUNT);
        debug_assert_eq!(generated_roots, ROOTS);

        Self {
            arena: builder.arena,
            roots: ROOTS,
        }
    }

    #[must_use]
    pub const fn arena(&self) -> &Arena {
        &self.arena
    }

    #[must_use]
    pub const fn roots(&self) -> Roots {
        self.roots
    }

    #[must_use]
    pub fn into_arena(self) -> Arena {
        self.arena
    }
}

impl Default for Init {
    fn default() -> Self {
        Self::new()
    }
}

fn required(reference: Option<Ref>) -> Ref {
    reference.expect("the fixed initialization arena is far smaller than u64::MAX rows")
}

fn build_not(arena: &mut Arena, bool_ty: Ref, falsehood: Ref) -> Ref {
    let proposition = required(arena.push_tm_fv(LOGIC_P_NAME, bool_ty));
    let body = required(arena.push_tm_eq(proposition, falsehood));
    let binder = required(arena.push_tm_fv(LOGIC_P_NAME, bool_ty));
    required(arena.push_lam(binder, body))
}

fn build_and(arena: &mut Arena, bool_ty: Ref, truth: Ref) -> Ref {
    let bool_to_bool = required(arena.push_ty_arr(bool_ty, bool_ty));
    let binary_bool = required(arena.push_ty_arr(bool_ty, bool_to_bool));
    let p = required(arena.push_tm_fv(LOGIC_P_NAME, bool_ty));
    let q = required(arena.push_tm_fv(LOGIC_Q_NAME, bool_ty));
    let function = required(arena.push_tm_fv(LOGIC_FUNCTION_NAME, binary_bool));
    let applied = required(arena.push_app(function, p));
    let lhs_body = required(arena.push_app(applied, q));
    let function_binder = required(arena.push_tm_fv(LOGIC_FUNCTION_NAME, binary_bool));
    let lhs = required(arena.push_lam(function_binder, lhs_body));

    let function = required(arena.push_tm_fv(LOGIC_FUNCTION_NAME, binary_bool));
    let applied = required(arena.push_app(function, truth));
    let rhs_body = required(arena.push_app(applied, truth));
    let function_binder = required(arena.push_tm_fv(LOGIC_FUNCTION_NAME, binary_bool));
    let rhs = required(arena.push_lam(function_binder, rhs_body));
    let body = required(arena.push_tm_eq(lhs, rhs));
    let q_binder = required(arena.push_tm_fv(LOGIC_Q_NAME, bool_ty));
    let right = required(arena.push_lam(q_binder, body));
    let p_binder = required(arena.push_tm_fv(LOGIC_P_NAME, bool_ty));
    required(arena.push_lam(p_binder, right))
}

fn build_or(arena: &mut Arena, bool_ty: Ref, not: Ref, and: Ref) -> Ref {
    let p = required(arena.push_tm_fv(LOGIC_P_NAME, bool_ty));
    let q = required(arena.push_tm_fv(LOGIC_Q_NAME, bool_ty));
    let not_p = required(arena.push_app(not, p));
    let not_q = required(arena.push_app(not, q));
    let partial = required(arena.push_app(and, not_p));
    let neither = required(arena.push_app(partial, not_q));
    let body = required(arena.push_app(not, neither));
    let q_binder = required(arena.push_tm_fv(LOGIC_Q_NAME, bool_ty));
    let right = required(arena.push_lam(q_binder, body));
    let p_binder = required(arena.push_tm_fv(LOGIC_P_NAME, bool_ty));
    required(arena.push_lam(p_binder, right))
}

fn build_imp(arena: &mut Arena, bool_ty: Ref, not: Ref, and: Ref) -> Ref {
    let p = required(arena.push_tm_fv(LOGIC_P_NAME, bool_ty));
    let q = required(arena.push_tm_fv(LOGIC_Q_NAME, bool_ty));
    let not_q = required(arena.push_app(not, q));
    let partial = required(arena.push_app(and, p));
    let both = required(arena.push_app(partial, not_q));
    let body = required(arena.push_app(not, both));
    let q_binder = required(arena.push_tm_fv(LOGIC_Q_NAME, bool_ty));
    let right = required(arena.push_lam(q_binder, body));
    let p_binder = required(arena.push_tm_fv(LOGIC_P_NAME, bool_ty));
    required(arena.push_lam(p_binder, right))
}

struct Builder {
    arena: Arena,
    bool_ty: Ref,
    truth: Ref,
    not: Ref,
    and: Ref,
    imp: Ref,
}

impl Builder {
    fn arr(&mut self, domain: Ref, codomain: Ref) -> Ref {
        required(self.arena.push_ty_arr(domain, codomain))
    }

    fn ty_fv(&mut self, name: u64, kind: Ref) -> Ref {
        required(self.arena.push_ty_fv(name, kind))
    }

    fn tm_fv(&mut self, name: u64, ty: Ref) -> Ref {
        required(self.arena.push_tm_fv(name, ty))
    }

    fn ty_exists(&mut self, name: u64, predicate: Ref) -> Ref {
        required(self.arena.push_ty_exists(name, predicate))
    }

    fn model(&mut self, name: u64, predicate: Ref) -> Ref {
        required(self.arena.push_model(name, predicate))
    }

    fn app(&mut self, function: Ref, argument: Ref) -> Ref {
        required(self.arena.push_app(function, argument))
    }

    fn app2(&mut self, function: Ref, first: Ref, second: Ref) -> Ref {
        let partial = self.app(function, first);
        self.app(partial, second)
    }

    fn lam(&mut self, name: u64, domain: Ref, body: Ref) -> Ref {
        let binder = self.tm_fv(name, domain);
        required(self.arena.push_lam(binder, body))
    }

    fn eq(&mut self, left: Ref, right: Ref) -> Ref {
        required(self.arena.push_tm_eq(left, right))
    }

    fn eps(&mut self, ty: Ref, predicate: Ref) -> Ref {
        required(self.arena.push_eps(ty, predicate))
    }

    fn not(&mut self, proposition: Ref) -> Ref {
        self.app(self.not, proposition)
    }

    fn and(&mut self, left: Ref, right: Ref) -> Ref {
        self.app2(self.and, left, right)
    }

    fn imp(&mut self, antecedent: Ref, consequent: Ref) -> Ref {
        self.app2(self.imp, antecedent, consequent)
    }

    fn forall(&mut self, name: u64, ty: Ref, body: Ref) -> Ref {
        let lhs = self.lam(name, ty, body);
        let rhs = self.lam(name, ty, self.truth);
        self.eq(lhs, rhs)
    }

    fn exists(&mut self, name: u64, ty: Ref, body: Ref) -> Ref {
        let predicate = self.lam(name, ty, body);
        let witness = self.eps(ty, predicate);
        self.app(predicate, witness)
    }

    fn reflects_equality(&mut self, carrier: Ref, function: Ref) -> Ref {
        let x = self.tm_fv(X_NAME, carrier);
        let y = self.tm_fv(Y_NAME, carrier);
        let fx = self.app(function, x);
        let fy = self.app(function, y);
        let image_eq = self.eq(fx, fy);
        let source_eq = self.eq(x, y);
        let reflected = self.eq(image_eq, source_eq);
        let forall_y = self.forall(Y_NAME, carrier, reflected);
        self.forall(X_NAME, carrier, forall_y)
    }

    fn misses_point(&mut self, carrier: Ref, function: Ref, zero: Ref) -> Ref {
        let x = self.tm_fv(X_NAME, carrier);
        let fx = self.app(function, x);
        let hits = self.eq(fx, zero);
        let misses = self.not(hits);
        self.forall(X_NAME, carrier, misses)
    }

    fn infinity_structure(&mut self, carrier: Ref, function: Ref, zero: Ref) -> Ref {
        let reflects = self.reflects_equality(carrier, function);
        let misses = self.misses_point(carrier, function, zero);
        self.and(reflects, misses)
    }

    fn peano_structure(&mut self, carrier: Ref, function: Ref, zero: Ref) -> Ref {
        let infinity = self.infinity_structure(carrier, function, zero);
        let predicate_ty = self.arr(carrier, self.bool_ty);
        let predicate = self.tm_fv(PREDICATE_NAME, predicate_ty);
        let base = self.app(predicate, zero);

        let n = self.tm_fv(N_NAME, carrier);
        let premise = self.app(predicate, n);
        let successor = self.app(function, n);
        let conclusion = self.app(predicate, successor);
        let step = self.imp(premise, conclusion);
        let step = self.forall(N_NAME, carrier, step);
        let cases = self.and(base, step);

        let n = self.tm_fv(N_NAME, carrier);
        let holds = self.app(predicate, n);
        let all = self.forall(N_NAME, carrier, holds);
        let induction = self.imp(cases, all);
        let induction = self.forall(PREDICATE_NAME, predicate_ty, induction);
        self.and(infinity, induction)
    }

    fn type_predicate(&mut self, carrier: Ref) -> Ref {
        let endomap = self.arr(carrier, carrier);
        let function = self.tm_fv(FUNCTION_NAME, endomap);
        let zero = self.tm_fv(ZERO_NAME, carrier);
        let structure = self.infinity_structure(carrier, function, zero);
        let choose_zero = self.exists(ZERO_NAME, carrier, structure);
        self.exists(FUNCTION_NAME, endomap, choose_zero)
    }

    fn peano_type_predicate(&mut self, carrier: Ref) -> Ref {
        let endomap = self.arr(carrier, carrier);
        let function = self.tm_fv(FUNCTION_NAME, endomap);
        let zero = self.tm_fv(ZERO_NAME, carrier);
        let structure = self.peano_structure(carrier, function, zero);
        let choose_zero = self.exists(ZERO_NAME, carrier, structure);
        self.exists(FUNCTION_NAME, endomap, choose_zero)
    }

    fn chosen_successor(&mut self, nat: Ref) -> Ref {
        let endomap = self.arr(nat, nat);
        let function = self.tm_fv(FUNCTION_NAME, endomap);
        let zero = self.tm_fv(ZERO_NAME, nat);
        let structure = self.peano_structure(nat, function, zero);
        let choose_zero = self.exists(ZERO_NAME, nat, structure);
        let predicate = self.lam(FUNCTION_NAME, endomap, choose_zero);
        self.eps(endomap, predicate)
    }

    fn chosen_zero(&mut self, nat: Ref, succ: Ref) -> Ref {
        let zero = self.tm_fv(ZERO_NAME, nat);
        let structure = self.peano_structure(nat, succ, zero);
        let predicate = self.lam(ZERO_NAME, nat, structure);
        self.eps(nat, predicate)
    }
}

#[cfg(test)]
mod tests {
    use std::{convert::Infallible, sync::Arc};

    use crate::{
        Import, Kernel, Link, Resolver, TrustedResolver,
        resolve::{Kind, Syntax, Value, resolve_at},
        wire,
    };

    use super::*;

    #[derive(Debug)]
    struct NoLinks;

    impl Resolver for NoLinks {
        type Error = Infallible;

        fn resolve(&self, _: &Link) -> Result<Option<Arc<Arena>>, Self::Error> {
            Ok(None)
        }
    }

    impl crate::resolve::trusted_resolver::Sealed for NoLinks {}
    impl TrustedResolver for NoLinks {}

    fn decode_hex(text: &str) -> Vec<u8> {
        let digits = text
            .bytes()
            .filter(|byte| !byte.is_ascii_whitespace())
            .collect::<Vec<_>>();
        assert_eq!(digits.len() % 2, 0);
        digits
            .chunks_exact(2)
            .map(|pair| {
                let digit = |byte: u8| match byte {
                    b'0'..=b'9' => byte - b'0',
                    b'a'..=b'f' => byte - b'a' + 10,
                    _ => panic!("standard fixture must contain lowercase hexadecimal"),
                };
                digit(pair[0]) << 4 | digit(pair[1])
            })
            .collect()
    }

    #[test]
    fn standard_cbor_fixture_is_stable() {
        let init = Init::new();
        let fixture = decode_hex(include_str!("../fixtures/standard.cbor.hex"));
        let mut encoded = Vec::new();
        wire::serialize(init.arena(), &mut encoded).unwrap();
        assert_eq!(encoded, fixture);
        assert_eq!(
            wire::deserialize(fixture.as_slice()).unwrap(),
            *init.arena()
        );
    }

    #[test]
    fn standard_roots_are_checked_core_ethane_definitions() {
        let init = Init::new();
        let roots = init.roots();
        let fuel = init.arena().len() + 32;
        let kernel = Kernel::try_from_arena(init.arena().clone(), Arc::new(NoLinks), fuel)
            .expect("the ordinary initialization arena must validate");

        let nat = resolve_at(kernel.arena(), kernel.resolver(), roots.nat, fuel).unwrap();
        let zero = resolve_at(kernel.arena(), kernel.resolver(), roots.zero, fuel).unwrap();
        let succ = resolve_at(kernel.arena(), kernel.resolver(), roots.succ, fuel).unwrap();
        let infinity = resolve_at(kernel.arena(), kernel.resolver(), roots.infinity, fuel).unwrap();
        let nat_exists =
            resolve_at(kernel.arena(), kernel.resolver(), roots.nat_exists, fuel).unwrap();

        let Value::Ty {
            kind: Kind::Star,
            expression: nat_expression,
        } = nat
        else {
            panic!("nat must resolve as a type")
        };
        assert!(matches!(nat_expression, Syntax::Model { .. }));
        assert!(matches!(
            zero,
            Value::Tm { ref ty, .. } if ty == &nat_expression
        ));
        assert!(matches!(
            succ,
            Value::Tm {
                ty: Syntax::Arr(ref domain, ref codomain),
                ..
            } if domain.as_ref() == &nat_expression && codomain.as_ref() == &nat_expression
        ));
        assert!(matches!(
            infinity,
            Value::Tm {
                ty: Syntax::BoolTy,
                expression: Syntax::TyExists { .. }
            }
        ));
        assert!(matches!(
            nat_exists,
            Value::Tm {
                ty: Syntax::BoolTy,
                expression: Syntax::TyExists { .. }
            }
        ));

        let mut consumer = Kernel::try_from_arena(Arena::empty(), Arc::new(NoLinks), 1).unwrap();
        let source = consumer.import_literal(fuel, init.into_arena()).unwrap();
        consumer.assert_valid(fuel, source).unwrap();
        consumer.ty_ref(fuel, source, roots.nat).unwrap();
        let zero = consumer.tm_ref(fuel, source, roots.zero).unwrap();
        let succ = consumer.tm_ref(fuel, source, roots.succ).unwrap();
        consumer.app(fuel, succ, zero).unwrap();
        assert!(matches!(
            consumer
                .arena()
                .imports()
                .get(usize::try_from(source.get() - 1).unwrap()),
            Some(Import::Literal(_))
        ));
    }
}
