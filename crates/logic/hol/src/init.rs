//! Pure-`HolE` construction of the v0 foundational arena.
//!
//! Besides booleans and their connectives, the arena defines a categorical
//! second-order Peano model, zero, successor, recursively specified addition,
//! and the numeral 256 by repeated doubling. A byte is the subtype of naturals
//! below 256; bytes are the categorical second-order list model over that
//! subtype. No surface natural or byte-string literal occurs in this arena.

#![allow(clippy::many_single_char_names)]

use crate::{Arena, ArenaError, Expr, Ix};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InitRefs {
    pub bool_ty: Ix,
    pub false_: Ix,
    pub true_: Ix,
    pub not: Ix,
    pub and: Ix,
    pub or: Ix,
    pub infinity: Ix,
    pub nat_exists: Ix,
    pub nat_ty: Ix,
    pub zero: Ix,
    pub succ: Ix,
    pub add: Ix,
    pub two_fifty_six: Ix,
    pub byte_ty: Ix,
    pub bytes_exists: Ix,
    pub bytes_ty: Ix,
    pub bytes_nil: Ix,
    pub bytes_cons: Ix,
}

struct Builder {
    arena: Arena,
    bool_ty: Ix,
    true_: Ix,
    not: Ix,
    and: Ix,
    or: Ix,
}

impl Builder {
    fn push(&mut self, expr: Expr) -> Result<Ix, ArenaError> {
        self.arena.push(expr)
    }
    fn arr(&mut self, domain: Ix, codomain: Ix) -> Result<Ix, ArenaError> {
        self.push(Expr::TyArr { domain, codomain })
    }
    fn bv(&mut self, index: u32) -> Result<Ix, ArenaError> {
        self.push(Expr::TmBv { index })
    }
    fn app(&mut self, function: Ix, argument: Ix) -> Result<Ix, ArenaError> {
        self.push(Expr::TmApp { function, argument })
    }
    fn lam(&mut self, domain: Ix, body: Ix) -> Result<Ix, ArenaError> {
        self.push(Expr::TmLam { domain, body })
    }
    fn eq(&mut self, ty: Ix, left: Ix, right: Ix) -> Result<Ix, ArenaError> {
        self.push(Expr::TmEq { ty, left, right })
    }
    fn eps(&mut self, ty: Ix, predicate: Ix) -> Result<Ix, ArenaError> {
        self.push(Expr::TmEps { ty, predicate })
    }
    fn not(&mut self, proposition: Ix) -> Result<Ix, ArenaError> {
        self.app(self.not, proposition)
    }
    fn and(&mut self, left: Ix, right: Ix) -> Result<Ix, ArenaError> {
        let partial = self.app(self.and, left)?;
        self.app(partial, right)
    }
    fn or(&mut self, left: Ix, right: Ix) -> Result<Ix, ArenaError> {
        let partial = self.app(self.or, left)?;
        self.app(partial, right)
    }
    fn imp(&mut self, antecedent: Ix, consequent: Ix) -> Result<Ix, ArenaError> {
        let negated = self.not(antecedent)?;
        self.or(negated, consequent)
    }
    fn app2(&mut self, function: Ix, first: Ix, second: Ix) -> Result<Ix, ArenaError> {
        let partial = self.app(function, first)?;
        self.app(partial, second)
    }
    fn forall(&mut self, ty: Ix, body: Ix) -> Result<Ix, ArenaError> {
        let predicate_ty = self.arr(ty, self.bool_ty)?;
        let lhs = self.lam(ty, body)?;
        let rhs = self.lam(ty, self.true_)?;
        self.eq(predicate_ty, lhs, rhs)
    }
    fn exists(&mut self, ty: Ix, body: Ix) -> Result<Ix, ArenaError> {
        let predicate = self.lam(ty, body)?;
        let witness = self.eps(ty, predicate)?;
        self.app(predicate, witness)
    }

    /// The infinity structure in context `[z : A, f : A → A]`.
    fn structure_bound(&mut self, a: Ix) -> Result<Ix, ArenaError> {
        let f = self.bv(3)?;
        let x = self.bv(1)?;
        let y = self.bv(0)?;
        let fx = self.app(f, x)?;
        let fy = self.app(f, y)?;
        let image_eq = self.eq(a, fx, fy)?;
        let source_eq = self.eq(a, x, y)?;
        let reflected = self.eq(self.bool_ty, image_eq, source_eq)?;
        let forall_y = self.forall(a, reflected)?;
        let reflects = self.forall(a, forall_y)?;

        let f = self.bv(2)?;
        let z = self.bv(1)?;
        let x = self.bv(0)?;
        let fx = self.app(f, x)?;
        let hits = self.eq(a, fx, z)?;
        let misses = self.not(hits)?;
        let misses = self.forall(a, misses)?;
        self.and(reflects, misses)
    }

    /// The second-order Peano structure in context `[z : A, f : A → A]`.
    fn peano_structure_bound(&mut self, a: Ix) -> Result<Ix, ArenaError> {
        let infinity = self.structure_bound(a)?;

        // Second-order induction. Before introducing `P`, the open context is
        // `[z : A, f : A -> A]`, so under `P` it is `[P, z, f]`.
        let predicate_ty = self.arr(a, self.bool_ty)?;
        let p = self.bv(0)?;
        let z = self.bv(1)?;
        let base = self.app(p, z)?;

        // Under the step's `n`, the context is `[n, P, z, f]`.
        let p = self.bv(1)?;
        let n = self.bv(0)?;
        let premise = self.app(p, n)?;
        let f = self.bv(3)?;
        let n = self.bv(0)?;
        let successor = self.app(f, n)?;
        let p = self.bv(1)?;
        let conclusion = self.app(p, successor)?;
        let step = self.imp(premise, conclusion)?;
        let step = self.forall(a, step)?;
        let cases = self.and(base, step)?;

        let p = self.bv(1)?;
        let n = self.bv(0)?;
        let holds = self.app(p, n)?;
        let all = self.forall(a, holds)?;
        let induction = self.imp(cases, all)?;
        let induction = self.forall(predicate_ty, induction)?;
        self.and(infinity, induction)
    }

    fn type_predicate(&mut self, a: Ix) -> Result<Ix, ArenaError> {
        let endomap = self.arr(a, a)?;
        let structure = self.structure_bound(a)?;
        let choose_z = self.exists(a, structure)?;
        self.exists(endomap, choose_z)
    }

    fn peano_type_predicate(&mut self, a: Ix) -> Result<Ix, ArenaError> {
        let endomap = self.arr(a, a)?;
        let structure = self.peano_structure_bound(a)?;
        let choose_zero = self.exists(a, structure)?;
        self.exists(endomap, choose_zero)
    }

    fn peano_zero_predicate(&mut self, a: Ix, successor: Ix) -> Result<Ix, ArenaError> {
        let endomap = self.arr(a, a)?;
        let structure = self.peano_structure_bound(a)?;
        let zero_predicate = self.lam(a, structure)?;
        let by_successor = self.lam(endomap, zero_predicate)?;
        self.app(by_successor, successor)
    }

    /// The defining recursion equations for addition, in context `[add]`.
    fn add_equations(&mut self, nat: Ix, zero: Ix, succ: Ix) -> Result<Ix, ArenaError> {
        let m = self.bv(0)?;
        let add = self.bv(1)?;
        let sum = self.app2(add, zero, m)?;
        let base = self.eq(nat, sum, m)?;
        let base = self.forall(nat, base)?;

        // Under `[m, n, add]`.
        let add = self.bv(2)?;
        let n = self.bv(1)?;
        let succ_n = self.app(succ, n)?;
        let m = self.bv(0)?;
        let lhs = self.app2(add, succ_n, m)?;
        let add = self.bv(2)?;
        let n = self.bv(1)?;
        let m = self.bv(0)?;
        let sum = self.app2(add, n, m)?;
        let rhs = self.app(succ, sum)?;
        let step = self.eq(nat, lhs, rhs)?;
        let step = self.forall(nat, step)?;
        let step = self.forall(nat, step)?;
        self.and(base, step)
    }

    /// The second-order list equations in context `[nil : L, cons : E -> L -> L]`.
    fn list_structure_bound(&mut self, element: Ix, list: Ix) -> Result<Ix, ArenaError> {
        // Under `[tail, head, nil, cons]`.
        let cons = self.bv(3)?;
        let head = self.bv(1)?;
        let tail = self.bv(0)?;
        let cell = self.app2(cons, head, tail)?;
        let nil = self.bv(2)?;
        let disjoint = self.eq(list, cell, nil)?;
        let disjoint = self.not(disjoint)?;
        let disjoint = self.forall(list, disjoint)?;
        let disjoint = self.forall(element, disjoint)?;

        // Under `[tail₂, head₂, tail₁, head₁, nil, cons]`.
        let cons = self.bv(5)?;
        let head_1 = self.bv(3)?;
        let tail_1 = self.bv(2)?;
        let left = self.app2(cons, head_1, tail_1)?;
        let cons = self.bv(5)?;
        let head_2 = self.bv(1)?;
        let tail_2 = self.bv(0)?;
        let right = self.app2(cons, head_2, tail_2)?;
        let cells_equal = self.eq(list, left, right)?;
        let head_1 = self.bv(3)?;
        let head_2 = self.bv(1)?;
        let heads_equal = self.eq(element, head_1, head_2)?;
        let tail_1 = self.bv(2)?;
        let tail_2 = self.bv(0)?;
        let tails_equal = self.eq(list, tail_1, tail_2)?;
        let components_equal = self.and(heads_equal, tails_equal)?;
        let injective = self.eq(self.bool_ty, cells_equal, components_equal)?;
        let injective = self.forall(list, injective)?;
        let injective = self.forall(element, injective)?;
        let injective = self.forall(list, injective)?;
        let injective = self.forall(element, injective)?;

        // Under `[P, nil, cons]`.
        let predicate_ty = self.arr(list, self.bool_ty)?;
        let p = self.bv(0)?;
        let nil = self.bv(1)?;
        let base = self.app(p, nil)?;
        // Under `[tail, head, P, nil, cons]`.
        let p = self.bv(2)?;
        let tail = self.bv(0)?;
        let premise = self.app(p, tail)?;
        let cons = self.bv(4)?;
        let head = self.bv(1)?;
        let tail = self.bv(0)?;
        let cell = self.app2(cons, head, tail)?;
        let p = self.bv(2)?;
        let conclusion = self.app(p, cell)?;
        let step = self.imp(premise, conclusion)?;
        let step = self.forall(list, step)?;
        let step = self.forall(element, step)?;
        let cases = self.and(base, step)?;
        let p = self.bv(1)?;
        let value = self.bv(0)?;
        let holds = self.app(p, value)?;
        let all = self.forall(list, holds)?;
        let induction = self.imp(cases, all)?;
        let induction = self.forall(predicate_ty, induction)?;
        let shape = self.and(disjoint, injective)?;
        self.and(shape, induction)
    }

    /// The predicate on `nil : L` obtained by fixing a closed `cons`.
    fn list_nil_predicate(&mut self, element: Ix, list: Ix, cons: Ix) -> Result<Ix, ArenaError> {
        // Use a one-off lambda/application to reuse the carefully audited open
        // form: `(fun cons => fun nil => structure cons nil) cons`.
        let cons_ty_tail = self.arr(list, list)?;
        let cons_ty = self.arr(element, cons_ty_tail)?;
        let structure = self.list_structure_bound(element, list)?;
        let nil_predicate = self.lam(list, structure)?;
        let predicate = self.lam(cons_ty, nil_predicate)?;
        self.app(predicate, cons)
    }

    fn list_type_predicate(&mut self, element: Ix, list: Ix) -> Result<Ix, ArenaError> {
        let cons_tail = self.arr(list, list)?;
        let cons_ty = self.arr(element, cons_tail)?;
        let structure = self.list_structure_bound(element, list)?;
        let choose_nil = self.exists(list, structure)?;
        self.exists(cons_ty, choose_nil)
    }
}

/// Build the reference form used to audit the generated static table.
///
/// # Errors
/// Returns an arena error if the reference construction violates an index invariant.
#[allow(clippy::too_many_lines)]
pub fn build_init_arena() -> Result<(Arena, InitRefs), ArenaError> {
    let mut arena = Arena::new(None);
    let _star = arena.push(Expr::KindStar)?;
    let bool_ty = arena.push(Expr::TyBool)?;
    let false_ = arena.push(Expr::TmBool { value: false })?;
    let true_ = arena.push(Expr::TmBool { value: true })?;

    let bool_var = arena.push(Expr::TmBv { index: 0 })?;
    let not_body = arena.push(Expr::TmEq {
        ty: bool_ty,
        left: bool_var,
        right: false_,
    })?;
    let not = arena.push(Expr::TmLam {
        domain: bool_ty,
        body: not_body,
    })?;

    let bool_to_bool = arena.push(Expr::TyArr {
        domain: bool_ty,
        codomain: bool_ty,
    })?;
    let binary_bool = arena.push(Expr::TyArr {
        domain: bool_ty,
        codomain: bool_to_bool,
    })?;
    let f = arena.push(Expr::TmBv { index: 0 })?;
    let left = arena.push(Expr::TmBv { index: 2 })?;
    let f_left = arena.push(Expr::TmApp {
        function: f,
        argument: left,
    })?;
    let right = arena.push(Expr::TmBv { index: 1 })?;
    let f_left_right = arena.push(Expr::TmApp {
        function: f_left,
        argument: right,
    })?;
    let lhs = arena.push(Expr::TmLam {
        domain: binary_bool,
        body: f_left_right,
    })?;
    let f = arena.push(Expr::TmBv { index: 0 })?;
    let f_true = arena.push(Expr::TmApp {
        function: f,
        argument: true_,
    })?;
    let f_true_true = arena.push(Expr::TmApp {
        function: f_true,
        argument: true_,
    })?;
    let rhs = arena.push(Expr::TmLam {
        domain: binary_bool,
        body: f_true_true,
    })?;
    let functional = arena.push(Expr::TyArr {
        domain: binary_bool,
        codomain: bool_ty,
    })?;
    let and_body = arena.push(Expr::TmEq {
        ty: functional,
        left: lhs,
        right: rhs,
    })?;
    let and_right = arena.push(Expr::TmLam {
        domain: bool_ty,
        body: and_body,
    })?;
    let and = arena.push(Expr::TmLam {
        domain: bool_ty,
        body: and_right,
    })?;

    let mut builder = Builder {
        arena,
        bool_ty,
        true_,
        not,
        and,
        // Replaced immediately after deriving disjunction below.
        or: true_,
    };
    let left = builder.bv(1)?;
    let left_not = builder.not(left)?;
    let right = builder.bv(0)?;
    let right_not = builder.not(right)?;
    let neither = builder.and(left_not, right_not)?;
    let either = builder.not(neither)?;
    let or_right = builder.lam(bool_ty, either)?;
    let or = builder.lam(bool_ty, or_right)?;
    builder.or = or;

    let a = builder.push(Expr::TyBv { index: 0 })?;
    let type_predicate = builder.type_predicate(a)?;
    let infinity = builder.push(Expr::TyExists {
        predicate: type_predicate,
    })?;
    // The categorical second-order Peano model used by the public Nat
    // definitions. Its existence is derived from `infinity` by the theory
    // layered on this initializer.
    let a = builder.push(Expr::TyBv { index: 0 })?;
    let peano_predicate = builder.peano_type_predicate(a)?;
    let nat_exists = builder.push(Expr::TyExists {
        predicate: peano_predicate,
    })?;
    let nat_ty = builder.push(Expr::TyModel {
        predicate: peano_predicate,
    })?;
    let endomap = builder.arr(nat_ty, nat_ty)?;
    let structure = builder.peano_structure_bound(nat_ty)?;
    let choose_zero = builder.exists(nat_ty, structure)?;
    let successor_predicate = builder.lam(endomap, choose_zero)?;
    let succ = builder.eps(endomap, successor_predicate)?;
    let zero_predicate = builder.peano_zero_predicate(nat_ty, succ)?;
    let zero = builder.eps(nat_ty, zero_predicate)?;

    let add_tail = builder.arr(nat_ty, nat_ty)?;
    let add_ty = builder.arr(nat_ty, add_tail)?;
    let add_equations = builder.add_equations(nat_ty, zero, succ)?;
    let add_predicate = builder.lam(add_ty, add_equations)?;
    let add = builder.eps(add_ty, add_predicate)?;

    let one = builder.app(succ, zero)?;
    let two = builder.app2(add, one, one)?;
    let four = builder.app2(add, two, two)?;
    let eight = builder.app2(add, four, four)?;
    let sixteen = builder.app2(add, eight, eight)?;
    let thirty_two = builder.app2(add, sixteen, sixteen)?;
    let sixty_four = builder.app2(add, thirty_two, thirty_two)?;
    let one_twenty_eight = builder.app2(add, sixty_four, sixty_four)?;
    let two_fifty_six = builder.app2(add, one_twenty_eight, one_twenty_eight)?;

    // Byte = {n : Nat | n < 256}, with n < 256 witnessed by a positive gap.
    // Under `[gap, n]`, `n + succ gap = 256`.
    let gap = builder.bv(0)?;
    let positive_gap = builder.app(succ, gap)?;
    let n = builder.bv(1)?;
    let reaches_256 = builder.app2(add, n, positive_gap)?;
    let below_256 = builder.eq(nat_ty, reaches_256, two_fifty_six)?;
    let below_256 = builder.exists(nat_ty, below_256)?;
    let below_256 = builder.lam(nat_ty, below_256)?;
    let byte_ty = builder.push(Expr::TySub {
        carrier: nat_ty,
        predicate: below_256,
    })?;

    let list = builder.push(Expr::TyBv { index: 0 })?;
    let bytes_predicate = builder.list_type_predicate(byte_ty, list)?;
    let bytes_exists = builder.push(Expr::TyExists {
        predicate: bytes_predicate,
    })?;
    let byte_string_ty = builder.push(Expr::TyModel {
        predicate: bytes_predicate,
    })?;
    let cons_tail = builder.arr(byte_string_ty, byte_string_ty)?;
    let cons_ty = builder.arr(byte_ty, cons_tail)?;
    let structure = builder.list_structure_bound(byte_ty, byte_string_ty)?;
    let choose_nil = builder.exists(byte_string_ty, structure)?;
    let cons_predicate = builder.lam(cons_ty, choose_nil)?;
    let bytes_cons = builder.eps(cons_ty, cons_predicate)?;
    let nil_predicate = builder.list_nil_predicate(byte_ty, byte_string_ty, bytes_cons)?;
    let bytes_nil = builder.eps(byte_string_ty, nil_predicate)?;

    let refs = InitRefs {
        bool_ty,
        false_,
        true_,
        not,
        and,
        or,
        infinity,
        nat_exists,
        nat_ty,
        zero,
        succ,
        add,
        two_fifty_six,
        byte_ty,
        bytes_exists,
        bytes_ty: byte_string_ty,
        bytes_nil,
        bytes_cons,
    };
    Ok((builder.arena, refs))
}

const fn i(value: u32) -> Ix {
    match Ix::new(value) {
        Ok(index) => index,
        Err(_) => panic!("invalid audited init index"),
    }
}

static INIT_DEFS: &[Expr] = &[
    Expr::KindStar,
    Expr::TyBool,
    Expr::TmBool { value: false },
    Expr::TmBool { value: true },
    Expr::TmBv { index: 0 },
    Expr::TmEq {
        ty: i(2),
        left: i(5),
        right: i(3),
    },
    Expr::TmLam {
        domain: i(2),
        body: i(6),
    },
    Expr::TyArr {
        domain: i(2),
        codomain: i(2),
    },
    Expr::TyArr {
        domain: i(2),
        codomain: i(8),
    },
    Expr::TmBv { index: 0 },
    Expr::TmBv { index: 2 },
    Expr::TmApp {
        function: i(10),
        argument: i(11),
    },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(12),
        argument: i(13),
    },
    Expr::TmLam {
        domain: i(9),
        body: i(14),
    },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(16),
        argument: i(4),
    },
    Expr::TmApp {
        function: i(17),
        argument: i(4),
    },
    Expr::TmLam {
        domain: i(9),
        body: i(18),
    },
    Expr::TyArr {
        domain: i(9),
        codomain: i(2),
    },
    Expr::TmEq {
        ty: i(20),
        left: i(15),
        right: i(19),
    },
    Expr::TmLam {
        domain: i(2),
        body: i(21),
    },
    Expr::TmLam {
        domain: i(2),
        body: i(22),
    },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(7),
        argument: i(24),
    },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(7),
        argument: i(26),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(25),
    },
    Expr::TmApp {
        function: i(28),
        argument: i(27),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(29),
    },
    Expr::TmLam {
        domain: i(2),
        body: i(30),
    },
    Expr::TmLam {
        domain: i(2),
        body: i(31),
    },
    Expr::TyBv { index: 0 },
    Expr::TyArr {
        domain: i(33),
        codomain: i(33),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(35),
        argument: i(36),
    },
    Expr::TmApp {
        function: i(35),
        argument: i(37),
    },
    Expr::TmEq {
        ty: i(33),
        left: i(38),
        right: i(39),
    },
    Expr::TmEq {
        ty: i(33),
        left: i(36),
        right: i(37),
    },
    Expr::TmEq {
        ty: i(2),
        left: i(40),
        right: i(41),
    },
    Expr::TyArr {
        domain: i(33),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(33),
        body: i(42),
    },
    Expr::TmLam {
        domain: i(33),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(43),
        left: i(44),
        right: i(45),
    },
    Expr::TyArr {
        domain: i(33),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(33),
        body: i(46),
    },
    Expr::TmLam {
        domain: i(33),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(47),
        left: i(48),
        right: i(49),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(51),
        argument: i(53),
    },
    Expr::TmEq {
        ty: i(33),
        left: i(54),
        right: i(52),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(55),
    },
    Expr::TyArr {
        domain: i(33),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(33),
        body: i(56),
    },
    Expr::TmLam {
        domain: i(33),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(57),
        left: i(58),
        right: i(59),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(50),
    },
    Expr::TmApp {
        function: i(61),
        argument: i(60),
    },
    Expr::TmLam {
        domain: i(33),
        body: i(62),
    },
    Expr::TmEps {
        ty: i(33),
        predicate: i(63),
    },
    Expr::TmApp {
        function: i(63),
        argument: i(64),
    },
    Expr::TmLam {
        domain: i(34),
        body: i(65),
    },
    Expr::TmEps {
        ty: i(34),
        predicate: i(66),
    },
    Expr::TmApp {
        function: i(66),
        argument: i(67),
    },
    Expr::TyExists { predicate: i(68) },
    Expr::TyBv { index: 0 },
    Expr::TyArr {
        domain: i(70),
        codomain: i(70),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(72),
        argument: i(73),
    },
    Expr::TmApp {
        function: i(72),
        argument: i(74),
    },
    Expr::TmEq {
        ty: i(70),
        left: i(75),
        right: i(76),
    },
    Expr::TmEq {
        ty: i(70),
        left: i(73),
        right: i(74),
    },
    Expr::TmEq {
        ty: i(2),
        left: i(77),
        right: i(78),
    },
    Expr::TyArr {
        domain: i(70),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(79),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(80),
        left: i(81),
        right: i(82),
    },
    Expr::TyArr {
        domain: i(70),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(83),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(84),
        left: i(85),
        right: i(86),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(88),
        argument: i(90),
    },
    Expr::TmEq {
        ty: i(70),
        left: i(91),
        right: i(89),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(92),
    },
    Expr::TyArr {
        domain: i(70),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(93),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(94),
        left: i(95),
        right: i(96),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(87),
    },
    Expr::TmApp {
        function: i(98),
        argument: i(97),
    },
    Expr::TyArr {
        domain: i(70),
        codomain: i(2),
    },
    Expr::TmBv { index: 0 },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(101),
        argument: i(102),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(104),
        argument: i(105),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(107),
        argument: i(108),
    },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(110),
        argument: i(109),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(106),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(112),
    },
    Expr::TmApp {
        function: i(113),
        argument: i(111),
    },
    Expr::TyArr {
        domain: i(70),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(114),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(115),
        left: i(116),
        right: i(117),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(103),
    },
    Expr::TmApp {
        function: i(119),
        argument: i(118),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(121),
        argument: i(122),
    },
    Expr::TyArr {
        domain: i(70),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(123),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(124),
        left: i(125),
        right: i(126),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(120),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(128),
    },
    Expr::TmApp {
        function: i(129),
        argument: i(127),
    },
    Expr::TyArr {
        domain: i(100),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(100),
        body: i(130),
    },
    Expr::TmLam {
        domain: i(100),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(131),
        left: i(132),
        right: i(133),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(99),
    },
    Expr::TmApp {
        function: i(135),
        argument: i(134),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(136),
    },
    Expr::TmEps {
        ty: i(70),
        predicate: i(137),
    },
    Expr::TmApp {
        function: i(137),
        argument: i(138),
    },
    Expr::TmLam {
        domain: i(71),
        body: i(139),
    },
    Expr::TmEps {
        ty: i(71),
        predicate: i(140),
    },
    Expr::TmApp {
        function: i(140),
        argument: i(141),
    },
    Expr::TyExists { predicate: i(142) },
    Expr::TyModel { predicate: i(142) },
    Expr::TyArr {
        domain: i(144),
        codomain: i(144),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(146),
        argument: i(147),
    },
    Expr::TmApp {
        function: i(146),
        argument: i(148),
    },
    Expr::TmEq {
        ty: i(144),
        left: i(149),
        right: i(150),
    },
    Expr::TmEq {
        ty: i(144),
        left: i(147),
        right: i(148),
    },
    Expr::TmEq {
        ty: i(2),
        left: i(151),
        right: i(152),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(153),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(154),
        left: i(155),
        right: i(156),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(157),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(158),
        left: i(159),
        right: i(160),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(162),
        argument: i(164),
    },
    Expr::TmEq {
        ty: i(144),
        left: i(165),
        right: i(163),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(166),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(167),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(168),
        left: i(169),
        right: i(170),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(161),
    },
    Expr::TmApp {
        function: i(172),
        argument: i(171),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmBv { index: 0 },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(175),
        argument: i(176),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(178),
        argument: i(179),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(181),
        argument: i(182),
    },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(184),
        argument: i(183),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(180),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(186),
    },
    Expr::TmApp {
        function: i(187),
        argument: i(185),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(188),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(189),
        left: i(190),
        right: i(191),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(177),
    },
    Expr::TmApp {
        function: i(193),
        argument: i(192),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(195),
        argument: i(196),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(197),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(198),
        left: i(199),
        right: i(200),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(194),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(202),
    },
    Expr::TmApp {
        function: i(203),
        argument: i(201),
    },
    Expr::TyArr {
        domain: i(174),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(174),
        body: i(204),
    },
    Expr::TmLam {
        domain: i(174),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(205),
        left: i(206),
        right: i(207),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(173),
    },
    Expr::TmApp {
        function: i(209),
        argument: i(208),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(210),
    },
    Expr::TmEps {
        ty: i(144),
        predicate: i(211),
    },
    Expr::TmApp {
        function: i(211),
        argument: i(212),
    },
    Expr::TmLam {
        domain: i(145),
        body: i(213),
    },
    Expr::TmEps {
        ty: i(145),
        predicate: i(214),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(144),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(217),
        argument: i(218),
    },
    Expr::TmApp {
        function: i(217),
        argument: i(219),
    },
    Expr::TmEq {
        ty: i(144),
        left: i(220),
        right: i(221),
    },
    Expr::TmEq {
        ty: i(144),
        left: i(218),
        right: i(219),
    },
    Expr::TmEq {
        ty: i(2),
        left: i(222),
        right: i(223),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(224),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(225),
        left: i(226),
        right: i(227),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(228),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(229),
        left: i(230),
        right: i(231),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(233),
        argument: i(235),
    },
    Expr::TmEq {
        ty: i(144),
        left: i(236),
        right: i(234),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(237),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(238),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(239),
        left: i(240),
        right: i(241),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(232),
    },
    Expr::TmApp {
        function: i(243),
        argument: i(242),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmBv { index: 0 },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(246),
        argument: i(247),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(249),
        argument: i(250),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(252),
        argument: i(253),
    },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(255),
        argument: i(254),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(251),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(257),
    },
    Expr::TmApp {
        function: i(258),
        argument: i(256),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(259),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(260),
        left: i(261),
        right: i(262),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(248),
    },
    Expr::TmApp {
        function: i(264),
        argument: i(263),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(266),
        argument: i(267),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(268),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(269),
        left: i(270),
        right: i(271),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(265),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(273),
    },
    Expr::TmApp {
        function: i(274),
        argument: i(272),
    },
    Expr::TyArr {
        domain: i(245),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(245),
        body: i(275),
    },
    Expr::TmLam {
        domain: i(245),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(276),
        left: i(277),
        right: i(278),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(244),
    },
    Expr::TmApp {
        function: i(280),
        argument: i(279),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(281),
    },
    Expr::TmLam {
        domain: i(216),
        body: i(282),
    },
    Expr::TmApp {
        function: i(283),
        argument: i(215),
    },
    Expr::TmEps {
        ty: i(144),
        predicate: i(284),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(144),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(286),
    },
    Expr::TmBv { index: 0 },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(289),
        argument: i(285),
    },
    Expr::TmApp {
        function: i(290),
        argument: i(288),
    },
    Expr::TmEq {
        ty: i(144),
        left: i(291),
        right: i(288),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(292),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(293),
        left: i(294),
        right: i(295),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(215),
        argument: i(298),
    },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(297),
        argument: i(299),
    },
    Expr::TmApp {
        function: i(301),
        argument: i(300),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(303),
        argument: i(304),
    },
    Expr::TmApp {
        function: i(306),
        argument: i(305),
    },
    Expr::TmApp {
        function: i(215),
        argument: i(307),
    },
    Expr::TmEq {
        ty: i(144),
        left: i(302),
        right: i(308),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(309),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(310),
        left: i(311),
        right: i(312),
    },
    Expr::TyArr {
        domain: i(144),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(313),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(314),
        left: i(315),
        right: i(316),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(296),
    },
    Expr::TmApp {
        function: i(318),
        argument: i(317),
    },
    Expr::TmLam {
        domain: i(287),
        body: i(319),
    },
    Expr::TmEps {
        ty: i(287),
        predicate: i(320),
    },
    Expr::TmApp {
        function: i(215),
        argument: i(285),
    },
    Expr::TmApp {
        function: i(321),
        argument: i(322),
    },
    Expr::TmApp {
        function: i(323),
        argument: i(322),
    },
    Expr::TmApp {
        function: i(321),
        argument: i(324),
    },
    Expr::TmApp {
        function: i(325),
        argument: i(324),
    },
    Expr::TmApp {
        function: i(321),
        argument: i(326),
    },
    Expr::TmApp {
        function: i(327),
        argument: i(326),
    },
    Expr::TmApp {
        function: i(321),
        argument: i(328),
    },
    Expr::TmApp {
        function: i(329),
        argument: i(328),
    },
    Expr::TmApp {
        function: i(321),
        argument: i(330),
    },
    Expr::TmApp {
        function: i(331),
        argument: i(330),
    },
    Expr::TmApp {
        function: i(321),
        argument: i(332),
    },
    Expr::TmApp {
        function: i(333),
        argument: i(332),
    },
    Expr::TmApp {
        function: i(321),
        argument: i(334),
    },
    Expr::TmApp {
        function: i(335),
        argument: i(334),
    },
    Expr::TmApp {
        function: i(321),
        argument: i(336),
    },
    Expr::TmApp {
        function: i(337),
        argument: i(336),
    },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(215),
        argument: i(339),
    },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(321),
        argument: i(341),
    },
    Expr::TmApp {
        function: i(342),
        argument: i(340),
    },
    Expr::TmEq {
        ty: i(144),
        left: i(343),
        right: i(338),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(344),
    },
    Expr::TmEps {
        ty: i(144),
        predicate: i(345),
    },
    Expr::TmApp {
        function: i(345),
        argument: i(346),
    },
    Expr::TmLam {
        domain: i(144),
        body: i(347),
    },
    Expr::TySub {
        carrier: i(144),
        predicate: i(348),
    },
    Expr::TyBv { index: 0 },
    Expr::TyArr {
        domain: i(350),
        codomain: i(350),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(351),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(353),
        argument: i(354),
    },
    Expr::TmApp {
        function: i(356),
        argument: i(355),
    },
    Expr::TmBv { index: 2 },
    Expr::TmEq {
        ty: i(350),
        left: i(357),
        right: i(358),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(359),
    },
    Expr::TyArr {
        domain: i(350),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(360),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(361),
        left: i(362),
        right: i(363),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(364),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(365),
        left: i(366),
        right: i(367),
    },
    Expr::TmBv { index: 5 },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 2 },
    Expr::TmApp {
        function: i(369),
        argument: i(370),
    },
    Expr::TmApp {
        function: i(372),
        argument: i(371),
    },
    Expr::TmBv { index: 5 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(374),
        argument: i(375),
    },
    Expr::TmApp {
        function: i(377),
        argument: i(376),
    },
    Expr::TmEq {
        ty: i(350),
        left: i(373),
        right: i(378),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 1 },
    Expr::TmEq {
        ty: i(349),
        left: i(380),
        right: i(381),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 0 },
    Expr::TmEq {
        ty: i(350),
        left: i(383),
        right: i(384),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(382),
    },
    Expr::TmApp {
        function: i(386),
        argument: i(385),
    },
    Expr::TmEq {
        ty: i(2),
        left: i(379),
        right: i(387),
    },
    Expr::TyArr {
        domain: i(350),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(388),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(389),
        left: i(390),
        right: i(391),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(392),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(393),
        left: i(394),
        right: i(395),
    },
    Expr::TyArr {
        domain: i(350),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(396),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(397),
        left: i(398),
        right: i(399),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(400),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(401),
        left: i(402),
        right: i(403),
    },
    Expr::TyArr {
        domain: i(350),
        codomain: i(2),
    },
    Expr::TmBv { index: 0 },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(406),
        argument: i(407),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(409),
        argument: i(410),
    },
    Expr::TmBv { index: 4 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(412),
        argument: i(413),
    },
    Expr::TmApp {
        function: i(415),
        argument: i(414),
    },
    Expr::TmBv { index: 2 },
    Expr::TmApp {
        function: i(417),
        argument: i(416),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(411),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(419),
    },
    Expr::TmApp {
        function: i(420),
        argument: i(418),
    },
    Expr::TyArr {
        domain: i(350),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(421),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(422),
        left: i(423),
        right: i(424),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(425),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(426),
        left: i(427),
        right: i(428),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(408),
    },
    Expr::TmApp {
        function: i(430),
        argument: i(429),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(432),
        argument: i(433),
    },
    Expr::TyArr {
        domain: i(350),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(434),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(435),
        left: i(436),
        right: i(437),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(431),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(439),
    },
    Expr::TmApp {
        function: i(440),
        argument: i(438),
    },
    Expr::TyArr {
        domain: i(405),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(405),
        body: i(441),
    },
    Expr::TmLam {
        domain: i(405),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(442),
        left: i(443),
        right: i(444),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(368),
    },
    Expr::TmApp {
        function: i(446),
        argument: i(404),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(447),
    },
    Expr::TmApp {
        function: i(448),
        argument: i(445),
    },
    Expr::TmLam {
        domain: i(350),
        body: i(449),
    },
    Expr::TmEps {
        ty: i(350),
        predicate: i(450),
    },
    Expr::TmApp {
        function: i(450),
        argument: i(451),
    },
    Expr::TmLam {
        domain: i(352),
        body: i(452),
    },
    Expr::TmEps {
        ty: i(352),
        predicate: i(453),
    },
    Expr::TmApp {
        function: i(453),
        argument: i(454),
    },
    Expr::TyExists { predicate: i(455) },
    Expr::TyModel { predicate: i(455) },
    Expr::TyArr {
        domain: i(457),
        codomain: i(457),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(458),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(460),
        argument: i(461),
    },
    Expr::TmApp {
        function: i(463),
        argument: i(462),
    },
    Expr::TmBv { index: 2 },
    Expr::TmEq {
        ty: i(457),
        left: i(464),
        right: i(465),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(466),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(467),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(468),
        left: i(469),
        right: i(470),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(471),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(472),
        left: i(473),
        right: i(474),
    },
    Expr::TmBv { index: 5 },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 2 },
    Expr::TmApp {
        function: i(476),
        argument: i(477),
    },
    Expr::TmApp {
        function: i(479),
        argument: i(478),
    },
    Expr::TmBv { index: 5 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(481),
        argument: i(482),
    },
    Expr::TmApp {
        function: i(484),
        argument: i(483),
    },
    Expr::TmEq {
        ty: i(457),
        left: i(480),
        right: i(485),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 1 },
    Expr::TmEq {
        ty: i(349),
        left: i(487),
        right: i(488),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 0 },
    Expr::TmEq {
        ty: i(457),
        left: i(490),
        right: i(491),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(489),
    },
    Expr::TmApp {
        function: i(493),
        argument: i(492),
    },
    Expr::TmEq {
        ty: i(2),
        left: i(486),
        right: i(494),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(495),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(496),
        left: i(497),
        right: i(498),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(499),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(500),
        left: i(501),
        right: i(502),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(503),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(504),
        left: i(505),
        right: i(506),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(507),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(508),
        left: i(509),
        right: i(510),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmBv { index: 0 },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(513),
        argument: i(514),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(516),
        argument: i(517),
    },
    Expr::TmBv { index: 4 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(519),
        argument: i(520),
    },
    Expr::TmApp {
        function: i(522),
        argument: i(521),
    },
    Expr::TmBv { index: 2 },
    Expr::TmApp {
        function: i(524),
        argument: i(523),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(518),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(526),
    },
    Expr::TmApp {
        function: i(527),
        argument: i(525),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(528),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(529),
        left: i(530),
        right: i(531),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(532),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(533),
        left: i(534),
        right: i(535),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(515),
    },
    Expr::TmApp {
        function: i(537),
        argument: i(536),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(539),
        argument: i(540),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(541),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(542),
        left: i(543),
        right: i(544),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(538),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(546),
    },
    Expr::TmApp {
        function: i(547),
        argument: i(545),
    },
    Expr::TyArr {
        domain: i(512),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(512),
        body: i(548),
    },
    Expr::TmLam {
        domain: i(512),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(549),
        left: i(550),
        right: i(551),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(475),
    },
    Expr::TmApp {
        function: i(553),
        argument: i(511),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(554),
    },
    Expr::TmApp {
        function: i(555),
        argument: i(552),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(556),
    },
    Expr::TmEps {
        ty: i(457),
        predicate: i(557),
    },
    Expr::TmApp {
        function: i(557),
        argument: i(558),
    },
    Expr::TmLam {
        domain: i(459),
        body: i(559),
    },
    Expr::TmEps {
        ty: i(459),
        predicate: i(560),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(457),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(562),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(564),
        argument: i(565),
    },
    Expr::TmApp {
        function: i(567),
        argument: i(566),
    },
    Expr::TmBv { index: 2 },
    Expr::TmEq {
        ty: i(457),
        left: i(568),
        right: i(569),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(570),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(571),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(572),
        left: i(573),
        right: i(574),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(575),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(576),
        left: i(577),
        right: i(578),
    },
    Expr::TmBv { index: 5 },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 2 },
    Expr::TmApp {
        function: i(580),
        argument: i(581),
    },
    Expr::TmApp {
        function: i(583),
        argument: i(582),
    },
    Expr::TmBv { index: 5 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(585),
        argument: i(586),
    },
    Expr::TmApp {
        function: i(588),
        argument: i(587),
    },
    Expr::TmEq {
        ty: i(457),
        left: i(584),
        right: i(589),
    },
    Expr::TmBv { index: 3 },
    Expr::TmBv { index: 1 },
    Expr::TmEq {
        ty: i(349),
        left: i(591),
        right: i(592),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 0 },
    Expr::TmEq {
        ty: i(457),
        left: i(594),
        right: i(595),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(593),
    },
    Expr::TmApp {
        function: i(597),
        argument: i(596),
    },
    Expr::TmEq {
        ty: i(2),
        left: i(590),
        right: i(598),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(599),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(600),
        left: i(601),
        right: i(602),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(603),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(604),
        left: i(605),
        right: i(606),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(607),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(608),
        left: i(609),
        right: i(610),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(611),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(612),
        left: i(613),
        right: i(614),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmBv { index: 0 },
    Expr::TmBv { index: 1 },
    Expr::TmApp {
        function: i(617),
        argument: i(618),
    },
    Expr::TmBv { index: 2 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(620),
        argument: i(621),
    },
    Expr::TmBv { index: 4 },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(623),
        argument: i(624),
    },
    Expr::TmApp {
        function: i(626),
        argument: i(625),
    },
    Expr::TmBv { index: 2 },
    Expr::TmApp {
        function: i(628),
        argument: i(627),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(622),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(630),
    },
    Expr::TmApp {
        function: i(631),
        argument: i(629),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(632),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(633),
        left: i(634),
        right: i(635),
    },
    Expr::TyArr {
        domain: i(349),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(636),
    },
    Expr::TmLam {
        domain: i(349),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(637),
        left: i(638),
        right: i(639),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(619),
    },
    Expr::TmApp {
        function: i(641),
        argument: i(640),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(643),
        argument: i(644),
    },
    Expr::TyArr {
        domain: i(457),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(645),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(646),
        left: i(647),
        right: i(648),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(642),
    },
    Expr::TmApp {
        function: i(32),
        argument: i(650),
    },
    Expr::TmApp {
        function: i(651),
        argument: i(649),
    },
    Expr::TyArr {
        domain: i(616),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(616),
        body: i(652),
    },
    Expr::TmLam {
        domain: i(616),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(653),
        left: i(654),
        right: i(655),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(579),
    },
    Expr::TmApp {
        function: i(657),
        argument: i(615),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(658),
    },
    Expr::TmApp {
        function: i(659),
        argument: i(656),
    },
    Expr::TmLam {
        domain: i(457),
        body: i(660),
    },
    Expr::TmLam {
        domain: i(563),
        body: i(661),
    },
    Expr::TmApp {
        function: i(662),
        argument: i(561),
    },
    Expr::TmEps {
        ty: i(457),
        predicate: i(663),
    },
];

/// Canonical, import-free, literal-free v0 definitions.
pub const INIT_ARENA: crate::StaticArena = crate::StaticArena::new_const(None, &[], 1, INIT_DEFS);

/// Stable references into [`INIT_ARENA`].
pub const INIT_REFS: InitRefs = InitRefs {
    bool_ty: i(2),
    false_: i(3),
    true_: i(4),
    not: i(7),
    and: i(23),
    or: i(32),
    infinity: i(69),
    nat_exists: i(143),
    nat_ty: i(144),
    zero: i(285),
    succ: i(215),
    add: i(321),
    two_fifty_six: i(338),
    byte_ty: i(349),
    bytes_exists: i(456),
    bytes_ty: i(457),
    bytes_nil: i(664),
    bytes_cons: i(561),
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_init_matches_the_readable_reference_builder() {
        let (arena, refs) = build_init_arena().unwrap();
        assert_eq!(refs, INIT_REFS);
        assert_eq!(arena.defs(), INIT_ARENA.defs());
        INIT_ARENA.validate().unwrap();
        assert!(
            INIT_ARENA
                .defs()
                .iter()
                .all(|expr| !matches!(expr, Expr::TmNat { .. } | Expr::TmBytes { .. }))
        );
        let encoded = crate::serialize_cbor(&INIT_ARENA).unwrap();
        let decoded: Arena = crate::deserialize_cbor(&encoded).unwrap();
        assert_eq!(decoded, INIT_ARENA.to_owned().unwrap());
        assert_eq!(crate::serialize_cbor(&decoded).unwrap(), encoded);
        let cached = crate::SharedArena::new(decoded).unwrap();
        assert_eq!(
            cached.address().to_string(),
            "347991489412c30c1c1838a1706812a77df44c0d949e24d1c46249edc135d6a1"
        );
    }
}
