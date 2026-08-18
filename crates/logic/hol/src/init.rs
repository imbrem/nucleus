//! Pure-`HolE` construction of the v0 foundational arena.

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
    pub nat_ty: Ix,
    pub zero: Ix,
    pub succ: Ix,
}

struct Builder {
    arena: Arena,
    bool_ty: Ix,
    true_: Ix,
    not: Ix,
    and: Ix,
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

    /// The infinity structure in context `[z : A]` for a closed `f`.
    fn structure_closed_function(&mut self, a: Ix, f: Ix) -> Result<Ix, ArenaError> {
        let x = self.bv(1)?;
        let y = self.bv(0)?;
        let fx = self.app(f, x)?;
        let fy = self.app(f, y)?;
        let image_eq = self.eq(a, fx, fy)?;
        let source_eq = self.eq(a, x, y)?;
        let reflected = self.eq(self.bool_ty, image_eq, source_eq)?;
        let forall_y = self.forall(a, reflected)?;
        let reflects = self.forall(a, forall_y)?;

        let z = self.bv(1)?;
        let x = self.bv(0)?;
        let fx = self.app(f, x)?;
        let hits = self.eq(a, fx, z)?;
        let misses = self.not(hits)?;
        let misses = self.forall(a, misses)?;
        self.and(reflects, misses)
    }

    fn type_predicate(&mut self, a: Ix) -> Result<Ix, ArenaError> {
        let endomap = self.arr(a, a)?;
        let structure = self.structure_bound(a)?;
        let choose_z = self.exists(a, structure)?;
        self.exists(endomap, choose_z)
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
    };
    let left = builder.bv(1)?;
    let left_not = builder.not(left)?;
    let right = builder.bv(0)?;
    let right_not = builder.not(right)?;
    let neither = builder.and(left_not, right_not)?;
    let either = builder.not(neither)?;
    let or_right = builder.lam(bool_ty, either)?;
    let or = builder.lam(bool_ty, or_right)?;

    let a = builder.push(Expr::TyBv { index: 0 })?;
    let type_predicate = builder.type_predicate(a)?;
    let infinity = builder.push(Expr::TyExists {
        predicate: type_predicate,
    })?;
    let nat_ty = builder.push(Expr::TyModel {
        predicate: type_predicate,
    })?;

    let endomap = builder.arr(nat_ty, nat_ty)?;
    let structure = builder.structure_bound(nat_ty)?;
    let choose_zero = builder.exists(nat_ty, structure)?;
    let successor_predicate = builder.lam(endomap, choose_zero)?;
    let succ = builder.eps(endomap, successor_predicate)?;
    let zero_structure = builder.structure_closed_function(nat_ty, succ)?;
    let zero_predicate = builder.lam(nat_ty, zero_structure)?;
    let zero = builder.eps(nat_ty, zero_predicate)?;

    let refs = InitRefs {
        bool_ty,
        false_,
        true_,
        not,
        and,
        or,
        infinity,
        nat_ty,
        zero,
        succ,
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
    Expr::TyModel { predicate: i(68) },
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
    Expr::TmLam {
        domain: i(70),
        body: i(99),
    },
    Expr::TmEps {
        ty: i(70),
        predicate: i(100),
    },
    Expr::TmApp {
        function: i(100),
        argument: i(101),
    },
    Expr::TmLam {
        domain: i(71),
        body: i(102),
    },
    Expr::TmEps {
        ty: i(71),
        predicate: i(103),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(104),
        argument: i(105),
    },
    Expr::TmApp {
        function: i(104),
        argument: i(106),
    },
    Expr::TmEq {
        ty: i(70),
        left: i(107),
        right: i(108),
    },
    Expr::TmEq {
        ty: i(70),
        left: i(105),
        right: i(106),
    },
    Expr::TmEq {
        ty: i(2),
        left: i(109),
        right: i(110),
    },
    Expr::TyArr {
        domain: i(70),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(111),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(112),
        left: i(113),
        right: i(114),
    },
    Expr::TyArr {
        domain: i(70),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(115),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(116),
        left: i(117),
        right: i(118),
    },
    Expr::TmBv { index: 1 },
    Expr::TmBv { index: 0 },
    Expr::TmApp {
        function: i(104),
        argument: i(121),
    },
    Expr::TmEq {
        ty: i(70),
        left: i(122),
        right: i(120),
    },
    Expr::TmApp {
        function: i(7),
        argument: i(123),
    },
    Expr::TyArr {
        domain: i(70),
        codomain: i(2),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(124),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(4),
    },
    Expr::TmEq {
        ty: i(125),
        left: i(126),
        right: i(127),
    },
    Expr::TmApp {
        function: i(23),
        argument: i(119),
    },
    Expr::TmApp {
        function: i(129),
        argument: i(128),
    },
    Expr::TmLam {
        domain: i(70),
        body: i(130),
    },
    Expr::TmEps {
        ty: i(70),
        predicate: i(131),
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
    nat_ty: i(70),
    zero: i(132),
    succ: i(104),
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
            "bd45466292e106cf30b9e596e4432058e18141460b9032d740c034ef614709ed"
        );
    }
}
