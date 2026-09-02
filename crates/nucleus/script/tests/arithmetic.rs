//! End-to-end coverage for the untrusted natural-number arithmetic layer.

use std::sync::OnceLock;

use covalence_lib_json::serde_json;
use covalence_logic_hol::{Kernel, Lit, Ref, ThmId, init};
use covalence_logic_hol_derived::{
    Expr, NaturalNormalizer, NaturalRing, NaturalRingExt, NaturalSubtraction,
    NaturalSubtractionExt, Naturals, ProvedEquality, join_same_syntax,
};
use covalence_nucleus_script::compile_init_library;

#[cfg(not(feature = "buck-test-fixtures"))]
const LOGICAL_INIT: &str = include_str!("../../../../theories/init-boolean.checked.json");
#[cfg(feature = "buck-test-fixtures")]
const LOGICAL_INIT: &str = include_str!("../theories/init-boolean.checked.json");

fn logical_init() -> init::Compiled {
    let manifest: init::Manifest = serde_json::from_str(LOGICAL_INIT).expect("logical manifest");
    init::compile(&manifest).expect("checked logical prefix")
}

/// The init slice extended with `add`, `mul`, `pred`, and truncated
/// subtraction, plus every law proved over them.
///
/// Deriving this takes seconds, so it is built once and forked per test.
struct Fixture {
    kernel: Kernel,
    naturals: Naturals,
    ring: NaturalRing,
    subtraction: NaturalSubtraction,
}

fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let init = logical_init();
        let library = compile_init_library(&init).expect("init library");
        let naturals = *library.naturals();
        let arithmetic = *library.arithmetic();
        let schemas = library.recursion_schemas();
        let (mut kernel, _) = library.into_parts();
        let ring = kernel
            .natural_ring(&naturals, &arithmetic)
            .expect("semiring laws");
        let subtraction = kernel
            .natural_subtraction(&naturals, &arithmetic, &ring, schemas)
            .expect("truncated subtraction");
        Fixture {
            kernel,
            naturals,
            ring,
            subtraction,
        }
    })
}

fn arithmetic_kernel() -> (Kernel, Naturals, NaturalRing) {
    let fixture = fixture();
    (fixture.kernel.fork(), fixture.naturals, fixture.ring)
}

fn subtraction_kernel() -> (Kernel, Naturals, NaturalRing, NaturalSubtraction) {
    let fixture = fixture();
    (
        fixture.kernel.fork(),
        fixture.naturals,
        fixture.ring,
        fixture.subtraction,
    )
}

fn check_exact_theorem(kernel: &Kernel, proposition: Ref, theorem: ThmId) {
    let theorem = kernel.thm().get(theorem).expect("resident theorem");
    assert!(theorem.lhs.rows().next().is_none());
    assert_eq!(
        theorem.rhs.rows().collect::<Vec<_>>(),
        vec![&[Lit::positive(proposition.get())][..]]
    );
}

#[test]
fn the_semiring_laws_are_premise_free_theorems() {
    let (kernel, _, ring) = arithmetic_kernel();
    let mut names = Vec::new();
    for (name, proposition, theorem) in ring.symbols() {
        check_exact_theorem(&kernel, proposition, theorem);
        names.push(name);
    }
    names.sort_unstable();
    let mut unique = names.clone();
    unique.dedup();
    assert_eq!(names, unique, "law names collide");
    assert_eq!(ring.symbols().len(), 18);
}

#[test]
fn every_law_is_reachable_by_name() {
    let (_, _, ring) = arithmetic_kernel();
    for name in [
        "nat.add.associative",
        "nat.add.exchange",
        "nat.mul.right_zero",
        "nat.mul.right_successor",
        "nat.mul.one",
        "nat.mul.right_one",
        "nat.mul.commutative",
        "nat.mul.associative",
        "nat.mul.exchange",
        "nat.mul.right_distributive",
        "nat.mul.left_distributive",
    ] {
        assert!(ring.get(name).is_some(), "missing statement for {name}");
        assert!(ring.theorem(name).is_some(), "missing theorem for {name}");
    }
    assert_eq!(ring.get("nat.mul.nonexistent"), None);
}

#[test]
fn derivation_is_deterministic() {
    let build = || {
        let init = logical_init();
        let library = compile_init_library(&init).expect("init library");
        let naturals = *library.naturals();
        let arithmetic = *library.arithmetic();
        let (mut kernel, _) = library.into_parts();
        let ring = kernel
            .natural_ring(&naturals, &arithmetic)
            .expect("semiring laws");
        (kernel.arena().addr(), ring.declaration)
    };
    assert_eq!(build(), build());
}

#[test]
fn a_low_binder_block_is_rejected_before_mutation() {
    let init = logical_init();
    let library = compile_init_library(&init).expect("init library");
    let naturals = *library.naturals();
    let arithmetic = *library.arithmetic();
    let (mut kernel, _) = library.into_parts();
    let before = kernel.fork();
    assert!(kernel.natural_ring_at(&naturals, &arithmetic, 0).is_err());
    assert_eq!(kernel.arena(), before.arena());
}

#[test]
fn the_subtraction_laws_are_premise_free_theorems() {
    let (kernel, _, _, subtraction) = subtraction_kernel();
    for (_, proposition, theorem) in subtraction.symbols() {
        check_exact_theorem(&kernel, proposition, theorem);
    }
    assert_eq!(subtraction.symbols().len(), 6);
    for name in [
        "nat.pred.zero",
        "nat.pred.successor",
        "nat.sub.zero",
        "nat.sub.successor",
        "nat.sub.successor_both",
        "nat.sub.add_cancel",
    ] {
        assert!(subtraction.get(name).is_some(), "missing statement {name}");
        assert!(
            subtraction.theorem(name).is_some(),
            "missing theorem {name}"
        );
    }
}

/// Three distinct `nat` variables to normalize over.
fn variables(kernel: &mut Kernel, naturals: &Naturals) -> [Ref; 3] {
    let mut names = kernel.fresh_name(&[naturals.ty]).expect("fresh name");
    let mut next = || {
        let term = kernel.tm_fv(names, naturals.ty).expect("variable");
        names += 1;
        term
    };
    [next(), next(), next()]
}

fn numeral(kernel: &mut Kernel, naturals: &Naturals, value: u64) -> Ref {
    let mut term = naturals.zero;
    for _ in 0..value {
        term = kernel.app(naturals.succ, term).expect("successor");
    }
    term
}

/// Checks that a proved equality is premise-free and concludes exactly itself.
fn check_proved(kernel: &Kernel, equality: &ProvedEquality) {
    check_exact_theorem(kernel, equality.equality, equality.theorem);
}

/// The arena appends rather than shares rows, so equal terms compare by
/// syntax, not by reference.
fn assert_same_term(kernel: &mut Kernel, left: Ref, right: Ref) {
    join_same_syntax(kernel, left, right).expect("syntactically equal terms");
}

#[test]
fn the_headline_expression_normalizes() {
    let (mut kernel, naturals, ring, subtraction) = subtraction_kernel();
    let [x, y, _] = variables(&mut kernel, &naturals);
    let normalizer = NaturalNormalizer::with_subtraction(&naturals, ring, subtraction);

    let goal = Expr::atom(x) * Expr::atom(y) + 5 - 3;
    let proof = normalizer
        .normalize(&mut kernel, &goal)
        .expect("normal form");
    check_proved(&kernel, &proof);

    let product = {
        let partial = kernel.app(ring.signature.mul, x).expect("mul x");
        kernel.app(partial, y).expect("x * y")
    };
    let two = numeral(&mut kernel, &naturals, 2);
    let expected = {
        let partial = kernel.app(ring.signature.add, product).expect("add");
        kernel.app(partial, two).expect("x * y + 2")
    };
    assert_same_term(&mut kernel, proof.right, expected);
    let source = normalizer.term(&mut kernel, &goal).expect("source term");
    assert_same_term(&mut kernel, proof.left, source);
}

#[test]
fn the_standard_laws_are_reachable_through_the_normalizer() {
    let (mut kernel, naturals, ring, _) = subtraction_kernel();
    let [x, y, z] = variables(&mut kernel, &naturals);
    let normalizer = NaturalNormalizer::new(&naturals, ring);
    let (x, y, z) = (Expr::atom(x), Expr::atom(y), Expr::atom(z));

    for (left, right) in [
        // commutativity
        (&x + &y, &y + &x),
        (&x * &y, &y * &x),
        // associativity
        ((&x + &y) + &z, &x + (&y + &z)),
        ((&x * &y) * &z, &x * (&y * &z)),
        // distributivity, both sides
        ((&x + &y) * &z, &x * &z + &y * &z),
        (&x * (&y + &z), &x * &y + &x * &z),
        // units and collection
        (&x + Expr::literal(0), x.clone()),
        (&x * Expr::literal(1), x.clone()),
        (&x + &x, &x * 2),
        (&x * &x + &x * &x, &x * &x * 2),
    ] {
        let proof = normalizer
            .prove_equal(&mut kernel, &left, &right)
            .expect("equal normal forms");
        check_proved(&kernel, &proof);
    }
}

#[test]
fn a_closed_expression_evaluates() {
    let (mut kernel, naturals, ring, subtraction) = subtraction_kernel();
    let normalizer = NaturalNormalizer::with_subtraction(&naturals, ring, subtraction);
    for (expr, value) in [
        ((Expr::literal(2) + 3) * 4, 20),
        (Expr::literal(7) - 4, 3),
        (Expr::literal(4) * 5 - 2, 18),
        (Expr::literal(0) * 9, 0),
    ] {
        let (evaluated, proof) = normalizer.evaluate(&mut kernel, &expr).expect("value");
        assert_eq!(evaluated, value);
        check_proved(&kernel, &proof);
        let expected = numeral(&mut kernel, &naturals, value);
        assert_same_term(&mut kernel, proof.right, expected);
    }
}

#[test]
fn an_undischargeable_subtraction_stays_an_atom() {
    let (mut kernel, naturals, ring, subtraction) = subtraction_kernel();
    let [x, y, _] = variables(&mut kernel, &naturals);
    let normalizer = NaturalNormalizer::with_subtraction(&naturals, ring, subtraction);
    let difference = Expr::atom(x) - Expr::atom(y);

    let proof = normalizer
        .prove_equal(
            &mut kernel,
            &(&difference + &difference),
            &(&difference * 2),
        )
        .expect("the difference collects like any other atom");
    check_proved(&kernel, &proof);

    // Truncation is not asserted: 5 - 7 is left alone rather than folded to 0.
    assert!(
        normalizer
            .evaluate(&mut kernel, &(Expr::literal(5) - 7))
            .is_err()
    );
}

#[test]
fn expressions_with_different_normal_forms_are_refused() {
    let (mut kernel, naturals, ring, _) = subtraction_kernel();
    let [x, y, _] = variables(&mut kernel, &naturals);
    let normalizer = NaturalNormalizer::new(&naturals, ring);
    assert!(
        normalizer
            .prove_equal(&mut kernel, &(Expr::atom(x) + 1), &Expr::atom(y))
            .is_err()
    );
}

#[test]
fn a_literal_above_the_numeral_bound_is_refused() {
    let (mut kernel, naturals, ring, _) = subtraction_kernel();
    let normalizer = NaturalNormalizer::new(&naturals, ring);
    let bound = covalence_logic_hol_derived::MAX_LITERAL;
    assert!(normalizer.numeral(&mut kernel, bound + 1).is_err());
}
