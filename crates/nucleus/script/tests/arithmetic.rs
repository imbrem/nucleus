//! End-to-end coverage for the untrusted natural-number arithmetic layer.

use std::sync::OnceLock;

use covalence_lib_json::serde_json;
use covalence_logic_hol::{Kernel, Lit, Ref, ThmId, init};
use covalence_logic_hol_derived::{
    Bytes, Expr, NaturalNormalizer, NaturalRing, NaturalRingExt, NaturalSubtraction,
    NaturalSubtractionExt, Naturals, NumeralEngine, ProvedEquality, join_same_syntax,
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
    assert_eq!(ring.symbols().len(), 19);
}

#[test]
fn every_law_is_reachable_by_name() {
    let (_, _, ring) = arithmetic_kernel();
    for name in [
        "nat.add.associative",
        "nat.add.exchange",
        "nat.add.interchange",
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
        // A fresh fork per case: the arena only grows, and a proof costs time
        // proportional to its size, so sharing one kernel makes later cases
        // pay for earlier ones.
        let mut case = kernel.fork();
        let normalizer = NaturalNormalizer::new(&naturals, ring);
        let proof = normalizer
            .prove_equal(&mut case, &left, &right)
            .expect("equal normal forms");
        check_proved(&case, &proof);
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

    // Two literals fold even when the result truncates.
    let (value, proof) = normalizer
        .evaluate(&mut kernel, &(Expr::literal(5) - 7))
        .expect("truncated difference");
    assert_eq!(value, 0);
    check_proved(&kernel, &proof);
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

#[test]
fn both_numeral_engines_evaluate_the_same_arithmetic() {
    let (kernel, naturals, ring, subtraction) = subtraction_kernel();
    for engine in [NumeralEngine::Unary, NumeralEngine::Binary] {
        let normalizer =
            NaturalNormalizer::with_subtraction(&naturals, ring, subtraction).with_engine(engine);
        for (expr, value) in [
            ((Expr::literal(2) + 3) * 4, 20),
            (Expr::literal(7) - 4, 3),
            (Expr::literal(4) * 5 - 2, 18),
            (Expr::literal(0) * 9, 0),
        ] {
            let mut case = kernel.fork();
            let (evaluated, proof) = normalizer
                .evaluate(&mut case, &expr)
                .unwrap_or_else(|error| panic!("{} engine: {error}", engine.name()));
            assert_eq!(evaluated, value, "{} engine", engine.name());
            check_proved(&case, &proof);
        }
    }
}

#[test]
fn the_binary_engine_reaches_literals_the_unary_one_cannot() {
    let (kernel, naturals, ring, _) = subtraction_kernel();
    let unary = NaturalNormalizer::new(&naturals, ring);
    let binary = NaturalNormalizer::new(&naturals, ring).with_engine(NumeralEngine::Binary);
    let beyond = covalence_logic_hol_derived::MAX_LITERAL + 1;

    let mut case = kernel.fork();
    assert!(unary.numeral(&mut case, beyond).is_err());

    // Well past the unary bound, and past what a succ tower could hold at all.
    for value in [beyond, 1_000_000, 4_294_967_296] {
        let mut case = kernel.fork();
        let (evaluated, proof) = binary
            .evaluate(&mut case, &Expr::literal(value))
            .expect("binary literal");
        assert_eq!(evaluated, value);
        check_proved(&case, &proof);
    }
}

#[test]
fn the_binary_engine_evaluates_a_nontrivial_product() {
    let (kernel, naturals, ring, _) = subtraction_kernel();
    let normalizer = NaturalNormalizer::new(&naturals, ring).with_engine(NumeralEngine::Binary);
    let mut case = kernel.fork();
    let goal = (Expr::literal(123) + 456) * 789;
    let (evaluated, proof) = normalizer.evaluate(&mut case, &goal).expect("product");
    assert_eq!(evaluated, (123 + 456) * 789);
    check_proved(&case, &proof);
}

/// What one evaluation cost the kernel.
struct Cost {
    micros: u128,
    rows: usize,
    theorems: usize,
}

fn measure(
    kernel: &Kernel,
    normalizer: &NaturalNormalizer<'_>,
    expr: &Expr,
) -> Result<(u64, Cost), covalence_logic_hol_derived::NaturalError> {
    let mut case = kernel.fork();
    let rows_before = case.arena().len();
    let theorems_before = case.thm().live_theorems().count();
    let start = std::time::Instant::now();
    let (value, _) = normalizer.evaluate(&mut case, expr)?;
    let micros = start.elapsed().as_micros();
    Ok((
        value,
        Cost {
            micros,
            rows: case.arena().len() - rows_before,
            theorems: case.thm().live_theorems().count() - theorems_before,
        },
    ))
}

/// Compares the numeral engines on closed arithmetic.
///
/// Ignored: it is a measurement, not an assertion. Run it with
/// `cargo test -p covalence-nucleus-script --test arithmetic -- --ignored --nocapture`.
#[test]
#[ignore = "benchmark"]
fn numeral_engines_benchmark() {
    let (kernel, naturals, ring, _) = subtraction_kernel();
    // Unary multiplication is quadratic, so the shared cases stay small. The
    // last two are past what unary can build at all.
    let cases: [(&str, Expr); 6] = [
        ("2 + 3", Expr::literal(2) + 3),
        ("60 + 40", Expr::literal(60) + 40),
        ("7 * 8", Expr::literal(7) * 8),
        ("(3 + 4) * 12", (Expr::literal(3) + 4) * 12),
        ("(123 + 456) * 789", (Expr::literal(123) + 456) * 789),
        ("999999 + 1", Expr::literal(999_999) + 1),
    ];

    println!(
        "\n{:<20} {:>8}  {:>12} {:>8} {:>9}",
        "expression", "engine", "micros", "rows", "theorems"
    );
    for (name, expr) in &cases {
        for engine in [NumeralEngine::Unary, NumeralEngine::Binary] {
            let normalizer = NaturalNormalizer::new(&naturals, ring).with_engine(engine);
            match measure(&kernel, &normalizer, expr) {
                Ok((value, cost)) => println!(
                    "{:<20} {:>8}  {:>12} {:>8} {:>9}   = {}",
                    name,
                    engine.name(),
                    cost.micros,
                    cost.rows,
                    cost.theorems,
                    value
                ),
                Err(error) => println!(
                    "{:<20} {:>8}  {:>12}",
                    name,
                    engine.name(),
                    format!("refused: {error}")
                        .chars()
                        .take(40)
                        .collect::<String>()
                ),
            }
        }
    }
    println!();
}

#[test]
fn byte_strings_evaluate_inside_arithmetic() {
    let (kernel, naturals, ring, subtraction) = subtraction_kernel();
    let normalizer = NaturalNormalizer::with_subtraction(&naturals, ring, subtraction)
        .with_engine(NumeralEngine::Binary);
    let hello = Bytes::literal(*b"hello");
    let world = Bytes::literal(*b" world");

    for (goal, expected) in [
        // Length, in arithmetic.
        (hello.len().expect("len") + 1, 6),
        // Concatenation adds lengths.
        (hello.cat(&world).len().expect("len"), 11),
        // Slicing, then measuring.
        (hello.slice(1, 4).len().expect("len"), 3),
        // Indexing yields a byte, which is a natural below 256.
        (hello.index(0).expect("index"), u64::from(b'h')),
        // A byte taking part in real arithmetic.
        (hello.index(1).expect("index") * 2, u64::from(b'e') * 2),
    ] {
        let mut case = kernel.fork();
        let (value, proof) = normalizer.evaluate(&mut case, &goal).expect("evaluate");
        assert_eq!(value, expected);
        check_proved(&case, &proof);
    }
}

#[test]
fn every_byte_evaluates_to_a_natural_below_the_byte_bound() {
    let (kernel, naturals, ring, _) = subtraction_kernel();
    let normalizer = NaturalNormalizer::new(&naturals, ring).with_engine(NumeralEngine::Binary);
    let raw = vec![0u8, 1, 127, 128, 255];
    let bytes = Bytes::literal(raw.clone());

    for (at, expected) in raw.iter().enumerate() {
        let index = u64::try_from(at).expect("index fits");
        let mut case = kernel.fork();
        let (value, proof) = normalizer
            .evaluate(&mut case, &bytes.index(index).expect("index"))
            .expect("evaluate");
        assert_eq!(value, u64::from(*expected));
        assert!(value < covalence_logic_hol_derived::BYTE_BOUND);
        check_proved(&case, &proof);
    }
}

#[test]
fn out_of_range_byte_access_is_refused() {
    let bytes = Bytes::literal(*b"abc");
    assert!(bytes.index(3).is_err());
    assert!(bytes.slice(0, 4).len().is_err());
    assert!(bytes.slice(2, 1).len().is_err());
    // A slice of a slice is checked against the inner slice, not the literal.
    assert!(bytes.slice(0, 2).slice(0, 3).len().is_err());
    assert!(bytes.slice(0, 2).index(1).is_ok());
}

#[test]
fn literal_subtraction_truncates_at_zero() {
    let (kernel, naturals, ring, subtraction) = subtraction_kernel();
    for engine in [NumeralEngine::Unary, NumeralEngine::Binary] {
        let normalizer =
            NaturalNormalizer::with_subtraction(&naturals, ring, subtraction).with_engine(engine);
        for (left, right) in [(5u64, 7u64), (7, 5), (4, 4), (0, 3), (9, 0)] {
            let mut case = kernel.fork();
            let (value, proof) = normalizer
                .evaluate(&mut case, &(Expr::literal(left) - right))
                .unwrap_or_else(|error| panic!("{} engine, {left} - {right}: {error}", engine.name()));
            assert_eq!(value, left.saturating_sub(right), "{left} - {right}");
            check_proved(&case, &proof);
        }
    }
}
