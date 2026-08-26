//! End-to-end coverage for the untrusted theory front end.

use covalence_lib_json::serde_json;
use covalence_logic_hol::{AX_INF, AX_SUB, Kernel, Sort, Tag, TmTag, init};
use covalence_logic_hol_derived::{
    NaturalArithmeticExt, NaturalExt, NaturalRecExt, NaturalRecSchemas, join_alpha_equivalent,
    join_same_syntax,
};
use covalence_logic_hol_script::{
    INIT_SOURCE, LogicEncoding, TheoryError, TheoryOptions, compile_init, compile_init_library,
    compile_init_slice, compile_theory, compile_theory_with_init,
};

#[cfg(not(feature = "buck-test-fixtures"))]
const LOGICAL_INIT: &str = include_str!("../../../../theories/init-boolean.checked.json");
#[cfg(feature = "buck-test-fixtures")]
const LOGICAL_INIT: &str = include_str!("../theories/init-boolean.checked.json");

fn logical_init() -> init::Compiled {
    let manifest: init::Manifest = serde_json::from_str(LOGICAL_INIT).expect("logical manifest");
    init::compile(&manifest).expect("checked logical prefix")
}

const COPRODUCT: &str = r"
  ; The universal property, as an open schema rather than an assertion.
  (define IsCoprod ('a 'b 't)
    (exists inl (-> 'a 't)
      (exists inr (-> 'b 't)
        (ty.forall 'c
          (forall f (-> 'a 'c)
            (forall g (-> 'b 'c)
              (exists h (-> 't 'c)
                (and
                  (and
                    (forall x 'a (= (h (inl x)) (f x)))
                    (forall y 'b (= (h (inr y)) (g y))))
                  (forall k (-> 't 'c)
                    (imp
                      (and
                        (forall x 'a (= (k (inl x)) (f x)))
                        (forall y 'b (= (k (inr y)) (g y))))
                      (= k h)))))))))))
";

const NAT_CARVING: &str = r"
  ; The predicate used to carve naturals out of an infinite carrier.
  (define NatMember ('a)
    (-> 'a (-> (-> 'a 'a) (-> 'a bool)))
    (lambda zero 'a
      (lambda succ (-> 'a 'a)
        (lambda n 'a
          (forall P (-> 'a bool)
            (imp
              (and
                (P zero)
                (forall k 'a (imp (P k) (P (succ k)))))
              (P n)))))))

  ; Explicit specialization is mandatory; the open row never leaks.
  (define BoolNatMember ()
    (-> bool (-> (-> bool bool) (-> bool bool)))
    (inst NatMember bool))
";

#[test]
fn coproduct_schema_compiles_to_a_checked_boolean_root() {
    let compiled = compile_theory(COPRODUCT).expect("coproduct schema");
    let root = compiled.get("IsCoprod").expect("public root");

    assert_eq!(
        compiled.kernel().category(root).expect("category"),
        Sort::Tm
    );
    let classifier = compiled.kernel().classifier(root).expect("classifier");
    assert_eq!(
        compiled.kernel().arena().tag(classifier),
        Some(Tag::Ty(covalence_logic_hol::TyTag::Bool))
    );
    assert_eq!(
        compiled.definitions().collect::<Vec<_>>(),
        [("IsCoprod", root)]
    );
    assert!(compiled.get("IsCoprod/'a").is_some());
    assert!(compiled.get("IsCoprod/'b").is_some());
    assert!(compiled.get("IsCoprod/'t").is_some());

    // The type universal sits beneath the existentially bound injections and
    // its body mentions them. This is the open-quantifier case from #991.
    let last = i32::try_from(compiled.kernel().arena().len()).expect("arena fits Ref");
    assert!((1..=last).any(|index| {
        covalence_logic_hol::Ref::new(index).is_some_and(|reference| {
            compiled.kernel().arena().tag(reference) == Some(Tag::Tm(TmTag::TyForall))
        })
    }));
}

#[test]
fn compilation_is_deterministic_but_names_are_external_metadata() {
    let left = compile_theory(COPRODUCT).expect("left");
    let right = compile_theory(COPRODUCT).expect("right");
    assert_eq!(left.kernel().arena().addr(), right.kernel().arena().addr());
    assert_eq!(
        left.definitions().collect::<Vec<_>>(),
        right.definitions().collect::<Vec<_>>()
    );
    assert_eq!(
        left.symbols().collect::<Vec<_>>(),
        right.symbols().collect::<Vec<_>>()
    );
}

#[test]
fn malformed_and_ill_typed_sources_never_escape_checked_construction() {
    assert!(matches!(
        compile_theory("(define P ('a) true"),
        Err(TheoryError::Read { .. })
    ));
    assert!(matches!(
        compile_theory("(define P ('a) missing)"),
        Err(TheoryError::Unknown { .. })
    ));
    assert!(matches!(
        compile_theory("(define P ('a) (true true))"),
        Err(TheoryError::Kernel { .. })
    ));
}

#[test]
fn nesting_is_bounded_before_elaboration() {
    let source = format!("{}true{}", "(".repeat(257), ")".repeat(257));
    assert!(matches!(
        compile_theory(&source),
        Err(TheoryError::Read { .. })
    ));
}

#[test]
fn typed_lambdas_and_explicit_schema_instantiation_are_checked() {
    let compiled = compile_theory(
        r"
        (define id ('a) (-> 'a 'a) (lambda x 'a x))
        (define const ('a 'b) (-> 'a (-> 'b 'a))
          (lambda x 'a (lambda y 'b x)))
        (define bool-id () (-> bool bool) (inst id bool))
        (define bool-id-again () (-> bool bool) (inst id bool))
        (define bool-const () (-> bool (-> bool bool)) (inst const bool bool))
        (define truth () bool ((inst id bool) true))
        ",
    )
    .expect("typed definitions");

    let id = compiled.get("id").expect("open identity");
    let bool_id = compiled.get("bool-id").expect("Boolean identity");
    assert_eq!(compiled.get("bool-id-again"), Some(bool_id));
    let truth = compiled.get("truth").expect("identity application");
    assert_eq!(compiled.kernel().arena().tag(id), Some(Tag::Tm(TmTag::Lam)));
    assert_eq!(
        compiled.kernel().arena().tag(bool_id),
        Some(Tag::Tm(TmTag::Lam))
    );
    assert_eq!(compiled.kernel().category(truth).expect("term"), Sort::Tm);
    assert!(compiled.get("id/'a").is_some());
}

#[test]
fn natural_induction_carving_is_a_reusable_open_definition() {
    let compiled = compile_theory(NAT_CARVING).expect("natural carving predicate");
    let open = compiled.get("NatMember").expect("open predicate");
    let specialized = compiled
        .get("BoolNatMember")
        .expect("specialized predicate");
    assert_eq!(
        compiled.kernel().arena().tag(open),
        Some(Tag::Tm(TmTag::Lam))
    );
    assert_eq!(
        compiled.kernel().arena().tag(specialized),
        Some(Tag::Tm(TmTag::Lam))
    );
    assert!(compiled.get("NatMember/'a").is_some());
}

#[test]
fn checked_init_source_is_a_deterministic_untrusted_compilation_unit() {
    let first = compile_theory(INIT_SOURCE).expect("init source");
    let second = compile_theory(INIT_SOURCE).expect("init source again");

    assert!(first.get("IsCoprod").is_some());
    assert!(first.get("NatMember").is_some());
    let recursor = first.get("NatRecSpec").expect("recursion specification");
    assert_eq!(
        first.kernel().arena().tag(recursor),
        Some(Tag::Tm(TmTag::Lam))
    );
    assert!(first.get("NatRecSpec/'a").is_some());
    assert!(first.get("NatRecSpec/'c").is_some());
    let graph = first.get("NatRecGraph").expect("recursion graph");
    assert_eq!(first.kernel().arena().tag(graph), Some(Tag::Tm(TmTag::Lam)));
    assert!(first.get("NatRecGraph/'a").is_some());
    assert!(first.get("NatRecGraph/'c").is_some());
    assert_eq!(
        first.kernel().arena().addr(),
        second.kernel().arena().addr()
    );
    assert!(first.kernel().arena().axioms().next().is_none());
}

#[test]
fn canonical_init_compilation_is_opcode_free() {
    let init = logical_init();
    let compiled = compile_init(&init).expect("opcode-free init source");
    assert!(compiled.get("IsCoprod").is_some());
    assert!(compiled.get("NatMember").is_some());
    assert!(compiled.get("NatRecSpec").is_some());
    assert!(compiled.get("NatRecGraph").is_some());

    let last = i32::try_from(compiled.kernel().arena().len()).expect("arena fits Ref");
    for index in 1..=last {
        let reference = covalence_logic_hol::Ref::new(index).expect("positive index");
        assert!(!matches!(
            compiled.kernel().arena().tag(reference),
            Some(Tag::Tm(TmTag::Op1 | TmTag::Op2))
        ));
    }
    assert!(compiled.kernel().arena().axioms().next().is_none());
}

#[test]
fn equality_only_source_uses_the_authoritative_logical_lowering() {
    let init = logical_init();
    let source = "(define sample () bool (and true false))";
    let raw = compile_theory_with_init(
        source,
        TheoryOptions {
            logic: LogicEncoding::EqualityOnly,
        },
        &init,
    )
    .expect("raw source");
    let raw_root = raw.get("sample").expect("raw root");
    assert_eq!(
        raw.kernel().arena().tag(raw_root),
        Some(Tag::Tm(TmTag::App))
    );

    let compact = compile_theory_with_init(
        source,
        TheoryOptions {
            logic: LogicEncoding::Compact,
        },
        &init,
    )
    .expect("compact source");
    let compact_root = compact.get("sample").expect("compact root");
    let (raw_kernel, _) = raw.into_parts();
    let (mut compact_kernel, _) = compact.into_parts();
    let copied = compact_kernel
        .copy_term_from(&raw_kernel, raw_root)
        .expect("copy raw expansion into compact kernel");
    let copied_raw = copied.roots()[0];
    let expansion = compact_kernel
        .lower_logical(&init, compact_root)
        .expect("canonical compact lowering");
    join_same_syntax(&mut compact_kernel, expansion, copied_raw)
        .expect("lowering equals direct source elaboration");

    let canonical = compile_init(&init).expect("canonical source over logical prefix");
    assert_eq!(canonical.logical_init(), Some(&init));
    let last = i32::try_from(canonical.kernel().arena().len()).expect("arena fits Ref");
    for index in 1..=last {
        let reference = covalence_logic_hol::Ref::new(index).expect("positive index");
        assert!(!matches!(
            canonical.kernel().arena().tag(reference),
            Some(Tag::Tm(TmTag::Op1 | TmTag::Op2))
        ));
    }
}

#[test]
fn compiled_nat_member_drives_the_userspace_natural_package() {
    let init = logical_init();
    let compiled = compile_theory_with_init(
        INIT_SOURCE,
        TheoryOptions {
            logic: LogicEncoding::Compact,
        },
        &init,
    )
    .expect("compact proof view of init source");
    let bool_ty = compiled.bool_type();
    let parameter = compiled
        .get("NatMember/'a")
        .expect("open carrier parameter");
    let schema = compiled.get("NatMember").expect("open member schema");
    let (mut kernel, names) = compiled.into_parts();

    kernel.add_axiom(AX_INF).expect("infinity capability");
    kernel.add_axiom(AX_SUB).expect("subtype capability");
    let naturals = kernel
        .choose_naturals_from_member_schema(bool_ty, parameter, schema)
        .expect("naturals from compiled schema");

    assert_eq!(names.get("NatMember"), Some(&schema));
    let predicate_ty = kernel.classifier(naturals.member).expect("member type");
    let mut predicate_parts = kernel
        .arena()
        .children(predicate_ty)
        .expect("predicate arrow");
    assert_eq!(predicate_parts.next(), Some(naturals.infinity.carrier));
    assert_eq!(predicate_parts.next(), Some(bool_ty));
    assert_eq!(naturals.subtype.predicate, naturals.member);
    assert_eq!(naturals.get("nat"), Some(naturals.ty));
    assert_eq!(naturals.get("nat.induction"), Some(naturals.induction));
}

#[test]
fn compiled_recursion_schemata_drive_the_complete_checked_package() {
    let init = logical_init();
    let compiled = compile_theory_with_init(
        INIT_SOURCE,
        TheoryOptions {
            logic: LogicEncoding::Compact,
        },
        &init,
    )
    .expect("compact proof view of init source");
    let bool_ty = compiled.bool_type();
    let natural_parameter = compiled.get("NatRecGraph/'a").expect("natural parameter");
    let codomain_parameter = compiled.get("NatRecGraph/'c").expect("codomain parameter");
    let schema = compiled.get("NatRecGraph").expect("graph schema");
    let specification_natural_parameter = compiled
        .get("NatRecSpec/'a")
        .expect("specification natural parameter");
    let specification_codomain_parameter = compiled
        .get("NatRecSpec/'c")
        .expect("specification codomain parameter");
    let specification_schema = compiled.get("NatRecSpec").expect("specification schema");
    let (mut kernel, _) = compiled.into_parts();
    kernel.add_axiom(AX_INF).expect("infinity capability");
    kernel.add_axiom(AX_SUB).expect("subtype capability");
    let naturals = kernel.choose_naturals(bool_ty).expect("naturals");

    let base = kernel.bool(bool_ty, true).expect("base");
    let n = kernel
        .tm_fv(
            kernel.fresh_name(&[naturals.ty]).expect("name"),
            naturals.ty,
        )
        .expect("natural binder");
    let accumulator = kernel
        .tm_fv(kernel.fresh_name(&[n]).expect("name"), bool_ty)
        .expect("accumulator binder");
    let inner = kernel.lam(accumulator, accumulator).expect("inner step");
    let step = kernel.lam(n, inner).expect("step");
    let schemas = NaturalRecSchemas {
        graph: schema,
        graph_natural: natural_parameter,
        graph_codomain: codomain_parameter,
        specification: specification_schema,
        specification_natural: specification_natural_parameter,
        specification_codomain: specification_codomain_parameter,
    };
    let recursor = kernel
        .natural_rec_from_schemata(&naturals, schemas, bool_ty, base, step)
        .expect("checked recursion package");
    let graph = recursor.graph;

    for (proposition, theorem) in [
        (graph.base, graph.base_theorem),
        (graph.step, graph.step_theorem),
        (graph.total, graph.total_theorem),
        (graph.has_shape, graph.has_shape_theorem),
        (graph.zero_value, graph.zero_value_theorem),
        (graph.successor_value, graph.successor_value_theorem),
        (graph.zero_functional, graph.zero_functional_theorem),
        (graph.functional, graph.functional_theorem),
        (graph.rec_graph, graph.rec_graph_theorem),
        (graph.rec_zero, graph.rec_zero_theorem),
        (graph.rec_successor, graph.rec_successor_theorem),
    ] {
        let theorem = kernel.thm().get(theorem).expect("graph theorem");
        assert!(theorem.lhs.rows().next().is_none());
        let conclusions = theorem.rhs.rows().collect::<Vec<_>>();
        assert_eq!(conclusions.len(), 1);
        assert_eq!(
            conclusions[0],
            [covalence_logic_hol::Lit::positive(proposition.get())]
        );
    }
    for (proposition, theorem) in [
        (recursor.specification, recursor.specification_theorem),
        (recursor.unique, recursor.unique_theorem),
    ] {
        let theorem = kernel.thm().get(theorem).expect("recursor theorem");
        assert!(theorem.lhs.rows().next().is_none());
        assert_eq!(
            theorem.rhs.rows().collect::<Vec<_>>(),
            vec![&[covalence_logic_hol::Lit::positive(proposition.get())][..]]
        );
    }

    check_primitive_arithmetic(&mut kernel, &naturals, schemas);
}

#[test]
fn init_library_workspace_assembles_reproducibly_outside_the_kernel() {
    let init = logical_init();
    let first = compile_init_library(&init).expect("first init library");
    let second = compile_init_library(&init).expect("second init library");

    assert_eq!(first.kernel().arena(), second.kernel().arena());
    assert_eq!(
        first.symbols().collect::<Vec<_>>(),
        second.symbols().collect::<Vec<_>>()
    );
    assert_eq!(first.get("star"), init.get("star"));
    assert_eq!(first.get("bool"), init.get("bool"));
    assert_eq!(first.get("nat"), Some(first.naturals().ty));
    assert_eq!(
        first.get("nat.add"),
        Some(first.arithmetic().declaration.add)
    );
    assert_eq!(
        first.get("nat.mul"),
        Some(first.arithmetic().declaration.mul)
    );
    assert_eq!(
        first.recursion_schemas().graph,
        first.get("NatRecGraph").expect("graph schema")
    );
    assert_eq!(
        first.kernel().arena().axioms().collect::<Vec<_>>(),
        [AX_INF, AX_SUB]
    );

    check_exact_theorem(
        first.kernel(),
        first.arithmetic().declaration.one_plus_one,
        first.arithmetic().proof.one_plus_one,
    );
}

#[test]
fn projected_init_slice_is_deterministic_complete_and_opcode_free() {
    let init = logical_init();
    let first = compile_init_slice(&init).expect("first projected slice");
    let second = compile_init_slice(&init).expect("second projected slice");

    assert_eq!(first.prefix().arena(), second.prefix().arena());
    assert_eq!(
        first.symbols().collect::<Vec<_>>(),
        second.symbols().collect::<Vec<_>>()
    );
    for name in [
        "star",
        "bool",
        "IsCoprod",
        "NatMember",
        "nat",
        "nat.induction",
        "nat.add",
        "nat.add.successor",
        "nat.mul",
        "nat.mul.successor",
        "nat.one_plus_one",
    ] {
        let reference = first.get(name).unwrap_or_else(|| panic!("missing {name}"));
        assert!(reference.get() <= i32::try_from(first.prefix().arena().len()).unwrap());
    }
    let arena = first.prefix().arena();
    for position in 1..=arena.len() {
        let reference = covalence_logic_hol::Ref::new(i32::try_from(position).unwrap()).unwrap();
        assert!(!matches!(
            arena.tag(reference),
            Some(Tag::Tm(TmTag::Op1 | TmTag::Op2))
        ));
    }
    let fork = first.kernel();
    assert_eq!(
        fork.init_prefix(),
        Some((arena.addr(), arena.len())),
        "the complete projected slice is the fork identity"
    );
    assert_eq!(fork.arena().axioms().collect::<Vec<_>>(), [AX_INF, AX_SUB]);
    for (name, reference) in first
        .naturals()
        .symbols()
        .chain(first.arithmetic().symbols())
    {
        assert_eq!(Some(reference), first.get(name), "typed root {name}");
    }
    for reference in first
        .naturals()
        .references()
        .chain(first.arithmetic().references())
    {
        assert!(
            reference.get() <= i32::try_from(arena.len()).unwrap(),
            "private replay root {reference:?} must reside in the frozen prefix"
        );
    }
    let schemas = first.recursion_schemas();
    for (name, reference) in [
        ("NatRecGraph", schemas.graph),
        ("NatRecGraph/'a", schemas.graph_natural),
        ("NatRecGraph/'c", schemas.graph_codomain),
        ("NatRecSpec", schemas.specification),
        ("NatRecSpec/'a", schemas.specification_natural),
        ("NatRecSpec/'c", schemas.specification_codomain),
    ] {
        assert_eq!(Some(reference), first.get(name), "typed schema {name}");
    }
}

#[test]
fn frozen_member_schema_replays_through_a_checked_compact_alias() {
    let init = logical_init();
    let slice = compile_init_slice(&init).expect("projected slice");
    let mut certificate = slice.kernel();
    let member = certificate
        .compact_logical_tree(&init, slice.get("NatMember").unwrap())
        .expect("checked compact schema alias");
    let replayed = certificate
        .choose_naturals_from_member_schema(
            slice.get("bool").unwrap(),
            slice.get("NatMember/'a").unwrap(),
            member.compact,
        )
        .expect("replayed natural derivation");

    assert_eq!(replayed.symbols().len(), slice.naturals().symbols().len());
    let frozen_symbols = slice.naturals().symbols().collect::<Vec<_>>();
    let roots = frozen_symbols
        .iter()
        .map(|(_, frozen)| *frozen)
        .collect::<Vec<_>>();
    let frozen_aliases = certificate
        .compact_logical_trees(&init, &roots)
        .expect("compact frozen natural declaration");
    let frozen = frozen_symbols
        .into_iter()
        .zip(frozen_aliases)
        .map(|((name, _), alias)| (name, alias.compact))
        .collect::<std::collections::BTreeMap<_, _>>();
    join_alpha_equivalent(
        &mut certificate,
        replayed.get("ind").expect("generated carrier"),
        frozen["ind"],
    )
    .expect("retarget selected carrier to frozen syntax");
    assert!(certificate.arena().len() > slice.prefix().len());
    assert_eq!(
        certificate.init_prefix(),
        Some((slice.prefix().addr(), slice.prefix().len()))
    );
}

#[test]
fn frozen_infinity_binder_plan_materializes_one_coherent_checked_package() {
    let init = logical_init();
    let slice = compile_init_slice(&init).expect("projected slice");
    let declaration = slice.naturals().infinity;
    let mut certificate = slice.kernel();
    let bool_ty = slice.get("bool").expect("Boolean type");
    for name in 10_000..10_016 {
        certificate
            .tm_fv(name, bool_ty)
            .expect("unrelated ambient suffix");
    }
    let package = slice
        .prove_infinity(&init, &mut certificate)
        .expect("exact userspace infinity replay");
    assert_eq!(package.declaration(), declaration);
    for (theorem, proposition) in [
        (package.axiom.theorem, declaration.axiom.exists_type),
        (package.model.theorem, declaration.model.specification),
        (package.theorem, declaration.property),
        (
            package.reflects_equality_theorem,
            declaration.reflects_equality,
        ),
        (package.avoids_missed_theorem, declaration.avoids_missed),
    ] {
        check_exact_theorem(&certificate, proposition, theorem);
    }
}

#[test]
fn frozen_infinity_replay_rejects_the_wrong_prefix_transactionally() {
    let init = logical_init();
    let slice = compile_init_slice(&init).expect("projected slice");
    let mut wrong = Kernel::new();
    wrong.star().expect("unrelated kernel");
    let before = wrong.fork();

    assert!(slice.prove_infinity(&init, &mut wrong).is_err());
    assert_eq!(wrong.arena(), before.arena());
    assert_eq!(
        wrong.thm().live_theorems().count(),
        before.thm().live_theorems().count()
    );
}

#[test]
fn frozen_subtype_package_replays_to_exact_statement_rows() {
    let init = logical_init();
    let slice = compile_init_slice(&init).expect("projected slice");
    let declaration = slice.naturals().subtype;
    let mut certificate = slice.kernel();
    let bool_ty = slice.get("bool").expect("Boolean type");
    for name in 20_000..20_016 {
        certificate
            .tm_fv(name, bool_ty)
            .expect("unrelated ambient suffix");
    }
    let package = slice
        .prove_subtype(&init, &mut certificate)
        .expect("exact userspace subtype replay");

    assert_eq!(package.declaration(), declaration);
    let axiom = package.axiom.expect("axiom evidence");
    let model = package.model.expect("model evidence");
    for (theorem, proposition) in [
        (axiom.theorem, axiom.exists_type),
        (model.theorem, declaration.model.unwrap().specification),
        (package.property_theorem.unwrap(), declaration.property),
        (package.abs_rep_theorem.unwrap(), declaration.abs_rep),
        (package.rep_abs_theorem.unwrap(), declaration.rep_abs),
        (
            package.rep_guarded_theorem.unwrap(),
            declaration.rep_guarded,
        ),
    ] {
        check_exact_theorem(&certificate, proposition, theorem);
    }
}

#[test]
fn frozen_subtype_replay_rejects_the_wrong_prefix_transactionally() {
    let init = logical_init();
    let slice = compile_init_slice(&init).expect("projected slice");
    let mut wrong = Kernel::new();
    wrong.star().expect("unrelated kernel");
    let before = wrong.fork();

    assert!(slice.prove_subtype(&init, &mut wrong).is_err());
    assert_eq!(wrong.arena(), before.arena());
    assert_eq!(
        wrong.thm().live_theorems().count(),
        before.thm().live_theorems().count()
    );
}

#[test]
fn frozen_natural_package_replays_to_exact_statement_rows() {
    let init = logical_init();
    let slice = compile_init_slice(&init).expect("projected slice");
    let declaration = *slice.naturals();
    let mut certificate = slice.kernel();
    let bool_ty = slice.get("bool").expect("Boolean type");
    for name in 30_000..30_016 {
        certificate
            .tm_fv(name, bool_ty)
            .expect("unrelated ambient suffix");
    }
    let package = slice
        .prove_naturals(&init, &mut certificate)
        .expect("exact userspace natural replay");

    assert_eq!(package.declaration, declaration);
    for (theorem, proposition) in [
        (package.proof.zero_member, declaration.zero_member),
        (package.proof.member_inhabited, declaration.member_inhabited),
        (package.proof.rep_member, declaration.rep_member),
        (package.proof.member_succ, declaration.member_succ),
        (package.proof.induction, declaration.induction),
        (package.proof.succ_injective, declaration.succ_injective),
        (package.proof.zero_ne_succ, declaration.zero_ne_succ),
    ] {
        check_exact_theorem(&certificate, proposition, theorem);
    }
}

#[test]
fn frozen_natural_replay_rejects_the_wrong_prefix_transactionally() {
    let init = logical_init();
    let slice = compile_init_slice(&init).expect("projected slice");
    let mut wrong = Kernel::new();
    wrong.star().expect("unrelated kernel");
    let before = wrong.fork();

    assert!(slice.prove_naturals(&init, &mut wrong).is_err());
    assert_eq!(wrong.arena(), before.arena());
    assert_eq!(
        wrong.thm().live_theorems().count(),
        before.thm().live_theorems().count()
    );
}

fn check_exact_theorem(
    kernel: &Kernel,
    proposition: covalence_logic_hol::Ref,
    theorem: covalence_logic_hol::ThmId,
) {
    let theorem = kernel.thm().get(theorem).expect("theorem row");
    assert!(theorem.lhs.rows().next().is_none());
    assert_eq!(
        theorem.rhs.rows().collect::<Vec<_>>(),
        vec![&[covalence_logic_hol::Lit::positive(proposition.get())][..]]
    );
}

fn check_primitive_arithmetic(
    kernel: &mut Kernel,
    naturals: &covalence_logic_hol_derived::Naturals,
    schemas: NaturalRecSchemas,
) {
    let arithmetic = kernel
        .natural_arithmetic(naturals, schemas)
        .expect("checked primitive arithmetic");
    let declaration = arithmetic.declaration;
    let proof = arithmetic.proof;
    for (proposition, theorem) in [
        (declaration.add_zero, proof.add_zero),
        (declaration.add_successor, proof.add_successor),
        (declaration.mul_zero, proof.mul_zero),
        (declaration.mul_successor, proof.mul_successor),
        (declaration.one_plus_one, proof.one_plus_one),
    ] {
        let theorem = kernel.thm().get(theorem).expect("arithmetic theorem");
        assert!(theorem.lhs.rows().next().is_none());
        assert_eq!(
            theorem.rhs.rows().collect::<Vec<_>>(),
            vec![&[covalence_logic_hol::Lit::positive(proposition.get())][..]]
        );
    }
    assert_eq!(arithmetic.get("nat.add"), Some(declaration.add));
    assert_eq!(arithmetic.get("nat.mul"), Some(declaration.mul));
    assert_eq!(arithmetic.symbols().len(), 9);
}

#[test]
fn polymorphic_schemata_cannot_leak_their_original_free_type_rows() {
    assert!(matches!(
        compile_theory(
            r"
            (define id ('a) (-> 'a 'a) (lambda x 'a x))
            (define leaked () (-> bool bool) id)
            ",
        ),
        Err(TheoryError::Invalid { .. })
    ));
    assert!(matches!(
        compile_theory(
            r"
            (define id ('a) (-> 'a 'a) (lambda x 'a x))
            (define wrong-arity () (-> bool bool) (inst id))
            ",
        ),
        Err(TheoryError::Invalid { .. })
    ));
    assert!(matches!(
        compile_theory("(define bad () bool (lambda x bool x))"),
        Err(TheoryError::TypeMismatch { .. })
    ));
}
