//! End-to-end coverage for the untrusted theory front end.

use covalence_logic_hol::{AX_INF, AX_SUB, Sort, Tag, TmTag};
use covalence_logic_hol_derived::{NaturalExt, NaturalRecExt};
use covalence_logic_hol_script::{INIT_SOURCE, TheoryError, compile_init, compile_theory};

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
    let compiled = compile_init().expect("opcode-free init source");
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
fn compiled_nat_member_drives_the_userspace_natural_package() {
    let compiled = compile_theory(INIT_SOURCE).expect("init source");
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
fn compiled_recursion_graph_has_a_checked_base_theorem() {
    let compiled = compile_theory(INIT_SOURCE).expect("init source");
    let bool_ty = compiled.bool_type();
    let natural_parameter = compiled.get("NatRecGraph/'a").expect("natural parameter");
    let codomain_parameter = compiled.get("NatRecGraph/'c").expect("codomain parameter");
    let schema = compiled.get("NatRecGraph").expect("graph schema");
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
    let graph = kernel
        .natural_rec_graph_from_schema(
            &naturals,
            natural_parameter,
            codomain_parameter,
            schema,
            bool_ty,
            base,
            step,
        )
        .expect("checked graph base");

    for (proposition, theorem) in [
        (graph.base, graph.base_theorem),
        (graph.step, graph.step_theorem),
        (graph.total, graph.total_theorem),
        (graph.has_shape, graph.has_shape_theorem),
        (graph.zero_value, graph.zero_value_theorem),
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
